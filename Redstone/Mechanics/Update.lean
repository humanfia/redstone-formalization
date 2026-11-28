module

public import Redstone.Mechanics.Behaviour
public import Redstone.Entity.Tnt.Tables

/-!
# Changing blocks, and the updates that follow

The operations of `Level` through which blocks act on the world: `setBlock` with its update
flags, neighbour updates, shape updates, scheduling ticks and block events. They follow
`Level.setBlock`, `LevelChunk.setBlockState` and `CollectingNeighborUpdater`.

## The neighbour updater

Updates are not delivered recursively. The first update requested starts the updater, which
then runs until nothing is left; updates requested meanwhile are collected and run later, most
recent request first, as `CollectingNeighborUpdater` does. In the game this is a loop inside
the first call. Here the operations that request updates are first written against an abstract
action `kick`, "run the updater if it was idle" (namespace `Level.Core`); the loop `runUpdates`
is then defined using them with a `kick` that does nothing, which is right because the updater
is busy for as long as the loop runs; and finally the operations are given their real meaning
by taking `kick := runUpdates`.

## What is left out

* Drops: destroying a block drops nothing.
* `setBlock` on a cell of an empty chunk section fails in the game when the new state is air.
  Here it only fails when the state does not change, which differs for the three kinds of air.
* Light, heightmaps and points of interest.
-/

@[expose] public section

namespace Redstone

/-! ### Update flags

The flags of `setBlock` (`Block.UPDATE_*`), as bit positions. -/

namespace UpdateFlag

/-- Send neighbour updates. -/
def neighbors : ℕ := 0
/-- Do not send shape updates. -/
def knownShape : ℕ := 4
/-- Do not drop items when a shape update destroys a block. -/
def suppressDrops : ℕ := 5
/-- The block is being moved by a piston. -/
def moveByPiston : ℕ := 6
/-- Redstone wire ignores the shape updates. -/
def skipShapeUpdateOnWire : ℕ := 7
/-- Do not run the side effects of removing a block entity. -/
def skipBlockEntitySideEffects : ℕ := 8
/-- Do not call `onPlace`. -/
def skipOnPlace : ℕ := 9

/-- `UPDATE_ALL`: neighbour updates and shape updates. The default of `setBlock`. -/
def all : ℕ := 3

end UpdateFlag

/-- `max-chained-neighbor-updates`: updates requested beyond this number in one run of the
updater are dropped. -/
def maxChainedNeighborUpdates : ℕ := 1000000

namespace Level

/-! ### Reading -/

/-- The block at `p`. -/
def getBlock (p : Pos) : M Block := return (← get).blockAt p

/-- The closed behaviour of a block state. -/
def behaviour (b : Block) : M (BehaviourOf (StateM Level)) := return (← read).block b

/-- Records that a bound of the model was reached. -/
def setOverflow : M Unit := modify fun l => { l with overflow := true }

/-! ### Block entities -/

/-- The block entity at `p`. -/
def getBlockEntity (p : Pos) : M (Option BlockEntity) := return (← get).blockEntities p

/-- Replaces the data of the block entity at `p`. -/
def setBlockEntity (p : Pos) (be : BlockEntity) : M Unit :=
  modify fun l => { l with blockEntities := Function.update l.blockEntities p (some be) }

/-- Stops ticking the block entity at `p`. -/
def removeBlockEntityTicker (p : Pos) : M Unit :=
  modify fun l => { l with
    blockEntityTickers := l.blockEntityTickers.erase p
    pendingBlockEntityTickers := l.pendingBlockEntityTickers.erase p }

/-- Starts ticking the block entity at `p`, unless it is ticked already. A ticker added while
block entities are being ticked starts on the next game tick. -/
def addBlockEntityTicker (p : Pos) : M Unit :=
  modify fun l =>
    if l.blockEntityTickers.contains p || l.pendingBlockEntityTickers.contains p then l
    else if l.tickingBlockEntities then
      { l with pendingBlockEntityTickers := l.pendingBlockEntityTickers ++ [p] }
    else { l with blockEntityTickers := l.blockEntityTickers ++ [p] }

/-- Removes the block entity at `p`. -/
def removeBlockEntity (p : Pos) : M Unit := do
  modify fun l => { l with blockEntities := Function.update l.blockEntities p none }
  removeBlockEntityTicker p

/-! ### Scheduled ticks and block events -/

/-- `scheduleTick(pos, block, delay, priority)`. Nothing is scheduled if a tick of the same
block at the same position is already waiting. -/
def scheduleTick (p : Pos) (block : BlockId) (delay : ℕ) (priority : TickPriority := .normal) :
    M Unit :=
  modify fun l =>
    let t : ScheduledTick := ⟨p, block, l.gameTime + delay, priority, l.subTickCount⟩
    let l := { l with subTickCount := l.subTickCount + 1 }
    if l.hasScheduledTick p block then l else { l with ticks := l.ticks ++ [t] }

/-- `blockEvent(pos, block, a, b)`: queues a block event, unless the same one is queued. -/
def blockEvent (p : Pos) (block : BlockId) (a b : ℤ) : M Unit :=
  modify fun l =>
    let e : BlockEvent := ⟨p, block, a, b⟩
    if l.blockEvents.contains e then l else { l with blockEvents := l.blockEvents ++ [e] }

/-- `gameEvent(event, pos, context)`: announces an event to vibration listeners. -/
def gameEvent (event : String) (p : Pos) (context : GameEventContext := {}) : M Unit := do
  (← read).gameEvent event p context

/-! ### Entities -/

/-- Adds an entity and returns its index. -/
def addEntity (base : Entities.Base) (data : EntityData) : M ℕ :=
  modifyGet fun l =>
    (l.nextEntityIndex,
      { l with
        entities := l.entities ++ [⟨l.nextEntityIndex, base, data⟩]
        nextEntityIndex := l.nextEntityIndex + 1 })

/-- Removes the entity with the given index. -/
def removeEntity (index : ℕ) : M Unit :=
  modify fun l => { l with entities := l.entities.filter (·.index != index) }

/-- Changes the entity with the given index. -/
def modifyEntity (index : ℕ) (f : Entity → Entity) : M Unit :=
  modify fun l =>
    { l with entities := l.entities.map fun e => if e.index == index then f e else e }

/-! ### Drops -/

/-- `Block.dropResources(state, level, pos, blockEntity, breaker, tool)` in a world where the
game rule `block_drops` is off: nothing is dropped, but `Block.popResource` draws the three
coordinates of every stack of the block's loot from the level's random number generator before
it finds that out. A block whose loot is not a function of its state sets `Level.overflow`. -/
def dropResources (state : Block) : M Unit :=
  match Entity.Tnt.brokenDropStacks state with
  | some n => modify fun l => { l with random := (·.nextDouble53.2)^[3 * n] l.random }
  | none => setOverflow

/-! ### Operations that request updates -/

/-- Adds an update to the neighbour updater (the first half of `addAndRun`). Returns whether
the updater was idle, in which case the caller has to run it. -/
def enqueueUpdate (u : NeighborUpdate) : M Bool :=
  modifyGet fun l =>
    let idle := l.updateCount == 0
    let l' := { l with updateCount := l.updateCount + 1 }
    if l.updateCount ≥ maxChainedNeighborUpdates then (idle, l')
    else if idle then (idle, { l' with updateStack := u :: l'.updateStack })
    else (idle, { l' with updatesAdded := l'.updatesAdded ++ [u] })

namespace Core

variable (kick : M Unit)

/-- `addAndRun`. -/
def addAndRun (u : NeighborUpdate) : M Unit := do
  if ← enqueueUpdate u then kick

/-- `updateNeighborsAtExceptFromFacing(pos, block, skip)`: tells the six neighbours of `p`,
except the one in direction `skip`, that `block` changed. -/
def updateNeighborsAtExceptFromFacing (p : Pos) (block : BlockId) (skip : Option Direction) :
    M Unit :=
  addAndRun kick (.multi p block skip (if Direction.updateOrder.head? = skip then 1 else 0))

/-- `updateNeighborsAt(pos, block)`: tells the six neighbours of `p` that `block` changed. -/
def updateNeighborsAt (p : Pos) (block : BlockId) : M Unit :=
  updateNeighborsAtExceptFromFacing kick p block none

/-- `neighborChanged(pos, block, orientation)`: tells the block at `p` that `block` changed. -/
def neighborChanged (p : Pos) (block : BlockId) : M Unit := addAndRun kick (.simple p block)

/-- `neighborChanged(state, pos, block, orientation, movedByPiston)`: as `neighborChanged`, but
the update is delivered to the behaviour of `state`. -/
def neighborChangedFor (state : Block) (p : Pos) (block : BlockId) (movedByPiston : Bool) :
    M Unit :=
  addAndRun kick (.full state p block movedByPiston)

/-- `neighborShapeChanged(direction, pos, neighborPos, neighborState, flags, limit)`: a shape
update for the block at `p`, whose neighbour in direction `dir` has become `neighborState`. -/
def neighborShapeChanged (dir : Direction) (p neighborPos : Pos) (neighborState : Block)
    (flags limit : ℕ) : M Unit :=
  addAndRun kick (.shape dir neighborState p neighborPos flags limit)

/-- `BlockState.updateNeighbourShapes(level, pos, flags, limit)`: shape updates for the six
neighbours of the block `state` at `p`. -/
def updateNeighbourShapes (state : Block) (p : Pos) (flags limit : ℕ) : M Unit :=
  Direction.shapeOrder.forM fun d =>
    neighborShapeChanged kick d.opposite (p.step d) p state flags limit

/-- `updateNeighbourForOutputSignal(pos, block)`: tells the comparators that read the block at
`p`, directly or through a conductor, that it changed. -/
def updateNeighbourForOutputSignal (p : Pos) (block : BlockId) : M Unit :=
  Direction.horizontals.forM fun d => do
    let q := p.step d
    let s ← getBlock q
    if s.is .comparator then neighborChangedFor kick s q block false
    else if s.isConductor then
      let q := q.step d
      let s ← getBlock q
      if s.is .comparator then neighborChangedFor kick s q block false

/-- `LevelChunk.setBlockState(pos, state, flags)`: puts `state` at `p`, takes care of the block
entity and runs `affectNeighborsAfterRemoval` and `onPlace`. Returns the old state, or `none`
if nothing was done or the block was replaced again meanwhile. -/
def setBlockInChunk (p : Pos) (state : Block) (flags : ℕ) : M (Option Block) := do
  let old ← getBlock p
  if old = state then return none
  modify (·.setBlockRaw p state)
  let blockChanged := old.id != state.id
  let moved := flags.testBit UpdateFlag.moveByPiston
  let oldB ← behaviour old
  let newB ← behaviour state
  if blockChanged && old.hasBlockEntity && !newB.keepsBlockEntity old then
    if !flags.testBit UpdateFlag.skipBlockEntitySideEffects && (← getBlockEntity p).isSome then
      oldB.preRemoveSideEffects p
    removeBlockEntity p
  if (blockChanged || state.isRail) && (flags.testBit UpdateFlag.neighbors || moved) then
    oldB.affectNeighborsAfterRemoval p moved
  if !(← getBlock p).is state.id then return none
  if !flags.testBit UpdateFlag.skipOnPlace then newB.onPlace p old moved
  if state.hasBlockEntity && (← getBlock p).is state.id then
    let valid (be : BlockEntity) := (BlockEntity.new? state.id).any (·.typeName == be.typeName)
    if ((← getBlockEntity p).any valid) then
      if newB.ticksBlockEntity then addBlockEntityTicker p else removeBlockEntityTicker p
    else
      removeBlockEntity p
      if let some be := newB.newBlockEntity then
        setBlockEntity p be
        if newB.ticksBlockEntity then addBlockEntityTicker p
  return some old

/-- `Level.setBlock(pos, state, flags, limit)`. Returns whether the block was changed. -/
def setBlock (p : Pos) (state : Block) (flags : ℕ := UpdateFlag.all) (limit : ℕ := 512) :
    M Bool := do
  let some old ← setBlockInChunk p state flags | return false
  if (← getBlock p) = state then
    if flags.testBit UpdateFlag.neighbors then
      updateNeighborsAt kick p old.id
      if state.attrs.analog then updateNeighbourForOutputSignal kick p state.id
    if !flags.testBit UpdateFlag.knownShape && limit > 0 then
      -- `flags & ~(UPDATE_NEIGHBORS | UPDATE_SUPPRESS_DROPS)`
      let flags := flags &&& 0x3de
      (← behaviour old).updateIndirectNeighbourShapes p flags (limit - 1)
      updateNeighbourShapes kick state p flags (limit - 1)
      (← behaviour state).updateIndirectNeighbourShapes p flags (limit - 1)
  return true

/-- `Level.destroyBlock(pos, drop, breaker, limit)`: breaks the block at `p`. Nothing is
dropped, whatever `drop` says, but with `drop` the level's random number generator advances
as it does in the game (`dropResources`). Returns whether a block was broken. -/
def destroyBlock (p : Pos) (drop : Bool) (limit : ℕ := 512) : M Bool := do
  let state ← getBlock p
  if state.isAir then return false
  if drop then dropResources state
  let destroyed ← setBlock kick p state.fluidBlock UpdateFlag.all limit
  if destroyed then gameEvent "minecraft:block_destroy" p { affectedState := some state }
  return destroyed

/-- `Level.removeBlock(pos, movedByPiston)`. -/
def removeBlock (p : Pos) (movedByPiston : Bool) : M Bool := do
  setBlock kick p (← getBlock p).fluidBlock (if movedByPiston then 67 else 3)

/-- `Block.updateOrDestroy(state, newState, level, pos, flags, limit)`. -/
def updateOrDestroy (state newState : Block) (p : Pos) (flags limit : ℕ) : M Unit := do
  if newState ≠ state then
    if newState.isAir then
      discard <| destroyBlock kick p (!flags.testBit UpdateFlag.suppressDrops) limit
    else
      -- `flags & ~UPDATE_SUPPRESS_DROPS`
      discard <| setBlock kick p newState (flags &&& 0x3df) limit

/-- `NeighborUpdater.executeShapeUpdate`: delivers a shape update. -/
def executeShapeUpdate (dir : Direction) (p neighborPos : Pos) (neighborState : Block)
    (flags limit : ℕ) : M Unit := do
  let cur ← getBlock p
  if flags.testBit UpdateFlag.skipShapeUpdateOnWire && cur.is .redstone_wire then return
  let new ← (← behaviour cur).updateShape p dir neighborPos neighborState
  updateOrDestroy kick cur new p flags limit

/-- `NeighborUpdates.runNext`: runs the next step of an update. Returns the update with which
to continue, or `none` when it is finished. -/
def runNext : NeighborUpdate → M (Option NeighborUpdate)
  | .shape dir neighborState p neighborPos flags limit => do
    executeShapeUpdate kick dir p neighborPos neighborState flags limit
    return none
  | .simple p block => do
    (← behaviour (← getBlock p)).neighborChanged p block false
    return none
  | .full state p block moved => do
    (← behaviour state).neighborChanged p block moved
    return none
  | .multi source block skip idx => do
    let some d := Direction.updateOrder[idx]? | return none
    let q := source.step d
    (← behaviour (← getBlock q)).neighborChanged q block false
    let idx := idx + 1
    let idx := if skip.isSome && Direction.updateOrder[idx]? = skip then idx + 1 else idx
    if idx < Direction.updateOrder.length then return some (.multi source block skip idx)
    else return none

end Core

/-! ### The updater's loop -/

/-- The loop of `CollectingNeighborUpdater.runUpdates`, bounded by `fuel` steps. Each step
moves the updates added meanwhile to the top of the stack, first added on top, and runs the
next step of the update that is then on top. -/
def runUpdatesLoop : ℕ → M Unit
  | 0 =>
    modify fun l =>
      { l with updateStack := [], updatesAdded := [], updateCount := 0, overflow := true }
  | fuel + 1 => do
    let l ← get
    match l.updatesAdded ++ l.updateStack with
    | [] => set { l with updateStack := [], updatesAdded := [], updateCount := 0 }
    | u :: rest =>
      set { l with updateStack := u :: rest, updatesAdded := [] }
      let next ← Core.runNext setOverflow u
      modify fun l => { l with updateStack := next.toList ++ rest }
      runUpdatesLoop fuel

/-- Runs the neighbour updater until nothing is left. Every update takes at most six steps and
at most `maxChainedNeighborUpdates` updates are accepted, so the bound is never reached. -/
def runUpdates : M Unit := runUpdatesLoop (6 * maxChainedNeighborUpdates + 1)

/-! ### The operations, with the updater in place -/

@[inherit_doc Core.updateNeighborsAt]
def updateNeighborsAt (p : Pos) (block : BlockId) : M Unit :=
  Core.updateNeighborsAt runUpdates p block

@[inherit_doc Core.updateNeighborsAtExceptFromFacing]
def updateNeighborsAtExceptFromFacing (p : Pos) (block : BlockId) (skip : Option Direction) :
    M Unit :=
  Core.updateNeighborsAtExceptFromFacing runUpdates p block skip

@[inherit_doc Core.neighborChanged]
def neighborChanged (p : Pos) (block : BlockId) : M Unit := Core.neighborChanged runUpdates p block

@[inherit_doc Core.neighborChangedFor]
def neighborChangedFor (state : Block) (p : Pos) (block : BlockId) (movedByPiston : Bool) :
    M Unit :=
  Core.neighborChangedFor runUpdates state p block movedByPiston

@[inherit_doc Core.updateNeighbourShapes]
def updateNeighbourShapes (state : Block) (p : Pos) (flags : ℕ) (limit : ℕ := 512) : M Unit :=
  Core.updateNeighbourShapes runUpdates state p flags limit

@[inherit_doc Core.updateNeighbourForOutputSignal]
def updateNeighbourForOutputSignal (p : Pos) (block : BlockId) : M Unit :=
  Core.updateNeighbourForOutputSignal runUpdates p block

@[inherit_doc Core.setBlock]
def setBlock (p : Pos) (state : Block) (flags : ℕ := UpdateFlag.all) (limit : ℕ := 512) : M Bool :=
  Core.setBlock runUpdates p state flags limit

@[inherit_doc Core.destroyBlock]
def destroyBlock (p : Pos) (drop : Bool) (limit : ℕ := 512) : M Bool :=
  Core.destroyBlock runUpdates p drop limit

@[inherit_doc Core.removeBlock]
def removeBlock (p : Pos) (movedByPiston : Bool) : M Bool :=
  Core.removeBlock runUpdates p movedByPiston

@[inherit_doc Core.updateOrDestroy]
def updateOrDestroy (state newState : Block) (p : Pos) (flags : ℕ) (limit : ℕ := 512) : M Unit :=
  Core.updateOrDestroy runUpdates state newState p flags limit

/-! ### Players -/

/-- A player uses the block at `p` with an empty hand on the given face. -/
def useWithoutItem (p : Pos) (face : Direction) : M Bool := do
  (← behaviour (← getBlock p)).useWithoutItem p face

/-- A player uses the item named `item` on the given face of the block at `p`. -/
def useItemOn (p : Pos) (face : Direction) (item : String) : M Bool := do
  (← behaviour (← getBlock p)).useItemOn p face item

end Level

end Redstone
