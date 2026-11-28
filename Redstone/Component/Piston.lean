module

public import Redstone.Mechanics.PistonMotion

/-!
# Pistons

Java classes: `PistonBaseBlock`, `PistonHeadBlock`, `MovingPistonBlock`,
`PistonMovingBlockEntity`.

A piston base (`piston`, `sticky_piston`) looks at the signal it receives whenever a neighbour
changes (`checkIfExtend`), including the signal that reaches the position above it
(quasi-connectivity, `getNeighborSignal`), and queues a block event: 0 to extend, 1 to retract,
2 to retract while the block in front is still on its way (a sticky piston then leaves that
block behind). The block event (`triggerEvent`) moves the blocks (`moveBlocks`): every moved
block becomes a `moving_piston` block with a block entity that carries the block, and so does
the head, or the base when retracting. The block entity is ticked: two ticks later it puts the
block down (`tick`); it can be made to do so at once (`finalTick`).

Which blocks move is decided by `Redstone.PistonMotion.resolve`.

## What is left out

* Entities: a moving block pushes, carries and bounces nothing (`moveCollidedEntities`,
  `moveStuckEntities`), and has no collision shape. A block that a piston destroys drops its
  loot (`Level.dropResources`) where the moving blocks arrive; when that makes an item or an
  experience orb (the game rule `block_drops` is on), `Level.overflow` is set.
* Players: `setPlacedBy`, `PistonHeadBlock.playerWillDestroy` and `MovingPistonBlock.destroy`
  are only called when a player places or breaks a block.
* The shape of a moving block. In the game the collision shape of a `moving_piston`, and with
  it whether its faces can support a lever or a torch, depends on its block entity. The model
  knows two cases (`Level.supportAttrs`): a base that is retracting supports what the extended
  base supports, and a moved block that has arrived supports what it supports at rest. The
  head that moves back into a retracting base, and a block half way, support nothing in the
  model. Components that ask for support through a block state alone (dust, repeater,
  comparator, door) still see a `moving_piston` that supports nothing.
-/

@[expose] public section

namespace Redstone.Component.Piston

open PistonMotion
open BlockEntities.Piston (from3DDataValue get3DDataValue)

/-! ### Helpers -/

/-- The block entity at `p`, if it is a `PistonMovingBlockEntity`. -/
def movingBlockEntity? (p : Pos) : M (Option BlockEntities.Piston) := do
  match ← Level.getBlockEntity p with
  | some (.piston d) => return some d
  | _ => return none

/-- `Level.setBlockEntity(MovingPistonBlock.newMovingBlockEntity(pos, ...))`: puts the block
entity at `p` and starts ticking it. The game refuses if the block at `p` does not accept the
block entity, that is, if it is not a `moving_piston`. -/
def setBlockEntity (p : Pos) (be : BlockEntities.Piston) : M Unit := do
  if (← Level.getBlock p).is .moving_piston then
    Level.setBlockEntity p (.piston be)
    Level.addBlockEntityTicker p

/-- `Block.updateFromNeighbourShapes(state, level, pos)`: the state after a shape update from
each of the six neighbours. -/
def updateFromNeighbourShapes (state : Block) (p : Pos) : M Block :=
  Direction.shapeOrder.foldlM
    (fun s d => do
      let q := p.step d
      (← Level.behaviour s).updateShape p d q (← Level.getBlock q))
    state

/-- `level.getRandom().nextFloat()`, drawn for the pitch of the piston's sound. -/
def nextFloat : M Unit := modify fun l => { l with random := l.random.nextFloat24.2 }

/-- `PistonType` of a base: sticky or not. -/
def pistonType (id : Blocks.PistonBase.Id) : PistonType :=
  match id with
  | .sticky_piston => .sticky
  | .piston => .normal

/-! ### The moving block entity -/

/-- `PistonMovingBlockEntity.finalTick()`, for the block entity `d` at `p`: ends the motion at
once. The head of an extending piston (a source) leaves air; a moved block is put down. -/
def finalTick (p : Pos) (d : BlockEntities.Piston) : M Unit := do
  if d.progressO < 1 then
    Level.removeBlockEntity p
    if (← Level.getBlock p).is .moving_piston then
      let newState ←
        if d.isSourcePiston then pure Block.AIR else updateFromNeighbourShapes d.movedState p
      discard <| Level.setBlock p newState 3
      Level.neighborChanged p newState.id

/-- `PistonMovingBlockEntity.tick`: advances the block by half a block; once it has arrived,
removes the block entity and puts the moved block down. Entities are not moved. -/
def tick (p : Pos) : M Unit := do
  let some d ← movingBlockEntity? p | return
  let d := { d with progressO := d.progress }
  if d.progressO ≥ 1 then
    Level.removeBlockEntity p
    if (← Level.getBlock p).is .moving_piston then
      let newState ← updateFromNeighbourShapes d.movedState p
      if newState.isAir then
        discard <| Level.setBlock p d.movedState 340
        Level.updateOrDestroy d.movedState newState p 3
      else
        let newState := newState.clearWaterlogged
        discard <| Level.setBlock p newState 67
        Level.neighborChanged p newState.id
  else
    Level.setBlockEntity p (.piston { d with progress := min (d.progress + 1 / 2) 1 })

/-! ### The base -/

/-- `PistonBaseBlock.getNeighborSignal(level, pos, pushDirection)`: the piston receives a
signal from a side other than its front, or the position above it does (quasi-connectivity). -/
def getNeighborSignal (p : Pos) (pushDirection : Direction) : M Bool := do
  for direction in Direction.values do
    if direction ≠ pushDirection then
      if ← Level.hasSignal (p.step direction) direction then return true
  if ← Level.hasSignal p .down then return true
  let above := p.step .up
  for direction in Direction.values do
    if direction ≠ .down then
      if ← Level.hasSignal (above.step direction) direction then return true
  return false

/-- `new PistonStructureResolver(level, pos, direction, extending).resolve()`. -/
def resolve (p : Pos) (direction : Direction) (extending : Bool) : M (Bool × Resolver) := do
  let r := PistonMotion.resolve (← get) p direction extending
  if r.2.overflow then Level.setOverflow
  return r

/-- `PistonBaseBlock.moveBlocks(level, pistonPos, direction, extending)`: moves the blocks in
front of the piston. Returns false if they cannot move. The order of the block changes and of
the updates is the game's. -/
def moveBlocks (id : Blocks.PistonBase.Id) (pistonPos : Pos) (direction : Direction)
    (extending : Bool) : M Bool := do
  let armPos := pistonPos.step direction
  if !extending && (← Level.getBlock armPos).is .piston_head then
    discard <| Level.setBlock armPos .AIR 276
  let (ok, resolver) ← resolve pistonPos direction extending
  if !ok then return false
  let toPush := resolver.toPush
  let toPushShapes ← toPush.mapM Level.getBlock
  let toDestroy := resolver.toDestroy
  let pushDirection := if extending then direction else direction.opposite
  let mut destroyed : List Block := []
  for pos in toDestroy.reverse do
    let state ← Level.getBlock pos
    -- `dropResources(state, level, pos, blockEntity)`. What the block drops lies in the way of
    -- the moving blocks, which push it; that is not modelled.
    let entities := (← get).nextEntityIndex
    Level.dropResources state pos (← Level.peekBlockEntity pos)
    if (← get).nextEntityIndex != entities then Level.setOverflow
    discard <| Level.setBlock pos .AIR 18
    Level.gameEvent "minecraft:block_destroy" pos
    destroyed := destroyed ++ [state]
  let mut pushed : List Block := []
  for (pos, shape) in (toPush.zip toPushShapes).reverse do
    let blockState ← Level.getBlock pos
    let pos := pos.step pushDirection
    discard <| Level.setBlock pos (.movingPiston ⟨direction, .normal⟩) 324
    setBlockEntity pos
      { movedState := shape, direction, extending, isSourcePiston := false }
    pushed := pushed ++ [blockState]
  if extending then
    let type := pistonType id
    discard <| Level.setBlock armPos (.movingPiston ⟨direction, type⟩) 324
    setBlockEntity armPos
      { movedState := .pistonHead ⟨direction, false, type⟩, direction
        extending := true, isSourcePiston := true }
  -- `deleteAfterMove`: the positions that were pushed from and not pushed into, in the order
  -- of the hash map.
  let order ←
    match hashMapOrder toPush with
    | some order => pure order
    | none => do
      Level.setOverflow
      pure toPush
  let filled := toPush.map (·.step pushDirection) ++ (if extending then [armPos] else [])
  let deleteAfterMove := (order.filter (!filled.contains ·)).filterMap fun pos =>
    ((toPush.zip toPushShapes).find? (·.1 == pos))
  for (pos, _) in deleteAfterMove do
    discard <| Level.setBlock pos .AIR 82
  for (pos, oldState) in deleteAfterMove do
    (← Level.behaviour oldState).updateIndirectNeighbourShapes pos 2 512
    Level.updateNeighbourShapes .AIR pos 2
    (← Level.behaviour .AIR).updateIndirectNeighbourShapes pos 2 512
  for (pos, state) in toDestroy.reverse.zip destroyed do
    (← Level.behaviour state).affectNeighborsAfterRemoval pos false
    (← Level.behaviour state).updateIndirectNeighbourShapes pos 2 512
    Level.updateNeighborsAt pos state.id
  for (pos, state) in toPush.reverse.zip pushed do
    Level.updateNeighborsAt pos state.id
  if extending then Level.updateNeighborsAt armPos .piston_head
  return true

/-- `PistonBaseBlock.checkIfExtend(level, pos, state)`: queues the block event that extends or
retracts the piston, if its signal asks for it.

When the piston retracts while the block two in front is still being pushed by it, the game
sends event 2 (drop the block) instead of 1 if that block is less than half way
(`getProgress(0) < 0.5`, which is `progressO`), or `level.getGameTime() ==
pistonEntity.getLastTicked()`, or `isHandlingTick()`. The time of the last tick is not kept in
the block entity; `Level.tickedBlockEntities` says whether it is the current game time. It is
kept by position, which is the same thing here: a moving block that took the place of another
one in the same game tick is new, so it is less than half way anyway. -/
def checkIfExtend (id : Blocks.PistonBase.Id) (s : Blocks.PistonBase) (p : Pos) : M Unit := do
  let direction := s.facing
  let extend ← getNeighborSignal p direction
  if extend && !s.extended then
    if (← resolve p direction true).1 then
      Level.blockEvent p id.toBlockId 0 (get3DDataValue direction)
  else if !extend && s.extended then
    let pushedPos := relative p direction 2
    let mut event : ℤ := 1
    if let .movingPiston m := ← Level.getBlock pushedPos then
      if m.facing = direction then
        if let some pistonEntity ← movingBlockEntity? pushedPos then
          if pistonEntity.extending && (pistonEntity.progressO < 1 / 2
              || (← get).tickedBlockEntities.contains pushedPos || (← get).handlingTick) then
            event := 2
    Level.blockEvent p id.toBlockId event (get3DDataValue direction)

/-- `PistonBaseBlock.triggerEvent(state, level, pos, b0, b1)`: the block event `b0` of a piston:
0 extends, 1 and 2 retract. Returns whether the event was carried out. -/
def triggerEvent (id : Blocks.PistonBase.Id) (s : Blocks.PistonBase) (p : Pos) (b0 b1 : ℤ) :
    M Bool := do
  let direction := s.facing
  let extendedState : Block := .pistonBase id { s with extended := true }
  let extend ← getNeighborSignal p direction
  if extend && (b0 = 1 || b0 = 2) then
    discard <| Level.setBlock p extendedState 2
    return false
  if !extend && b0 = 0 then return false
  if b0 = 0 then
    if !(← moveBlocks id p direction true) then return false
    discard <| Level.setBlock p extendedState 67
    nextFloat
    Level.gameEvent "minecraft:block_activate" p
  else if b0 = 1 || b0 = 2 then
    let headPos := p.step direction
    if let some pistonMovingBlockEntity ← movingBlockEntity? headPos then
      finalTick headPos pistonMovingBlockEntity
    let movingPistonState : Block := .movingPiston ⟨direction, pistonType id⟩
    discard <| Level.setBlock p movingPistonState 276
    setBlockEntity p
      { movedState := .pistonBase id ⟨false, from3DDataValue (b1 % 8)⟩, direction
        extending := false, isSourcePiston := true }
    Level.updateNeighborsAt p .moving_piston
    Level.updateNeighbourShapes movingPistonState p 2
    if pistonType id = .sticky then
      let twoPos := relative p direction 2
      let movingState ← Level.getBlock twoPos
      let mut pistonPiece := false
      if movingState.is .moving_piston then
        if let some entity ← movingBlockEntity? twoPos then
          if entity.direction = direction && entity.extending then
            finalTick twoPos entity
            pistonPiece := true
      if !pistonPiece then
        if b0 ≠ 1 || movingState.isAir
            || !isPushable movingState twoPos direction.opposite false direction
            || (movingState.attrs.push ≠ .push_pull && !movingState.is .piston
              && !movingState.is .sticky_piston) then
          discard <| Level.removeBlock headPos false
        else
          discard <| moveBlocks id p direction false
    else
      discard <| Level.removeBlock headPos false
    nextFloat
    Level.gameEvent "minecraft:block_deactivate" p
  return true

/-- The behaviour of a piston base. -/
def base (id : Blocks.PistonBase.Id) (s : Blocks.PistonBase) : Behaviour :=
  let self : Block := .pistonBase id s
  { Behaviour.inert self with
    neighborChanged := fun p _ _ => checkIfExtend id s p
    onPlace := fun p oldState _ => do
      if !oldState.is self.id then
        if (← Level.getBlockEntity p).isNone then checkIfExtend id s p
    triggerEvent := triggerEvent id s }

/-! ### The head -/

/-- `PistonHeadBlock.isFittingBase(armState, potentialBase)`: the block is the extended base
of this head. -/
def isFittingBase (s : Blocks.PistonHead) (potentialBase : Block) : Bool :=
  match potentialBase with
  | .pistonBase id b => pistonType id = s.type && b.extended && b.facing = s.facing
  | _ => false

/-- `PistonHeadBlock.canSurvive`: behind the head is its base, or a moving block facing the
same way. -/
def headCanSurvive (s : Blocks.PistonHead) (l : Level) (p : Pos) : Bool :=
  let base := l.blockAt (p.step s.facing.opposite)
  isFittingBase s base ||
    match base with
    | .movingPiston m => m.facing = s.facing
    | _ => false

/-- The behaviour of a piston head. -/
def head (s : Blocks.PistonHead) : Behaviour :=
  let self : Block := .pistonHead s
  { Behaviour.inert self with
    canSurvive := headCanSurvive s
    affectNeighborsAfterRemoval := fun p _ => do
      let basePos := p.step s.facing.opposite
      if isFittingBase s (← Level.getBlock basePos) then
        discard <| Level.destroyBlock basePos true
    updateShape := fun p directionToNeighbour _ _ => do
      if directionToNeighbour.opposite = s.facing && !headCanSurvive s (← get) p then
        return .AIR
      else return self
    neighborChanged := fun p block _ => do
      if headCanSurvive s (← get) p then
        Level.neighborChanged (p.step s.facing.opposite) block }

/-! ### The moving block -/

/-- The behaviour of a `moving_piston` block. The block creates no block entity by itself
(`newBlockEntity` returns null); `moveBlocks` and `triggerEvent` add it. -/
def moving (s : Blocks.MovingPiston) : Behaviour :=
  let self : Block := .movingPiston s
  { Behaviour.inert self with
    newBlockEntity := none
    ticksBlockEntity := true
    blockEntityTick := tick
    preRemoveSideEffects := fun p => do
      if let some d ← movingBlockEntity? p then finalTick p d
    useWithoutItem := fun p _ => do
      if (← Level.getBlockEntity p).isNone then
        discard <| Level.removeBlock p false
        return true
      else return false }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .pistonBase id s => base id s
  | .pistonHead s => head s
  | .movingPiston s => moving s
  | _ => .inert self

end Redstone.Component.Piston
