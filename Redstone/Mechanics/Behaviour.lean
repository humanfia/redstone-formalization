module

public import Redstone.World.Level

/-!
# Block and entity behaviours

In the game every block class overrides some of the methods of `BlockBehaviour`: what signal the
block emits, how it reacts when a neighbour changes, what it does on a scheduled tick, and so
on. `Behaviour` is the record of these methods for one block state. Each component of the
formalization defines the behaviour of its blocks, and `Redstone.Mechanics.Dispatch` collects
them into one table.

The reactions run in the monad `M`: they read and change the `Level`, and they can reach every
other block's behaviour through the environment `Env`. This is how the mutual recursion of the
game is expressed: placing a block calls the reactions of its neighbours, which may place
blocks themselves. The environment holds the behaviours already closed over a smaller
environment, so the nesting depth is bounded; see `Redstone.Mechanics.Dispatch`.

The `orientation` argument that the game passes with neighbour updates is omitted. It is only
used by the experimental redstone wire, which is not enabled.
-/

@[expose] public section

namespace Redstone

/-- The methods of `BlockBehaviour` (and of `Block` and `EntityBlock`) that matter here, for one
block state, with reactions running in the monad `m`. Positions are always the position of the
block itself. -/
structure BehaviourOf (m : Type → Type) where
  /-- `getSignal(state, level, pos, direction)`: the signal the block gives to its neighbour in
  direction `direction.opposite`; `direction` points from that neighbour to the block. -/
  signal : Level → Pos → Direction → ℕ
  /-- `ownSignal(state, level, pos)`: the signal of the block as a source, whatever the
  direction. `BlockBehaviour.getSignal` returns it by default. -/
  ownSignal : Level → Pos → ℕ
  /-- `getDirectSignal`: as `signal`, but only the strong power, which conductors pass on. -/
  directSignal : Level → Pos → Direction → ℕ
  /-- `getAnalogOutputSignal`: what a comparator reads from the block. -/
  analogSignal : Level → Pos → Direction → ℕ
  /-- `canSurvive`: the block can stay where it is. -/
  canSurvive : Level → Pos → Bool
  /-- `newBlockEntity`: the block entity created with the block, if it has one. -/
  newBlockEntity : Option BlockEntity
  /-- `shouldChangedStateKeepBlockEntity(oldState)`: when the block replaces `oldState`, a block
  of another kind, the block entity that was there is kept. -/
  keepsBlockEntity : Block → Bool
  /-- `getTicker` is not null: the block's block entity is ticked every game tick. -/
  ticksBlockEntity : Bool
  /-- `neighborChanged(state, level, pos, block, orientation, movedByPiston)`: a neighbour update.
  `block` is the block that changed. -/
  neighborChanged : Pos → BlockId → Bool → m Unit
  /-- `onPlace(state, level, pos, oldState, movedByPiston)`. -/
  onPlace : Pos → Block → Bool → m Unit
  /-- `affectNeighborsAfterRemoval(state, level, pos, movedByPiston)`. -/
  affectNeighborsAfterRemoval : Pos → Bool → m Unit
  /-- `updateShape(state, level, ticks, pos, direction, neighborPos, neighborState, random)`: a
  shape update. Returns the state the block should take. -/
  updateShape : Pos → Direction → Pos → Block → m Block
  /-- `updateIndirectNeighbourShapes(state, level, pos, flags, limit)`. -/
  updateIndirectNeighbourShapes : Pos → ℕ → ℕ → m Unit
  /-- `tick(state, level, pos, random)`: a scheduled tick. -/
  tick : Pos → m Unit
  /-- `randomTick(state, level, pos, random)`: a random tick. The game only gives random ticks
  to states with `isRandomlyTicking` (`Attrs.randomlyTicks`). -/
  randomTick : Pos → m Unit
  /-- `triggerEvent(state, level, pos, a, b)`: a block event. -/
  triggerEvent : Pos → ℤ → ℤ → m Bool
  /-- `useWithoutItem(state, level, pos, player, hit)`: a player uses the block with an empty
  hand on the given face. Returns whether the block reacted. -/
  useWithoutItem : Pos → Direction → m Bool
  /-- `useItemOn`: a player uses the item with the given name on the block. Returns whether the
  block consumed the action. -/
  useItemOn : Pos → Direction → String → m Bool
  /-- Whether `useItemOn` with this item on this face, when it does not consume the action,
  answers `TRY_WITH_EMPTY_HAND` (as `BlockBehaviour.useItemOn` does) rather than `PASS`: the
  game then tries `useWithoutItem`. -/
  tryEmptyHand : Direction → String → Bool
  /-- `entityInside(state, level, pos, entity, ...)`: the entity with the given index touches
  the inside of the block. -/
  entityInside : Pos → ℕ → m Unit
  /-- `stepOn(level, pos, state, entity)`: the entity walks on the block. -/
  stepOn : Pos → ℕ → m Unit
  /-- `onProjectileHit(level, state, hit, projectile)`: the projectile with the given index hits
  the given face at the given point (`BlockHitResult.getLocation`). -/
  onProjectileHit : Pos → Direction → Vec3 → ℕ → m Unit
  /-- `onExplosionHit(state, level, pos, explosion, ...)`. -/
  onExplosionHit : Pos → m Unit
  /-- `BlockEntity.preRemoveSideEffects(pos, state)`: called before the block entity is removed
  because the block was replaced. -/
  preRemoveSideEffects : Pos → m Unit
  /-- The block entity's ticker (`BlockEntityTicker.tick`), run once per game tick when
  `ticksBlockEntity` holds. -/
  blockEntityTick : Pos → m Unit

/-- `GameEvent.Context`: what comes with a game event. -/
structure GameEventContext where
  /-- `sourceEntity`: the entity that caused the event. -/
  sourceEntity : Option GameEventSource := none
  /-- `affectedState`: the block state the event is about. -/
  affectedState : Option Block := none

/-- The methods of `Entity` that matter here, for one entity. -/
structure EntityBehaviourOf (m : Type → Type) where
  /-- `tick()`: what the entity with the given index does in a game tick. -/
  tick : ℕ → m Unit

/-- What a reaction can reach besides the level: the behaviour of every block and entity, with
the reactions given as plain state transformers. -/
structure Env where
  /-- The behaviour of a block state. -/
  block : Block → BehaviourOf (StateM Level)
  /-- The behaviour of an entity. -/
  entity : Entity → EntityBehaviourOf (StateM Level)
  /-- `Level.gameEvent`: something happened at a position that vibration listeners may hear. The
  event is given by its registry name. -/
  gameEvent : String → Pos → GameEventContext → StateM Level Unit

/-- The monad of reactions: a reader of the environment over a state of the level. -/
abbrev M := ReaderT Env (StateM Level)

/-- The behaviour of a block state, as components define it. -/
abbrev Behaviour := BehaviourOf M

/-- The behaviour of an entity, as components define it. -/
abbrev EntityBehaviour := EntityBehaviourOf M

namespace Behaviour

/-- The behaviour of a block that does nothing: no signal, no reaction, and the block entity
the game creates for the block. It is the behaviour of `BlockBehaviour` itself, and the base
that components override. -/
def inert (self : Block) : Behaviour where
  signal _ _ _ := 0
  ownSignal _ _ := 0
  directSignal _ _ _ := 0
  analogSignal _ _ _ := 0
  canSurvive _ _ := true
  newBlockEntity := BlockEntity.new? self.id
  keepsBlockEntity _ := false
  ticksBlockEntity := false
  neighborChanged _ _ _ := pure ()
  onPlace _ _ _ := pure ()
  affectNeighborsAfterRemoval _ _ := pure ()
  updateShape _ _ _ _ := pure self
  updateIndirectNeighbourShapes _ _ _ := pure ()
  tick _ := pure ()
  randomTick _ := pure ()
  triggerEvent _ _ _ := pure false
  useWithoutItem _ _ := pure false
  useItemOn _ _ _ := pure false
  tryEmptyHand _ _ := true
  entityInside _ _ := pure ()
  stepOn _ _ := pure ()
  onProjectileHit _ _ _ _ := pure ()
  onExplosionHit _ := pure ()
  preRemoveSideEffects _ := pure ()
  blockEntityTick _ := pure ()

/-- Closes a behaviour over an environment. -/
def close (b : Behaviour) (env : Env) : BehaviourOf (StateM Level) where
  signal := b.signal
  ownSignal := b.ownSignal
  directSignal := b.directSignal
  analogSignal := b.analogSignal
  canSurvive := b.canSurvive
  newBlockEntity := b.newBlockEntity
  keepsBlockEntity := b.keepsBlockEntity
  ticksBlockEntity := b.ticksBlockEntity
  neighborChanged p s m := (b.neighborChanged p s m).run env
  onPlace p o m := (b.onPlace p o m).run env
  affectNeighborsAfterRemoval p m := (b.affectNeighborsAfterRemoval p m).run env
  updateShape p d q s := (b.updateShape p d q s).run env
  updateIndirectNeighbourShapes p f n := (b.updateIndirectNeighbourShapes p f n).run env
  tick p := (b.tick p).run env
  randomTick p := (b.randomTick p).run env
  triggerEvent p x y := (b.triggerEvent p x y).run env
  useWithoutItem p d := (b.useWithoutItem p d).run env
  useItemOn p d i := (b.useItemOn p d i).run env
  tryEmptyHand := b.tryEmptyHand
  entityInside p e := (b.entityInside p e).run env
  stepOn p e := (b.stepOn p e).run env
  onProjectileHit p d v e := (b.onProjectileHit p d v e).run env
  onExplosionHit p := (b.onExplosionHit p).run env
  preRemoveSideEffects p := (b.preRemoveSideEffects p).run env
  blockEntityTick p := (b.blockEntityTick p).run env

/-- A behaviour whose reactions do nothing but record that the nesting bound was reached. Its
signals are those of `b`, since reading a signal never nests. -/
def exhausted (b : Behaviour) : BehaviourOf (StateM Level) :=
  let stop {α : Type} (a : α) : StateM Level α := do
    modify fun l => { l with overflow := true }
    pure a
  { signal := b.signal
    ownSignal := b.ownSignal
    directSignal := b.directSignal
    analogSignal := b.analogSignal
    canSurvive := b.canSurvive
    newBlockEntity := b.newBlockEntity
    keepsBlockEntity := b.keepsBlockEntity
    ticksBlockEntity := b.ticksBlockEntity
    neighborChanged := fun _ _ _ => stop ()
    onPlace := fun _ _ _ => stop ()
    affectNeighborsAfterRemoval := fun _ _ => stop ()
    updateShape := fun _ _ _ s => stop s
    updateIndirectNeighbourShapes := fun _ _ _ => stop ()
    tick := fun _ => stop ()
    randomTick := fun _ => stop ()
    triggerEvent := fun _ _ _ => stop false
    useWithoutItem := fun _ _ => stop false
    useItemOn := fun _ _ _ => stop false
    tryEmptyHand := b.tryEmptyHand
    entityInside := fun _ _ => stop ()
    stepOn := fun _ _ => stop ()
    onProjectileHit := fun _ _ _ _ => stop ()
    onExplosionHit := fun _ => stop ()
    preRemoveSideEffects := fun _ => stop ()
    blockEntityTick := fun _ => stop () }

end Behaviour

namespace EntityBehaviour

/-- The behaviour of an entity that does nothing. -/
def inert : EntityBehaviour := ⟨fun _ => pure ()⟩

/-- Closes an entity behaviour over an environment. -/
def close (b : EntityBehaviour) (env : Env) : EntityBehaviourOf (StateM Level) :=
  ⟨fun i => (b.tick i).run env⟩

end EntityBehaviour

/-- The tables that components fill in: the behaviour of every block state and entity, and the
reaction to game events. -/
structure Rules where
  block : Block → Behaviour
  entity : Entity → EntityBehaviour
  gameEvent : String → Pos → GameEventContext → M Unit

namespace Rules

/-- The environment in which reactions may nest `depth` deep. At depth zero every reaction
stops and sets `Level.overflow`.

The behaviour of a block is looked up through `Block.pinned`, which changes nothing
(`Block.pinned_eq`) but lets the kernel look up the behaviour of air, or of stone, once in an
evaluation and not once for every cell that holds it: the lookup was a quarter of the kernel's
time in a neighbour update of redstone dust (`docs/proof-feasibility.md`). -/
def env (r : Rules) : ℕ → Env
  | 0 =>
    { block := fun b => (r.block b).exhausted
      entity := fun _ => ⟨fun _ => modify fun l => { l with overflow := true }⟩
      gameEvent := fun _ _ _ => modify fun l => { l with overflow := true } }
  | depth + 1 =>
    { block := fun b => b.pinned fun b => (r.block b).close (r.env depth)
      entity := fun e => (r.entity e).close (r.env depth)
      gameEvent := fun n p c => (r.gameEvent n p c).run (r.env depth) }

end Rules

end Redstone
