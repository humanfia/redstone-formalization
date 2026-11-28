module

public import Redstone.Mechanics.Tick

/-!
# Comparator

Java classes: `ComparatorBlock`, with the part of `DiodeBlock` it inherits, and
`ComparatorBlockEntity`.

A comparator reads a signal at its back (the side its `facing` property names), compares it
with the signals at its two sides, and emits the result at its front. The result is kept in
the block entity; the block state only records whether the comparator is on and its mode. A
change of the inputs takes effect through a scheduled tick two game ticks later.

The input is the redstone signal of the block behind, or the level of redstone wire there; if
that block can be measured (`hasAnalogOutputSignal`) its measure replaces the signal; if it is
a conductor that gives less than 15, the measure of the block behind it replaces the signal.

## What is left out

* Item frames. Behind a conductor the game also looks for a single item frame facing the
  comparator and reads its `getAnalogOutput`. The model's entities do not keep the direction
  or the content of an item frame, so `inputSignal` here behaves as if there were none.
* `setPlacedBy` (a tick scheduled when a player places a comparator that should be on): placing
  blocks from items is not modelled.
* Sounds and item drops.
-/

@[expose] public section

namespace Redstone.Component.Comparator

/-- `Direction.getClockWise` for horizontal directions; the vertical ones are left alone. -/
def clockWise : Direction → Direction
  | .north => .east
  | .east => .south
  | .south => .west
  | .west => .north
  | d => d

/-- `Direction.getCounterClockWise` for horizontal directions. -/
def counterClockWise : Direction → Direction
  | .north => .west
  | .west => .south
  | .south => .east
  | .east => .north
  | d => d

/-- The value of `FACING`: the direction from the comparator to the block it reads. -/
def facing (s : Blocks.Comparator) : Direction := s.facing.toDirection

/-- `DiodeBlock.isDiode(state)`: the block is a repeater or a comparator. If so, its `FACING`. -/
def diodeFacing? : Block → Option Direction
  | .repeater s => some s.facing.toDirection
  | .comparator s => some s.facing.toDirection
  | _ => none

/-- `ComparatorBlockEntity.getOutputSignal` of the block entity at `p`, or 0 if there is no
comparator block entity there (`ComparatorBlock.getOutputSignal`). -/
def outputSignal (l : Level) (p : Pos) : ℕ :=
  match l.blockEntities p with
  | some (.comparator d) => d.output
  | _ => 0

/-- `DiodeBlock.ownSignal`: the stored output while the comparator is powered. -/
def ownSignal (s : Blocks.Comparator) (l : Level) (p : Pos) : ℕ :=
  if s.powered then outputSignal l p else 0

/-- `DiodeBlock.getSignal`: the comparator gives its signal only to the block in front of it,
which asks in the direction `FACING`. `getDirectSignal` is the same. -/
def signal (s : Blocks.Comparator) (l : Level) (p : Pos) (d : Direction) : ℕ :=
  if facing s = d then ownSignal s l p else 0

/-- `DiodeBlock.canSurviveOn`: the top face of the block below is sturdy (`SupportType.RIGID`). -/
def canSurviveOn (below : Block) : Bool := below.attrs.isFaceSturdyRigid .up

/-- `DiodeBlock.canSurvive`. -/
def canSurvive (l : Level) (p : Pos) : Bool := canSurviveOn (l.blockAt (p.step .down))

/-- The value of `RedstoneWireBlock.POWER` if the block is redstone wire, else 0. -/
def wirePower : Block → ℕ
  | .redstoneWire w => w.power.val
  | _ => 0

/-- `DiodeBlock.getInputSignal`: the signal the block behind gives, or the level of redstone
wire there if that is more. -/
def diodeInputSignal (s : Blocks.Comparator) (p : Pos) : M ℕ := do
  let d := facing s
  let target := p.step d
  let input ← Level.getSignal target d
  if input ≥ 15 then return input
  return max input (wirePower (← Level.getBlock target))

/-- `ComparatorBlock.getInputSignal`: the input of `DiodeBlock`, replaced by the measure of the
block behind if it has one, or else, if that block is a conductor and the input is below 15, by
the measure of the block behind it if that has one. Item frames are not read. -/
def inputSignal (s : Blocks.Comparator) (p : Pos) : M ℕ := do
  let result ← diodeInputSignal s p
  let d := facing s
  let targetPos := p.step d
  let target ← Level.getBlock targetPos
  if target.attrs.analog then
    return (← Level.behaviour target).analogSignal (← get) targetPos d.opposite
  else if result < 15 && target.isConductor then
    let targetPos := targetPos.step d
    let target ← Level.getBlock targetPos
    if target.attrs.analog then
      return (← Level.behaviour target).analogSignal (← get) targetPos d.opposite
    else return result
  else return result

/-- `SignalGetter.getControlInputSignal(pos, direction, false)`: what the block at `p` gives to
the side of a diode: 15 for a block of redstone, the level of redstone wire, the direct signal
of any other signal source, and nothing otherwise. -/
def controlInputSignal (p : Pos) (d : Direction) : M ℕ := do
  let b ← Level.getBlock p
  if b.is .redstone_block then return 15
  else if b.is .redstone_wire then return wirePower b
  else if b.attrs.signalSource then Level.getDirectSignal p d
  else return 0

/-- `DiodeBlock.getAlternateSignal`: the stronger of the two side inputs. -/
def alternateSignal (s : Blocks.Comparator) (p : Pos) : M ℕ := do
  let cw := clockWise (facing s)
  let ccw := counterClockWise (facing s)
  return max (← controlInputSignal (p.step cw) cw) (← controlInputSignal (p.step ccw) ccw)

/-- `ComparatorBlock.calculateOutputSignal`: nothing if there is no input or the side input is
stronger; otherwise the input, less the side input in subtract mode. -/
def calculateOutputSignal (s : Blocks.Comparator) (p : Pos) : M ℕ := do
  let input ← inputSignal s p
  if input = 0 then return 0
  let alternate ← alternateSignal s p
  if alternate > input then return 0
  return if s.mode = .subtract then input - alternate else input

/-- `ComparatorBlock.shouldTurnOn`: there is an input, and it is stronger than the side input,
or equal to it in compare mode. -/
def shouldTurnOn (s : Blocks.Comparator) (p : Pos) : M Bool := do
  let input ← inputSignal s p
  if input = 0 then return false
  let side ← alternateSignal s p
  return if input > side then true else input = side && s.mode = .compare

/-- `DiodeBlock.shouldPrioritize`: the block in front is a repeater or comparator that does not
face the comparator. -/
def shouldPrioritize (s : Blocks.Comparator) (p : Pos) : M Bool := do
  let d := (facing s).opposite
  return ((diodeFacing? (← Level.getBlock (p.step d))).any (· ≠ d))

/-- `ComparatorBlock.checkTickOnNeighbor`: schedules a tick two game ticks ahead if the output
or the powered state is out of date, unless a tick of the comparator is still to run in the
current game tick. -/
def checkTickOnNeighbor (s : Blocks.Comparator) (p : Pos) : M Unit := do
  if !(← get).willTickThisTick p .comparator then
    let outputValue ← calculateOutputSignal s p
    let oldValue := outputSignal (← get) p
    if outputValue != oldValue || s.powered != (← shouldTurnOn s p) then
      let priority := if ← shouldPrioritize s p then TickPriority.high else .normal
      Level.scheduleTick p .comparator 2 priority

/-- `DiodeBlock.updateNeighborsInFront`: a neighbour update for the block in front of the
comparator, then for that block's neighbours other than the comparator. -/
def updateNeighborsInFront (s : Blocks.Comparator) (p : Pos) : M Unit := do
  let d := facing s
  let front := p.step d.opposite
  Level.neighborChanged front .comparator
  Level.updateNeighborsAtExceptFromFacing front .comparator (some d)

/-- `ComparatorBlock.refreshOutputState`: stores the new output in the block entity, and if it
changed or the comparator is in compare mode, sets the powered state and updates the
neighbours in front. -/
def refreshOutputState (s : Blocks.Comparator) (p : Pos) : M Unit := do
  let outputValue ← calculateOutputSignal s p
  let oldValue ←
    match ← Level.getBlockEntity p with
    | some (.comparator d) => do
      Level.setBlockEntity p (.comparator { d with output := outputValue })
      pure d.output
    | _ => pure 0
  if oldValue != outputValue || s.mode = .compare then
    let sourceOn ← shouldTurnOn s p
    if s.powered && !sourceOn then
      discard <| Level.setBlock p (.comparator { s with powered := false }) 2
    else if !s.powered && sourceOn then
      discard <| Level.setBlock p (.comparator { s with powered := true }) 2
    updateNeighborsInFront s p

/-- `DiodeBlock.neighborChanged`: checks the inputs, or removes the comparator if it has lost
its support and updates the neighbours of its six neighbours. -/
def neighborChanged (s : Blocks.Comparator) (p : Pos) : M Unit := do
  if (← Level.getBlock p).is .comparator then
    if canSurvive (← get) p then checkTickOnNeighbor s p
    else
      discard <| Level.removeBlock p false
      Direction.values.forM fun d => Level.updateNeighborsAt (p.step d) .comparator

/-- `ComparatorBlock.useWithoutItem`: switches between compare and subtract mode and refreshes
the output at once. The player may always build. -/
def useWithoutItem (s : Blocks.Comparator) (p : Pos) : M Bool := do
  let s := { s with mode := if s.mode = .compare then .subtract else .compare }
  discard <| Level.setBlock p (.comparator s) 2
  if (← Level.getBlock p).is .comparator then refreshOutputState s p
  return true

/-- The behaviour of a comparator. `newBlockEntity` is that of `Behaviour.inert`, a comparator
block entity with output 0; it has no ticker. `triggerEvent` returns false as in
`Behaviour.inert`: neither `BlockBehaviour` nor `BlockEntity` reacts to a block event. -/
def comparator (s : Blocks.Comparator) : Behaviour :=
  let self : Block := .comparator s
  { Behaviour.inert self with
    signal := signal s
    ownSignal := ownSignal s
    directSignal := signal s
    canSurvive := canSurvive
    neighborChanged := fun p _ _ => neighborChanged s p
    onPlace := fun p _ _ => updateNeighborsInFront s p
    affectNeighborsAfterRemoval := fun p moved => do
      if !moved then updateNeighborsInFront s p
    updateShape := fun _ d _ neighborState => do
      if d = .down && !canSurviveOn neighborState then return .AIR else return self
    tick := fun p => refreshOutputState s p
    useWithoutItem := fun p _ => useWithoutItem s p }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .comparator s => comparator s
  | _ => .inert self

end Redstone.Component.Comparator
