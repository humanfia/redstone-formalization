module

public import Redstone.Mechanics.Tick

/-!
# Diodes

Java classes: `DiodeBlock` (the common superclass of `RepeaterBlock` and `ComparatorBlock`), and
`SignalGetter.getControlInputSignal`.

A diode lies flat on a block. Its `facing` property points towards its input: it reads the
signal of the block at `pos.relative(facing)` and gives its output to the block on the other
side, at `pos.relative(facing.getOpposite())`. A change of the input does not change the diode
at once: it schedules a tick, and the tick switches the diode.

`Diode` collects what `DiodeBlock` needs to know about one block state, including the methods
its subclasses override. The definitions of this file are the methods of `DiodeBlock` written
against that record.

Not formalized: `getStateForPlacement` and `setPlacedBy`, which run when a player places the
item.
-/

@[expose] public section

namespace Redstone.Component

/-- A block state of a `DiodeBlock`, with the methods that the subclasses define. -/
structure Diode where
  /-- The block (`this`). -/
  id : BlockId
  /-- The state itself. -/
  self : Block
  /-- The property `FACING`: the direction from the diode towards its input. -/
  facing : Direction
  /-- The property `POWERED`. -/
  powered : Bool
  /-- `state.setValue(POWERED, value)`. -/
  setPowered : Bool → Block
  /-- `getDelay(state)`, in game ticks. -/
  delay : ℕ
  /-- `isLocked(level, pos, state)`. -/
  isLocked : Pos → M Bool
  /-- `shouldTurnOn(level, pos, state)`. -/
  shouldTurnOn : Pos → M Bool
  /-- `getOutputSignal(level, pos, state)`. -/
  outputSignal : Level → Pos → ℕ

namespace Diode

/-- `Direction.getClockWise` for a horizontal direction; other directions are left alone (the
game throws for them). -/
def clockWise : Direction → Direction
  | .north => .east
  | .east => .south
  | .south => .west
  | .west => .north
  | d => d

/-- `Direction.getCounterClockWise` for a horizontal direction. -/
def counterClockWise : Direction → Direction
  | .north => .west
  | .west => .south
  | .south => .east
  | .east => .north
  | d => d

/-- The property `FACING` of a state of a `DiodeBlock`; `none` for every other block. -/
def facing? : Block → Option Direction
  | .repeater s => some s.facing.toDirection
  | .comparator s => some s.facing.toDirection
  | _ => none

/-- `DiodeBlock.isDiode(state)`: the block is a repeater or a comparator. -/
def isDiode (b : Block) : Bool := (facing? b).isSome

/-- `canSurviveOn(level, pos, state)`: the top face of `state` is sturdy with
`SupportType.RIGID`. -/
def canSurviveOn (below : Block) : Bool := below.attrs.isFaceSturdyRigid .up

/-- `canSurvive`: the diode can lie on the block below it. -/
def canSurvive (l : Level) (p : Pos) : Bool := canSurviveOn (l.blockAt (p.step .down))

/-- `DiodeBlock.getInputSignal`: the signal the diode with the given `facing` at `p` receives at
its input. Redstone wire counts with its power even when it does not point at the diode. -/
def getInputSignal (facing : Direction) (p : Pos) : M ℕ := do
  let target := p.step facing
  let input ← Level.getSignal target facing
  if input ≥ 15 then return input
  match ← Level.getBlock target with
  | .redstoneWire w => return max input w.power.val
  | _ => return input

/-- `SignalGetter.getControlInputSignal(pos, direction, onlyDiodes)`: the signal that the block
at `p` gives to the side of a diode. `direction` points from the diode to `p`. -/
def getControlInputSignal (p : Pos) (direction : Direction) (onlyDiodes : Bool) : M ℕ := do
  let state ← Level.getBlock p
  if onlyDiodes then
    if isDiode state then Level.getDirectSignal p direction else return 0
  else if state.is .redstone_block then return 15
  else
    match state with
    | .redstoneWire w => return w.power.val
    | _ => if state.attrs.signalSource then Level.getDirectSignal p direction else return 0

/-- `DiodeBlock.getAlternateSignal`: the stronger of the signals at the two sides of the diode
with the given `facing` at `p`. -/
def getAlternateSignal (facing : Direction) (p : Pos) (sideInputDiodesOnly : Bool) : M ℕ := do
  let cw := clockWise facing
  let ccw := counterClockWise facing
  return max (← getControlInputSignal (p.step cw) cw sideInputDiodesOnly)
    (← getControlInputSignal (p.step ccw) ccw sideInputDiodesOnly)

/-- `DiodeBlock.shouldPrioritize`: the block at the output of the diode with the given `facing`
is a diode that does not point the same way. -/
def shouldPrioritize (facing : Direction) (l : Level) (p : Pos) : Bool :=
  let direction := facing.opposite
  match facing? (l.blockAt (p.step direction)) with
  | some f => f != direction
  | none => false

variable (d : Diode)

/-- `DiodeBlock.ownSignal`. -/
def ownSignal (l : Level) (p : Pos) : ℕ := if d.powered then d.outputSignal l p else 0

/-- `DiodeBlock.getSignal`: the diode gives its signal to the block at its output only.
`getDirectSignal` is the same. -/
def signal (l : Level) (p : Pos) (direction : Direction) : ℕ :=
  if d.facing = direction then d.ownSignal l p else 0

/-- `DiodeBlock.updateNeighborsInFront`: a neighbour update for the block at the output, then
for its neighbours except the diode itself. -/
def updateNeighborsInFront (p : Pos) : M Unit := do
  let oppositePos := p.step d.facing.opposite
  Level.neighborChanged oppositePos d.id
  Level.updateNeighborsAtExceptFromFacing oppositePos d.id (some d.facing)

/-- `DiodeBlock.tick`: the scheduled tick. A powered diode whose input is gone turns off. An
unpowered diode turns on whatever the input is by now, and if the input is gone it schedules
the tick that turns it off again, so that a pulse lasts at least as long as the delay. -/
def tick (p : Pos) : M Unit := do
  if !(← d.isLocked p) then
    let on := d.powered
    let shouldTurnOn ← d.shouldTurnOn p
    if on && !shouldTurnOn then
      discard <| Level.setBlock p (d.setPowered false) 2
    else if !on then
      discard <| Level.setBlock p (d.setPowered true) 2
      if !shouldTurnOn then Level.scheduleTick p d.id d.delay .veryHigh

/-- `DiodeBlock.checkTickOnNeighbor`: schedules a tick when the diode is not locked, does not
agree with its input and is not about to tick. -/
def checkTickOnNeighbor (p : Pos) : M Unit := do
  if !(← d.isLocked p) then
    let on := d.powered
    let shouldTurnOn ← d.shouldTurnOn p
    let l ← get
    if on != shouldTurnOn && !l.willTickThisTick p d.id then
      let priority : TickPriority :=
        if shouldPrioritize d.facing l p then .extremelyHigh
        else if on then .veryHigh
        else .high
      Level.scheduleTick p d.id d.delay priority

/-- `DiodeBlock.neighborChanged`: checks the input, or drops and removes the diode when the
block below cannot carry it any more. -/
def neighborChanged (p : Pos) : M Unit := do
  if (← Level.getBlock p).is d.id then
    if canSurvive (← get) p then checkTickOnNeighbor d p
    else
      Level.dropResources d.self p
      discard <| Level.removeBlock p false
      Direction.values.forM fun dir => Level.updateNeighborsAt (p.step dir) d.id

/-- The methods that `DiodeBlock` overrides, for the diode `d`: signals, survival, the
scheduled tick, and the neighbour updates on placement and removal. -/
def behaviour : Behaviour :=
  { Behaviour.inert d.self with
    signal := d.signal
    ownSignal := d.ownSignal
    directSignal := d.signal
    canSurvive := canSurvive
    neighborChanged := fun p _ _ => d.neighborChanged p
    onPlace := fun p _ _ => d.updateNeighborsInFront p
    affectNeighborsAfterRemoval := fun p moved => do
      if !moved then d.updateNeighborsInFront p
    tick := d.tick }

end Diode

end Redstone.Component
