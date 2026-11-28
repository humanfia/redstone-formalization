module

public import Redstone.Mechanics.Tick
public import Redstone.Entity.Still

/-!
# Pressure plates

Java classes: `BasePressurePlateBlock`, `PressurePlateBlock`, `WeightedPressurePlateBlock`, and
`BlockSetType` for the sensitivity of each plate.

A pressure plate gives a signal while entities are in the box just above it. An entity that
touches a plate that is off makes it count the entities (`entityInside`); a plate that is on
counts them again every 20 game ticks (10 for the weighted plates) with a scheduled tick, and
goes off at the first count that finds none. So a plate stays on for at least 20 (or 10) ticks.

* Wooden plates count all entities, stone and polished blackstone plates only living ones;
  both give 15.
* The light weighted plate gives the number of entities, at most 15; the heavy one gives the
  number of entities divided by ten and rounded up, at most 15.

The plate gives its signal to all its neighbours, and strong power to the block below it. It
needs a block below whose top face supports it (`canSurvive`).

Which entities there are, their bounding boxes and when they touch a block comes from
`Redstone.Entity.Still`; see there for what is assumed about entities. Sounds are left out.
-/

@[expose] public section

namespace Redstone.Component.PressurePlate


/-- `BlockSetType.PressurePlateSensitivity`: what a plate with a boolean state detects. -/
inductive Sensitivity
  /-- All entities (`Entity.class`). -/
  | everything
  /-- Living entities only (`LivingEntity.class`). -/
  | mobs
  deriving DecidableEq, Repr

/-- `BlockSetType.pressurePlateSensitivity()` of the block set type of each plate: `STONE` and
`POLISHED_BLACKSTONE` detect mobs, the wooden types everything. -/
def sensitivity : Blocks.PressurePlate.Id → Sensitivity
  | .stone_pressure_plate | .polished_blackstone_pressure_plate => .mobs
  | _ => .everything

/-- The `maxWeight` of the weighted plates: 15 for the light (gold) one, 150 for the heavy
(iron) one. -/
def maxWeight : Blocks.WeightedPressurePlate.Id → ℕ
  | .light_weighted_pressure_plate => 15
  | .heavy_weighted_pressure_plate => 150

/-- `TOUCH_AABB.move(pos)`: the box in which entities are counted, 14 pixels wide and 4 pixels
high, at the bottom of the plate's cell. -/
def touchBox (p : Pos) : AABB := (⟨0.0625, 0.0, 0.0625, 0.9375, 0.25, 0.9375⟩ : AABB).atBlock p

/-- `getEntityCount(level, box, entityClass)`: the number of entities of the class in the box
that are not spectators and do not ignore block triggers. -/
def getEntityCount (l : Level) (box : AABB) (livingOnly : Bool) : ℕ :=
  (Entity.Still.getTriggeringEntities l box livingOnly).length

/-- `PressurePlateBlock.getSignalStrength`: 15 if an entity of the kind the plate detects is in
the box, and 0 otherwise. -/
def plateSignalStrength (id : Blocks.PressurePlate.Id) (l : Level) (p : Pos) : ℕ :=
  if getEntityCount l (touchBox p) (sensitivity id == .mobs) > 0 then 15 else 0

/-- The signal of a weighted plate with `count` entities on it: with `float` arithmetic as in
`WeightedPressurePlateBlock.getSignalStrength`, `ceil(min(maxWeight, count) / maxWeight * 15)`. -/
def weightedSignal (maxWeight count : ℕ) : ℕ :=
  let count := min count maxWeight
  if count > 0 then
    let percent : Float32 := Float32.ofNat (min maxWeight count) / Float32.ofNat maxWeight
    (percent * 15.0).ceil.toUInt8.toNat
  else 0

/-! With these `float` operations the light plate gives the number of entities up to 15, and
the heavy plate a tenth of it rounded up: the rounding errors of the division never carry the
product over an integer. The check below is run when the file is compiled; the same table was
obtained from the Java expression. -/

#guard (List.range 161).all fun n =>
  weightedSignal 15 n == min n 15 && weightedSignal 150 n == min 15 ((min n 150 + 9) / 10)

/-- `WeightedPressurePlateBlock.getSignalStrength`: all entities in the box are counted. -/
def weightedSignalStrength (id : Blocks.WeightedPressurePlate.Id) (l : Level) (p : Pos) : ℕ :=
  weightedSignal (maxWeight id) (getEntityCount l (touchBox p) false)

/-- What distinguishes the two classes of plates: the abstract methods of
`BasePressurePlateBlock`, for one block state. -/
structure Kind where
  /-- The block. -/
  block : BlockId
  /-- `getSignalForState(state)`: the signal the state stands for. -/
  signalForState : ℕ
  /-- `setSignalForState(state, signal)`: the state that stands for a signal. -/
  setSignalForState : ℕ → Block
  /-- `getSignalStrength(level, pos)`: the signal the entities on the plate call for. -/
  signalStrength : Level → Pos → ℕ
  /-- `getPressedTime()`: the number of ticks between two counts while the plate is on. -/
  pressedTime : ℕ

/-- `PressurePlateBlock`: the state is on or off, the signal 15 or 0. -/
def plateKind (id : Blocks.PressurePlate.Id) (s : Blocks.PressurePlate) : Kind where
  block := id.toBlockId
  signalForState := if s.powered then 15 else 0
  setSignalForState signal := .pressurePlate id { s with powered := signal > 0 }
  signalStrength := plateSignalStrength id
  pressedTime := 20

/-- `WeightedPressurePlateBlock`: the state is the signal itself. -/
def weightedKind (id : Blocks.WeightedPressurePlate.Id) (s : Blocks.WeightedPressurePlate) :
    Kind where
  block := id.toBlockId
  signalForState := s.power.val
  setSignalForState signal := .weightedPressurePlate id { s with power := Fin.ofNat 16 signal }
  signalStrength := weightedSignalStrength id
  pressedTime := 10

/-- `canSurvive`: the top face of the block below supports a rigid block, or at least supports
one at its centre. -/
def canSurvive (l : Level) (p : Pos) : Bool :=
  let below := l.supportAttrs (p.step .down)
  below.isFaceSturdyRigid .up || below.isFaceSturdyCenter .up

/-- `updateNeighbours`: neighbour updates around the plate and around the block below it. -/
def updateNeighbours (k : Kind) (p : Pos) : M Unit := do
  Level.updateNeighborsAt p k.block
  Level.updateNeighborsAt (p.step .down) k.block

/-- `checkPressed(sourceEntity, level, pos, state, oldSignal)`: counts the entities and takes
the state that goes with them. A plate that is on afterwards asks to be ticked again. -/
def checkPressed (k : Kind) (p : Pos) (oldSignal : ℕ) : M Unit := do
  let signal := k.signalStrength (← get) p
  let wasPressed := oldSignal > 0
  let isPressed := signal > 0
  if oldSignal != signal then
    discard <| Level.setBlock p (k.setSignalForState signal) 2
    updateNeighbours k p
  if !isPressed && wasPressed then Level.gameEvent "minecraft:block_deactivate" p
  else if isPressed && !wasPressed then Level.gameEvent "minecraft:block_activate" p
  if isPressed then Level.scheduleTick p k.block k.pressedTime

/-- The behaviour of `BasePressurePlateBlock`, for a state `self` of the kind `k`. -/
def base (k : Kind) (self : Block) : Behaviour :=
  { Behaviour.inert self with
    signal := fun _ _ _ => k.signalForState
    ownSignal := fun _ _ => k.signalForState
    directSignal := fun _ _ d => if d = .up then k.signalForState else 0
    canSurvive := canSurvive
    updateShape := fun p d _ _ => do
      if d = .down && !canSurvive (← get) p then return .AIR else return self
    tick := fun p => do
      if k.signalForState > 0 then checkPressed k p k.signalForState
    entityInside := fun p _ => do
      if k.signalForState == 0 then checkPressed k p k.signalForState
    affectNeighborsAfterRemoval := fun p moved => do
      if !moved && k.signalForState > 0 then updateNeighbours k p }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .pressurePlate id s => base (plateKind id s) self
  | .weightedPressurePlate id s => base (weightedKind id s) self
  | _ => .inert self

end Redstone.Component.PressurePlate
