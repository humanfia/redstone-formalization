module

public import Redstone.Component.PressurePlate
public import Redstone.Component.Rail
public import Redstone.Component.Tripwire

/-!
# Lemmas about the blocks that entities press, in a level without entities

Pressure plates, weighted plates, detector rails and tripwire are switched by entities. These
lemmas say, for an arbitrary level whose list of entities is empty, that what such a block
measures is nothing, and that its check then leaves it off or switches it off. The theorems
about concrete layouts are in `Redstone/Theorems/RailMisc`.

* **What is measured.** With no entities a plate of either class counts none and calls for the
  signal zero (`getEntityCount_of_no_entities`, `plateSignalStrength_of_no_entities`,
  `weightedSignalStrength_of_no_entities`), and a detector rail finds no minecart
  (`hasMinecart_of_no_entities`), and a string has no entity to look at
  (`Tripwire.no_candidates_of_no_entities`).
* **Attribute lemmas.** The signal a plate state stands for (`signalForState_plateKind`,
  `signalForState_weightedKind`), and the state that stands for no signal
  (`setSignalForState_plateKind_zero`, `setSignalForState_weightedKind_zero`); a plate, a
  detector rail or a tripwire hook that is off gives no signal (`signal_base_of_off`,
  `signal_detector_of_off`, `Tripwire.signal_hook_of_off`).
* **Single reactions.** `checkPressed_of_off`: a plate that is off and measures nothing does
  nothing. `checkPressed_of_on`: a plate that is on and measures nothing takes the state for
  the signal zero, updates its neighbours and announces `block_deactivate`; it schedules no
  further tick. `tick_of_off`: the scheduled tick of a plate that is off does nothing.

Left out:

* What the three calls of `checkPressed_of_on` do to the level: `Level.setBlock` and the
  neighbour updates run the reactions of the blocks around the plate.
* The checks of the detector rail and of the tripwire as reactions
  (`Rail.checkPressed`, `Tripwire.checkPressed`): both end in calls that reach other blocks
  (`Level.updateNeighbourForOutputSignal`, `updateSource`) even when nothing is pressed; the
  layouts without entities are evaluated in `Redstone/Theorems/RailMisc/IdleSensors.lean` and
  `TripwireHooks.lean`.
-/

@[expose] public section

namespace Redstone.Component

namespace PressurePlate

/-! ### What is measured -/

/-- With no entities in the level, no entity is counted. -/
theorem getEntityCount_of_no_entities (l : Level) (box : AABB) (livingOnly : Bool)
    (h : l.entities = []) : getEntityCount l box livingOnly = 0 := by
  simp [getEntityCount, Entity.Still.getTriggeringEntities, h]

/-- With no entities in the level, a pressure plate calls for the signal zero. -/
theorem plateSignalStrength_of_no_entities (id : Blocks.PressurePlate.Id) (l : Level) (p : Pos)
    (h : l.entities = []) : plateSignalStrength id l p = 0 := by
  simp [plateSignalStrength, getEntityCount_of_no_entities _ _ _ h]

/-- A weighted plate with nothing on it gives no signal, whatever its maximal weight. -/
@[simp]
theorem weightedSignal_zero (maxWeight : ℕ) : weightedSignal maxWeight 0 = 0 := by
  simp [weightedSignal]

/-- With no entities in the level, a weighted plate calls for the signal zero. -/
theorem weightedSignalStrength_of_no_entities (id : Blocks.WeightedPressurePlate.Id) (l : Level)
    (p : Pos) (h : l.entities = []) : weightedSignalStrength id l p = 0 := by
  simp [weightedSignalStrength, getEntityCount_of_no_entities _ _ _ h]

/-! ### Attribute lemmas -/

/-- A pressure plate stands for the signal 15 when it is powered and for zero otherwise. -/
theorem signalForState_plateKind (id : Blocks.PressurePlate.Id) (s : Blocks.PressurePlate) :
    (plateKind id s).signalForState = if s.powered then 15 else 0 := rfl

/-- A weighted plate stands for the signal that is its `power` property. -/
theorem signalForState_weightedKind (id : Blocks.WeightedPressurePlate.Id)
    (s : Blocks.WeightedPressurePlate) : (weightedKind id s).signalForState = s.power.val := rfl

/-- The state of a pressure plate for the signal zero is the plate that is not powered. -/
theorem setSignalForState_plateKind_zero (id : Blocks.PressurePlate.Id)
    (s : Blocks.PressurePlate) :
    (plateKind id s).setSignalForState 0 = .pressurePlate id { s with powered := false } := by
  simp [plateKind]

/-- The state of a weighted plate for the signal zero is the plate with power zero. -/
theorem setSignalForState_weightedKind_zero (id : Blocks.WeightedPressurePlate.Id)
    (s : Blocks.WeightedPressurePlate) :
    (weightedKind id s).setSignalForState 0 = .weightedPressurePlate id { s with power := 0 } :=
  rfl

/-- A plate that is off gives no signal in any direction. -/
theorem signal_base_of_off (k : Kind) (self : Block) (h : k.signalForState = 0) (l : Level)
    (p : Pos) (d : Direction) :
    (base k self).signal l p d = 0 ∧ (base k self).directSignal l p d = 0 := by
  refine ⟨h, ?_⟩
  change (if d = .up then k.signalForState else 0) = 0
  simp [h]

/-! ### Single reactions -/

/-- **A plate that is off and measures nothing does nothing.** -/
theorem checkPressed_of_off (k : Kind) (p : Pos) (env : Env) (l : Level)
    (h : k.signalStrength l p = 0) : checkPressed k p 0 env l = ((), l) := by
  simp [checkPressed, bind, ReaderT.bind, StateT.bind, get, getThe, MonadStateOf.get, liftM,
    monadLift, MonadLift.monadLift, StateT.get, pure, ReaderT.pure, StateT.pure, h]

/-- **A plate that is on and measures nothing goes off.** It takes the state that stands for
the signal zero, updates the neighbours around itself and around the block below, announces
`block_deactivate`, and schedules no further tick. -/
theorem checkPressed_of_on (k : Kind) (p : Pos) (oldSignal : ℕ) (env : Env) (l : Level)
    (h : k.signalStrength l p = 0) (hold : 0 < oldSignal) :
    checkPressed k p oldSignal env l =
      (do
        discard <| Level.setBlock p (k.setSignalForState 0) 2
        updateNeighbours k p
        Level.gameEvent "minecraft:block_deactivate" p
        pure () : M Unit) env l := by
  have hne : (oldSignal != 0) = true := by simpa using Nat.pos_iff_ne_zero.mp hold
  simp [checkPressed, bind, ReaderT.bind, StateT.bind, get, getThe, MonadStateOf.get, liftM,
    monadLift, MonadLift.monadLift, StateT.get, pure, ReaderT.pure, StateT.pure, h, hne, hold]

/-- **The scheduled tick of a plate that is off does nothing.** -/
theorem tick_of_off (k : Kind) (self : Block) (p : Pos) (h : k.signalForState = 0) :
    (base k self).tick p = pure () := by
  change (if k.signalForState > 0 then checkPressed k p k.signalForState else pure ()) = _
  simp [h]

end PressurePlate

namespace Rail

/-- With no entities in the level, a detector rail finds no minecart. -/
theorem hasMinecart_of_no_entities (l : Level) (p : Pos) (h : l.entities = []) :
    hasMinecart l p = false := by
  simp [hasMinecart, h]

/-- A detector rail that is not powered gives no signal in any direction. -/
theorem signal_detector_of_off (s : Blocks.DetectorRail) (h : s.powered = false) (l : Level)
    (p : Pos) (d : Direction) :
    (detector s).signal l p d = 0 ∧ (detector s).directSignal l p d = 0 := by
  constructor
  · change (if s.powered then 15 else 0) = 0
    simp [h]
  · change (if s.powered && d = .up then 15 else 0) = 0
    simp [h]

/-- A comparator reads zero from a detector rail in the model, whatever its state (the contents
of minecarts are not kept). -/
theorem analogSignal_detector (s : Blocks.DetectorRail) :
    (detector s).analogSignal = fun _ _ _ => 0 := rfl

end Rail

namespace Tripwire

/-- A tripwire hook that is not powered gives no signal in any direction, attached or not. -/
theorem signal_hook_of_off (s : Blocks.TripWireHook) (h : s.powered = false) (l : Level)
    (p : Pos) (d : Direction) :
    (hook s).signal l p d = 0 ∧ (hook s).directSignal l p d = 0 := by
  constructor
  · change (if s.powered then 15 else 0) = 0
    simp [h]
  · change (if s.powered && s.facing.toDirection = d then 15 else 0) = 0
    simp [h]

/-- With no entities in the level, the list of entities a string looks at is empty: nothing
can press it. -/
theorem no_candidates_of_no_entities (l : Level) (h : l.entities = []) :
    l.entities.filter (ignoresBlockTriggers · != some true) = [] := by
  simp [h]

end Tripwire

end Redstone.Component
