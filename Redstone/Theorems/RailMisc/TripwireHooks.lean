import Redstone.Proof.Circuit

/-!
# A pair of tripwire hooks: attached by the last string, pulsed by a broken one

Two tripwire hooks that face each other, three cells apart, each on a stone block with a lamp
behind it. Everything is at y = 1, z = 0:

```
x =   -2  -1   0   1   2   3   4   5   6
       M   S   H   .   .   .   H   S   M      M lamp, S stone, H hook, . the three cells for string
```

The west hook faces east and the east hook faces west. The three strings are placed one after
the other, from west to east, each in the state a player's placement gives it (connected to
what is already beside it).

* **Attaching.** With one or two strings the hooks are not attached. When the third string
  completes the line, both hooks and all three strings become `attached` in the same game
  tick (`TripWireHookBlock.calculateState`). The hooks are not powered and the lamps stay
  dark; ten game ticks after the first string the west hook's scheduled tick runs and changes
  nothing, and the circuit is at rest.
* **Breaking.** When the middle string is destroyed (not cut with shears: the string is not
  `disarmed`), both hooks become `powered` in the same game tick and the lamps light: a hook
  gives strong power to the block it hangs on. The hook's tick runs ten game ticks later:
  the hooks are then neither powered nor attached, and the two remaining strings are no
  longer attached. The lamps go dark four game ticks after that. So breaking the string gives
  a pulse of ten game ticks (five redstone ticks) at each hook, fourteen at the lamps.

No entity is involved: a string that an entity touches is out of reach of these proofs
(`Overview`).

The level is loaded raw with the hooks and no string; `circuit_quiescent` shows that it is at
rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.RailMisc.TripwireHooks

/-- The position of the west hook. -/
def hookW : Pos := ⟨0, 1, 0⟩

/-- The position of the east hook. -/
def hookE : Pos := ⟨4, 1, 0⟩

/-- The lamp behind the block of the west hook. -/
def lampW : Pos := ⟨-2, 1, 0⟩

/-- The lamp behind the block of the east hook. -/
def lampE : Pos := ⟨6, 1, 0⟩

/-- The three cells between the hooks, from west to east. -/
def strings : List Pos := [⟨1, 1, 0⟩, ⟨2, 1, 0⟩, ⟨3, 1, 0⟩]

/-- A tripwire hook. -/
def hook (facing : HorizontalDirection) (attached powered : Bool) : Block :=
  .tripWireHook ⟨attached, facing, powered⟩

/-- The two hooks, west and east, with the same `attached` and `powered`. -/
def hooks (attached powered : Bool) : List Block :=
  [hook .east attached powered, hook .west attached powered]

/-- A string that is armed and not powered, with its connections to the east and west. -/
def string (attached east west : Bool) : Block :=
  .tripWire { attached := attached, disarmed := false, east := east, north := false,
              powered := false, south := false, west := west }

/-- A lamp, lit or dark. -/
def lampState (lit : Bool) : Block := .redstoneLamp ⟨lit⟩

/-- The two hooks on their blocks, with the lamps, and no string. -/
def circuit : Level :=
  .ofCells [(⟨-1, 1, 0⟩, .plain .stone), (⟨5, 1, 0⟩, .plain .stone), (lampW, lampState false),
    (lampE, lampState false), (hookW, hook .east false false), (hookE, hook .west false false)]

/-- The strings are placed before game ticks 1, 2 and 3, from west to east; the middle string
is destroyed before game tick 16; 32 game ticks in all. -/
def schedule : Schedule :=
  .first [.set ⟨1, 1, 0⟩ (string false false true)] 1 ++
    .first [.set ⟨2, 1, 0⟩ (string false false true)] 1 ++
    .first [.set ⟨3, 1, 0⟩ (string false true true)] 13 ++
    .first [.destroy ⟨2, 1, 0⟩] 17

checkpoints state := schedule from circuit

/-- The hooks without string are at rest, not attached and not powered. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **An incomplete line does not attach.** After the first and after the second string the
hooks are not attached. -/
theorem incomplete_not_attached :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt [hookW, hookE] = hooks false false ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt [hookW, hookE] =
        hooks false false ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt strings =
        [string false true true, string false false true, .AIR] ∧
      (rules.runSchedule (schedule.take 2) circuit).overflow = false := by
  rw [state_run_1, state_run_2]
  circuit_decide

assert_standard_axioms incomplete_not_attached

/-- **The last string attaches the pair.** In the game tick in which the third string is
placed, both hooks and all three strings are `attached`; the hooks are not powered and the
lamps are dark. -/
theorem complete_attaches :
    (rules.runSchedule (schedule.take 3) circuit).blocksAt [hookW, hookE] = hooks true false ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt strings =
        [string true true true, string true true true, string true true true] ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt [lampW, lampE] =
        [lampState false, lampState false] ∧
      (rules.runSchedule (schedule.take 3) circuit).overflow = false := by
  rw [state_run_3]
  circuit_decide

assert_standard_axioms complete_attaches

/-- **The attached pair stays attached and unpowered**, for ever: the west hook's scheduled
tick (due in game tick 10, ten game ticks after the first string was placed) changes nothing,
and after game tick 15 the level is at rest. -/
theorem attached_stays (n : ℕ) :
    (rules.runSchedule (schedule.take 9) circuit).pending =
        [(hookW, .tripwire_hook, 1, .normal)] ∧
      (rules.runSchedule (schedule.take 10) circuit).blocksAt [hookW, hookE] =
        hooks true false ∧
      (rules.steps n (rules.runSchedule (schedule.take 15) circuit)).blocksAt [hookW, hookE] =
        hooks true false ∧
      (rules.steps n (rules.runSchedule (schedule.take 15) circuit)).blocksAt [lampW, lampE] =
        [lampState false, lampState false] ∧
      (rules.steps n (rules.runSchedule (schedule.take 15) circuit)).overflow = false := by
  rw [state_run_9, state_run_10, state_run_15, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms attached_stays

/-- **Breaking the string powers both hooks at once.** In the game tick in which the middle
string is destroyed (game tick 16), both hooks are `powered` and still `attached`, and both
lamps are lit. -/
theorem broken_powers :
    (rules.runSchedule (schedule.take 16) circuit).blocksAt [hookW, hookE] = hooks true true ∧
      (rules.runSchedule (schedule.take 16) circuit).blocksAt strings =
        [string true false true, .AIR, string true true false] ∧
      (rules.runSchedule (schedule.take 16) circuit).blocksAt [lampW, lampE] =
        [lampState true, lampState true] ∧
      (rules.runSchedule (schedule.take 16) circuit).overflow = false := by
  rw [state_run_16]
  circuit_decide

assert_standard_axioms broken_powers

/-- **The pulse is ten game ticks long.** The hooks are still powered after game tick 24 and
are neither powered nor attached after game tick 25, ten game ticks after the string was
destroyed; the two remaining strings are no longer attached. The lamps are lit after game tick
28 and dark after game tick 29. -/
theorem pulse_length :
    (rules.runSchedule (schedule.take 24) circuit).blocksAt [hookW, hookE] = hooks true true ∧
      (rules.runSchedule (schedule.take 25) circuit).blocksAt [hookW, hookE] =
        hooks false false ∧
      (rules.runSchedule (schedule.take 25) circuit).blocksAt strings =
        [string false false true, .AIR, string false true false] ∧
      (rules.runSchedule (schedule.take 28) circuit).blocksAt [lampW, lampE] =
        [lampState true, lampState true] ∧
      (rules.runSchedule (schedule.take 29) circuit).blocksAt [lampW, lampE] =
        [lampState false, lampState false] ∧
      (rules.runSchedule (schedule.take 29) circuit).overflow = false := by
  rw [state_run_24, state_run_25, state_run_28, state_run_29]
  circuit_decide

assert_standard_axioms pulse_length

/-- **After the pulse the pair is detached**, for ever: hooks not attached and not powered,
lamps dark. -/
theorem detached_stays (n : ℕ) :
    (rules.steps n (rules.runSchedule schedule circuit)).blocksAt [hookW, hookE] =
        hooks false false ∧
      (rules.steps n (rules.runSchedule schedule circuit)).blocksAt [lampW, lampE] =
        [lampState false, lampState false] ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms detached_stays

end Redstone.Theorems.RailMisc.TripwireHooks
