import Redstone.Theorems.Memory.Observe

/-!
# The repeater-lock latch (gated D latch)

A repeater whose side is fed by a second repeater. While the second repeater is powered the
first one is *locked*: it keeps its output whatever its input does. While it is not, the first
repeater is an ordinary repeater and its output follows its input.

```
z = -2:  .  L  .        L: the lock lever           y = 1, seen from above, x to the right
z = -1:  .  v  .        v: the lock repeater, pointing south into the side of R
z =  0:  D  R  O        D: the data lever, R: the data repeater pointing east, O: a lamp
```

In the terms of a gated D latch the data lever is `D`, the output of the data repeater is
`Q`, and the lock lever is the inverted enable: with the lock lever off the latch is
transparent, with it on the latch holds.

What is proved, as a table over the state `Q`, the data input and the lock:

* **Transparent** (lock off): `Q` follows `D` after one redstone tick: the lever is used
  before game tick `k`, the repeater switches in game tick `k + 1` (`follows_on`,
  `follows_off`).
* **Hold** (lock on): `Q` stays what it was when the lock came on, through every change of
  `D`, for both values of `Q` and both directions of the change (`holds_table`), and for ever
  (`holds_one`, `holds_zero`).
* **Unlocking** makes `Q` take the value `D` has by then, three game ticks after the lock
  lever: one redstone tick for the lock repeater and one for the data repeater
  (`unlock_takes_zero`, `unlock_takes_one`).

The level is loaded raw and is at rest (`circuit_quiescent`); after the whole schedule the
blocks are those it started with (`back_to_start`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Memory.RepeaterLatch

/-- The data lever `D`. -/
def dataLever : Pos := ⟨0, 1, 0⟩

/-- The data repeater: its `powered` property is the state `Q` of the latch. -/
def repeater : Pos := ⟨1, 1, 0⟩

/-- The lamp at the output. -/
def lamp : Pos := ⟨2, 1, 0⟩

/-- The repeater that points into the side of the data repeater. -/
def lockRepeater : Pos := ⟨1, 1, -1⟩

/-- The lock lever: on means hold. -/
def lockLever : Pos := ⟨1, 1, -2⟩

/-- The stone floor under the circuit. -/
def floor : List (Pos × Block) :=
  (List.range 3).flatMap fun x =>
    (List.range 3).map fun z => (⟨x, 0, (z : ℤ) - 2⟩, Block.plain .stone)

/-- The latch with both levers off: transparent, with `Q = D = 0`. -/
def circuit : Level :=
  .ofCells (floor ++ [
    (dataLever, .lever ⟨.floor, .north, false⟩),
    (repeater, blk% "minecraft:repeater[delay=1,facing=west,locked=false,powered=false]"),
    (lamp, .redstoneLamp ⟨false⟩),
    (lockRepeater, blk% "minecraft:repeater[delay=1,facing=north,locked=false,powered=false]"),
    (lockLever, .lever ⟨.floor, .north, false⟩)])

/-- The data lever is used; eight game ticks. -/
def useData : Schedule := .first [.use dataLever .up] 8

/-- The lock lever is used; eight game ticks. -/
def useLock : Schedule := .first [.use lockLever .up] 8

/-- Twelve inputs, eight game ticks apart. Transparent: `D` on (game tick 1). Lock on (9),
then `D` off, on, off (17, 25, 33) with `Q = 1` held. Lock off (41): `Q` takes `D = 0`. Lock
on (49), then `D` on, off, on (57, 65, 73) with `Q = 0` held. Lock off (81): `Q` takes
`D = 1`. Transparent: `D` off (89). -/
def schedule : Schedule :=
  useData ++ useLock ++ useData ++ useData ++ useData ++ useLock ++
    useLock ++ useData ++ useData ++ useData ++ useLock ++ useData

checkpoints state := schedule from circuit

/-- The inputs and the state: the data lever, the lock lever, and `Q` (the `powered` property
of the data repeater). -/
def latch (l : Level) : Option Bool × Option Bool × Option Bool :=
  (leverAt? l dataLever, leverAt? l lockLever, (repeaterAt? l repeater).map (·.1))

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Transparent, `D` goes on.** The data lever is switched on before game tick 1; the
repeater is still off after game tick 1 and on after game tick 2, and the lamp with it. The
repeater is not locked. -/
theorem follows_on :
    latch circuit = (some false, some false, some false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 1) circuit) repeater = some (false, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 2) circuit) repeater = some (true, false) ∧
      lampAt? (rules.runSchedule (schedule.take 2) circuit) lamp = some true ∧
      (rules.runSchedule (schedule.take 8) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 8) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_8]
  circuit_decide

assert_standard_axioms follows_on

/-- **Locking.** The lock lever is switched on before game tick 9. After game tick 10 the lock
repeater is powered and the data repeater shows `locked`; its output is unchanged. -/
theorem locks :
    repeaterAt? (rules.runSchedule (schedule.take 9) circuit) repeater = some (true, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 10) circuit) lockRepeater =
        some (true, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 10) circuit) repeater = some (true, true) ∧
      (rules.runSchedule (schedule.take 10) circuit).overflow = false := by
  rw [state_run_9, state_run_10]
  circuit_decide

assert_standard_axioms locks

/-- **Hold: the table.** With the lock on, `Q` does not move when `D` does. The entries are
(data lever, lock lever, `Q`) at the end of each eight-tick phase: `Q = 1` is held through
`D` going off (game tick 17), on (25) and off (33); `Q = 0` is held through `D` going on
(57), off (65) and on (73). -/
theorem holds_table :
    latch (rules.runSchedule (schedule.take 16) circuit) = (some true, some true, some true) ∧
      latch (rules.runSchedule (schedule.take 24) circuit) = (some false, some true, some true) ∧
      latch (rules.runSchedule (schedule.take 32) circuit) = (some true, some true, some true) ∧
      latch (rules.runSchedule (schedule.take 40) circuit) = (some false, some true, some true) ∧
      latch (rules.runSchedule (schedule.take 56) circuit) = (some false, some true, some false) ∧
      latch (rules.runSchedule (schedule.take 64) circuit) = (some true, some true, some false) ∧
      latch (rules.runSchedule (schedule.take 72) circuit) = (some false, some true, some false) ∧
      latch (rules.runSchedule (schedule.take 80) circuit) = (some true, some true, some false) ∧
      (rules.runSchedule (schedule.take 80) circuit).overflow = false := by
  rw [state_run_16, state_run_24, state_run_32, state_run_40, state_run_56, state_run_64,
    state_run_72, state_run_80]
  circuit_decide

assert_standard_axioms holds_table

/-- **Hold, `Q = 1`, for ever.** The data lever is switched off before game tick 17 while the
lock is on. The level is at rest at once, with the data lever off and the output still on,
and stays so for ever: the lamp stays lit. -/
theorem holds_one (n : ℕ) :
    latch (rules.steps n (rules.runSchedule (schedule.take 17) circuit)) =
        (some false, some true, some true) ∧
      lampAt? (rules.steps n (rules.runSchedule (schedule.take 17) circuit)) lamp = some true ∧
      (rules.steps n (rules.runSchedule (schedule.take 17) circuit)).overflow = false := by
  rw [state_run_17, rules.steps_of_quiescent (by circuit_decide)]
  simp only [latch, leverAt?, repeaterAt?, lampAt?, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms holds_one

/-- **Unlocking with `D = 0`, `Q = 1`.** The lock lever is switched off before game tick 41.
After game tick 42 the lock repeater is off and the data repeater is unlocked, still on; after
game tick 44 it is off: `Q` has taken the value of `D`. The lamp goes out four game ticks
later. -/
theorem unlock_takes_zero :
    latch (rules.runSchedule (schedule.take 40) circuit) = (some false, some true, some true) ∧
      repeaterAt? (rules.runSchedule (schedule.take 41) circuit) repeater = some (true, true) ∧
      repeaterAt? (rules.runSchedule (schedule.take 42) circuit) repeater = some (true, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 43) circuit) repeater = some (true, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 44) circuit) repeater = some (false, false) ∧
      lampAt? (rules.runSchedule (schedule.take 47) circuit) lamp = some true ∧
      lampAt? (rules.runSchedule (schedule.take 48) circuit) lamp = some false ∧
      (rules.runSchedule (schedule.take 48) circuit).overflow = false := by
  rw [state_run_40, state_run_41, state_run_42, state_run_43, state_run_44, state_run_47,
    state_run_48]
  circuit_decide

assert_standard_axioms unlock_takes_zero

/-- **Hold, `Q = 0`, for ever.** The lock is on again from game tick 49, with `Q = 0`; the
data lever is switched on before game tick 57. The level is at rest at once, with the data
lever on and the output still off, and stays so for ever: the lamp stays dark. -/
theorem holds_zero (n : ℕ) :
    latch (rules.steps n (rules.runSchedule (schedule.take 57) circuit)) =
        (some true, some true, some false) ∧
      lampAt? (rules.steps n (rules.runSchedule (schedule.take 57) circuit)) lamp = some false ∧
      (rules.steps n (rules.runSchedule (schedule.take 57) circuit)).overflow = false := by
  rw [state_run_57, rules.steps_of_quiescent (by circuit_decide)]
  simp only [latch, leverAt?, repeaterAt?, lampAt?, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms holds_zero

/-- **Unlocking with `D = 1`, `Q = 0`.** The lock lever is switched off before game tick 81.
After game tick 82 the data repeater is unlocked, still off; after game tick 84 it is on, and
the lamp with it. -/
theorem unlock_takes_one :
    latch (rules.runSchedule (schedule.take 80) circuit) = (some true, some true, some false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 82) circuit) repeater = some (false, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 83) circuit) repeater = some (false, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 84) circuit) repeater = some (true, false) ∧
      lampAt? (rules.runSchedule (schedule.take 84) circuit) lamp = some true ∧
      (rules.runSchedule (schedule.take 88) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 88) circuit).overflow = false := by
  rw [state_run_80, state_run_82, state_run_83, state_run_84, state_run_88]
  circuit_decide

assert_standard_axioms unlock_takes_one

/-- **Transparent, `D` goes off.** The data lever is switched off before game tick 89; the
repeater is off after game tick 90, and the lamp four game ticks later. -/
theorem follows_off :
    repeaterAt? (rules.runSchedule (schedule.take 89) circuit) repeater = some (true, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 90) circuit) repeater = some (false, false) ∧
      lampAt? (rules.runSchedule (schedule.take 93) circuit) lamp = some true ∧
      lampAt? (rules.runSchedule (schedule.take 94) circuit) lamp = some false ∧
      (rules.runSchedule (schedule.take 94) circuit).overflow = false := by
  rw [state_run_89, state_run_90, state_run_93, state_run_94]
  circuit_decide

assert_standard_axioms follows_off

/-- After the whole schedule the blocks are those the circuit started with, and the level is
at rest. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).blockEntities = circuit.blockEntities ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Memory.RepeaterLatch
