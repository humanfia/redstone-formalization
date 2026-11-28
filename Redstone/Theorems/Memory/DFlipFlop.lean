import Redstone.Theorems.Memory.Observe

/-!
# The edge-triggered D flip-flop (two repeater latches, master and slave)

Two repeaters in a row, each with a lock repeater at its side. The first (*master*) is locked
while the clock is high, the second (*slave*) while the clock is low: the clock lever sits on
a stone block that feeds the master's lock repeater directly, and a torch on the side of that
block feeds the slave's lock repeater with the inverted clock.

```
z = -2:  .  C  T  .      C: stone block with the clock lever on top, T: torch on its east side
z = -1:  .  v  v  .      v: the two lock repeaters, pointing south
z =  0:  D  M  S  O      D: the data lever, M: master, S: slave (both pointing east), O: lamp
                         y = 1, seen from above, x to the right
```

While the clock is low the master follows `D` and the slave holds `Q`. A rising edge locks the
master first (one redstone tick) and opens the slave after it (two redstone ticks: torch and
lock repeater), so the slave takes what the master held at the edge: `Q := D`. A falling edge
opens the master and locks the slave in the same game tick; the slave's tick comes too late
to pass the lock.

What is proved (`Q` is the `powered` property of the slave):

* **Rising edge: `Q := D`**, for the four combinations of `Q` and `D`, each from a level at
  rest. The clock lever is used before game tick `k`; when `Q` changes, the slave switches in
  game tick `k + 5` (`rising_sets`, `rising_clears`, `rising_keeps_one`,
  `rising_keeps_zero`).
* **A falling edge does not change `Q`**, for either value of `Q`, with `D` opposite to `Q`
  (`falling_keeps`).
* **`D` does not reach `Q` between edges**: while the clock is high (`high_holds_one`,
  `high_holds_zero`: for ever) and while it is low (`low_holds`: `D` off and on again under
  `Q = 1`; `low_holds_zero`: for ever).
* After the whole schedule the blocks are those the circuit started with (`back_to_start`).

The level is loaded raw, with the clock low, `D = 0` and `Q = 0`: the slave is locked, the
master is not. It is at rest (`circuit_quiescent`), and it is the state the circuit itself
returns to.
-/

set_option Elab.async false

namespace Redstone.Theorems.Memory.DFlipFlop

/-- The data lever `D`. -/
def dataLever : Pos := ⟨0, 1, 0⟩

/-- The master repeater. -/
def master : Pos := ⟨1, 1, 0⟩

/-- The slave repeater: its `powered` property is `Q`. -/
def slave : Pos := ⟨2, 1, 0⟩

/-- The lamp at the output. -/
def lamp : Pos := ⟨3, 1, 0⟩

/-- The clock lever, on top of the stone block. -/
def clockLever : Pos := ⟨1, 2, -2⟩

/-- The torch on the clock block: the inverted clock. -/
def clockTorch : Pos := ⟨2, 1, -2⟩

/-- The repeater that locks the master while the clock is high. -/
def masterLock : Pos := ⟨1, 1, -1⟩

/-- The repeater that locks the slave while the clock is low. -/
def slaveLock : Pos := ⟨2, 1, -1⟩

/-- The stone floor under the circuit. -/
def floor : List (Pos × Block) :=
  (List.range 4).flatMap fun x =>
    (List.range 3).map fun z => (⟨x, 0, (z : ℤ) - 2⟩, Block.plain .stone)

/-- The flip-flop with the clock low, `D = 0` and `Q = 0`. -/
def circuit : Level :=
  .ofCells (floor ++ [
    (dataLever, .lever ⟨.floor, .north, false⟩),
    (master, blk% "minecraft:repeater[delay=1,facing=west,locked=false,powered=false]"),
    (slave, blk% "minecraft:repeater[delay=1,facing=west,locked=true,powered=false]"),
    (lamp, .redstoneLamp ⟨false⟩),
    (⟨1, 1, -2⟩, .plain .stone),
    (clockLever, .lever ⟨.floor, .north, false⟩),
    (clockTorch, .redstoneWallTorch ⟨.east, true⟩),
    (masterLock, blk% "minecraft:repeater[delay=1,facing=north,locked=false,powered=false]"),
    (slaveLock, blk% "minecraft:repeater[delay=1,facing=north,locked=false,powered=true]")])

/-- The data lever is used; ten game ticks. -/
def useData : Schedule := .first [.use dataLever .up] 10

/-- The clock lever is used; ten game ticks. -/
def useClock : Schedule := .first [.use clockLever .up] 10

/-- Eighteen inputs, ten game ticks apart. The game tick before which each is applied:
`D` on (1); clock up (11, `Q := 1`); `D` off (21); clock down (31); clock up (41, `Q := 0`);
`D` on (51); clock down (61); clock up (71, `Q := 1`); clock down (81); `D` off (91); `D` on
(101); clock up (111, `Q` stays 1); `D` off (121); clock down (131); clock up (141,
`Q := 0`); clock down (151); clock up (161, `Q` stays 0); clock down (171). -/
def schedule : Schedule :=
  useData ++ useClock ++ useData ++ useClock ++ useClock ++ useData ++ useClock ++ useClock ++
    useClock ++ useData ++ useData ++ useClock ++ useData ++ useClock ++ useClock ++ useClock ++
    useClock ++ useClock

checkpoints state := schedule from circuit

/-- The inputs and the state: the data lever, the clock lever, and `Q` (the `powered` property
of the slave). -/
def flipFlop (l : Level) : Option Bool × Option Bool × Option Bool :=
  (leverAt? l dataLever, leverAt? l clockLever, (repeaterAt? l slave).map (·.1))

/-- The circuit as built is at rest, with `D = 0`, the clock low and `Q = 0`. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧ flipFlop circuit = (some false, some false, some false) := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **`D` changes while the clock is low, `Q = 0`: nothing reaches `Q`, for ever.** `D` is
switched on before game tick 1. The master follows after game tick 2; the slave stays locked
and off. The level is at rest after game tick 10 and `Q` stays 0 for ever. -/
theorem low_holds_zero (n : ℕ) :
    repeaterAt? (rules.runSchedule (schedule.take 2) circuit) master = some (true, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 2) circuit) slave = some (false, true) ∧
      flipFlop (rules.steps n (rules.runSchedule (schedule.take 10) circuit)) =
        (some true, some false, some false) ∧
      (rules.steps n (rules.runSchedule (schedule.take 10) circuit)).overflow = false := by
  rw [state_run_2, state_run_10, rules.steps_of_quiescent (by circuit_decide)]
  simp only [flipFlop, leverAt?, repeaterAt?, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms low_holds_zero

/-- **Rising edge with `D = 1`, `Q = 0`: `Q` becomes 1.** The level is at rest; the clock
lever is switched on before game tick 11. After game tick 12 the master is locked; after game
tick 14 the slave is unlocked, still off; after game tick 16 it is on, and the lamp is lit. -/
theorem rising_sets :
    flipFlop (rules.runSchedule (schedule.take 10) circuit) =
        (some true, some false, some false) ∧
      (rules.runSchedule (schedule.take 10) circuit).Quiescent ∧
      repeaterAt? (rules.runSchedule (schedule.take 12) circuit) master = some (true, true) ∧
      repeaterAt? (rules.runSchedule (schedule.take 13) circuit) slave = some (false, true) ∧
      repeaterAt? (rules.runSchedule (schedule.take 14) circuit) slave = some (false, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 15) circuit) slave = some (false, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 16) circuit) slave = some (true, false) ∧
      lampAt? (rules.runSchedule (schedule.take 16) circuit) lamp = some true ∧
      (rules.runSchedule (schedule.take 16) circuit).overflow = false := by
  rw [state_run_10, state_run_12, state_run_13, state_run_14, state_run_15, state_run_16]
  circuit_decide

assert_standard_axioms rising_sets

/-- **`D` changes while the clock is high, `Q = 1`: `Q` holds for ever.** `D` is switched off
before game tick 21. The level is at rest at once, and `Q` stays 1 for ever. -/
theorem high_holds_one (n : ℕ) :
    flipFlop (rules.steps n (rules.runSchedule (schedule.take 21) circuit)) =
        (some false, some true, some true) ∧
      (rules.steps n (rules.runSchedule (schedule.take 21) circuit)).overflow = false := by
  rw [state_run_21, rules.steps_of_quiescent (by circuit_decide)]
  simp only [flipFlop, leverAt?, repeaterAt?, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms high_holds_one

/-- **A falling edge does not change `Q`.** With `D = 0` and `Q = 1` the clock lever is
switched off before game tick 31: after game tick 34 the master has taken `D` and the slave
is locked, still on. With `D = 1` and `Q = 0` the clock lever is switched off before game
tick 61: after game tick 64 the master is on and the slave is locked, still off. Both times
the level is at rest again six game ticks later. -/
theorem falling_keeps :
    flipFlop (rules.runSchedule (schedule.take 30) circuit) =
        (some false, some true, some true) ∧
      repeaterAt? (rules.runSchedule (schedule.take 34) circuit) master = some (false, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 34) circuit) slave = some (true, true) ∧
      flipFlop (rules.runSchedule (schedule.take 40) circuit) =
        (some false, some false, some true) ∧
      (rules.runSchedule (schedule.take 40) circuit).Quiescent ∧
      flipFlop (rules.runSchedule (schedule.take 60) circuit) =
        (some true, some true, some false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 64) circuit) master = some (true, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 64) circuit) slave = some (false, true) ∧
      flipFlop (rules.runSchedule (schedule.take 70) circuit) =
        (some true, some false, some false) ∧
      (rules.runSchedule (schedule.take 70) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 70) circuit).overflow = false := by
  rw [state_run_30, state_run_34, state_run_40, state_run_60, state_run_64, state_run_70]
  circuit_decide

assert_standard_axioms falling_keeps

/-- **Rising edge with `D = 0`, `Q = 1`: `Q` becomes 0.** The level is at rest; the clock
lever is switched on before game tick 41. After game tick 45 the slave is still on, after
game tick 46 it is off; the lamp goes out after game tick 50. -/
theorem rising_clears :
    flipFlop (rules.runSchedule (schedule.take 40) circuit) =
        (some false, some false, some true) ∧
      (rules.runSchedule (schedule.take 40) circuit).Quiescent ∧
      repeaterAt? (rules.runSchedule (schedule.take 45) circuit) slave = some (true, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 46) circuit) slave = some (false, false) ∧
      lampAt? (rules.runSchedule (schedule.take 49) circuit) lamp = some true ∧
      lampAt? (rules.runSchedule (schedule.take 50) circuit) lamp = some false ∧
      (rules.runSchedule (schedule.take 50) circuit).overflow = false := by
  rw [state_run_40, state_run_45, state_run_46, state_run_49, state_run_50]
  circuit_decide

assert_standard_axioms rising_clears

/-- **`D` changes while the clock is high, `Q = 0`: `Q` holds for ever.** `D` is switched on
before game tick 51. The level is at rest at once, and `Q` stays 0 for ever. -/
theorem high_holds_zero (n : ℕ) :
    flipFlop (rules.steps n (rules.runSchedule (schedule.take 51) circuit)) =
        (some true, some true, some false) ∧
      (rules.steps n (rules.runSchedule (schedule.take 51) circuit)).overflow = false := by
  rw [state_run_51, rules.steps_of_quiescent (by circuit_decide)]
  simp only [flipFlop, leverAt?, repeaterAt?, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms high_holds_zero

/-- **`D` changes while the clock is low, `Q = 1`: nothing reaches `Q`.** After the rising
edge of game tick 71 and the falling edge of game tick 81, `Q = 1` and the clock is low. `D`
is switched off before game tick 91 and on again before game tick 101: the master follows
both times (after game ticks 92 and 102), the slave stays locked and on, and the level is at
rest after game ticks 100 and 110. -/
theorem low_holds :
    flipFlop (rules.runSchedule (schedule.take 90) circuit) =
        (some true, some false, some true) ∧
      repeaterAt? (rules.runSchedule (schedule.take 92) circuit) master = some (false, false) ∧
      flipFlop (rules.runSchedule (schedule.take 100) circuit) =
        (some false, some false, some true) ∧
      (rules.runSchedule (schedule.take 100) circuit).Quiescent ∧
      repeaterAt? (rules.runSchedule (schedule.take 102) circuit) master = some (true, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 110) circuit) slave = some (true, true) ∧
      flipFlop (rules.runSchedule (schedule.take 110) circuit) =
        (some true, some false, some true) ∧
      (rules.runSchedule (schedule.take 110) circuit).overflow = false := by
  rw [state_run_90, state_run_92, state_run_100, state_run_102, state_run_110]
  circuit_decide

assert_standard_axioms low_holds

/-- **Rising edge with `D = 1`, `Q = 1`: `Q` stays 1.** The level is at rest; the clock lever
is switched on before game tick 111. The slave is unlocked after game tick 114 and is on
after every game tick up to 120, when the level is at rest again. -/
theorem rising_keeps_one :
    flipFlop (rules.runSchedule (schedule.take 110) circuit) =
        (some true, some false, some true) ∧
      (rules.runSchedule (schedule.take 110) circuit).Quiescent ∧
      repeaterAt? (rules.runSchedule (schedule.take 114) circuit) slave = some (true, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 116) circuit) slave = some (true, false) ∧
      flipFlop (rules.runSchedule (schedule.take 120) circuit) =
        (some true, some true, some true) ∧
      (rules.runSchedule (schedule.take 120) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 120) circuit).overflow = false := by
  rw [state_run_110, state_run_114, state_run_116, state_run_120]
  circuit_decide

assert_standard_axioms rising_keeps_one

/-- **Rising edge with `D = 0`, `Q = 0`: `Q` stays 0.** After `Q` was cleared by the edge of
game tick 141 and the clock went down again, the level is at rest; the clock lever is
switched on before game tick 161. The slave is unlocked after game tick 164 and is off after
every game tick up to 170, when the level is at rest again. -/
theorem rising_keeps_zero :
    flipFlop (rules.runSchedule (schedule.take 160) circuit) =
        (some false, some false, some false) ∧
      (rules.runSchedule (schedule.take 160) circuit).Quiescent ∧
      repeaterAt? (rules.runSchedule (schedule.take 164) circuit) slave = some (false, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 166) circuit) slave = some (false, false) ∧
      flipFlop (rules.runSchedule (schedule.take 170) circuit) =
        (some false, some true, some false) ∧
      (rules.runSchedule (schedule.take 170) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 170) circuit).overflow = false := by
  rw [state_run_160, state_run_164, state_run_166, state_run_170]
  circuit_decide

assert_standard_axioms rising_keeps_zero

/-- **The table of rising edges, at a glance.** (`D`, clock, `Q`) before each of the six
rising edges of the schedule (first list) and ten game ticks after it (second list): `Q` after
the edge is `D` before it. -/
theorem rising_table :
    ([10, 40, 70, 110, 140, 160].map fun k =>
        flipFlop (rules.runSchedule (schedule.take k) circuit)) =
        [(some true, some false, some false), (some false, some false, some true),
          (some true, some false, some false), (some true, some false, some true),
          (some false, some false, some true), (some false, some false, some false)] ∧
      ([20, 50, 80, 120, 150, 170].map fun k =>
        flipFlop (rules.runSchedule (schedule.take k) circuit)) =
        [(some true, some true, some true), (some false, some true, some false),
          (some true, some true, some true), (some true, some true, some true),
          (some false, some true, some false), (some false, some true, some false)] ∧
      (rules.runSchedule (schedule.take 170) circuit).overflow = false := by
  simp only [List.map_cons, List.map_nil]
  rw [state_run_10, state_run_20, state_run_40, state_run_50, state_run_70, state_run_80,
    state_run_110, state_run_120, state_run_140, state_run_150, state_run_160, state_run_170]
  circuit_decide

assert_standard_axioms rising_table

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

end Redstone.Theorems.Memory.DFlipFlop
