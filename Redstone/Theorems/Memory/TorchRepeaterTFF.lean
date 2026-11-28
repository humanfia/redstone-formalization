import Redstone.Theorems.Memory.Observe

/-!
# A T flip-flop from a torch and repeater latches

The D flip-flop of `DFlipFlop.lean` with its output fed back, inverted, to its data input:
on every rising edge of the clock `Q` becomes `not Q`. The inverter is a redstone torch on
the block the slave powers; two repeaters carry its signal back to a block next to the single
piece of dust in front of the master.

```
z = -2:  .  C  T  .  .     C: stone block with the input lever on top, T: torch on its east side
z = -1:  .  v  v  .  .     v: the two lock repeaters, pointing south
z =  0:  d  M  S  X  O     d: dust, M: master, S: slave (both pointing east), X: stone, O: lamp
z =  1:  J  <  <  t  .     t: torch on the south side of X, <: repeaters pointing west, J: stone
                           y = 1, seen from above, x to the right
```

This is the level-triggered input turned into a toggle: the lever may stay on or off for any
time, and only its going on counts. It is not the classic torch-only design (see
`Redstone/Theorems/Memory/Index.lean` for what is not proved).

What is proved (`Q` is the `powered` property of the slave; the lamp shows it):

* **A rising edge toggles**, for both values of `Q`, from a level at rest: the lever is used
  before game tick `k`, the slave switches in game tick `k + 5` (`toggles_on`,
  `toggles_off`).
* **Nothing else toggles**: while the lever stays on, `Q` holds for ever, although the
  feedback has changed the data input (`high_holds_on`, `high_holds_off`); the falling edge
  leaves `Q` as it is, and with the lever off `Q` holds for ever (`falling_keeps_on`;
  `circuit_quiescent` for `Q = 0`).
* **The feedback** is back at the master twelve game ticks after the edge (`feedback`).
* Two pulses bring back the blocks the circuit started with (`back_to_start`).

The level is loaded raw with the lever off and `Q = 0`: the torch `t` is lit, so the dust and
the master are on. It is at rest, and it is the state the circuit itself returns to.
-/

set_option Elab.async false

namespace Redstone.Theorems.Memory.TorchRepeaterTFF

/-- The input lever `T`, on top of the clock block. -/
def lever : Pos := ⟨1, 2, -2⟩

/-- The master repeater. -/
def master : Pos := ⟨1, 1, 0⟩

/-- The slave repeater: its `powered` property is `Q`. -/
def slave : Pos := ⟨2, 1, 0⟩

/-- The lamp at the output. -/
def lamp : Pos := ⟨4, 1, 0⟩

/-- The torch that inverts `Q`. -/
def feedbackTorch : Pos := ⟨3, 1, 1⟩

/-- The dust in front of the master: the data input. -/
def dust : Pos := ⟨0, 1, 0⟩

/-- The stone floor under the circuit. -/
def floor : List (Pos × Block) :=
  (List.range 5).flatMap fun x =>
    (List.range 4).map fun z => (⟨x, 0, (z : ℤ) - 2⟩, Block.plain .stone)

/-- The flip-flop with the lever off and `Q = 0`. -/
def circuit : Level :=
  .ofCells (floor ++ [
    (master, blk% "minecraft:repeater[delay=1,facing=west,locked=false,powered=true]"),
    (slave, blk% "minecraft:repeater[delay=1,facing=west,locked=true,powered=false]"),
    (⟨3, 1, 0⟩, .plain .stone),
    (lamp, .redstoneLamp ⟨false⟩),
    (⟨1, 1, -2⟩, .plain .stone),
    (lever, .lever ⟨.floor, .north, false⟩),
    (⟨2, 1, -2⟩, .redstoneWallTorch ⟨.east, true⟩),
    (⟨1, 1, -1⟩, blk% "minecraft:repeater[delay=1,facing=north,locked=false,powered=false]"),
    (⟨2, 1, -1⟩, blk% "minecraft:repeater[delay=1,facing=north,locked=false,powered=true]"),
    (feedbackTorch, .redstoneWallTorch ⟨.south, true⟩),
    (⟨2, 1, 1⟩, blk% "minecraft:repeater[delay=1,facing=east,locked=false,powered=true]"),
    (⟨1, 1, 1⟩, blk% "minecraft:repeater[delay=1,facing=east,locked=false,powered=true]"),
    (⟨0, 1, 1⟩, .plain .stone),
    (dust, blk% "minecraft:redstone_wire[east=side,north=none,power=15,south=none,west=side]")])

/-- Two pulses of 16 game ticks, 16 game ticks apart: the lever goes on before game ticks 1
and 33 and off before game ticks 17 and 49; 64 game ticks. -/
def schedule : Schedule :=
  .first [.use lever .up] 16 ++ .first [.use lever .up] 16 ++
    .first [.use lever .up] 16 ++ .first [.use lever .up] 16

checkpoints state := schedule from circuit

/-- The input and the state: the lever, `Q` (the `powered` property of the slave), and the
lamp. -/
def flipFlop (l : Level) : Option Bool × Option Bool × Option Bool :=
  (leverAt? l lever, (repeaterAt? l slave).map (·.1), lampAt? l lamp)

/-- The circuit as built is at rest, with the lever off and `Q = 0`. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧ flipFlop circuit = (some false, some false, some false) := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Rising edge, `Q = 0`: `Q` becomes 1.** The lever is switched on before game tick 1.
After game tick 5 the slave is still off; after game tick 6 it is on and the lamp is lit. -/
theorem toggles_on :
    flipFlop (rules.runSchedule (schedule.take 5) circuit) = (some true, some false, some false) ∧
      flipFlop (rules.runSchedule (schedule.take 6) circuit) = (some true, some true, some true) ∧
      (rules.runSchedule (schedule.take 6) circuit).overflow = false := by
  rw [state_run_5, state_run_6]
  circuit_decide

assert_standard_axioms toggles_on

/-- **The feedback.** The torch that inverts `Q` is out after game tick 8, and the dust in
front of the master has lost its power after game tick 12, twelve game ticks after the edge.
The master is locked and keeps the old value: `Q` does not toggle a second time. -/
theorem feedback :
    torchAt? (rules.runSchedule (schedule.take 7) circuit) feedbackTorch = some true ∧
      torchAt? (rules.runSchedule (schedule.take 8) circuit) feedbackTorch = some false ∧
      (rules.runSchedule (schedule.take 11) circuit).dustPower dust = 15 ∧
      (rules.runSchedule (schedule.take 12) circuit).dustPower dust = 0 ∧
      repeaterAt? (rules.runSchedule (schedule.take 12) circuit) master = some (true, true) ∧
      (rules.runSchedule (schedule.take 12) circuit).overflow = false := by
  rw [state_run_7, state_run_8, state_run_11, state_run_12]
  circuit_decide

assert_standard_axioms feedback

/-- **While the lever stays on, `Q = 1` holds for ever.** After game tick 13 the level is at
rest with the lever on. -/
theorem high_holds_on (n : ℕ) :
    flipFlop (rules.steps n (rules.runSchedule (schedule.take 13) circuit)) =
        (some true, some true, some true) ∧
      (rules.steps n (rules.runSchedule (schedule.take 13) circuit)).overflow = false := by
  rw [state_run_13, rules.steps_of_quiescent (by circuit_decide)]
  simp only [flipFlop, leverAt?, repeaterAt?, lampAt?, Level.blockAt_advance,
    Level.overflow_advance]
  circuit_decide

assert_standard_axioms high_holds_on

/-- **The falling edge does not toggle, and with the lever off `Q = 1` holds for ever.** The
lever is switched off before game tick 17. After game tick 20 the master has taken the new
data (`not Q`, off) and the slave is locked, still on. After game tick 22 the level is at
rest. -/
theorem falling_keeps_on (n : ℕ) :
    repeaterAt? (rules.runSchedule (schedule.take 20) circuit) master = some (false, false) ∧
      repeaterAt? (rules.runSchedule (schedule.take 20) circuit) slave = some (true, true) ∧
      flipFlop (rules.steps n (rules.runSchedule (schedule.take 22) circuit)) =
        (some false, some true, some true) ∧
      (rules.steps n (rules.runSchedule (schedule.take 22) circuit)).overflow = false := by
  rw [state_run_20, state_run_22, rules.steps_of_quiescent (by circuit_decide)]
  simp only [flipFlop, leverAt?, repeaterAt?, lampAt?, Level.blockAt_advance,
    Level.overflow_advance]
  circuit_decide

assert_standard_axioms falling_keeps_on

/-- **Rising edge, `Q = 1`: `Q` becomes 0.** The level is at rest; the lever is switched on
before game tick 33. After game tick 37 the slave is still on; after game tick 38 it is off.
The lamp goes out after game tick 42. -/
theorem toggles_off :
    flipFlop (rules.runSchedule (schedule.take 32) circuit) = (some false, some true, some true) ∧
      (rules.runSchedule (schedule.take 32) circuit).Quiescent ∧
      flipFlop (rules.runSchedule (schedule.take 37) circuit) = (some true, some true, some true) ∧
      flipFlop (rules.runSchedule (schedule.take 38) circuit) = (some true, some false, some true) ∧
      flipFlop (rules.runSchedule (schedule.take 41) circuit) = (some true, some false, some true) ∧
      flipFlop (rules.runSchedule (schedule.take 42) circuit) =
        (some true, some false, some false) ∧
      (rules.runSchedule (schedule.take 42) circuit).overflow = false := by
  rw [state_run_32, state_run_37, state_run_38, state_run_41, state_run_42]
  circuit_decide

assert_standard_axioms toggles_off

/-- **While the lever stays on, `Q = 0` holds for ever.** After game tick 45 the level is at
rest with the lever on. -/
theorem high_holds_off (n : ℕ) :
    flipFlop (rules.steps n (rules.runSchedule (schedule.take 45) circuit)) =
        (some true, some false, some false) ∧
      (rules.steps n (rules.runSchedule (schedule.take 45) circuit)).overflow = false := by
  rw [state_run_45, rules.steps_of_quiescent (by circuit_decide)]
  simp only [flipFlop, leverAt?, repeaterAt?, lampAt?, Level.blockAt_advance,
    Level.overflow_advance]
  circuit_decide

assert_standard_axioms high_holds_off

/-- **Two pulses return to the start.** The second falling edge (before game tick 49) leaves
`Q = 0`; after the whole schedule the blocks are those the circuit started with, and the
level is at rest. -/
theorem back_to_start :
    flipFlop (rules.runSchedule (schedule.take 53) circuit) =
        (some false, some false, some false) ∧
      (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).blockEntities = circuit.blockEntities ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_53, state_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Memory.TorchRepeaterTFF
