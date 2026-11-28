import Redstone.Theorems.Memory.Observe

/-!
# A two-bit ripple counter from two copper-bulb T flip-flops

Two copper bulbs in a row. The first is toggled by a stone button. A comparator reads the
first bulb into a stone block, and a redstone torch on that block feeds the second bulb: the
torch is lit while the first bulb is unlit, so the second bulb sees a signal *appear* exactly
when the first bulb goes out. That is the carry of a binary counter.

```
z = 0:  b  C0  >  B  T  C1     b: stone button, C0: the low bit, >: comparator pointing east,
                               B: stone block, T: torch on the east side of B, C1: the high bit
                               y = 1, seen from above, x to the right
```

The count is the pair (light of `C1`, light of `C0`). What is proved:

* **Counting.** Starting from 0, the count after each of four presses of the button is 1, 2,
  3 and 0 again (`counts`); each time the level is at rest before the next press.
* **Each count holds for ever** while the button is not pressed (`holds_one`, `holds_two`,
  `holds_three`; the count 0 is the circuit as built, `circuit_quiescent`).
* **The carry**: the button is pressed before game tick `k`; the comparator switches in game
  tick `k + 1`, and the torch and with it the high bulb in game tick `k + 3` (`carry_sets`,
  `carry_clears`).
* **Four presses return to the start**: the blocks and block entities are those the counter
  started with (`back_to_start`).

The level is loaded raw, in the state with count 0: both bulbs unlit, the high bulb powered by
the torch. The counter itself is in that state after every fourth press.
-/

set_option Elab.async false

namespace Redstone.Theorems.Memory.RippleCounter

/-- The stone button: the pulses to count. -/
def button : Pos := ⟨0, 1, 0⟩

/-- The bulb of the low bit. -/
def low : Pos := ⟨1, 1, 0⟩

/-- The comparator that reads the low bit. -/
def comparator : Pos := ⟨2, 1, 0⟩

/-- The torch that inverts the low bit: the carry. -/
def torch : Pos := ⟨4, 1, 0⟩

/-- The bulb of the high bit. -/
def high : Pos := ⟨5, 1, 0⟩

/-- The stone floor under the circuit. -/
def floor : List (Pos × Block) := (List.range 6).map fun x => (⟨x, 0, 0⟩, Block.plain .stone)

/-- The counter at 0. -/
def circuit : Level :=
  .ofCells (floor ++ [
    (button, blk% "minecraft:stone_button[face=floor,facing=north,powered=false]"),
    (low, blk% "minecraft:waxed_copper_bulb[lit=false,powered=false]"),
    (comparator, blk% "minecraft:comparator[facing=west,mode=compare,powered=false]"),
    (⟨3, 1, 0⟩, .plain .stone),
    (torch, .redstoneWallTorch ⟨.east, true⟩),
    (high, blk% "minecraft:waxed_copper_bulb[lit=false,powered=true]")])

/-- The button is pressed before game ticks 1, 29, 57 and 85; 112 game ticks. -/
def schedule : Schedule :=
  .first [.use button .up] 28 ++ .first [.use button .up] 28 ++
    .first [.use button .up] 28 ++ .first [.use button .up] 28

checkpoints state := schedule from circuit

/-- The count: the lights of the high bulb and of the low bulb. -/
def count (l : Level) : Option Bool × Option Bool :=
  ((bulbAt? l high).map (·.1), (bulbAt? l low).map (·.1))

/-- The circuit as built is at rest, at count 0. -/
theorem circuit_quiescent : circuit.Quiescent ∧ count circuit = (some false, some false) := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Counting.** After the first press the count is 1, after the second 2, after the third 3
and after the fourth 0. Each count is read 28 game ticks after its press, when the level is
at rest again. -/
theorem counts :
    count (rules.runSchedule (schedule.take 28) circuit) = (some false, some true) ∧
      (rules.runSchedule (schedule.take 28) circuit).Quiescent ∧
      count (rules.runSchedule (schedule.take 56) circuit) = (some true, some false) ∧
      (rules.runSchedule (schedule.take 56) circuit).Quiescent ∧
      count (rules.runSchedule (schedule.take 84) circuit) = (some true, some true) ∧
      (rules.runSchedule (schedule.take 84) circuit).Quiescent ∧
      count (rules.runSchedule (schedule.take 112) circuit) = (some false, some false) ∧
      (rules.runSchedule (schedule.take 112) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 112) circuit).overflow = false := by
  rw [state_run_28, state_run_56, state_run_84, state_run_112]
  circuit_decide

assert_standard_axioms counts

/-- **The low bit toggles at once.** After the very game tick of each press the low bulb has
switched its light. -/
theorem low_bit_toggles :
    (count (rules.runSchedule (schedule.take 1) circuit)).2 = some true ∧
      (count (rules.runSchedule (schedule.take 29) circuit)).2 = some false ∧
      (count (rules.runSchedule (schedule.take 57) circuit)).2 = some true ∧
      (count (rules.runSchedule (schedule.take 85) circuit)).2 = some false ∧
      (rules.runSchedule (schedule.take 85) circuit).overflow = false := by
  rw [state_run_1, state_run_29, state_run_57, state_run_85]
  circuit_decide

assert_standard_axioms low_bit_toggles

/-- **The carry sets the high bit.** The second press (before game tick 29) puts the low bulb
out. The torch is lit again after game tick 32, and with it the high bulb: neither is lit
after game tick 31, both are after game tick 32. -/
theorem carry_sets :
    torchAt? (rules.runSchedule (schedule.take 31) circuit) torch = some false ∧
      bulbAt? (rules.runSchedule (schedule.take 31) circuit) high = some (false, false) ∧
      torchAt? (rules.runSchedule (schedule.take 32) circuit) torch = some true ∧
      bulbAt? (rules.runSchedule (schedule.take 32) circuit) high = some (true, true) ∧
      (rules.runSchedule (schedule.take 32) circuit).overflow = false := by
  rw [state_run_31, state_run_32]
  circuit_decide

assert_standard_axioms carry_sets

/-- **No carry when the low bit goes on.** The first and the third press light the low bulb;
the torch goes out (after game ticks 4 and 60) and the high bulb only clears `powered`: its
light is as before. -/
theorem no_carry :
    bulbAt? (rules.runSchedule (schedule.take 3) circuit) high = some (false, true) ∧
      bulbAt? (rules.runSchedule (schedule.take 4) circuit) high = some (false, false) ∧
      bulbAt? (rules.runSchedule (schedule.take 59) circuit) high = some (true, true) ∧
      bulbAt? (rules.runSchedule (schedule.take 60) circuit) high = some (true, false) ∧
      (rules.runSchedule (schedule.take 60) circuit).overflow = false := by
  rw [state_run_3, state_run_4, state_run_59, state_run_60]
  circuit_decide

assert_standard_axioms no_carry

/-- **The carry clears the high bit.** The fourth press (before game tick 85) puts the low
bulb out; after game tick 88 the torch is lit and the high bulb, which was lit, is out: the
counter wraps from 3 to 0. -/
theorem carry_clears :
    bulbAt? (rules.runSchedule (schedule.take 87) circuit) high = some (true, false) ∧
      bulbAt? (rules.runSchedule (schedule.take 88) circuit) high = some (false, true) ∧
      (rules.runSchedule (schedule.take 88) circuit).overflow = false := by
  rw [state_run_87, state_run_88]
  circuit_decide

assert_standard_axioms carry_clears

/-- **The count 1 holds for ever** while the button is not pressed. -/
theorem holds_one (n : ℕ) :
    count (rules.steps n (rules.runSchedule (schedule.take 28) circuit)) =
        (some false, some true) ∧
      (rules.steps n (rules.runSchedule (schedule.take 28) circuit)).overflow = false := by
  rw [state_run_28, rules.steps_of_quiescent (by circuit_decide)]
  simp only [count, bulbAt?, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms holds_one

/-- **The count 2 holds for ever** while the button is not pressed. -/
theorem holds_two (n : ℕ) :
    count (rules.steps n (rules.runSchedule (schedule.take 56) circuit)) =
        (some true, some false) ∧
      (rules.steps n (rules.runSchedule (schedule.take 56) circuit)).overflow = false := by
  rw [state_run_56, rules.steps_of_quiescent (by circuit_decide)]
  simp only [count, bulbAt?, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms holds_two

/-- **The count 3 holds for ever** while the button is not pressed. -/
theorem holds_three (n : ℕ) :
    count (rules.steps n (rules.runSchedule (schedule.take 84) circuit)) =
        (some true, some true) ∧
      (rules.steps n (rules.runSchedule (schedule.take 84) circuit)).overflow = false := by
  rw [state_run_84, rules.steps_of_quiescent (by circuit_decide)]
  simp only [count, bulbAt?, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms holds_three

/-- **Four presses return to the start.** After the whole schedule the blocks and the block
entities are those the counter started with, and the level is at rest. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).blockEntities = circuit.blockEntities ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Memory.RippleCounter
