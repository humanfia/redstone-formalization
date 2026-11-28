import Redstone.Proof.Circuit

/-!
# The comparator subtraction clock

A comparator in subtraction mode whose output is led back into its own side by three pieces
of redstone dust, with a block of redstone at its input. The layer `y = 1` on a 2×2 stone
floor, seen from above (east is right, south is down); `R` is the block of redstone, `C` the
comparator (its output is to the east), `d` dust:

```
       x=-1  0  1
  z=0    R   C  d
  z=1        d  d
```

In subtraction mode the output is the input minus the side signal. The input is always 15.
While the output is 15 the dust carries 15, 14 and 13 round to the side, so the comparator
computes 15 - 13 = 2; while the output is 2 the dust carries 2, 1 and 0, the side signal is
0, and the comparator computes 15 again. A comparator changes its output 2 game ticks after
its inputs change, so **the output alternates between 15 and 2 every 2 game ticks (one
redstone tick), with a period of 4 game ticks**. The output is never zero: the `powered`
property of the comparator stays on, and what alternates is the signal strength, which the
comparator keeps in its block entity.

What is proved:

* the output signal of the comparator and the power of the three pieces of dust after each
  of 14 game ticks (`alternates`): the start and three periods;
* the cycle certificate (`cycle`): 4 game ticks take the level after game tick 6 to itself,
  moved on in time by 4 game ticks, with 26 more ticks scheduled.

The certificate says that the level repeats once. That it repeats for ever follows only if
a game tick commutes with the time shift on these levels (`Rules.periodic_of_shiftInvariant`).
`Redstone/Lemmas/ShiftInvariant.lean` proves that for levels without redstone dust; for dust
it is not proved. It is not proved for the comparator either.

The level is loaded raw, without the block of redstone, and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Clock.ComparatorSubtraction

/-- The 2×2 stone floor. -/
def floor : List (Pos × Block) :=
  (List.range 2).flatMap fun x => (List.range 2).map fun z => (⟨x, 0, z⟩, Block.plain .stone)

/-- The position of the comparator. Its input is to the west, its output to the east. -/
def comparator : Pos := ⟨0, 1, 0⟩

/-- The cell at the input of the comparator, where the block of redstone is put. -/
def source : Pos := ⟨-1, 1, 0⟩

/-- The three pieces of dust, from the output of the comparator round to its south side. -/
def wires : List Pos := [⟨1, 1, 0⟩, ⟨1, 1, 1⟩, ⟨0, 1, 1⟩]

/-- The comparator in subtraction mode with its loop of dust, and nothing at its input: all
off. -/
def circuit : Level :=
  .ofCells (floor ++ [
    (comparator, blk% "minecraft:comparator[facing=west,mode=subtract,powered=false]"),
    (⟨1, 1, 0⟩, blk% "minecraft:redstone_wire[east=none,north=none,power=0,south=side,west=side]"),
    (⟨1, 1, 1⟩, blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=none,west=side]"),
    (⟨0, 1, 1⟩, blk% "minecraft:redstone_wire[east=side,north=side,power=0,south=none,west=none]")])

/-- A block of redstone is put at the input before game tick 1; 14 game ticks in all. -/
def schedule : Schedule := [[.set source (.plain .redstone_block)]] ++ Schedule.idle 13

/-- The output signal the comparator keeps in its block entity, and the power of the three
pieces of dust. -/
def look (l : Level) : ℕ × List ℕ :=
  (match l.blockEntities comparator with
    | some (.comparator d) => d.output
    | _ => 0,
    wires.map l.dustPower)

checkpoints state := schedule from circuit

/-- The comparator and its loop, with nothing at the input, are at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **The output alternates between 15 and 2.** The block of redstone is put at the input
before game tick 1. After game tick 2 the output is 15 and the dust carries 15, 14, 13; after
game tick 4 the output is 2 and the dust carries 2, 1, 0; and so on, every two game ticks,
for three periods of four game ticks. The model reaches no bound. -/
theorem alternates :
    look (rules.runSchedule (schedule.take 1) circuit) = (0, [0, 0, 0]) ∧
      look (rules.runSchedule (schedule.take 2) circuit) = (15, [15, 14, 13]) ∧
      look (rules.runSchedule (schedule.take 3) circuit) = (15, [15, 14, 13]) ∧
      look (rules.runSchedule (schedule.take 4) circuit) = (2, [2, 1, 0]) ∧
      look (rules.runSchedule (schedule.take 5) circuit) = (2, [2, 1, 0]) ∧
      look (rules.runSchedule (schedule.take 6) circuit) = (15, [15, 14, 13]) ∧
      look (rules.runSchedule (schedule.take 7) circuit) = (15, [15, 14, 13]) ∧
      look (rules.runSchedule (schedule.take 8) circuit) = (2, [2, 1, 0]) ∧
      look (rules.runSchedule (schedule.take 9) circuit) = (2, [2, 1, 0]) ∧
      look (rules.runSchedule (schedule.take 10) circuit) = (15, [15, 14, 13]) ∧
      look (rules.runSchedule (schedule.take 11) circuit) = (15, [15, 14, 13]) ∧
      look (rules.runSchedule (schedule.take 12) circuit) = (2, [2, 1, 0]) ∧
      look (rules.runSchedule (schedule.take 13) circuit) = (2, [2, 1, 0]) ∧
      look (rules.runSchedule (schedule.take 14) circuit) = (15, [15, 14, 13]) ∧
      (rules.runSchedule (schedule.take 14) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13,
    state_run_14]
  circuit_decide

assert_standard_axioms alternates

/-- **The cycle certificate.** Four game ticks take the level after game tick 6 to itself,
moved on in time by 4 game ticks, with 26 more ticks scheduled: every block, the block entity
of the comparator with its output signal, the scheduled tick, every counter. -/
theorem cycle : rules.Cycle (rules.runSchedule (schedule.take 6) circuit) 4 26 := by
  rw [state_run_6]
  exact (Rules.steps_of_runs (k := 6) (m := 4) state_run_6 state_run_10
    (by circuit_decide)).trans (Level.eq_of_beqBlocks (by circuit_decide))

assert_standard_axioms cycle

end Redstone.Theorems.Clock.ComparatorSubtraction
