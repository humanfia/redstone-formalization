import Redstone.Theorems.Analog.Common

/-!
# The analog memory cell: a ring of comparators that holds a signal strength

Four comparators in a ring, each reading one piece of redstone dust that the comparator before
it powers. A comparator gives the dust in front of it exactly the strength it emits, and the
next comparator reads the power of the dust at its back, so nothing is lost on the way round:
whatever strength is in the ring stays there. A fifth comparator feeds the ring from a source
block; a lever with a piece of dust at the side of one ring comparator, which is in subtract
mode, is the reset.

```
z = -2:   S                         S:  the source (a composter, a cake, a block of redstone)
z = -1:   I                         I:  input comparator (reads north, emits south)
z =  0:   d4  C1  d1                C1: reads west, emits east
z =  1:   C4      C2                C2: reads north, emits south; C4: reads south, emits north
z =  2:   d3  C3  d2                C3: reads east, emits west, subtract mode
z =  3:       r                     r:  reset dust at the side of C3
z =  4:       L                     L:  reset lever
x =       -1  0   1                 y = 1, seen from above; d1 .. d4: the dust of the ring
```

What is proved (1 redstone tick = 2 game ticks):

* **Write** (`writes_three`): a composter of level 3 is put at the source before game tick 1.
  The input comparator emits 3 in game tick 2, and the 3 goes round the ring, one comparator
  every two game ticks: `C1` in game tick 4, `C2` in 6, `C3` in 8, `C4` in 10.
* **Hold** (`holds_three`, `holds_for_ever`): the source is removed; the input comparator goes
  off and the ring keeps 3. The level is at rest, so the 3 is held for ever. The same for 14
  and for 15.
* **Only a stronger signal overwrites** (`keeps_the_stronger`): with 3 stored, a cake (14) at
  the source brings the ring to 14; with 14 stored, a composter of level 8 changes nothing.
  The cell stores the strongest signal it has seen since the last reset.
* **Reset** (`resets`, `resets_fifteen`): the lever gives 15 to the side of `C3`, which
  subtracts: `C3` goes off two game ticks later, and the zero goes round the ring, which is
  empty eight game ticks after the lever. Subtract mode is what makes the reset work for a
  stored 15 too: in compare mode a side input of 15 would let a rear input of 15 pass. After
  the lever is released the blocks are those the circuit started with.

The level is loaded raw with all comparators off and no source, and is at rest
(`circuit_quiescent`).
-/

set_option Elab.async false
-- The statements are conjunctions of comparisons of lists; finding their `Decidable` instance
-- takes more steps than the default allows.
set_option synthInstance.maxSize 4096

namespace Redstone.Theorems.Analog.MemoryCell

/-- The place of the source block that the input comparator reads. -/
def source : Pos := ⟨-1, 1, -2⟩

/-- The input comparator. -/
def input : Pos := ⟨-1, 1, -1⟩

/-- The four comparators of the ring, in the order in which the signal passes them. -/
def ring : List Pos := [⟨0, 1, 0⟩, ⟨1, 1, 1⟩, ⟨0, 1, 2⟩, ⟨-1, 1, 1⟩]

/-- The four pieces of dust of the ring: `d1` in front of `C1`, and so on. -/
def dust : List Pos := [⟨1, 1, 0⟩, ⟨1, 1, 2⟩, ⟨-1, 1, 2⟩, ⟨-1, 1, 0⟩]

/-- The reset dust at the side of `C3`. -/
def resetDust : Pos := ⟨0, 1, 3⟩

/-- The reset lever. -/
def lever : Pos := ⟨0, 1, 4⟩

/-- The ring of four comparators and four pieces of dust, the input comparator, and the reset
lever with its dust, on a stone floor. -/
def circuit : Level :=
  .ofCells (floor [-1, 0, 1] [-2, -1, 0, 1, 2, 3, 4] ++
    [(input, .comparator ⟨.north, .compare, false⟩),
      (⟨0, 1, 0⟩, .comparator ⟨.west, .compare, false⟩),
      (⟨1, 1, 1⟩, .comparator ⟨.north, .compare, false⟩),
      (⟨0, 1, 2⟩, .comparator ⟨.east, .subtract, false⟩),
      (⟨-1, 1, 1⟩, .comparator ⟨.south, .compare, false⟩),
      (⟨1, 1, 0⟩, .redstoneWire ⟨.none, .none, 0, .side, .side⟩),
      (⟨1, 1, 2⟩, .redstoneWire ⟨.none, .side, 0, .none, .side⟩),
      (⟨-1, 1, 2⟩, .redstoneWire ⟨.side, .side, 0, .none, .none⟩),
      (⟨-1, 1, 0⟩, .redstoneWire ⟨.side, .side, 0, .side, .none⟩),
      (resetDust, wireNS), (lever, .lever ⟨.floor, .north, false⟩)])

/-- A composter of level 3 at the source for twelve game ticks, then no source for four; a
cake for twelve, none for four; a composter of level 8 for six, none for four; the reset lever
on for ten game ticks and off for three. Fifty-five game ticks. -/
def schedule : Schedule :=
  .first [.set source (.composter ⟨3⟩)] 12 ++ .first [.set source .AIR] 4 ++
    .first [.set source (.cake ⟨0⟩)] 12 ++ .first [.set source .AIR] 4 ++
    .first [.set source (.composter ⟨8⟩)] 6 ++ .first [.set source .AIR] 4 ++
    .first [.use lever .up] 10 ++ .first [.use lever .up] 3

/-- From the empty cell: a block of redstone at the source for twelve game ticks, then no
source for four; the reset lever on for ten game ticks and off for three. Twenty-nine game
ticks. -/
def scheduleFifteen : Schedule :=
  .first [.set source (.plain .redstone_block)] 12 ++ .first [.set source .AIR] 4 ++
    .first [.use lever .up] 10 ++ .first [.use lever .up] 3

checkpoints state := schedule from circuit
checkpoints full := scheduleFifteen from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- What the four comparators of the ring emit, in the order of the ring: the stored output of
each while it is powered, and 0 while it is not. -/
def stored (l : Level) : List ℕ := ring.map (emitted l)

/-- The powers of the four pieces of dust of the ring. -/
def powers (l : Level) : List ℕ := dust.map l.dustPower

/-- **Writing 3.** The input comparator emits 3 two game ticks after the source appears, and
the 3 goes round the ring, one comparator every two game ticks. -/
theorem writes_three :
    stored circuit = [0, 0, 0, 0] ∧
      comparator (rules.runSchedule (schedule.take 1) circuit) input = (false, 0) ∧
      comparator (rules.runSchedule (schedule.take 2) circuit) input = (true, 3) ∧
      stored (rules.runSchedule (schedule.take 2) circuit) = [0, 0, 0, 0] ∧
      stored (rules.runSchedule (schedule.take 3) circuit) = [0, 0, 0, 0] ∧
      stored (rules.runSchedule (schedule.take 4) circuit) = [3, 0, 0, 0] ∧
      stored (rules.runSchedule (schedule.take 5) circuit) = [3, 0, 0, 0] ∧
      stored (rules.runSchedule (schedule.take 6) circuit) = [3, 3, 0, 0] ∧
      stored (rules.runSchedule (schedule.take 7) circuit) = [3, 3, 0, 0] ∧
      stored (rules.runSchedule (schedule.take 8) circuit) = [3, 3, 3, 0] ∧
      stored (rules.runSchedule (schedule.take 9) circuit) = [3, 3, 3, 0] ∧
      stored (rules.runSchedule (schedule.take 10) circuit) = [3, 3, 3, 3] ∧
      powers (rules.runSchedule (schedule.take 10) circuit) = [3, 3, 3, 3] ∧
      (rules.runSchedule (schedule.take 12) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 12) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_12]
  circuit_decide

assert_standard_axioms writes_three

/-- **Holding 3.** The source is removed before game tick 13: the input comparator is off in
game tick 14, and the ring keeps 3; the level is at rest. -/
theorem holds_three :
    comparator (rules.runSchedule (schedule.take 13) circuit) input = (true, 3) ∧
      comparator (rules.runSchedule (schedule.take 14) circuit) input = (false, 0) ∧
      stored (rules.runSchedule (schedule.take 16) circuit) = [3, 3, 3, 3] ∧
      powers (rules.runSchedule (schedule.take 16) circuit) = [3, 3, 3, 3] ∧
      (rules.runSchedule (schedule.take 16) circuit).blockAt source = .AIR ∧
      (rules.runSchedule (schedule.take 16) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 16) circuit).overflow = false := by
  rw [state_run_13, state_run_14, state_run_16]
  circuit_decide

assert_standard_axioms holds_three

/-- **The cell holds its strength for ever.** With no source and the reset lever off, the ring
keeps 3, keeps 14 and keeps 15: each of the three levels is at rest. -/
theorem holds_for_ever (n : ℕ) :
    stored (rules.steps n (rules.runSchedule (schedule.take 16) circuit)) = [3, 3, 3, 3] ∧
      stored (rules.steps n (rules.runSchedule (schedule.take 32) circuit)) =
        [14, 14, 14, 14] ∧
      stored (rules.steps n (rules.runSchedule (scheduleFifteen.take 16) circuit)) =
        [15, 15, 15, 15] ∧
      (rules.steps n (rules.runSchedule (schedule.take 16) circuit)).overflow = false ∧
      (rules.steps n (rules.runSchedule (schedule.take 32) circuit)).overflow = false ∧
      (rules.steps n (rules.runSchedule (scheduleFifteen.take 16) circuit)).overflow = false := by
  rw [state_run_16, state_run_32, full_run_16,
    rules.steps_of_quiescent (l := state_16) (by circuit_decide),
    rules.steps_of_quiescent (l := state_32) (by circuit_decide),
    rules.steps_of_quiescent (l := full_16) (by circuit_decide)]
  simp only [stored, emitted_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms holds_for_ever

/-- **Only a stronger signal overwrites.** With 3 stored, a cake at the source (14) brings the
ring to 14, again one comparator every two game ticks, and the 14 stays when the cake is
removed. With 14 stored, a composter of level 8 at the source makes the input comparator emit
8 and changes nothing in the ring. -/
theorem keeps_the_stronger :
    comparator (rules.runSchedule (schedule.take 18) circuit) input = (true, 14) ∧
      stored (rules.runSchedule (schedule.take 18) circuit) = [3, 3, 3, 3] ∧
      stored (rules.runSchedule (schedule.take 20) circuit) = [14, 3, 3, 3] ∧
      stored (rules.runSchedule (schedule.take 22) circuit) = [14, 14, 3, 3] ∧
      stored (rules.runSchedule (schedule.take 24) circuit) = [14, 14, 14, 3] ∧
      stored (rules.runSchedule (schedule.take 26) circuit) = [14, 14, 14, 14] ∧
      stored (rules.runSchedule (schedule.take 32) circuit) = [14, 14, 14, 14] ∧
      (rules.runSchedule (schedule.take 32) circuit).blockAt source = .AIR ∧
      (rules.runSchedule (schedule.take 32) circuit).Quiescent ∧
      comparator (rules.runSchedule (schedule.take 34) circuit) input = (true, 8) ∧
      stored (rules.runSchedule (schedule.take 38) circuit) = [14, 14, 14, 14] ∧
      (rules.runSchedule (schedule.take 38) circuit).Quiescent ∧
      stored (rules.runSchedule (schedule.take 42) circuit) = [14, 14, 14, 14] ∧
      (rules.runSchedule (schedule.take 42) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 42) circuit).overflow = false := by
  rw [state_run_18, state_run_20, state_run_22, state_run_24, state_run_26, state_run_32,
    state_run_34, state_run_38, state_run_42]
  circuit_decide

assert_standard_axioms keeps_the_stronger

/-- **Reset.** The lever is switched on before game tick 43, and the reset dust has 15 at once.
`C3` goes off in game tick 44, `C4` in 46, `C1` in 48, `C2` in 50: the ring is empty eight
game ticks after the lever. The lever is released before game tick 53, and the blocks and
block entities are then those the circuit started with. -/
theorem resets :
    (rules.runSchedule (schedule.take 43) circuit).dustPower resetDust = 15 ∧
      stored (rules.runSchedule (schedule.take 43) circuit) = [14, 14, 14, 14] ∧
      stored (rules.runSchedule (schedule.take 44) circuit) = [14, 14, 0, 14] ∧
      stored (rules.runSchedule (schedule.take 46) circuit) = [14, 14, 0, 0] ∧
      stored (rules.runSchedule (schedule.take 48) circuit) = [0, 14, 0, 0] ∧
      stored (rules.runSchedule (schedule.take 50) circuit) = [0, 0, 0, 0] ∧
      powers (rules.runSchedule (schedule.take 50) circuit) = [0, 0, 0, 0] ∧
      (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).blockEntities = circuit.blockEntities ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_43, state_run_44, state_run_46, state_run_48, state_run_50, state_run]
  circuit_decide

assert_standard_axioms resets

/-- **A stored 15 is written, held and reset too.** A block of redstone at the source gives
15: the ring holds 15 after the block is gone, and the reset empties it, because `C3`
subtracts the 15 at its side from the 15 at its back. -/
theorem resets_fifteen :
    stored (rules.runSchedule (scheduleFifteen.take 10) circuit) = [15, 15, 15, 15] ∧
      stored (rules.runSchedule (scheduleFifteen.take 16) circuit) = [15, 15, 15, 15] ∧
      (rules.runSchedule (scheduleFifteen.take 16) circuit).blockAt source = .AIR ∧
      comparator (rules.runSchedule (scheduleFifteen.take 16) circuit) input = (false, 0) ∧
      (rules.runSchedule (scheduleFifteen.take 16) circuit).Quiescent ∧
      stored (rules.runSchedule (scheduleFifteen.take 18) circuit) = [15, 15, 0, 15] ∧
      stored (rules.runSchedule (scheduleFifteen.take 24) circuit) = [0, 0, 0, 0] ∧
      (rules.runSchedule scheduleFifteen circuit).world = circuit.world ∧
      (rules.runSchedule scheduleFifteen circuit).Quiescent ∧
      (rules.runSchedule scheduleFifteen circuit).overflow = false := by
  rw [full_run_10, full_run_16, full_run_18, full_run_24, full_run]
  circuit_decide

assert_standard_axioms resets_fifteen

end Redstone.Theorems.Analog.MemoryCell
