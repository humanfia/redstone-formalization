import Redstone.Theorems.Analog.Common

/-!
# What counts as a side input of a comparator

A comparator in compare mode reads a whole cake (14) at its back and has a piece of redstone
dust in front. Different blocks are put at its sides, one after the other, and the output
shows which of them the comparator takes for a side input.

```
z = -2:      (R)           (R): a block of redstone, placed late, that feeds the repeater
z = -1:       N            N:   the north side, where the blocks are tried
z =  0:   K   C   o        K: cake, C: comparator (reads west, emits east), o: output dust
z =  1:       X            X:   stone at the south side, with a lever on top (y = 2)
x =      -1   0   1        y = 1, seen from above
```

The rule of the game (`SignalGetter.getControlInputSignal`): a block of redstone counts 15,
redstone dust its power, any other signal source its *direct* signal towards the comparator,
and every other block nothing. What is proved (1 redstone tick = 2 game ticks), each step
starting from a level at rest:

| at the side | side input | output |
|---|---|---|
| nothing | 0 | 14 |
| a stone block powered with 15 by a lever | 0 | 14 (`powered_block_is_no_side_input`) |
| a lit redstone torch | 0 | 14 (`torch_is_no_side_input`) |
| a block of redstone | 15 | 0 (`redstone_block_is_side_input`) |
| a repeater that points at the comparator, off | 0 | 14 |
| the same repeater, on | 15 | 0 (`repeater_is_side_input`) |

A powered solid block gives its power to the dust and the lamps around it, but not to the side
of a comparator; a redstone torch is a signal source, but its direct signal goes up only.
Redstone dust at the side, with a power below and above the input, is in
`CompareSubtract.lean`; a comparator that points at the side in `SubtractionChain.lean`.
The generic statements are `Comparator.controlInput_redstone_block`, `controlInput_wire`,
`controlInput_of_not_source` and `controlInput_of_source` in
`Redstone/Lemmas/Comparator.lean`.

The level is loaded raw without the cake and with the lever off, and is at rest
(`circuit_quiescent`).
-/

set_option Elab.async false
-- The statements are conjunctions of comparisons of tuples; finding their `Decidable`
-- instance takes more steps than the default allows.
set_option synthInstance.maxSize 4096

namespace Redstone.Theorems.Analog.SideInput

/-- The cake at the back of the comparator. -/
def cake : Pos := ⟨-1, 1, 0⟩

/-- The comparator. -/
def cmp : Pos := ⟨0, 1, 0⟩

/-- The dust in front of the comparator. -/
def out : Pos := ⟨1, 1, 0⟩

/-- The north side of the comparator, where blocks are tried. -/
def north : Pos := ⟨0, 1, -1⟩

/-- The place behind the north side, where the block of redstone that feeds the repeater is
put. -/
def feed : Pos := ⟨0, 1, -2⟩

/-- The stone block at the south side of the comparator. -/
def south : Pos := ⟨0, 1, 1⟩

/-- The lever on top of the stone block. -/
def lever : Pos := ⟨0, 2, 1⟩

/-- A repeater at the north side that points at the comparator: it reads the block to its
north and emits to the south. -/
def repeater (powered : Bool) : Block :=
  .repeater { delay := ⟨1, by decide, by decide⟩, facing := .north, locked := false, powered }

/-- A comparator with a piece of dust in front, and a stone block with a lever on top at its
south side, on a stone floor. The cake is placed by the schedule. -/
def circuit : Level :=
  .ofCells (floor [-1, 0, 1] [-2, -1, 0, 1] ++
    [(cmp, .comparator ⟨.west, .compare, false⟩), (out, wireEW), (south, .plain .stone),
      (lever, .lever ⟨.floor, .north, false⟩)])

/-- The cake is placed before game tick 1. The lever is switched on before game tick 5 and off
before game tick 9. A lit redstone torch is put at the north side before game tick 11, a block
of redstone in its place before game tick 15, and air before game tick 19. Before game tick 23
the repeater is put at the north side and then a block of redstone behind it; before game tick
29 that block is removed. Thirty-four game ticks. -/
def schedule : Schedule :=
  .first [.set cake (.cake ⟨0⟩)] 4 ++ .first [.use lever .up] 4 ++ .first [.use lever .up] 2 ++
    .first [.set north (.redstoneTorch ⟨true⟩)] 4 ++
    .first [.set north (.plain .redstone_block)] 4 ++ .first [.set north .AIR] 4 ++
    .first [.set north (repeater false), .set feed (.plain .redstone_block)] 6 ++
    .first [.set feed .AIR] 6

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- What is observed: the block at the north side, the comparator, and the power of the dust
at the output. -/
def observe (l : Level) : Block × (Bool × ℕ) × ℕ :=
  (l.blockAt north, comparator l cmp, l.dustPower out)

/-- With nothing at the sides the comparator emits the 14 of the cake. -/
theorem no_side_input :
    observe circuit = (.AIR, (false, 0), 0) ∧
      observe (rules.runSchedule (schedule.take 4) circuit) = (.AIR, (true, 14), 14) ∧
      (rules.runSchedule (schedule.take 4) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_4]
  circuit_decide

assert_standard_axioms no_side_input

/-- **A powered solid block is not a side input.** With the lever on, the stone block at the
south side receives 15, and the comparator goes on emitting 14: nothing is even scheduled. -/
theorem powered_block_is_no_side_input :
    (rules.runSchedule (schedule.take 4) circuit).signalTo south = 0 ∧
      (rules.runSchedule (schedule.take 5) circuit).signalTo south = 15 ∧
      (rules.runSchedule (schedule.take 8) circuit).signalTo south = 15 ∧
      observe (rules.runSchedule (schedule.take 5) circuit) = (.AIR, (true, 14), 14) ∧
      observe (rules.runSchedule (schedule.take 8) circuit) = (.AIR, (true, 14), 14) ∧
      (rules.runSchedule (schedule.take 5) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 8) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 10) circuit).signalTo south = 0 ∧
      (rules.runSchedule (schedule.take 10) circuit).overflow = false := by
  rw [state_run_4, state_run_5, state_run_8, state_run_10]
  circuit_decide

assert_standard_axioms powered_block_is_no_side_input

/-- **A redstone torch is not a side input**: its direct signal goes up only. With a lit torch
at the north side the comparator goes on emitting 14. -/
theorem torch_is_no_side_input :
    observe (rules.runSchedule (schedule.take 11) circuit) =
        (.redstoneTorch ⟨true⟩, (true, 14), 14) ∧
      observe (rules.runSchedule (schedule.take 14) circuit) =
        (.redstoneTorch ⟨true⟩, (true, 14), 14) ∧
      (rules.runSchedule (schedule.take 11) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 14) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 14) circuit).overflow = false := by
  rw [state_run_11, state_run_14]
  circuit_decide

assert_standard_axioms torch_is_no_side_input

/-- **A block of redstone at the side counts 15**: it is stronger than the 14 at the back, and
the comparator is off two game ticks after the block is placed, and on again two game ticks
after it is taken away. -/
theorem redstone_block_is_side_input :
    observe (rules.runSchedule (schedule.take 15) circuit) =
        (.plain .redstone_block, (true, 14), 14) ∧
      observe (rules.runSchedule (schedule.take 16) circuit) =
        (.plain .redstone_block, (false, 0), 0) ∧
      observe (rules.runSchedule (schedule.take 18) circuit) =
        (.plain .redstone_block, (false, 0), 0) ∧
      observe (rules.runSchedule (schedule.take 19) circuit) = (.AIR, (false, 0), 0) ∧
      observe (rules.runSchedule (schedule.take 20) circuit) = (.AIR, (true, 14), 14) ∧
      observe (rules.runSchedule (schedule.take 22) circuit) = (.AIR, (true, 14), 14) ∧
      (rules.runSchedule (schedule.take 18) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 22) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 22) circuit).overflow = false := by
  rw [state_run_15, state_run_16, state_run_18, state_run_19, state_run_20, state_run_22]
  circuit_decide

assert_standard_axioms redstone_block_is_side_input

/-- **A repeater that points at the side counts when it is on.** The repeater and its feed are
placed before game tick 23: the repeater is off and the comparator emits 14. The repeater
switches on in game tick 24, and the comparator is off in game tick 26. The feed is removed
before game tick 29: the repeater is off in game tick 30 and the comparator emits 14 again in
game tick 32. -/
theorem repeater_is_side_input :
    observe (rules.runSchedule (schedule.take 23) circuit) = (repeater false, (true, 14), 14) ∧
      observe (rules.runSchedule (schedule.take 24) circuit) = (repeater true, (true, 14), 14) ∧
      observe (rules.runSchedule (schedule.take 25) circuit) = (repeater true, (true, 14), 14) ∧
      observe (rules.runSchedule (schedule.take 26) circuit) = (repeater true, (false, 0), 0) ∧
      observe (rules.runSchedule (schedule.take 28) circuit) = (repeater true, (false, 0), 0) ∧
      observe (rules.runSchedule (schedule.take 30) circuit) = (repeater false, (false, 0), 0) ∧
      observe (rules.runSchedule (schedule.take 32) circuit) = (repeater false, (true, 14), 14) ∧
      observe (rules.runSchedule schedule circuit) = (repeater false, (true, 14), 14) ∧
      (rules.runSchedule (schedule.take 28) circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_23, state_run_24, state_run_25, state_run_26, state_run_28, state_run_30,
    state_run_32, state_run]
  circuit_decide

assert_standard_axioms repeater_is_side_input

end Redstone.Theorems.Analog.SideInput
