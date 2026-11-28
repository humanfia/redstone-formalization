import Redstone.Proof.Circuit

/-!
# Two droppers facing each other are not a T flip-flop

A dropper that points up, a dropper on top of it that points down, and one item. A lever on
the side of the lower dropper powers both: the lower one directly, the upper one through the
lower one, which is a full block. A comparator reads the lower dropper. The idea, listed in
catalogues of circuits as a T flip-flop, is that each pulse makes the dropper that holds the
item push it into the other one, so that the comparator toggles with every pulse.

```
y = 2:       D            D (upper): dropper pointing down
y = 1:   C   D   l        D (lower): dropper pointing up; l: lever on its east side
y = 0:   s                C: comparator reading the lower dropper; s: stone
x:      -1   0   1
```

It does not toggle, in the model and by the game's code. Both droppers are triggered by the
same neighbour update and both schedule their tick four game ticks ahead; the two ticks run
in the same game tick, the lower dropper's first. If the lower dropper holds the item, it
pushes it up, and the upper dropper, whose tick runs next and which now holds the item, pushes
it down again. If the upper dropper holds the item, the lower one finds nothing to push, and
the upper one pushes the item down. Either way the item ends in the dropper whose tick runs
first.

What is proved:

* `at_rest`: both starting levels are quiescent.
* `pulse_from_above`: the item is in the upper dropper. A pulse of eight game ticks: the item
  is in the lower dropper after game tick 4, and the comparator gives 1 after game tick 6.
* `pulse_from_below`: the item is in the lower dropper. The same pulse: the item is in the
  lower dropper after every game tick, and the comparator gives 1 throughout.
* `second_pulse`: a second pulse on the level that the first one left (`pulse_from_above`)
  leaves the item in the lower dropper as well.
* `item_stays_below`: after the pulse, from either start, the level is quiescent: the item is
  in the lower dropper and the comparator gives 1 for ever.

So this circuit is a latch that a pulse sets and nothing resets. A T flip-flop needs the two
droppers to be triggered in turn, not together.

## Not proved

A working T flip-flop made of droppers and a hopper. The layouts that toggle gate the trigger
with the comparator's output; no such layout was found whose every state is a state of rest of
the model, and none is claimed here.

The levels are loaded raw; with the item in the lower dropper the comparator starts on, with
output 1, as it is at rest.
-/

set_option Elab.async false

-- The theorems are conjunctions of many equations between tuples, and the instance that
-- decides such an equation is large.
set_option synthInstance.maxSize 100000

namespace Redstone.Theorems.ContainerSignal.DropperPair

/-- The lower dropper, which points up. -/
def lower : Pos := ⟨0, 1, 0⟩

/-- The upper dropper, which points down. -/
def upper : Pos := ⟨0, 2, 0⟩

/-- The lever on the east side of the lower dropper. -/
def lever : Pos := ⟨1, 1, 0⟩

/-- The comparator that reads the lower dropper. -/
def comparator : Pos := ⟨-1, 1, 0⟩

/-- One piece of redstone in the first of nine slots. -/
def oneItem : Inventory := (Inventory.empty 9).setItem 0 (.of "minecraft:redstone" 1)

/-- The two droppers with the item in the upper one; the comparator is off. -/
def itemAbove : Level :=
  .ofCells [(lower, .dropper ⟨.up, false⟩), (upper, .dropper ⟨.down, false⟩),
      (lever, .lever ⟨.wall, .east, false⟩), (⟨-1, 0, 0⟩, .plain .stone),
      (comparator, .comparator ⟨.east, .compare, false⟩)]
    [(upper, .dropper { items := oneItem })]

/-- The two droppers with the item in the lower one; the comparator is on, with output 1. -/
def itemBelow : Level :=
  .ofCells [(lower, .dropper ⟨.up, false⟩), (upper, .dropper ⟨.down, false⟩),
      (lever, .lever ⟨.wall, .east, false⟩), (⟨-1, 0, 0⟩, .plain .stone),
      (comparator, .comparator ⟨.east, .compare, true⟩)]
    [(lower, .dropper { items := oneItem }), (comparator, .comparator { output := 1 })]

/-- One pulse: the lever is switched on before game tick 1 and off before game tick 9; 16 game
ticks. -/
def schedule : Schedule := .first [.use lever .up] 8 ++ .first [.use lever .up] 8

/-- The number of items in the dropper at `p`. -/
def dropperCount (l : Level) (p : Pos) : ℕ :=
  match l.blockEntities p with
  | some (.dropper d) => (d.items.map (·.count)).sum
  | _ => 0

/-- The output the comparator has stored. -/
def output (l : Level) : ℕ :=
  match l.blockEntities comparator with
  | some (.comparator d) => d.output
  | _ => 0

/-- What is observed: the numbers of items in the lower and in the upper dropper, and the
output of the comparator. -/
def observe (l : Level) : ℕ × ℕ × ℕ := (dropperCount l lower, dropperCount l upper, output l)

checkpoints above := schedule from itemAbove
checkpoints below := schedule from itemBelow
checkpoints again := schedule from above_16

/-- Both starting levels are at rest, with the item where it should be and the comparator
showing whether the lower dropper holds it. -/
theorem at_rest :
    itemAbove.Quiescent ∧ itemBelow.Quiescent ∧ observe itemAbove = (0, 1, 0) ∧
      observe itemBelow = (1, 0, 1) := by
  circuit_decide

assert_standard_axioms at_rest

/-- **A pulse with the item above moves it down.** Each line is the state after one game tick:
the items in the lower dropper, the items in the upper dropper, and the output of the
comparator. The lever is switched on before game tick 1; both droppers tick in game tick 4, and
the item is in the lower dropper after it; the comparator gives 1 after game tick 6. Switching
the lever off before game tick 9 changes nothing. -/
theorem pulse_from_above :
    observe (rules.runSchedule (schedule.take 1) itemAbove) = (0, 1, 0) ∧
      observe (rules.runSchedule (schedule.take 2) itemAbove) = (0, 1, 0) ∧
      observe (rules.runSchedule (schedule.take 3) itemAbove) = (0, 1, 0) ∧
      observe (rules.runSchedule (schedule.take 4) itemAbove) = (1, 0, 0) ∧
      observe (rules.runSchedule (schedule.take 5) itemAbove) = (1, 0, 0) ∧
      observe (rules.runSchedule (schedule.take 6) itemAbove) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 7) itemAbove) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 8) itemAbove) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 9) itemAbove) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 10) itemAbove) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 11) itemAbove) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 12) itemAbove) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 13) itemAbove) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 14) itemAbove) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 15) itemAbove) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 16) itemAbove) = (1, 0, 1) ∧
      (rules.runSchedule (schedule.take 16) itemAbove).overflow = false := by
  rw [above_run_1, above_run_2, above_run_3, above_run_4, above_run_5, above_run_6, above_run_7,
    above_run_8, above_run_9, above_run_10, above_run_11, above_run_12, above_run_13,
    above_run_14, above_run_15, above_run_16]
  circuit_decide

assert_standard_axioms pulse_from_above

/-- **A pulse with the item below leaves it below.** In game tick 4 the lower dropper pushes
the item up and the upper dropper pushes it down again: after every game tick of the run the
item is in the lower dropper and the comparator gives 1. -/
theorem pulse_from_below :
    observe (rules.runSchedule (schedule.take 1) itemBelow) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 2) itemBelow) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 3) itemBelow) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 4) itemBelow) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 5) itemBelow) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 6) itemBelow) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 7) itemBelow) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 8) itemBelow) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 9) itemBelow) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 10) itemBelow) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 11) itemBelow) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 12) itemBelow) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 13) itemBelow) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 14) itemBelow) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 15) itemBelow) = (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.take 16) itemBelow) = (1, 0, 1) ∧
      (rules.runSchedule (schedule.take 16) itemBelow).overflow = false := by
  rw [below_run_1, below_run_2, below_run_3, below_run_4, below_run_5, below_run_6, below_run_7,
    below_run_8, below_run_9, below_run_10, below_run_11, below_run_12, below_run_13,
    below_run_14, below_run_15, below_run_16]
  circuit_decide

assert_standard_axioms pulse_from_below

/-- The observation does not depend on the clocks. -/
theorem observe_advance (l : Level) (n : ℕ) : observe (l.advance n) = observe l := rfl

/-- **A second pulse does not move the item back.** The same pulse again, on the level the
first pulse left when the item started above: the item is in the lower dropper after the game
tick in which the droppers tick, and at the end. -/
theorem second_pulse :
    observe (rules.runSchedule (schedule.take 4) (rules.runSchedule schedule itemAbove)) =
        (1, 0, 1) ∧
      observe (rules.runSchedule (schedule.andThen schedule) itemAbove) = (1, 0, 1) ∧
      (rules.runSchedule (schedule.andThen schedule) itemAbove).overflow = false := by
  rw [Rules.runSchedule_andThen above_run again_run, above_run, again_run_4]
  circuit_decide

assert_standard_axioms second_pulse

/-- **After the pulse the item is in the lower dropper for ever**, wherever it started: the
level after the pulse is quiescent, so any number of further game ticks leaves the item in
the lower dropper and the comparator at 1, and the model reaches no bound. -/
theorem item_stays_below (n : ℕ) :
    observe (rules.steps n (rules.runSchedule schedule itemAbove)) = (1, 0, 1) ∧
      observe (rules.steps n (rules.runSchedule schedule itemBelow)) = (1, 0, 1) ∧
      (rules.steps n (rules.runSchedule schedule itemAbove)).overflow = false ∧
      (rules.steps n (rules.runSchedule schedule itemBelow)).overflow = false := by
  rw [above_run, below_run, rules.steps_of_quiescent (by circuit_decide),
    rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms item_stays_below

end Redstone.Theorems.ContainerSignal.DropperPair
