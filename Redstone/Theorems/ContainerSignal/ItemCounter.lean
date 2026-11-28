import Redstone.Lemmas.ContainerSignal
import Redstone.Proof.Circuit

/-!
# The item counter: a lamp that lights at 23 items

A hopper that keeps what it gets, read by a comparator; two pieces of dust between the
comparator and a lamp. A hopper gives the signal 1 for 1 to 22 ordinary items and 2 from 23
items on (`Redstone.Component.Container.hopper_thresholds`). The dust takes one off the
signal on the way, so the lamp is lit exactly when the comparator gives 2 or more: when the
hopper holds 23 items or more. Longer dust, or a second comparator in subtraction mode, moves
the threshold to the other entries of the table in the same way.

Seen from the side, `x` to the right:

```
y = 2:   U   .   .   .   .      U: the hopper the items come from, pointing down
y = 1:   K   C   d   d   L      K: the counting hopper, pointing down at stone; C: comparator
y = 0:   S   S   S   S   .      d: dust; L: lamp; S: stone
x:       0   1   2   3   4
```

What is proved:

* `below_threshold`: with 22 items in the counting hopper the comparator gives 1, the first
  dust has power 1, the second none, and the lamp is dark; four game ticks change nothing.
* `counts`: the counting hopper holds 20 items and three more are in the hopper above. Two of
  them arrive in game tick 1 (the upper hopper pushes one and the counting hopper pulls one),
  which makes 22: the lamp stays dark. The third arrives in game tick 9, eight game ticks
  later, which makes 23: the comparator gives 2 after game tick 11, and in the same game tick
  the second dust has power 1 and the lamp is lit. It is still lit after game tick 24.
* `numbers`: the signal of a hopper is 1 for 22 items and 2 for 23, and 23 is the threshold of
  the signal 2 in the table.

Hoppers are ticking block entities: no level here is quiescent, and the statements are about
bounded runs. The level is loaded raw, in the state of rest the model settles in when the
redstone is placed next to a counting hopper that gives the signal 1.

## Not proved

That the lamp stays lit for ever (a level with a hopper is never quiescent), and the same
counter for the other thresholds of the table, which differ in the dust only.
-/

set_option Elab.async false

-- The theorems are conjunctions of many equations between tuples, and the instance that
-- decides such an equation is large.
set_option synthInstance.maxSize 100000

namespace Redstone.Theorems.ContainerSignal.ItemCounter

/-- The hopper the items come from. -/
def source : Pos := ⟨0, 2, 0⟩

/-- The hopper that counts: it points down at a stone block and keeps what it gets. -/
def counter : Pos := ⟨0, 1, 0⟩

/-- The comparator that reads the counting hopper. -/
def comparator : Pos := ⟨1, 1, 0⟩

/-- The first piece of dust, in front of the comparator. -/
def dust1 : Pos := ⟨2, 1, 0⟩

/-- The second piece of dust, which runs into the lamp. -/
def dust2 : Pos := ⟨3, 1, 0⟩

/-- The lamp. -/
def lamp : Pos := ⟨4, 1, 0⟩

/-- The counter with `held` items in the counting hopper and `more` in the hopper above it;
comparator, dust and lamp in the state of rest of a counting hopper that gives the signal 1. -/
def counterWith (held more : ℕ) : Level :=
  .ofCells [
      (source, .hopper ⟨true, .down⟩), (counter, .hopper ⟨true, .down⟩),
      (⟨0, 0, 0⟩, .plain .stone), (⟨1, 0, 0⟩, .plain .stone), (⟨2, 0, 0⟩, .plain .stone),
      (⟨3, 0, 0⟩, .plain .stone),
      (comparator, .comparator ⟨.west, .compare, true⟩),
      (dust1, .redstoneWire ⟨.side, .none, 1, .none, .side⟩),
      (dust2, .redstoneWire ⟨.side, .none, 0, .none, .side⟩),
      (lamp, .redstoneLamp ⟨false⟩)]
    [(source, .hopper { items := (Inventory.empty 5).setItem 0 (.of "minecraft:redstone" more) }),
      (counter, .hopper { items := (Inventory.empty 5).setItem 0 (.of "minecraft:redstone" held) }),
      (comparator, .comparator { output := 1 })]

/-- 20 items counted, three more to come. -/
def circuit : Level := counterWith 20 3

/-- 22 items counted, none to come. -/
def resting : Level := counterWith 22 0

/-- 24 game ticks without input. -/
def schedule : Schedule := .idle 24

/-- Four game ticks without input. -/
def restSchedule : Schedule := .idle 4

/-- The output the comparator has stored. -/
def output (l : Level) : ℕ :=
  match l.blockEntities comparator with
  | some (.comparator d) => d.output
  | _ => 0

/-- What is observed: the numbers of items in the source and in the counting hopper, the
output of the comparator, the power of the two pieces of dust, and whether the lamp is lit. -/
def observe (l : Level) : ℕ × ℕ × ℕ × ℕ × ℕ × Bool :=
  (l.itemCount source, l.itemCount counter, output l, l.dustPower dust1, l.dustPower dust2,
    l.blockAt lamp == .redstoneLamp ⟨true⟩)

checkpoints rest := restSchedule from resting
checkpoints state := schedule from circuit

/-- At the start the hopper above holds three items and the counting hopper 20; the
comparator gives 1, the dust has power 1 and 0, the lamp is dark, and nothing is scheduled. -/
theorem start : observe circuit = (3, 20, 1, 1, 0, false) ∧ circuit.pending = [] := by
  circuit_decide

assert_standard_axioms start

/-- **22 items: the lamp is dark.** With 22 items in the counting hopper and none to come,
after each of four game ticks the comparator gives 1, the first dust has power 1, the second
none, and the lamp is dark; nothing is scheduled. -/
theorem below_threshold :
    observe (rules.runSchedule (restSchedule.take 1) resting) = (0, 22, 1, 1, 0, false) ∧
      observe (rules.runSchedule (restSchedule.take 2) resting) = (0, 22, 1, 1, 0, false) ∧
      observe (rules.runSchedule (restSchedule.take 3) resting) = (0, 22, 1, 1, 0, false) ∧
      observe (rules.runSchedule (restSchedule.take 4) resting) = (0, 22, 1, 1, 0, false) ∧
      (rules.runSchedule (restSchedule.take 4) resting).pending = [] ∧
      (rules.runSchedule (restSchedule.take 4) resting).overflow = false := by
  rw [rest_run_1, rest_run_2, rest_run_3, rest_run_4]
  circuit_decide

assert_standard_axioms below_threshold

/-- **The lamp lights with the 23rd item.** Each line is the state after one game tick: the
items in the upper hopper, the items in the counting hopper, the output of the comparator, the
power of the two pieces of dust, and whether the lamp is lit. After game ticks 1 to 8 the
counting hopper holds 22 items and the lamp is dark. The 23rd item arrives in game tick 9; the
comparator gives 2 after game tick 11, two game ticks later, and the lamp is lit from then on.
-/
theorem counts :
    observe (rules.runSchedule (schedule.take 1) circuit) = (1, 22, 1, 1, 0, false) ∧
      observe (rules.runSchedule (schedule.take 2) circuit) = (1, 22, 1, 1, 0, false) ∧
      observe (rules.runSchedule (schedule.take 3) circuit) = (1, 22, 1, 1, 0, false) ∧
      observe (rules.runSchedule (schedule.take 4) circuit) = (1, 22, 1, 1, 0, false) ∧
      observe (rules.runSchedule (schedule.take 5) circuit) = (1, 22, 1, 1, 0, false) ∧
      observe (rules.runSchedule (schedule.take 6) circuit) = (1, 22, 1, 1, 0, false) ∧
      observe (rules.runSchedule (schedule.take 7) circuit) = (1, 22, 1, 1, 0, false) ∧
      observe (rules.runSchedule (schedule.take 8) circuit) = (1, 22, 1, 1, 0, false) ∧
      observe (rules.runSchedule (schedule.take 9) circuit) = (0, 23, 1, 1, 0, false) ∧
      observe (rules.runSchedule (schedule.take 10) circuit) = (0, 23, 1, 1, 0, false) ∧
      observe (rules.runSchedule (schedule.take 11) circuit) = (0, 23, 2, 2, 1, true) ∧
      observe (rules.runSchedule (schedule.take 12) circuit) = (0, 23, 2, 2, 1, true) ∧
      observe (rules.runSchedule (schedule.take 13) circuit) = (0, 23, 2, 2, 1, true) ∧
      observe (rules.runSchedule (schedule.take 14) circuit) = (0, 23, 2, 2, 1, true) ∧
      observe (rules.runSchedule (schedule.take 15) circuit) = (0, 23, 2, 2, 1, true) ∧
      observe (rules.runSchedule (schedule.take 16) circuit) = (0, 23, 2, 2, 1, true) ∧
      observe (rules.runSchedule (schedule.take 17) circuit) = (0, 23, 2, 2, 1, true) ∧
      observe (rules.runSchedule (schedule.take 18) circuit) = (0, 23, 2, 2, 1, true) ∧
      observe (rules.runSchedule (schedule.take 19) circuit) = (0, 23, 2, 2, 1, true) ∧
      observe (rules.runSchedule (schedule.take 20) circuit) = (0, 23, 2, 2, 1, true) ∧
      observe (rules.runSchedule (schedule.take 21) circuit) = (0, 23, 2, 2, 1, true) ∧
      observe (rules.runSchedule (schedule.take 22) circuit) = (0, 23, 2, 2, 1, true) ∧
      observe (rules.runSchedule (schedule.take 23) circuit) = (0, 23, 2, 2, 1, true) ∧
      observe (rules.runSchedule (schedule.take 24) circuit) = (0, 23, 2, 2, 1, true) ∧
      (rules.runSchedule (schedule.take 24) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13,
    state_run_14, state_run_15, state_run_16, state_run_17, state_run_18, state_run_19,
    state_run_20, state_run_21, state_run_22, state_run_23, state_run_24]
  circuit_decide

assert_standard_axioms counts

/-- The numbers behind the counter: a hopper with 22 ordinary items gives 1, with 23 it gives
2, and 23 is the least number of items that gives 2. -/
theorem numbers :
    Component.Container.signalOf 5 64 22 = 1 ∧ Component.Container.signalOf 5 64 23 = 2 ∧
      Component.Container.threshold 5 64 2 = 23 := by
  decide

assert_standard_axioms numbers

end Redstone.Theorems.ContainerSignal.ItemCounter
