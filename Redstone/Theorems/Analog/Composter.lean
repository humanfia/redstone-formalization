import Redstone.Theorems.Analog.Common

/-!
# A composter behind a comparator

A composter, a comparator that reads it, and a piece of redstone dust in front of the
comparator, on a stone floor.

```
z = 0:  P  C  o        P: composter, C: comparator (reads west, emits east), o: output dust
x =     0  1  2        y = 1, seen from above
```

A comparator reads the level of a composter (`AnalogSource.analogSignal_composter`). A player
composts seven pumpkin pies, one every three game ticks; a pumpkin pie always adds a layer, so
no random number is drawn. What is proved (1 redstone tick = 2 game ticks):

* **Level `k` gives strength `k`** (`fills`): three game ticks after the `k`-th pie the
  composter has level `k` and the comparator emits `k`, for `k` from 1 to 7; for the fourth
  pie, that the comparator follows in the second game tick and not in the first (`delay`).
* **A full composter ripens by itself** (`ripens`): the seventh pie is added before game tick
  19; twenty game ticks later, in game tick 38, the composter goes from level 7 to level 8 (the
  bone meal is ready), and the comparator emits 8 from game tick 40 on. The level is then at
  rest, and the 8 is kept for ever (`ready_for_ever`).

## Not proved here

Taking the bone meal out (which sets the level back to 0) drops an item, and a level with an
entity is out of reach of the checkpoints (`Redstone/Proof/README.md`).

The level is loaded raw with an empty composter, and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Analog.Composter

/-- The composter. -/
def composter : Pos := ⟨0, 1, 0⟩

/-- The comparator that reads the composter. -/
def cmp : Pos := ⟨1, 1, 0⟩

/-- The dust in front of the comparator. -/
def out : Pos := ⟨2, 1, 0⟩

/-- An empty composter, a comparator that reads it and a piece of dust, on a stone floor. -/
def circuit : Level :=
  .ofCells (floor [0, 1, 2] [0] ++
    [(composter, .composter ⟨0⟩), (cmp, .comparator ⟨.west, .compare, false⟩), (out, wireEW)])

/-- A pumpkin pie is composted before game ticks 1, 4, 7, 10, 13, 16 and 19; then twenty-two
game ticks without input; forty-three game ticks. -/
def schedule : Schedule :=
  (List.replicate 7
    (Schedule.first [.useItem composter .up "minecraft:pumpkin_pie"] 3)).flatten ++
    Schedule.idle 22

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- What is observed: the level of the composter, the comparator, and the power of the dust at
the output. -/
def observe (l : Level) : ℕ × (Bool × ℕ) × ℕ :=
  (match l.blockAt composter with
    | .composter s => s.level.val
    | _ => 0,
   comparator l cmp, l.dustPower out)

/-- **A composter of level `k` gives strength `k`.** Three game ticks after the `k`-th pumpkin
pie, the composter has level `k` and the comparator emits `k`, for `k` from 1 to 7. -/
theorem fills :
    observe circuit = (0, (false, 0), 0) ∧
      observe (rules.runSchedule (schedule.take 3) circuit) = (1, (true, 1), 1) ∧
      observe (rules.runSchedule (schedule.take 6) circuit) = (2, (true, 2), 2) ∧
      observe (rules.runSchedule (schedule.take 9) circuit) = (3, (true, 3), 3) ∧
      observe (rules.runSchedule (schedule.take 12) circuit) = (4, (true, 4), 4) ∧
      observe (rules.runSchedule (schedule.take 15) circuit) = (5, (true, 5), 5) ∧
      observe (rules.runSchedule (schedule.take 18) circuit) = (6, (true, 6), 6) ∧
      observe (rules.runSchedule (schedule.take 21) circuit) = (7, (true, 7), 7) ∧
      (rules.runSchedule (schedule.take 21) circuit).overflow = false := by
  rw [state_run_3, state_run_6, state_run_9, state_run_12, state_run_15, state_run_18,
    state_run_21]
  circuit_decide

assert_standard_axioms fills

/-- **The comparator follows two game ticks later.** The fourth pie is composted before game
tick 10: after game tick 10 the composter has level 4 and the comparator still emits 3; after
game tick 11 it emits 4. -/
theorem delay :
    observe (rules.runSchedule (schedule.take 9) circuit) = (3, (true, 3), 3) ∧
      observe (rules.runSchedule (schedule.take 10) circuit) = (4, (true, 3), 3) ∧
      observe (rules.runSchedule (schedule.take 11) circuit) = (4, (true, 4), 4) := by
  rw [state_run_9, state_run_10, state_run_11]
  circuit_decide

assert_standard_axioms delay

/-- **A full composter ripens after twenty game ticks.** The seventh pie is composted before
game tick 19. After game tick 37 the composter still has level 7; after game tick 38 it has
level 8 and the comparator still emits 7; after game tick 40 the comparator emits 8, and the
level is at rest at the end of the run. -/
theorem ripens :
    observe (rules.runSchedule (schedule.take 19) circuit) = (7, (true, 6), 6) ∧
      observe (rules.runSchedule (schedule.take 37) circuit) = (7, (true, 7), 7) ∧
      observe (rules.runSchedule (schedule.take 38) circuit) = (8, (true, 7), 7) ∧
      observe (rules.runSchedule (schedule.take 39) circuit) = (8, (true, 7), 7) ∧
      observe (rules.runSchedule (schedule.take 40) circuit) = (8, (true, 8), 8) ∧
      observe (rules.runSchedule schedule circuit) = (8, (true, 8), 8) ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_19, state_run_37, state_run_38, state_run_39, state_run_40, state_run]
  circuit_decide

assert_standard_axioms ripens

/-- A composter whose bone meal is ready gives 8 for ever. -/
theorem ready_for_ever (n : ℕ) :
    observe (rules.steps n (rules.runSchedule schedule circuit)) = (8, (true, 8), 8) ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, comparator_advance, Level.blockAt_advance, Level.dustPower_advance,
    Level.overflow_advance]
  circuit_decide

assert_standard_axioms ready_for_ever

end Redstone.Theorems.Analog.Composter
