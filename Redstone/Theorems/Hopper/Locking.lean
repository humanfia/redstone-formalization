import Redstone.Theorems.Hopper.Common

/-!
# Locking a hopper

A hopper that receives a redstone signal is *locked*: it neither pushes nor pulls. The layout
is a hopper pipe with a lever beside it:

```
y = 3:   C  /      the upper chest (0, 3, 0) with 3 redstone; the lever (1, 3, 0) on the stone
y = 2:   H  S      the hopper (0, 2, 0), facing down; a stone block (1, 2, 0)
y = 1:   C         the lower chest (0, 1, 0)
```

The lever stands on the stone block and powers it; the powered block is a neighbour of the
hopper, so the hopper receives a signal while the lever is on.

The run: the pipe runs for two game ticks (the hopper pulls one item). The lever is switched
on before game tick 3 and off again before game tick 23; then the pipe runs for 18 more game
ticks.

* `locks_at_once`: the hopper's block state has `enabled = false` after the game tick in which
  the lever was used. There is no delay: the lock is set in the neighbour update itself.
* `holds_while_locked`: for the 20 game ticks with the lever on, the hopper keeps its item,
  although the chest above has items to pull and the chest below has room, and although its
  cooldown runs out after game tick 9.
* `locked_for_ever`: the level after game tick 3 is at rest in the sense of
  `Level.HoppersLocked`. So, if the lever is never touched again, **no item moves for any
  number of game ticks**, the hopper stays locked, and the model reaches no bound. This is a
  statement for all `n`, proved from `Level.step_of_hoppersLocked`, not by evaluation.
* `resumes`: the hopper is enabled again after the game tick in which the lever was switched
  off, and since its cooldown has run out it moves in that very game tick: it pushes its item
  and pulls the next. The remaining items follow 8 game ticks apart.

The level is loaded raw, with the hopper off cooldown. It is not quiescent (it has a hopper).
-/

set_option Elab.async false

namespace Redstone.Theorems.Hopper.Locking

/-- The upper chest. -/
def top : Pos := ⟨0, 3, 0⟩

/-- The hopper. -/
def hopper : Pos := ⟨0, 2, 0⟩

/-- The lower chest. -/
def bottom : Pos := ⟨0, 1, 0⟩

/-- The stone block beside the hopper. -/
def stone : Pos := ⟨1, 2, 0⟩

/-- The lever, on top of the stone block. -/
def lever : Pos := ⟨1, 3, 0⟩

/-- A hopper pipe with three pieces of redstone in the upper chest, and a lever on a stone
block beside the hopper. -/
def circuit : Level :=
  .ofCells [(top, .chest ⟨.north, .single, false⟩), (hopper, .hopper ⟨true, .down⟩),
      (bottom, .chest ⟨.north, .single, false⟩), (stone, .plain .stone),
      (lever, .lever ⟨.floor, .north, false⟩)]
    [(top, .chest { items := (Inventory.empty 27).setItem 0 (.of redstone 3) })]

/-- Two game ticks; the lever is switched on, 20 game ticks; the lever is switched off, 18
game ticks. -/
def schedule : Schedule :=
  Schedule.idle 2 ++ Schedule.first [.use lever .up] 20 ++ Schedule.first [.use lever .up] 18

checkpoints state := schedule from circuit

/-- The number of items in the upper chest, in the hopper and in the lower chest. -/
def counts (l : Level) : ℕ × ℕ × ℕ := (count l top, count l hopper, count l bottom)

/-- At the start the three items are in the upper chest, the hopper is enabled and the lever
is off. -/
theorem start :
    counts circuit = (3, 0, 0) ∧ enabled circuit hopper = true ∧
      circuit.blockAt lever = .lever ⟨.floor, .north, false⟩ ∧
      circuit.blockEntityTickers = [hopper] := by
  circuit_decide

assert_standard_axioms start

/-- Before the lever is used the pipe runs: the hopper pulls the first item in game tick 1 and
is on cooldown. -/
theorem runs_before :
    counts (rules.runSchedule (schedule.take 1) circuit) = (2, 1, 0) ∧
      counts (rules.runSchedule (schedule.take 2) circuit) = (2, 1, 0) ∧
      cooldown (rules.runSchedule (schedule.take 2) circuit) hopper = 7 ∧
      enabled (rules.runSchedule (schedule.take 2) circuit) hopper = true := by
  rw [state_run_1, state_run_2]
  circuit_decide

assert_standard_axioms runs_before

/-- **The hopper is locked at once**: after the game tick before which the lever was switched
on, the lever is on and the hopper's block state has `enabled = false`. -/
theorem locks_at_once :
    (rules.runSchedule (schedule.take 3) circuit).blockAt lever =
        .lever ⟨.floor, .north, true⟩ ∧
      enabled (rules.runSchedule (schedule.take 3) circuit) hopper = false ∧
      (rules.runSchedule (schedule.take 3) circuit).blockAt hopper =
        .hopper ⟨false, .down⟩ := by
  rw [state_run_3]
  circuit_decide

assert_standard_axioms locks_at_once

/-- **A locked hopper neither pushes nor pulls.** For the 20 game ticks with the lever on (3
to 22) the upper chest keeps its two items, the hopper its one, and the lower chest stays
empty. The hopper's cooldown, 6 after game tick 3, has run out after game tick 9; an enabled
hopper would have moved in game tick 9. -/
theorem holds_while_locked :
    counts (rules.runSchedule (schedule.take 3) circuit) = (2, 1, 0) ∧
      cooldown (rules.runSchedule (schedule.take 3) circuit) hopper = 6 ∧
      counts (rules.runSchedule (schedule.take 8) circuit) = (2, 1, 0) ∧
      counts (rules.runSchedule (schedule.take 9) circuit) = (2, 1, 0) ∧
      cooldown (rules.runSchedule (schedule.take 9) circuit) hopper = 0 ∧
      counts (rules.runSchedule (schedule.take 10) circuit) = (2, 1, 0) ∧
      counts (rules.runSchedule (schedule.take 16) circuit) = (2, 1, 0) ∧
      counts (rules.runSchedule (schedule.take 22) circuit) = (2, 1, 0) ∧
      cooldown (rules.runSchedule (schedule.take 22) circuit) hopper = 0 ∧
      enabled (rules.runSchedule (schedule.take 22) circuit) hopper = false := by
  rw [state_run_3, state_run_8, state_run_9, state_run_10, state_run_16, state_run_22]
  circuit_decide

assert_standard_axioms holds_while_locked

/-- The level after game tick 3 is at rest but for its hopper, which is locked. -/
theorem locked_at_rest : (rules.runSchedule (schedule.take 3) circuit).HoppersLocked := by
  rw [state_run_3]
  circuit_decide

assert_standard_axioms locked_at_rest

/-- **A locked hopper holds its items for ever.** Left alone after game tick 3, with the lever
on, the level keeps two items in the upper chest, one in the hopper and none in the lower
chest after any number `n` of further game ticks; the hopper stays locked, and the model never
reaches a bound. -/
theorem locked_for_ever (n : ℕ) :
    counts (rules.steps n (rules.runSchedule (schedule.take 3) circuit)) = (2, 1, 0) ∧
      slots (rules.steps n (rules.runSchedule (schedule.take 3) circuit)) hopper =
        [(0, redstone, 1)] ∧
      enabled (rules.steps n (rules.runSchedule (schedule.take 3) circuit)) hopper = false ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).overflow = false := by
  have h := locked_at_rest
  rw [counts, count_steps_of_hoppersLocked h, count_steps_of_hoppersLocked h,
    count_steps_of_hoppersLocked h, slots_steps_of_hoppersLocked h,
    enabled_steps_of_hoppersLocked h, Level.overflow_steps_of_hoppersLocked h, state_run_3]
  circuit_decide

assert_standard_axioms locked_for_ever

/-- **The hopper resumes when the signal goes.** After the game tick before which the lever
was switched off (23) the hopper is enabled, and in that same game tick it has pushed its item
into the lower chest and pulled the next from the upper one. The last two items follow in the
game ticks 31 and 39. The model has not reached a bound. -/
theorem resumes :
    enabled (rules.runSchedule (schedule.take 23) circuit) hopper = true ∧
      counts (rules.runSchedule (schedule.take 23) circuit) = (1, 1, 1) ∧
      cooldown (rules.runSchedule (schedule.take 23) circuit) hopper = 8 ∧
      counts (rules.runSchedule (schedule.take 30) circuit) = (1, 1, 1) ∧
      counts (rules.runSchedule (schedule.take 31) circuit) = (0, 1, 2) ∧
      counts (rules.runSchedule (schedule.take 38) circuit) = (0, 1, 2) ∧
      counts (rules.runSchedule (schedule.take 39) circuit) = (0, 0, 3) ∧
      counts (rules.runSchedule schedule circuit) = (0, 0, 3) ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run, state_run_23, state_run_30, state_run_31, state_run_38, state_run_39]
  circuit_decide

assert_standard_axioms resumes

end Redstone.Theorems.Hopper.Locking
