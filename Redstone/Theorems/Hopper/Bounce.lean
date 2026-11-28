import Redstone.Theorems.Hopper.Common
import Redstone.Theorems.Hopper.CycleStamps

/-!
# Two hoppers that face each other

The core of every hopper clock: two hoppers side by side, each pointing into the other, and
one item.

```
y = 1:   L→ ←R        L = (0, 1, 0) faces east, R = (1, 1, 0) faces west
```

The left hopper holds one piece of redstone and is ticked first. The item moves to the right
hopper in game tick 1, back in game tick 8, to the right again in game tick 15, and so on:
**one hop every 7 game ticks, a period of 14 game ticks** (7 redstone ticks).

Why 7 and not 8: a hopper that receives an item while it is empty is put on a cooldown of 8
game ticks, or of 7 if it was already ticked in this game tick. The right hopper gets its 8 in
game tick 1 before its own tick, which brings it to 7; the left hopper gets the item back in
game tick 8 after its own tick, so it gets 7. Either way the receiver is ready 7 game ticks
later. (The sender's own cooldown of 8 never matters here: it has nothing left to send.)

The statements are a run of 30 game ticks and a cycle certificate: the 14 game ticks from
game tick 15 to game tick 29 take the level to itself, moved on in time by 14 game ticks, the
time stamps of the two hoppers included (`Cycle`, `CycleStamps.lean`). The certificate of the
foundation, which leaves those stamps alone, is false for this level
(`not_cycle_without_stamps`). As for every clock, the certificate is one period, not a proof
that the item goes back and forth for ever.

The level is loaded raw, with both hoppers off cooldown; a level with a hopper is never
quiescent.
-/

set_option Elab.async false

namespace Redstone.Theorems.Hopper.Bounce

/-- The left hopper, which faces east. -/
def left : Pos := ⟨0, 1, 0⟩

/-- The right hopper, which faces west. -/
def right : Pos := ⟨1, 1, 0⟩

/-- Two hoppers that point into each other; the left one holds one piece of redstone and is
ticked first. -/
def circuit : Level :=
  .ofCells [(left, .hopper ⟨true, .east⟩), (right, .hopper ⟨true, .west⟩)]
    [(left, .hopper { items := (Inventory.empty 5).setItem 0 (.of "minecraft:redstone" 1) })]

/-- Thirty game ticks without input. -/
def schedule : Schedule := .idle 30

checkpoints state := schedule from circuit

/-- The number of items in the left and in the right hopper. -/
def counts (l : Level) : ℕ × ℕ := (count l left, count l right)

/-- The transfer cooldowns of the left and of the right hopper. -/
def cooldowns (l : Level) : ℤ × ℤ := (cooldown l left, cooldown l right)

/-- At the start the item is in the left hopper, and the left hopper is ticked first. -/
theorem start : counts circuit = (1, 0) ∧ circuit.blockEntityTickers = [left, right] := by
  circuit_decide

assert_standard_axioms start

/-- **The item changes sides every 7 game ticks.** It is in the right hopper after the game
ticks 1 to 7, in the left one after 8 to 14, in the right one after 15 to 21, in the left one
after 22 to 28, and in the right one again after game tick 29. -/
theorem back_and_forth :
    counts (rules.runSchedule (schedule.take 1) circuit) = (0, 1) ∧
      counts (rules.runSchedule (schedule.take 2) circuit) = (0, 1) ∧
      counts (rules.runSchedule (schedule.take 3) circuit) = (0, 1) ∧
      counts (rules.runSchedule (schedule.take 4) circuit) = (0, 1) ∧
      counts (rules.runSchedule (schedule.take 5) circuit) = (0, 1) ∧
      counts (rules.runSchedule (schedule.take 6) circuit) = (0, 1) ∧
      counts (rules.runSchedule (schedule.take 7) circuit) = (0, 1) ∧
      counts (rules.runSchedule (schedule.take 8) circuit) = (1, 0) ∧
      counts (rules.runSchedule (schedule.take 9) circuit) = (1, 0) ∧
      counts (rules.runSchedule (schedule.take 10) circuit) = (1, 0) ∧
      counts (rules.runSchedule (schedule.take 11) circuit) = (1, 0) ∧
      counts (rules.runSchedule (schedule.take 12) circuit) = (1, 0) ∧
      counts (rules.runSchedule (schedule.take 13) circuit) = (1, 0) ∧
      counts (rules.runSchedule (schedule.take 14) circuit) = (1, 0) ∧
      counts (rules.runSchedule (schedule.take 15) circuit) = (0, 1) ∧
      counts (rules.runSchedule (schedule.take 16) circuit) = (0, 1) ∧
      counts (rules.runSchedule (schedule.take 17) circuit) = (0, 1) ∧
      counts (rules.runSchedule (schedule.take 18) circuit) = (0, 1) ∧
      counts (rules.runSchedule (schedule.take 19) circuit) = (0, 1) ∧
      counts (rules.runSchedule (schedule.take 20) circuit) = (0, 1) ∧
      counts (rules.runSchedule (schedule.take 21) circuit) = (0, 1) ∧
      counts (rules.runSchedule (schedule.take 22) circuit) = (1, 0) ∧
      counts (rules.runSchedule (schedule.take 23) circuit) = (1, 0) ∧
      counts (rules.runSchedule (schedule.take 24) circuit) = (1, 0) ∧
      counts (rules.runSchedule (schedule.take 25) circuit) = (1, 0) ∧
      counts (rules.runSchedule (schedule.take 26) circuit) = (1, 0) ∧
      counts (rules.runSchedule (schedule.take 27) circuit) = (1, 0) ∧
      counts (rules.runSchedule (schedule.take 28) circuit) = (1, 0) ∧
      counts (rules.runSchedule (schedule.take 29) circuit) = (0, 1) ∧
      (rules.runSchedule (schedule.take 29) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13,
    state_run_14, state_run_15, state_run_16, state_run_17, state_run_18, state_run_19,
    state_run_20, state_run_21, state_run_22, state_run_23, state_run_24, state_run_25,
    state_run_26, state_run_27, state_run_28, state_run_29]
  circuit_decide

assert_standard_axioms back_and_forth

/-- **The cooldowns after a hop.** After game tick 1 the sender (left) has 8 game ticks of
cooldown left and the receiver (right) 7: it got 8 and was then ticked. After game tick 8 the
sender (right) has 8 and the receiver (left) 7: it had been ticked already, so it got 7. After
game tick 15 the cooldowns are those after game tick 1. -/
theorem cooldowns_after_hop :
    cooldowns (rules.runSchedule (schedule.take 1) circuit) = (8, 7) ∧
      cooldowns (rules.runSchedule (schedule.take 7) circuit) = (2, 1) ∧
      cooldowns (rules.runSchedule (schedule.take 8) circuit) = (7, 8) ∧
      cooldowns (rules.runSchedule (schedule.take 14) circuit) = (1, 2) ∧
      cooldowns (rules.runSchedule (schedule.take 15) circuit) = (8, 7) := by
  rw [state_run_1, state_run_7, state_run_8, state_run_14, state_run_15]
  circuit_decide

assert_standard_axioms cooldowns_after_hop

/-- **The cycle certificate.** Fourteen game ticks take the level after game tick 15 to
itself, moved on in time by 14 game ticks: every block, the slots and cooldowns of both
hoppers, their time stamps (14 later), every counter and the random number generator. No tick
is ever scheduled. -/
theorem cycle : Cycle (rules.runSchedule (schedule.take 15) circuit) 14 0 := by
  rw [state_run_15]
  exact (Rules.steps_of_runs (k := 15) (m := 14) state_run_15 state_run_29
    (by circuit_decide)).trans (Level.eq_of_beqBlocks (by circuit_decide))

assert_standard_axioms cycle

/-- The certificate of the foundation fails for this level: after 14 game ticks the level is
not `Level.shift` of itself, because the two hoppers have recorded a later game time. This is
why `Cycle` moves the time stamps too. -/
theorem not_cycle_without_stamps :
    ¬ rules.Cycle (rules.runSchedule (schedule.take 15) circuit) 14 0 := by
  rw [state_run_15]
  intro h
  have h₁ : state_29 = state_15.shift 14 0 :=
    (Rules.steps_of_runs (k := 15) (m := 14) state_run_15 state_run_29
      (by circuit_decide)).symm.trans h
  have h₂ : state_29.blockEntities ≠ (state_15.shift 14 0).blockEntities := by circuit_decide
  exact h₂ (congrArg Level.blockEntities h₁)

assert_standard_axioms not_cycle_without_stamps

end Redstone.Theorems.Hopper.Bounce
