import Redstone.Theorems.Hopper.Common

/-!
# A chain of three hoppers

A horizontal hopper line, the item transport of most farms and sorters: three hoppers, each
pointing into the next, and a dropper at the end to collect.

```
y = 1:   A→ B→ C      A = (0, 1, 0) and B = (1, 1, 0) face east, C = (2, 1, 0) faces down
y = 0:         D      D = (2, 0, 0), a dropper
```

The first hopper holds three pieces of redstone.

**An item takes 7 game ticks per hopper, and the items follow each other 8 game ticks apart.**
The first item is pushed into `B` in game tick 1, into `C` in game tick 8 and into the dropper
in game tick 15; the second and the third arrive in the game ticks 23 and 31. With `n` hoppers
and `k` items the last item is in the container at the end after game tick `7 n + 8 (k - 1) -
6`; here `7 * 3 + 8 * 2 - 6 = 31`. (Checked for this layout, `n = 3` and `k = 3`.)

Why 7 per hop: a hopper that receives an item while empty is put on a cooldown of 8 game
ticks, or of 7 if it was ticked in this game tick before the sender. If it gets 8, its own
tick is still to come in the same game tick and brings it to 7. So the receiver is ready 7
game ticks later **whatever the order in which the hoppers are ticked**. That is what the
game's rule is for, and `order_independent` states it: the layout is built twice, with the
hoppers ticked from the source to the end (`circuit`) and from the end to the source
(`circuitRev`), and both runs agree in every count and every cooldown at the game ticks
stated. The sender itself waits 8 game ticks after a push, which is why the items are 8 apart.

(Two hoppers on top of each other are different: there the lower one also pulls, and the
order matters. See `PairOrder.lean`.)

The levels are loaded raw, with the hoppers off cooldown, and are never quiescent; the
statements are about runs of 34 game ticks.
-/

set_option Elab.async false

namespace Redstone.Theorems.Hopper.Chain

/-- The first hopper, which holds the items and faces east. -/
def a : Pos := ⟨0, 1, 0⟩

/-- The second hopper, which faces east. -/
def b : Pos := ⟨1, 1, 0⟩

/-- The third hopper, which faces down. -/
def c : Pos := ⟨2, 1, 0⟩

/-- The dropper under the third hopper. -/
def d : Pos := ⟨2, 0, 0⟩

/-- The blocks, in the order from the source to the end. -/
def cells : List (Pos × Block) :=
  [(a, .hopper ⟨true, .east⟩), (b, .hopper ⟨true, .east⟩), (c, .hopper ⟨true, .down⟩),
    (d, .dropper ⟨.up, false⟩)]

/-- The first hopper holds three pieces of redstone. -/
def cargo : List (Pos × BlockEntity) :=
  [(a, .hopper { items := (Inventory.empty 5).setItem 0 (.of redstone 3) })]

/-- The chain with its hoppers ticked from the source to the end. -/
def circuit : Level := .ofCells cells cargo

/-- The same chain with its hoppers ticked from the end to the source. -/
def circuitRev : Level := .ofCells cells.reverse cargo

/-- Thirty-four game ticks without input. -/
def schedule : Schedule := .idle 34

checkpoints state := schedule from circuit

checkpoints rev := schedule from circuitRev

/-- The number of items in the three hoppers and in the dropper. -/
def counts (l : Level) : ℕ × ℕ × ℕ × ℕ := (count l a, count l b, count l c, count l d)

/-- The transfer cooldowns of the three hoppers. -/
def cooldowns (l : Level) : ℤ × ℤ × ℤ := (cooldown l a, cooldown l b, cooldown l c)

/-- The counts and the cooldowns together. -/
def snapshot (l : Level) : (ℕ × ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ) :=
  (counts l, cooldowns l)

/-- The two levels hold the same blocks and items, and tick their hoppers in opposite
orders. -/
theorem start :
    counts circuit = (3, 0, 0, 0) ∧ counts circuitRev = (3, 0, 0, 0) ∧
      circuit.blockEntityTickers = [a, b, c] ∧ circuitRev.blockEntityTickers = [c, b, a] ∧
      circuit.world = circuitRev.world := by
  circuit_decide

assert_standard_axioms start

/-- **Seven game ticks per hop.** The first item is in the second hopper after game tick 1 and
still after game tick 7, in the third after game tick 8 and still after game tick 14, and in the
dropper after game tick 15. The receiver of a hop shows a cooldown of 7 after the game tick of
the hop. -/
theorem seven_per_hop :
    counts (rules.runSchedule (schedule.take 1) circuit) = (2, 1, 0, 0) ∧
      cooldowns (rules.runSchedule (schedule.take 1) circuit) = (8, 7, 0) ∧
      counts (rules.runSchedule (schedule.take 7) circuit) = (2, 1, 0, 0) ∧
      cooldowns (rules.runSchedule (schedule.take 7) circuit) = (2, 1, 0) ∧
      counts (rules.runSchedule (schedule.take 8) circuit) = (2, 0, 1, 0) ∧
      cooldowns (rules.runSchedule (schedule.take 8) circuit) = (1, 8, 7) ∧
      counts (rules.runSchedule (schedule.take 14) circuit) = (1, 1, 1, 0) ∧
      cooldowns (rules.runSchedule (schedule.take 14) circuit) = (3, 2, 1) ∧
      counts (rules.runSchedule (schedule.take 15) circuit) = (1, 1, 0, 1) ∧
      cooldowns (rules.runSchedule (schedule.take 15) circuit) = (2, 1, 8) := by
  rw [state_run_1, state_run_7, state_run_8, state_run_14, state_run_15]
  circuit_decide

assert_standard_axioms seven_per_hop

/-- **Eight game ticks between items.** The first hopper pushes in the game ticks 1, 9 and 17,
and the items reach the dropper in the game ticks 15, 23 and 31: after game tick 31 all three
are there, and nothing moves afterwards. -/
theorem eight_between_items :
    counts (rules.runSchedule (schedule.take 8) circuit) = (2, 0, 1, 0) ∧
      counts (rules.runSchedule (schedule.take 9) circuit) = (1, 1, 1, 0) ∧
      counts (rules.runSchedule (schedule.take 16) circuit) = (1, 0, 1, 1) ∧
      counts (rules.runSchedule (schedule.take 17) circuit) = (0, 1, 1, 1) ∧
      counts (rules.runSchedule (schedule.take 22) circuit) = (0, 1, 1, 1) ∧
      counts (rules.runSchedule (schedule.take 23) circuit) = (0, 1, 0, 2) ∧
      counts (rules.runSchedule (schedule.take 30) circuit) = (0, 0, 1, 2) ∧
      counts (rules.runSchedule (schedule.take 31) circuit) = (0, 0, 0, 3) ∧
      counts (rules.runSchedule (schedule.take 34) circuit) = (0, 0, 0, 3) ∧
      slots (rules.runSchedule schedule circuit) d = [(0, redstone, 3)] ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run, state_run_8, state_run_9, state_run_16, state_run_17, state_run_22, state_run_23,
    state_run_30, state_run_31, state_run_34]
  circuit_decide

assert_standard_axioms eight_between_items

/-- **The order of ticking does not matter.** The counts and the cooldowns after each of the
34 game ticks, in order, are the same for the chain whose hoppers are ticked from the source to
the end and for the chain whose hoppers are ticked from the end to the source. Neither run
reaches a bound of the model. -/
theorem order_independent :
    [snapshot (rules.runSchedule (schedule.take 1) circuit),
        snapshot (rules.runSchedule (schedule.take 2) circuit),
        snapshot (rules.runSchedule (schedule.take 3) circuit),
        snapshot (rules.runSchedule (schedule.take 4) circuit),
        snapshot (rules.runSchedule (schedule.take 5) circuit),
        snapshot (rules.runSchedule (schedule.take 6) circuit),
        snapshot (rules.runSchedule (schedule.take 7) circuit),
        snapshot (rules.runSchedule (schedule.take 8) circuit),
        snapshot (rules.runSchedule (schedule.take 9) circuit),
        snapshot (rules.runSchedule (schedule.take 10) circuit),
        snapshot (rules.runSchedule (schedule.take 11) circuit),
        snapshot (rules.runSchedule (schedule.take 12) circuit),
        snapshot (rules.runSchedule (schedule.take 13) circuit),
        snapshot (rules.runSchedule (schedule.take 14) circuit),
        snapshot (rules.runSchedule (schedule.take 15) circuit),
        snapshot (rules.runSchedule (schedule.take 16) circuit),
        snapshot (rules.runSchedule (schedule.take 17) circuit),
        snapshot (rules.runSchedule (schedule.take 18) circuit),
        snapshot (rules.runSchedule (schedule.take 19) circuit),
        snapshot (rules.runSchedule (schedule.take 20) circuit),
        snapshot (rules.runSchedule (schedule.take 21) circuit),
        snapshot (rules.runSchedule (schedule.take 22) circuit),
        snapshot (rules.runSchedule (schedule.take 23) circuit),
        snapshot (rules.runSchedule (schedule.take 24) circuit),
        snapshot (rules.runSchedule (schedule.take 25) circuit),
        snapshot (rules.runSchedule (schedule.take 26) circuit),
        snapshot (rules.runSchedule (schedule.take 27) circuit),
        snapshot (rules.runSchedule (schedule.take 28) circuit),
        snapshot (rules.runSchedule (schedule.take 29) circuit),
        snapshot (rules.runSchedule (schedule.take 30) circuit),
        snapshot (rules.runSchedule (schedule.take 31) circuit),
        snapshot (rules.runSchedule (schedule.take 32) circuit),
        snapshot (rules.runSchedule (schedule.take 33) circuit),
        snapshot (rules.runSchedule (schedule.take 34) circuit)] =
      [snapshot (rules.runSchedule (schedule.take 1) circuitRev),
        snapshot (rules.runSchedule (schedule.take 2) circuitRev),
        snapshot (rules.runSchedule (schedule.take 3) circuitRev),
        snapshot (rules.runSchedule (schedule.take 4) circuitRev),
        snapshot (rules.runSchedule (schedule.take 5) circuitRev),
        snapshot (rules.runSchedule (schedule.take 6) circuitRev),
        snapshot (rules.runSchedule (schedule.take 7) circuitRev),
        snapshot (rules.runSchedule (schedule.take 8) circuitRev),
        snapshot (rules.runSchedule (schedule.take 9) circuitRev),
        snapshot (rules.runSchedule (schedule.take 10) circuitRev),
        snapshot (rules.runSchedule (schedule.take 11) circuitRev),
        snapshot (rules.runSchedule (schedule.take 12) circuitRev),
        snapshot (rules.runSchedule (schedule.take 13) circuitRev),
        snapshot (rules.runSchedule (schedule.take 14) circuitRev),
        snapshot (rules.runSchedule (schedule.take 15) circuitRev),
        snapshot (rules.runSchedule (schedule.take 16) circuitRev),
        snapshot (rules.runSchedule (schedule.take 17) circuitRev),
        snapshot (rules.runSchedule (schedule.take 18) circuitRev),
        snapshot (rules.runSchedule (schedule.take 19) circuitRev),
        snapshot (rules.runSchedule (schedule.take 20) circuitRev),
        snapshot (rules.runSchedule (schedule.take 21) circuitRev),
        snapshot (rules.runSchedule (schedule.take 22) circuitRev),
        snapshot (rules.runSchedule (schedule.take 23) circuitRev),
        snapshot (rules.runSchedule (schedule.take 24) circuitRev),
        snapshot (rules.runSchedule (schedule.take 25) circuitRev),
        snapshot (rules.runSchedule (schedule.take 26) circuitRev),
        snapshot (rules.runSchedule (schedule.take 27) circuitRev),
        snapshot (rules.runSchedule (schedule.take 28) circuitRev),
        snapshot (rules.runSchedule (schedule.take 29) circuitRev),
        snapshot (rules.runSchedule (schedule.take 30) circuitRev),
        snapshot (rules.runSchedule (schedule.take 31) circuitRev),
        snapshot (rules.runSchedule (schedule.take 32) circuitRev),
        snapshot (rules.runSchedule (schedule.take 33) circuitRev),
        snapshot (rules.runSchedule (schedule.take 34) circuitRev)] ∧
      (rules.runSchedule schedule circuitRev).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13, state_run_14,
    state_run_15, state_run_16, state_run_17, state_run_18, state_run_19, state_run_20,
    state_run_21, state_run_22, state_run_23, state_run_24, state_run_25, state_run_26,
    state_run_27, state_run_28, state_run_29, state_run_30, state_run_31, state_run_32,
    state_run_33, state_run_34]
  rw [rev_run, rev_run_1, rev_run_2, rev_run_3, rev_run_4, rev_run_5, rev_run_6, rev_run_7,
    rev_run_8, rev_run_9, rev_run_10, rev_run_11, rev_run_12, rev_run_13, rev_run_14, rev_run_15,
    rev_run_16, rev_run_17, rev_run_18, rev_run_19, rev_run_20, rev_run_21, rev_run_22, rev_run_23,
    rev_run_24, rev_run_25, rev_run_26, rev_run_27, rev_run_28, rev_run_29, rev_run_30, rev_run_31,
    rev_run_32, rev_run_33, rev_run_34]
  circuit_decide

assert_standard_axioms order_independent

end Redstone.Theorems.Hopper.Chain
