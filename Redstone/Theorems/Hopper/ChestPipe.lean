import Redstone.Theorems.Hopper.Common

/-!
# A hopper between two chests

The hopper pipe: a chest, a hopper under it that points down, and a chest under the hopper.

```
y = 2:   C     the upper chest, (0, 2, 0): 3 redstone in slot 0, 2 iron ingots in slot 1
y = 1:   H     the hopper, (0, 1, 0), facing down
y = 0:   C     the lower chest, (0, 0, 0), empty
```

**A hopper moves one item every 8 game ticks** (4 redstone ticks, 2.5 items a second). In
game tick 1 the hopper pulls the first item out of the upper chest and goes on cooldown for 8
game ticks (`MOVE_ITEM_SPEED`). In game tick 9 it pushes that item into the lower chest *and*
pulls the next one, in this order, and waits again. So item `i` leaves the upper chest in game
tick `8 (i - 1) + 1` and reaches the lower chest in game tick `8 i + 1`; the five items are
down after game tick 41.

What the theorems say:

* `one_item_every_eight`: the number of items in the upper chest, the hopper and the lower
  chest after the game ticks at which they change, and just before.
* `push_before_pull`: in one game tick the hopper first pushes, then pulls. In game tick 25 it
  holds a piece of redstone in its first slot and pulls an iron ingot: the ingot ends up in the
  first slot, which the push has emptied by then.
* `drained_in_order`: the hopper takes from the first slot of the chest that has an item, and
  the lower chest is filled from its first slot.
* `conserved`: after every one of the 44 game ticks the three containers hold five items.
* `finished`: after game tick 41 nothing moves any more (stated up to game tick 44), and the
  model has not reached a bound.

The level is loaded raw, with the hopper off cooldown. A level with a hopper is never
quiescent, so the statements are about a bounded run of 44 game ticks.
-/

set_option Elab.async false

namespace Redstone.Theorems.Hopper.ChestPipe

/-- The upper chest. -/
def top : Pos := ⟨0, 2, 0⟩

/-- The hopper. -/
def hopper : Pos := ⟨0, 1, 0⟩

/-- The lower chest. -/
def bottom : Pos := ⟨0, 0, 0⟩

/-- What the upper chest holds at the start: three pieces of redstone in the first slot and
two iron ingots in the second. -/
def cargo : Inventory :=
  ((Inventory.empty 27).setItem 0 (.of redstone 3)).setItem 1 (.of ironIngot 2)

/-- A chest, a hopper that points down, and a chest. -/
def circuit : Level :=
  .ofCells [(top, .chest ⟨.north, .single, false⟩), (hopper, .hopper ⟨true, .down⟩),
      (bottom, .chest ⟨.north, .single, false⟩)]
    [(top, .chest { items := cargo })]

/-- Forty-four game ticks without input. -/
def schedule : Schedule := .idle 44

checkpoints state := schedule from circuit

/-- The number of items in the upper chest, in the hopper and in the lower chest. -/
def counts (l : Level) : ℕ × ℕ × ℕ := (count l top, count l hopper, count l bottom)

/-- The number of items in the three containers together. -/
def total (l : Level) : ℕ := count l top + count l hopper + count l bottom

/-- At the start the five items are in the upper chest, and the hopper is the only block
entity that is ticked. -/
theorem start :
    counts circuit = (5, 0, 0) ∧
      slots circuit top = [(0, redstone, 3), (1, ironIngot, 2)] ∧
      circuit.blockEntityTickers = [hopper] := by
  circuit_decide

assert_standard_axioms start

/-- **One item every 8 game ticks.** The first item leaves the upper chest in game tick 1, the
second in game tick 9, and so on; each reaches the lower chest 8 game ticks after it left the
upper one. Between these game ticks nothing moves, and the hopper is on cooldown for 8 game
ticks after each move. -/
theorem one_item_every_eight :
    counts (rules.runSchedule (schedule.take 1) circuit) = (4, 1, 0) ∧
      counts (rules.runSchedule (schedule.take 8) circuit) = (4, 1, 0) ∧
      counts (rules.runSchedule (schedule.take 9) circuit) = (3, 1, 1) ∧
      counts (rules.runSchedule (schedule.take 16) circuit) = (3, 1, 1) ∧
      counts (rules.runSchedule (schedule.take 17) circuit) = (2, 1, 2) ∧
      counts (rules.runSchedule (schedule.take 24) circuit) = (2, 1, 2) ∧
      counts (rules.runSchedule (schedule.take 25) circuit) = (1, 1, 3) ∧
      counts (rules.runSchedule (schedule.take 32) circuit) = (1, 1, 3) ∧
      counts (rules.runSchedule (schedule.take 33) circuit) = (0, 1, 4) ∧
      counts (rules.runSchedule (schedule.take 40) circuit) = (0, 1, 4) ∧
      counts (rules.runSchedule (schedule.take 41) circuit) = (0, 0, 5) ∧
      cooldown (rules.runSchedule (schedule.take 1) circuit) hopper = 8 ∧
      cooldown (rules.runSchedule (schedule.take 8) circuit) hopper = 1 ∧
      cooldown (rules.runSchedule (schedule.take 9) circuit) hopper = 8 := by
  rw [state_run_1, state_run_8, state_run_9, state_run_16, state_run_17, state_run_24,
    state_run_25, state_run_32, state_run_33, state_run_40, state_run_41]
  circuit_decide

assert_standard_axioms one_item_every_eight

/-- **Push before pull.** After game tick 24 the hopper holds a piece of redstone in its first
slot, and the next item of the chest is an iron ingot. In game tick 25 the hopper pushes the
redstone down and then pulls the ingot, which therefore lands in the first slot. -/
theorem push_before_pull :
    slots (rules.runSchedule (schedule.take 24) circuit) hopper = [(0, redstone, 1)] ∧
      slots (rules.runSchedule (schedule.take 25) circuit) hopper = [(0, ironIngot, 1)] := by
  rw [state_run_24, state_run_25]
  circuit_decide

assert_standard_axioms push_before_pull

/-- **The slots are drained in order.** The hopper empties the first slot of the upper chest
before it touches the second, and the lower chest is filled from its first slot: the redstone
ends up in slot 0 and the iron in slot 1. -/
theorem drained_in_order :
    slots (rules.runSchedule (schedule.take 9) circuit) top =
        [(0, redstone, 1), (1, ironIngot, 2)] ∧
      slots (rules.runSchedule (schedule.take 17) circuit) top = [(1, ironIngot, 2)] ∧
      slots (rules.runSchedule (schedule.take 25) circuit) top = [(1, ironIngot, 1)] ∧
      slots (rules.runSchedule (schedule.take 33) circuit) top = [] ∧
      slots (rules.runSchedule (schedule.take 25) circuit) bottom = [(0, redstone, 3)] ∧
      slots (rules.runSchedule (schedule.take 33) circuit) bottom =
        [(0, redstone, 3), (1, ironIngot, 1)] ∧
      slots (rules.runSchedule (schedule.take 41) circuit) bottom =
        [(0, redstone, 3), (1, ironIngot, 2)] := by
  rw [state_run_9, state_run_17, state_run_25, state_run_33, state_run_41]
  circuit_decide

assert_standard_axioms drained_in_order

/-- **No item is lost or made.** After each of the 44 game ticks the two chests and the hopper
hold five items together. -/
theorem conserved :
    total (rules.runSchedule (schedule.take 1) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 2) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 3) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 4) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 5) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 6) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 7) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 8) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 9) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 10) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 11) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 12) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 13) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 14) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 15) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 16) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 17) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 18) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 19) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 20) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 21) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 22) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 23) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 24) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 25) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 26) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 27) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 28) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 29) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 30) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 31) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 32) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 33) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 34) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 35) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 36) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 37) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 38) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 39) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 40) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 41) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 42) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 43) circuit) = 5 ∧
      total (rules.runSchedule (schedule.take 44) circuit) = 5 := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13, state_run_14,
    state_run_15, state_run_16, state_run_17, state_run_18, state_run_19, state_run_20,
    state_run_21, state_run_22, state_run_23, state_run_24, state_run_25, state_run_26,
    state_run_27, state_run_28, state_run_29, state_run_30, state_run_31, state_run_32,
    state_run_33, state_run_34, state_run_35, state_run_36, state_run_37, state_run_38,
    state_run_39, state_run_40, state_run_41, state_run_42, state_run_43, state_run_44]
  circuit_decide

assert_standard_axioms conserved

/-- After game tick 41 all five items are in the lower chest, and nothing moves in the game ticks
that follow. The model has not reached a bound. -/
theorem finished :
    counts (rules.runSchedule (schedule.take 41) circuit) = (0, 0, 5) ∧
      counts (rules.runSchedule (schedule.take 42) circuit) = (0, 0, 5) ∧
      counts (rules.runSchedule (schedule.take 43) circuit) = (0, 0, 5) ∧
      counts (rules.runSchedule (schedule.take 44) circuit) = (0, 0, 5) ∧
      slots (rules.runSchedule (schedule.take 44) circuit) bottom =
        [(0, redstone, 3), (1, ironIngot, 2)] ∧
      (rules.runSchedule (schedule.take 44) circuit).overflow = false := by
  rw [state_run_41, state_run_42, state_run_43, state_run_44]
  circuit_decide

assert_standard_axioms finished

end Redstone.Theorems.Hopper.ChestPipe
