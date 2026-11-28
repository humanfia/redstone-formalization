import Redstone.Theorems.Hopper.Common

/-!
# A hopper on a hopper: the order of ticking decides

Two hoppers, one on top of the other, both pointing down; the upper one holds four pieces of
redstone. This is the layout of `Redstone/Theorems/Basics/HopperPair.lean`, built twice: with
the upper hopper ticked first (`upperFirst`) and with the lower hopper ticked first
(`lowerFirst`). In the game the order is the order in which the block entities were loaded or
placed.

```
y = 2:   U     the upper hopper, (0, 2, 0), facing down, 4 redstone
y = 1:   L     the lower hopper, (0, 1, 0), facing down
```

Between two such hoppers an item can move in two ways: the upper hopper pushes it, or the
lower hopper pulls it. Each hopper does one move and then waits 8 game ticks, so **two items
go down every 8 game ticks**, one pushed and one pulled. When they go depends on the order:

* **Upper first.** Game tick 1: the upper hopper pushes one item. The lower hopper was empty,
  so it is put on cooldown (8, and 7 after its own tick in the same game tick) and cannot pull.
  Game tick 8: the lower hopper pulls the second item. Game tick 9: the upper hopper pushes
  the third. Game tick 16: the lower hopper pulls the fourth. All four are down after game
  tick 16.
* **Lower first.** Game tick 1: the lower hopper pulls one item, then the upper hopper pushes
  another; the lower one is not empty any more, so the push changes no cooldown. Both wait 8
  game ticks. Game tick 9: the same again. All four are down after game tick 9.

So the same blocks with the same items take 16 or 9 game ticks, and the second item arrives in
game tick 8 or in game tick 1. (In a horizontal line no hopper pulls from its neighbour, and
the order does not matter: `Chain.lean`.)

Both levels are loaded raw, with the hoppers off cooldown, and are never quiescent; the
statements are about runs of 18 game ticks.
-/

set_option Elab.async false

namespace Redstone.Theorems.Hopper.PairOrder

/-- The upper hopper. -/
def upper : Pos := ⟨0, 2, 0⟩

/-- The lower hopper. -/
def lower : Pos := ⟨0, 1, 0⟩

/-- The upper hopper holds four pieces of redstone. -/
def cargo : List (Pos × BlockEntity) :=
  [(upper, .hopper { items := (Inventory.empty 5).setItem 0 (.of redstone 4) })]

/-- The two hoppers, with the upper one ticked first. -/
def upperFirst : Level :=
  .ofCells [(upper, .hopper ⟨true, .down⟩), (lower, .hopper ⟨true, .down⟩)] cargo

/-- The two hoppers, with the lower one ticked first. -/
def lowerFirst : Level :=
  .ofCells [(lower, .hopper ⟨true, .down⟩), (upper, .hopper ⟨true, .down⟩)] cargo

/-- Eighteen game ticks without input. -/
def schedule : Schedule := .idle 18

checkpoints up := schedule from upperFirst

checkpoints low := schedule from lowerFirst

/-- The number of items in the upper and in the lower hopper. -/
def counts (l : Level) : ℕ × ℕ := (count l upper, count l lower)

/-- The transfer cooldowns of the upper and of the lower hopper. -/
def cooldowns (l : Level) : ℤ × ℤ := (cooldown l upper, cooldown l lower)

/-- The two levels hold the same blocks and the same items; they differ in the order in which
the hoppers are ticked. -/
theorem start :
    counts upperFirst = (4, 0) ∧ counts lowerFirst = (4, 0) ∧
      upperFirst.world = lowerFirst.world ∧
      upperFirst.blockEntities = lowerFirst.blockEntities ∧
      upperFirst.blockEntityTickers = [upper, lower] ∧
      lowerFirst.blockEntityTickers = [lower, upper] := by
  circuit_decide

assert_standard_axioms start

/-- **Upper hopper first: one item per game tick 1, 8, 9, 16.** The upper hopper pushes in the
game ticks 1 and 9; the lower hopper, on a cooldown of 7 after the first push, pulls in the
game ticks 8 and 16. -/
theorem upper_first :
    counts (rules.runSchedule (schedule.take 1) upperFirst) = (3, 1) ∧
      cooldowns (rules.runSchedule (schedule.take 1) upperFirst) = (8, 7) ∧
      counts (rules.runSchedule (schedule.take 7) upperFirst) = (3, 1) ∧
      counts (rules.runSchedule (schedule.take 8) upperFirst) = (2, 2) ∧
      cooldowns (rules.runSchedule (schedule.take 8) upperFirst) = (1, 8) ∧
      counts (rules.runSchedule (schedule.take 9) upperFirst) = (1, 3) ∧
      cooldowns (rules.runSchedule (schedule.take 9) upperFirst) = (8, 7) ∧
      counts (rules.runSchedule (schedule.take 15) upperFirst) = (1, 3) ∧
      counts (rules.runSchedule (schedule.take 16) upperFirst) = (0, 4) ∧
      counts (rules.runSchedule schedule upperFirst) = (0, 4) ∧
      (rules.runSchedule schedule upperFirst).overflow = false := by
  rw [up_run, up_run_1, up_run_7, up_run_8, up_run_9, up_run_15, up_run_16]
  circuit_decide

assert_standard_axioms upper_first

/-- **Lower hopper first: two items in game tick 1 and two in game tick 9.** The lower hopper
pulls, then the upper hopper pushes, in the same game tick; both then wait 8 game ticks. -/
theorem lower_first :
    counts (rules.runSchedule (schedule.take 1) lowerFirst) = (2, 2) ∧
      cooldowns (rules.runSchedule (schedule.take 1) lowerFirst) = (8, 8) ∧
      counts (rules.runSchedule (schedule.take 8) lowerFirst) = (2, 2) ∧
      cooldowns (rules.runSchedule (schedule.take 8) lowerFirst) = (1, 1) ∧
      counts (rules.runSchedule (schedule.take 9) lowerFirst) = (0, 4) ∧
      counts (rules.runSchedule schedule lowerFirst) = (0, 4) ∧
      (rules.runSchedule schedule lowerFirst).overflow = false := by
  rw [low_run, low_run_1, low_run_8, low_run_9]
  circuit_decide

assert_standard_axioms lower_first

/-- **The order of ticking decides when the items arrive.** After game tick 9 the lower hopper
holds all four items if it is ticked first, and three of them if the upper hopper is ticked
first; the fourth follows in game tick 16. After that the two levels hold the same items in
the same slots. -/
theorem order_matters :
    counts (rules.runSchedule (schedule.take 9) lowerFirst) = (0, 4) ∧
      counts (rules.runSchedule (schedule.take 9) upperFirst) = (1, 3) ∧
      counts (rules.runSchedule (schedule.take 16) upperFirst) = (0, 4) ∧
      slots (rules.runSchedule schedule upperFirst) lower = [(0, redstone, 4)] ∧
      slots (rules.runSchedule schedule lowerFirst) lower = [(0, redstone, 4)] := by
  rw [up_run, low_run, low_run_9, up_run_9, up_run_16]
  circuit_decide

assert_standard_axioms order_matters

end Redstone.Theorems.Hopper.PairOrder
