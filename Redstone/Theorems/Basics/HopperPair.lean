import Redstone.Proof.Circuit

/-!
# Two hoppers and the transfer cooldown

A hopper on top of a hopper, both pointing down; the upper one holds two pieces of redstone.
One item moves in the first game tick. Then both hoppers are on cooldown, and the second item
moves in game tick 8.

What the cooldowns are (`HopperBlockEntity`): a hopper that moved an item waits 8 game ticks
(`MOVE_ITEM_SPEED`). The upper hopper pushes the first item in game tick 1 and is on cooldown
until game tick 9. The lower hopper, which was empty when it received that item, is put on a
cooldown of 8 as well, and is then ticked itself in the same game tick, which brings it to 7;
when that runs out, in game tick 8, the lower hopper pulls the second item from the hopper
above, one game tick before the upper one could push it.

A hopper is a ticking block entity, and it records the game time of its last tick: a level
with a hopper is never quiescent (`Level.Quiescent`), so the statements here are about a
bounded run of ten game ticks.

The level is loaded raw: the block entities are put in place with the hoppers off cooldown.
-/

set_option Elab.async false

namespace Redstone.Theorems.Basics.HopperPair

/-- The position of the upper hopper. -/
def upper : Pos := ⟨0, 2, 0⟩

/-- The position of the lower hopper. -/
def lower : Pos := ⟨0, 1, 0⟩

/-- Two hoppers, one on top of the other, both pointing down. The upper one holds two pieces
of redstone in its first slot; it is ticked first. -/
def circuit : Level :=
  .ofCells [(upper, .hopper ⟨true, .down⟩), (lower, .hopper ⟨true, .down⟩)]
    [(upper, .hopper { items := (Inventory.empty 5).setItem 0 (.of "minecraft:redstone" 2) })]

/-- Ten game ticks without input. -/
def schedule : Schedule := .idle 10

checkpoints state := schedule from circuit

/-- The transfer cooldown of the hopper at `p`; zero if there is no hopper. -/
def cooldown (l : Level) (p : Pos) : ℤ :=
  match l.blockEntities p with
  | some (.hopper d) => d.cooldownTime
  | _ => 0

/-- The number of items in the upper and in the lower hopper. -/
def counts (l : Level) : ℕ × ℕ := (l.itemCount upper, l.itemCount lower)

/-- At the start both items are in the upper hopper, and both hoppers are ticked, the upper
one first. -/
theorem start : counts circuit = (2, 0) ∧ circuit.blockEntityTickers = [upper, lower] := by
  circuit_decide

assert_standard_axioms start

/-- **The first item moves in the first game tick**, and both hoppers go on cooldown. After the
game tick the upper one has 8 game ticks left; the lower one, which got its 8 before it was
ticked in the same game tick, has 7. -/
theorem first_item :
    counts (rules.runSchedule (schedule.take 1) circuit) = (1, 1) ∧
      cooldown (rules.runSchedule (schedule.take 1) circuit) upper = 8 ∧
      cooldown (rules.runSchedule (schedule.take 1) circuit) lower = 7 ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms first_item

/-- **Nothing moves while the hoppers are on cooldown**: after each of the game ticks 2 to 7
there is still one item in each hopper. -/
theorem cooldown_holds :
    counts (rules.runSchedule (schedule.take 2) circuit) = (1, 1) ∧
      counts (rules.runSchedule (schedule.take 3) circuit) = (1, 1) ∧
      counts (rules.runSchedule (schedule.take 4) circuit) = (1, 1) ∧
      counts (rules.runSchedule (schedule.take 5) circuit) = (1, 1) ∧
      counts (rules.runSchedule (schedule.take 6) circuit) = (1, 1) ∧
      counts (rules.runSchedule (schedule.take 7) circuit) = (1, 1) ∧
      cooldown (rules.runSchedule (schedule.take 7) circuit) upper = 2 ∧
      cooldown (rules.runSchedule (schedule.take 7) circuit) lower = 1 := by
  rw [state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7]
  circuit_decide

assert_standard_axioms cooldown_holds

/-- **The second item moves in game tick 8**: the lower hopper's cooldown has run out and it
pulls the item from the hopper above, which is still on cooldown itself. The lower hopper is
then on cooldown for 8 game ticks. -/
theorem second_item :
    counts (rules.runSchedule (schedule.take 8) circuit) = (0, 2) ∧
      cooldown (rules.runSchedule (schedule.take 8) circuit) upper = 1 ∧
      cooldown (rules.runSchedule (schedule.take 8) circuit) lower = 8 ∧
      (rules.runSchedule (schedule.take 8) circuit).overflow = false := by
  rw [state_run_8]
  circuit_decide

assert_standard_axioms second_item

/-- After ten game ticks both items are in the lower hopper, in one stack, and the model has
not reached a bound. -/
theorem all_moved :
    counts (rules.runSchedule schedule circuit) = (0, 2) ∧
      (rules.runSchedule schedule circuit).blockEntities lower =
        some (.hopper { items := (Inventory.empty 5).setItem 0 (.of "minecraft:redstone" 2)
                        cooldownTime := 6, tickedGameTime := 10 }) ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms all_moved

end Redstone.Theorems.Basics.HopperPair
