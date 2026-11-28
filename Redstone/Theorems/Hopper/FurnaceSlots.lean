import Redstone.Theorems.Hopper.Common

/-!
# Hoppers around a furnace: which face gives which slot

The layout of every automatic furnace: a hopper on top for what is to be smelted, a hopper at
the side for the fuel, and a hopper underneath for the result.

```
y = 2:   T        T = (0, 2, 0), a hopper facing down, with 1 redstone
y = 1:   F ←S     F = (0, 1, 0), the furnace; S = (1, 1, 0), a hopper facing west,
y = 0:   B                       with 1 redstone (slot 0) and 1 coal (slot 1)
                  B = (0, 0, 0), a hopper facing down
```

The furnace has three slots: the ingredient (0), the fuel (1) and the result (2); the result
slot holds one iron ingot at the start.

* **Through the top** an item goes into the ingredient slot, whatever it is: the redstone of
  the upper hopper lands in slot 0.
* **Through a side** only fuel goes in, into the fuel slot. The side hopper's first item is
  redstone, which is no fuel: it is refused, and the hopper pushes the coal from its second
  slot instead, into slot 1 ("the first slot that has an item the container accepts").
* **Through the bottom** a hopper takes the result (slot 2), and from the fuel slot only what
  is left of a fuel (an empty bucket): the lower hopper takes the iron ingot and leaves the
  coal.

All three moves happen in game tick 1. Redstone dust cannot be smelted, so the furnace never
lights, and afterwards nothing changes: the lower hopper, off cooldown again from game tick 9
on, does not take the coal. The statements are about a run of 12 game ticks.

The level is loaded raw, with the hoppers off cooldown; it is never quiescent (three hoppers
and the furnace are ticked).
-/

set_option Elab.async false

namespace Redstone.Theorems.Hopper.FurnaceSlots

/-- The hopper on top of the furnace. -/
def above : Pos := ⟨0, 2, 0⟩

/-- The hopper beside the furnace, pointing into it. -/
def beside : Pos := ⟨1, 1, 0⟩

/-- The furnace. -/
def furnace : Pos := ⟨0, 1, 0⟩

/-- The hopper under the furnace. -/
def below : Pos := ⟨0, 0, 0⟩

/-- What the side hopper holds: redstone in its first slot and coal in its second. -/
def sideCargo : Inventory :=
  ((Inventory.empty 5).setItem 0 (.of redstone 1)).setItem 1 (.of coal 1)

/-- A furnace with an iron ingot in its result slot, and a hopper above, beside and below
it. -/
def circuit : Level :=
  .ofCells [(above, .hopper ⟨true, .down⟩), (beside, .hopper ⟨true, .west⟩),
      (furnace, .furnace ⟨.north, false⟩), (below, .hopper ⟨true, .down⟩)]
    [(above, .hopper { items := (Inventory.empty 5).setItem 0 (.of redstone 1) }),
      (beside, .hopper { items := sideCargo }),
      (furnace, .furnace { items := (Inventory.empty 3).setItem 2 (.of ironIngot 1) })]

/-- Twelve game ticks without input. -/
def schedule : Schedule := .idle 12

checkpoints state := schedule from circuit

/-- At the start the furnace holds only the iron ingot, in its result slot. -/
theorem start :
    slots circuit above = [(0, redstone, 1)] ∧
      slots circuit beside = [(0, redstone, 1), (1, coal, 1)] ∧
      slots circuit furnace = [(2, ironIngot, 1)] ∧
      slots circuit below = [] ∧
      circuit.blockEntityTickers = [above, beside, furnace, below] := by
  circuit_decide

assert_standard_axioms start

/-- **Top: ingredient. Side: fuel. Bottom: result.** After game tick 1 the redstone from above
is in slot 0 of the furnace and the coal from the side in slot 1; the side hopper still has
its redstone, which the furnace refused; and the lower hopper has taken the iron ingot out of
slot 2. -/
theorem routing :
    slots (rules.runSchedule (schedule.take 1) circuit) furnace =
        [(0, redstone, 1), (1, coal, 1)] ∧
      slots (rules.runSchedule (schedule.take 1) circuit) above = [] ∧
      slots (rules.runSchedule (schedule.take 1) circuit) beside = [(0, redstone, 1)] ∧
      slots (rules.runSchedule (schedule.take 1) circuit) below = [(0, ironIngot, 1)] ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms routing

/-- **Nothing else moves.** After game tick 12 every container holds what it held after game
tick 1: the lower hopper, whose cooldown ran out in game tick 9, has not taken the coal out of
the fuel slot, and the side hopper has not got rid of its redstone. The furnace is not lit,
and the model has not reached a bound. -/
theorem settled :
    slots (rules.runSchedule schedule circuit) furnace = [(0, redstone, 1), (1, coal, 1)] ∧
      slots (rules.runSchedule schedule circuit) beside = [(0, redstone, 1)] ∧
      slots (rules.runSchedule schedule circuit) below = [(0, ironIngot, 1)] ∧
      cooldown (rules.runSchedule (schedule.take 8) circuit) below = 1 ∧
      cooldown (rules.runSchedule schedule circuit) below = 0 ∧
      (rules.runSchedule schedule circuit).blockAt furnace = .furnace ⟨.north, false⟩ ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run, state_run_8]
  circuit_decide

assert_standard_axioms settled

end Redstone.Theorems.Hopper.FurnaceSlots
