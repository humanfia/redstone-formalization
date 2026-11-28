import Redstone.Theorems.Hopper.Common

/-!
# Hoppers at a brewing stand: which face gives which slot

A brewing stand with a hopper on top and a hopper at the side, as in an automatic brewer.

```
y = 2:   T        T = (0, 2, 0), a hopper facing down: cobblestone (slot 0), nether wart (slot 1)
y = 1:   B ←S     B = (0, 1, 0), the brewing stand; S = (1, 1, 0), a hopper facing west:
                                 nether wart (slot 0), blaze powder (slot 1)
```

The brewing stand has five slots: three bottles (0 to 2), the ingredient (3) and the fuel
(4).

* **Through the top** only the ingredient slot is reached, and it takes brewing ingredients
  only: the cobblestone is refused and the nether wart from the hopper's second slot goes into
  slot 3.
* **Through a side** the bottle slots and the fuel slot are reached, not the ingredient slot:
  the nether wart of the side hopper is refused, and the blaze powder goes into slot 4.

Both moves happen in game tick 1. The brewing stand is ticked before the hoppers here, so it
sees the blaze powder in game tick 2 and burns it: the fuel slot is empty again and the stand
has fuel for 20 brews. Nothing else moves; the statements are about a run of 10 game ticks.

Bottles are not part of this layout: a potion carries its contents in a data component, and
the model's brewing stand answers a stack with components by setting `Level.overflow`
(`Redstone.Component.Container`, under what is left out).

The level is loaded raw, with the hoppers off cooldown; it is never quiescent.
-/

set_option Elab.async false

namespace Redstone.Theorems.Hopper.BrewingStandSlots

/-- Cobblestone, which is no brewing ingredient. -/
def cobblestone : String := "minecraft:cobblestone"

/-- Nether wart, a brewing ingredient. -/
def netherWart : String := "minecraft:nether_wart"

/-- Blaze powder, the fuel of a brewing stand. -/
def blazePowder : String := "minecraft:blaze_powder"

/-- The brewing stand. -/
def stand : Pos := ⟨0, 1, 0⟩

/-- The hopper on top of the brewing stand. -/
def above : Pos := ⟨0, 2, 0⟩

/-- The hopper beside the brewing stand, pointing into it. -/
def beside : Pos := ⟨1, 1, 0⟩

/-- Two stacks of one item, in the first two slots of a hopper. -/
def two (first second : String) : Inventory :=
  ((Inventory.empty 5).setItem 0 (.of first 1)).setItem 1 (.of second 1)

/-- A brewing stand, ticked first, with a hopper above and a hopper beside it. -/
def circuit : Level :=
  .ofCells [(stand, .brewingStand ⟨false, false, false⟩), (above, .hopper ⟨true, .down⟩),
      (beside, .hopper ⟨true, .west⟩)]
    [(above, .hopper { items := two cobblestone netherWart }),
      (beside, .hopper { items := two netherWart blazePowder })]

/-- Ten game ticks without input. -/
def schedule : Schedule := .idle 10

checkpoints state := schedule from circuit

/-- The fuel the brewing stand has left, in brews. -/
def fuel (l : Level) : ℤ :=
  match l.blockEntities stand with
  | some (.brewingStand d) => d.fuel
  | _ => 0

/-- At the start the brewing stand is empty and has no fuel. -/
theorem start :
    slots circuit stand = [] ∧ fuel circuit = 0 ∧
      slots circuit above = [(0, cobblestone, 1), (1, netherWart, 1)] ∧
      slots circuit beside = [(0, netherWart, 1), (1, blazePowder, 1)] ∧
      circuit.blockEntityTickers = [stand, above, beside] := by
  circuit_decide

assert_standard_axioms start

/-- **Top: ingredient. Side: fuel.** After game tick 1 the nether wart from above is in slot 3
and the blaze powder from the side in slot 4. The upper hopper keeps its cobblestone, which is
no ingredient, and the side hopper its nether wart, which does not go in through a side. -/
theorem routing :
    slots (rules.runSchedule (schedule.take 1) circuit) stand =
        [(3, netherWart, 1), (4, blazePowder, 1)] ∧
      slots (rules.runSchedule (schedule.take 1) circuit) above = [(0, cobblestone, 1)] ∧
      slots (rules.runSchedule (schedule.take 1) circuit) beside = [(0, netherWart, 1)] ∧
      fuel (rules.runSchedule (schedule.take 1) circuit) = 0 ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms routing

/-- **The stand burns the blaze powder in the next game tick**: after game tick 2 the fuel
slot is empty and the stand has fuel for 20 brews. After game tick 10 nothing else has
changed, and the model has not reached a bound. -/
theorem fuelled :
    slots (rules.runSchedule (schedule.take 2) circuit) stand = [(3, netherWart, 1)] ∧
      fuel (rules.runSchedule (schedule.take 2) circuit) = 20 ∧
      slots (rules.runSchedule schedule circuit) stand = [(3, netherWart, 1)] ∧
      fuel (rules.runSchedule schedule circuit) = 20 ∧
      slots (rules.runSchedule schedule circuit) above = [(0, cobblestone, 1)] ∧
      slots (rules.runSchedule schedule circuit) beside = [(0, netherWart, 1)] ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run, state_run_2]
  circuit_decide

assert_standard_axioms fuelled

end Redstone.Theorems.Hopper.BrewingStandSlots
