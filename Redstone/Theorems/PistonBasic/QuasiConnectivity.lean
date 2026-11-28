import Redstone.Proof.Circuit
import Redstone.Lemmas.Piston

/-!
# Quasi-connectivity: a piston powered through the position above it

```
y = 2:   .  D  L       D  redstone dust, L  lever (both on glass)
y = 1:   P  G  G       P  piston facing south (it pushes the stone block at z = 1)
         x = 0, 1, 2   G  glass
```

A piston at (0, 1, 0) facing south, with a stone block in front of it at (0, 1, 1). East of
the piston two glass blocks; on the first redstone dust, on the second a lever. The dust runs
east–west, so when the lever is on it points into the empty cell above the piston.

Nothing gives the piston itself a signal: glass does not conduct, the dust is not next to the
piston, and the cell above the piston is air. The piston is powered all the same, because a
piston also asks whether the position above it receives a signal (`getNeighborSignal`,
`Redstone.Component.Piston.neighborSignal`): quasi-connectivity. And it notices, because dust
that changes its power updates the neighbours of its neighbours, and the piston is a
neighbour of the cell the dust points into.

What is proved:

* **The piston is powered only through the position above it**
  (`powered_through_the_position_above`): with the lever on, `Level.powered` (the game's
  `hasNeighborSignal`) is false for the piston and true for the cell above it, and the
  piston's own rule answers true. With the lever off all three are false.
* **It extends with the usual timing** (`piston_extends`): the lever is switched on before game
  tick 1; in game tick 1 the piston starts, and after game tick 3 the head is out and the
  block one cell further south. `Level.powered` is false for the piston all the time.
* **It retracts when the lever is switched off** (`piston_retracts`).

The piston that is powered in this way and *not* updated is
`Redstone/Theorems/PistonBasic/BudSwitch.lean`.

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonBasic.QuasiConnectivity

open Redstone.Component.Piston (neighborSignal)

/-- The position of the lever. -/
def lever : Pos := ⟨2, 2, 0⟩

/-- The position of the redstone dust. -/
def dust : Pos := ⟨1, 2, 0⟩

/-- The position of the piston. -/
def piston : Pos := ⟨0, 1, 0⟩

/-- The cell above the piston. -/
def above : Pos := ⟨0, 2, 0⟩

/-- The cell in front of the piston. -/
def front : Pos := ⟨0, 1, 1⟩

/-- The cell after that. -/
def beyond : Pos := ⟨0, 1, 2⟩

/-- The `moving_piston` block of the piston. -/
def moving : Block := .movingPiston ⟨.south, .normal⟩

/-- The piston, retracted. -/
def retracted : Block := .pistonBase .piston ⟨false, .south⟩

/-- The piston, extended. -/
def extended : Block := .pistonBase .piston ⟨true, .south⟩

/-- A piston facing south with a stone block in front of it; east of it two glass blocks with
redstone dust and a lever on top. -/
def circuit : Level :=
  .ofCells [(piston, retracted), (front, .plain .stone),
    (⟨1, 1, 0⟩, .plain .glass), (⟨2, 1, 0⟩, .plain .glass),
    (dust, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]"),
    (lever, .lever ⟨.floor, .north, false⟩)]

/-- The lever is switched on before game tick 1 and off before game tick 5; eight game ticks
in all. -/
def schedule : Schedule := .first [.use lever .up] 4 ++ .first [.use lever .up] 4

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **The piston is powered only through the position above it.** Before the lever is used,
neither the piston nor the cell above it receives a signal, and the piston's rule answers
false. After game tick 4, with the lever on and the level at rest, the dust has power 15, the
piston still receives no signal, the cell above it does, and the piston's rule answers
true. -/
theorem powered_through_the_position_above :
    circuit.powered piston = false ∧ circuit.powered above = false ∧
      neighborSignal (rules.env maxDepth) circuit piston .south = false ∧
      (rules.runSchedule (schedule.take 4) circuit).dustPower dust = 15 ∧
      (rules.runSchedule (schedule.take 4) circuit).blockAt above = .AIR ∧
      (rules.runSchedule (schedule.take 4) circuit).powered piston = false ∧
      (rules.runSchedule (schedule.take 4) circuit).powered above = true ∧
      neighborSignal (rules.env maxDepth) (rules.runSchedule (schedule.take 4) circuit)
        piston .south = true ∧
      (rules.runSchedule (schedule.take 4) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_4]
  circuit_decide

assert_standard_axioms powered_through_the_position_above

/-- **The piston extends, with the usual timing.** The lever is switched on before game tick 1.
After game ticks 1 and 2 the base is extended and the two cells in front of it are moving;
after game tick 3 the head is in front of the piston and the stone block one cell further
south. After each of these game ticks the piston receives no signal of its own. -/
theorem piston_extends :
    circuit.blocksAt [piston, front, beyond] = [retracted, .plain .stone, .AIR] ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt [piston, front, beyond] =
        [extended, moving, moving] ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt [piston, front, beyond] =
        [extended, moving, moving] ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt [piston, front, beyond] =
        [extended, .pistonHead ⟨.south, false, .normal⟩, .plain .stone] ∧
      (rules.runSchedule (schedule.take 1) circuit).powered piston = false ∧
      (rules.runSchedule (schedule.take 2) circuit).powered piston = false ∧
      (rules.runSchedule (schedule.take 3) circuit).powered piston = false ∧
      (rules.runSchedule (schedule.take 3) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3]
  circuit_decide

assert_standard_axioms piston_extends

/-- **The piston retracts when the lever is switched off.** The lever is switched off before
game tick 5: the dust loses its power in game tick 5, the base is moving after game ticks 5
and 6 and is a retracted piston after game tick 7. The block stays where it was pushed to,
and the level ends at rest. -/
theorem piston_retracts :
    (rules.runSchedule (schedule.take 5) circuit).dustPower dust = 0 ∧
      (rules.runSchedule (schedule.take 5) circuit).blocksAt [piston, front, beyond] =
        [moving, .AIR, .plain .stone] ∧
      (rules.runSchedule (schedule.take 6) circuit).blocksAt [piston, front, beyond] =
        [moving, .AIR, .plain .stone] ∧
      (rules.runSchedule (schedule.take 7) circuit).blocksAt [piston, front, beyond] =
        [retracted, .AIR, .plain .stone] ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_5, state_run_6, state_run_7, state_run]
  circuit_decide

assert_standard_axioms piston_retracts

end Redstone.Theorems.PistonBasic.QuasiConnectivity
