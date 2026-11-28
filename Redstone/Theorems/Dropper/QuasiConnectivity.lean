import Redstone.Theorems.Dropper.Basic

/-!
# Quasi-connectivity of a dropper

```
y = 2    S L .        S  stone      L  lever on the east face of the stone
y = 1    . . D C      D  dropper facing east, two pieces of redstone      C  chest
     x = -2 -1 0 1    .  air
```

The lever is beside the air block above the dropper. It powers that position, and nothing
that touches the dropper. A dropper (and a dispenser) also counts as powered when the position
above it receives a signal, as a piston does (`DispenserBlock.neighborChanged` asks
`hasNeighborSignal(pos) || hasNeighborSignal(pos.above())`); but it only asks when it gets a
block update, and the lever updates its own neighbours and those of the stone, not the
dropper. So the dropper is in the state the community calls *budded*.

The schedule: the lever is switched on before game tick 1; a stone block is placed south of
the dropper before game tick 7, which updates the dropper; the lever is switched off before
game tick 13; the stone block is removed before game tick 16.

What the theorems say:

* the lever alone changes nothing at the dropper, for ever, although the dropper would count
  as powered;
* the block update makes it `triggered`, and four game ticks later one item is in the chest;
* switching the lever off does not reach the dropper either: it stays `triggered`, for ever,
  with no signal anywhere near it;
* the next block update clears `triggered`.
-/

set_option Elab.async false

namespace Redstone.Theorems.Dropper.QuasiConnectivity

/-- The position of the dropper. -/
def dropper : Pos := ⟨0, 1, 0⟩

/-- The position of the chest. -/
def chest : Pos := ⟨1, 1, 0⟩

/-- The position of the lever. -/
def lever : Pos := ⟨-1, 2, 0⟩

/-- The position above the dropper: air. -/
def above : Pos := ⟨0, 2, 0⟩

/-- The position south of the dropper, where a block is placed and removed to update it. -/
def beside : Pos := ⟨0, 1, 1⟩

/-- A dropper facing east into a chest; a lever on the side of a stone block, next to the air
above the dropper. The dropper holds two pieces of redstone. -/
def circuit : Level :=
  .ofCells [(dropper, .dropper ⟨.east, false⟩), (chest, .chest ⟨.north, .single, false⟩),
    (⟨-2, 2, 0⟩, .plain .stone), (lever, .lever ⟨.wall, .east, false⟩)]
    [(dropper, .dropper { items := (Inventory.empty 9).setItem 0 (.of "minecraft:redstone" 2) })]

/-- Lever on before game tick 1, a block placed beside the dropper before game tick 7, lever
off before game tick 13, the block removed before game tick 16; 18 game ticks in all. -/
def schedule : Schedule :=
  .first [.use lever .east] 6 ++ Schedule.first [.set beside (.plain .stone)] 6 ++
    Schedule.first [.use lever .east] 3 ++ Schedule.first [.destroy beside] 3

checkpoints state := schedule from circuit

/-- The circuit as built is at rest, and nothing powers the dropper or the position above. -/
theorem start :
    circuit.Quiescent ∧ circuit.powered dropper = false ∧ circuit.powered above = false := by
  circuit_decide

assert_standard_axioms start

/-- **Powered through the position above, and not triggered.** With the lever on, the position
above the dropper receives a signal and the dropper itself receives none; the dropper is not
`triggered`, nothing is scheduled, and the level is at rest: it stays so for ever. -/
theorem powered_not_triggered (n : ℕ) :
    (rules.runSchedule (schedule.take 1) circuit).blockAt lever = .lever ⟨.wall, .east, true⟩ ∧
      (rules.runSchedule (schedule.take 1) circuit).powered above = true ∧
      (rules.runSchedule (schedule.take 1) circuit).powered dropper = false ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).blockAt dropper =
        .dropper ⟨.east, false⟩ ∧
      contents (rules.steps n (rules.runSchedule (schedule.take 1) circuit)) chest = [] ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).overflow = false := by
  rw [state_run_1, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blockAt_advance, Level.overflow_advance, contents_advance]
  circuit_decide

assert_standard_axioms powered_not_triggered

/-- **A block update fires the dropper.** In the game tick in which a block is placed beside
it, the dropper becomes `triggered` and schedules its tick, due four game ticks after the
update; after two more game ticks both items are still in it, and after the third one item is
in the chest. -/
theorem update_fires :
    (rules.runSchedule (schedule.take 6) circuit).blockAt dropper = .dropper ⟨.east, false⟩ ∧
      (rules.runSchedule (schedule.take 7) circuit).blockAt dropper = .dropper ⟨.east, true⟩ ∧
      (rules.runSchedule (schedule.take 7) circuit).pending = [(dropper, .dropper, 3, .normal)] ∧
      contents (rules.runSchedule (schedule.take 9) circuit) dropper =
        [(0, "minecraft:redstone", 2)] ∧
      contents (rules.runSchedule (schedule.take 10) circuit) dropper =
        [(0, "minecraft:redstone", 1)] ∧
      contents (rules.runSchedule (schedule.take 10) circuit) chest =
        [(0, "minecraft:redstone", 1)] ∧
      (rules.runSchedule (schedule.take 10) circuit).overflow = false := by
  rw [state_run_6, state_run_7, state_run_9, state_run_10]
  circuit_decide

assert_standard_axioms update_fires

/-- **The falling edge is not seen either.** After the lever is switched off, nothing powers
the position above the dropper, and the dropper is still `triggered`; the level is at rest and
stays so for ever. -/
theorem stays_triggered (n : ℕ) :
    (rules.runSchedule (schedule.take 13) circuit).blockAt lever = .lever ⟨.wall, .east, false⟩ ∧
      (rules.runSchedule (schedule.take 13) circuit).powered above = false ∧
      (rules.runSchedule (schedule.take 13) circuit).powered dropper = false ∧
      (rules.steps n (rules.runSchedule (schedule.take 13) circuit)).blockAt dropper =
        .dropper ⟨.east, true⟩ ∧
      (rules.steps n (rules.runSchedule (schedule.take 13) circuit)).overflow = false := by
  rw [state_run_13, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stays_triggered

/-- **The next block update clears `triggered`**, in the game tick in which the block beside
the dropper is removed; nothing is scheduled and no item moves. The level is then at rest for
ever, with one item in the dropper and one in the chest. -/
theorem update_clears (n : ℕ) :
    (rules.runSchedule (schedule.take 15) circuit).blockAt dropper = .dropper ⟨.east, true⟩ ∧
      (rules.runSchedule (schedule.take 16) circuit).blockAt dropper = .dropper ⟨.east, false⟩ ∧
      (rules.runSchedule (schedule.take 16) circuit).pending = [] ∧
      (rules.steps n (rules.runSchedule schedule circuit)).blockAt dropper =
        .dropper ⟨.east, false⟩ ∧
      contents (rules.steps n (rules.runSchedule schedule circuit)) dropper =
        [(0, "minecraft:redstone", 1)] ∧
      contents (rules.steps n (rules.runSchedule schedule circuit)) chest =
        [(0, "minecraft:redstone", 1)] ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run_15, state_run_16, state_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blockAt_advance, Level.overflow_advance, contents_advance]
  circuit_decide

assert_standard_axioms update_clears

end Redstone.Theorems.Dropper.QuasiConnectivity
