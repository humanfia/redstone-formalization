import Redstone.Proof.Circuit

/-!
# The slab staircase: dust that carries a signal up and not down

Dust on a staircase of blocks that are not conductors (top slabs, glass) carries a signal
upwards only. Dust reads the dust one level *below* it past a neighbour that is not a
conductor, but it reads the dust one level *above* it only on top of a neighbour that is a
conductor: on slabs or glass the upper piece sees the lower one and the lower piece does not
see the upper one. Seen from the south (`z = 0`; `x` to the right, `y` upwards):

```
y = 4:               d4 L2       s: step (a top slab, or glass)     d1 .. d4: dust on the steps
y = 3:            d3 s  S        L1: lever at the bottom, next to d1, on a stone block S
y = 2:         d2 s              L2: lever at the top, next to d4, on a stone block S
y = 1:   L1 d1 s
y = 0:   S  s
    x = -1  0  1  2  3  4
```

The same is proved for a staircase of smooth stone top slabs (`slabs`) and for one of glass
(`glass`). On slabs the lower dust connects sideways to the step above it, on glass it
connects up the step; the power is the same.

* **Upwards.** The bottom lever is switched on before game tick 1: in that game tick the dust
  has the powers 15, 14, 13, 12 from the bottom up, one less per step (`slabs_up`,
  `glass_up`). It is switched off before game tick 3 and all the dust is dark.
* **Not downwards.** The top lever is switched on before game tick 5: the top piece has power
  15 and the three pieces below it stay at 0 (`slabs_not_down`, `glass_not_down`), for ever
  (`slabs_not_down_for_ever`, `glass_not_down_for_ever`).
* After the top lever is switched off again the blocks are those the circuit started with
  (`back_to_start`).

The generic statement is `Dust.wireSignal_down_le_wireReach` (`Redstone/Lemmas/Dust.lean`).
The levels are loaded raw and are at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Wire.SlabStaircase

/-- The lever at the bottom. -/
def bottomLever : Pos := ⟨-1, 1, 0⟩

/-- The lever at the top. -/
def topLever : Pos := ⟨4, 4, 0⟩

/-- The four pieces of dust, from the bottom up. -/
def dust : List Pos := [⟨0, 1, 0⟩, ⟨1, 2, 0⟩, ⟨2, 3, 0⟩, ⟨3, 4, 0⟩]

/-- A piece of dust connected to the west and to the east; `east` says how. -/
def wire (east : RedstoneSide) (power : Fin 16) : Block :=
  .redstoneWire ⟨east, .none, power, .none, .side⟩

/-- The four pieces of dust with the given powers, from the bottom up; `east` is how the three
lower ones connect to the step above them. -/
def wires (east : RedstoneSide) (p₁ p₂ p₃ p₄ : Fin 16) : List Block :=
  [wire east p₁, wire east p₂, wire east p₃, wire .side p₄]

/-- The staircase with steps made of `step`; `east` is how the three lower pieces of dust
connect to the step above them. -/
def staircase (step : Block) (east : RedstoneSide) : Level :=
  .ofCells [(⟨-1, 0, 0⟩, .plain .stone), (⟨4, 3, 0⟩, .plain .stone),
    (⟨0, 0, 0⟩, step), (⟨1, 1, 0⟩, step), (⟨2, 2, 0⟩, step), (⟨3, 3, 0⟩, step),
    (bottomLever, .lever ⟨.floor, .north, false⟩), (topLever, .lever ⟨.floor, .north, false⟩),
    (⟨0, 1, 0⟩, wire east 0), (⟨1, 2, 0⟩, wire east 0), (⟨2, 3, 0⟩, wire east 0),
    (⟨3, 4, 0⟩, wire .side 0)]

/-- The staircase of smooth stone top slabs. -/
def slabs : Level := staircase (.slab .smooth_stone_slab ⟨.top, false⟩) .side

/-- The staircase of glass. -/
def glass : Level := staircase (.plain .glass) .up

/-- The bottom lever on before game tick 1 and off before game tick 3; the top lever on
before game tick 5 and off before game tick 7; eight game ticks. -/
def schedule : Schedule :=
  .first [.use bottomLever .up] 2 ++ .first [.use bottomLever .up] 2 ++
    .first [.use topLever .up] 2 ++ .first [.use topLever .up] 2

checkpoints onSlabs := schedule from slabs
checkpoints onGlass := schedule from glass

/-- Both staircases as built are at rest, with all the dust dark. -/
theorem circuit_quiescent :
    slabs.Quiescent ∧ glass.Quiescent ∧ slabs.blocksAt dust = wires .side 0 0 0 0 ∧
      glass.blocksAt dust = wires .up 0 0 0 0 := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Up the slabs.** With the bottom lever on, the dust has the powers 15, 14, 13, 12 from
the bottom up, in the game tick of the lever; with the lever off again it is dark. The dust
is observed as blocks: each piece is there, with its shape. -/
theorem slabs_up :
    (rules.runSchedule (schedule.take 1) slabs).blocksAt dust =
        wires .side 15 14 13 12 ∧
      (rules.runSchedule (schedule.take 3) slabs).blocksAt dust =
        wires .side 0 0 0 0 ∧
      (rules.runSchedule (schedule.take 3) slabs).overflow = false := by
  rw [onSlabs_run_1, onSlabs_run_3]
  circuit_decide

assert_standard_axioms slabs_up

/-- **Not down the slabs.** With the top lever on, the top piece has power 15 and the three
pieces below it have none. -/
theorem slabs_not_down :
    (rules.runSchedule (schedule.take 5) slabs).blocksAt dust =
        wires .side 0 0 0 15 ∧
      (rules.runSchedule (schedule.take 5) slabs).overflow = false := by
  rw [onSlabs_run_5]
  circuit_decide

assert_standard_axioms slabs_not_down

/-- With the top lever on, the slab staircase is at rest: the lower pieces stay dark for
ever. -/
theorem slabs_not_down_for_ever (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 5) slabs)).blocksAt dust =
        wires .side 0 0 0 15 ∧
      (rules.steps n (rules.runSchedule (schedule.take 5) slabs)).overflow = false := by
  rw [onSlabs_run_5, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms slabs_not_down_for_ever

/-- **Up the glass.** With the bottom lever on, the dust has the powers 15, 14, 13, 12 from
the bottom up, in the game tick of the lever; with the lever off again it is dark. The dust
is observed as blocks: each piece is there, with its shape. -/
theorem glass_up :
    (rules.runSchedule (schedule.take 1) glass).blocksAt dust =
        wires .up 15 14 13 12 ∧
      (rules.runSchedule (schedule.take 3) glass).blocksAt dust =
        wires .up 0 0 0 0 ∧
      (rules.runSchedule (schedule.take 3) glass).overflow = false := by
  rw [onGlass_run_1, onGlass_run_3]
  circuit_decide

assert_standard_axioms glass_up

/-- **Not down the glass.** With the top lever on, the top piece has power 15 and the three
pieces below it have none. -/
theorem glass_not_down :
    (rules.runSchedule (schedule.take 5) glass).blocksAt dust =
        wires .up 0 0 0 15 ∧
      (rules.runSchedule (schedule.take 5) glass).overflow = false := by
  rw [onGlass_run_5]
  circuit_decide

assert_standard_axioms glass_not_down

/-- With the top lever on, the glass staircase is at rest: the lower pieces stay dark for
ever. -/
theorem glass_not_down_for_ever (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 5) glass)).blocksAt dust =
        wires .up 0 0 0 15 ∧
      (rules.steps n (rules.runSchedule (schedule.take 5) glass)).overflow = false := by
  rw [onGlass_run_5, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms glass_not_down_for_ever

/-- After the whole schedule the blocks of both staircases are those they started with, and
the levels are at rest. -/
theorem back_to_start :
    (rules.runSchedule schedule slabs).world = slabs.world ∧
      (rules.runSchedule schedule slabs).Quiescent ∧
      (rules.runSchedule schedule slabs).overflow = false ∧
      (rules.runSchedule schedule glass).world = glass.world ∧
      (rules.runSchedule schedule glass).Quiescent ∧
      (rules.runSchedule schedule glass).overflow = false := by
  rw [onSlabs_run, onGlass_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Wire.SlabStaircase
