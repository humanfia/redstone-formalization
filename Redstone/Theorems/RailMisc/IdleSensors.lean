import Redstone.Proof.Circuit

/-!
# The blocks that entities switch, with no entity: they stay off

A row of the blocks that give a signal only when an entity (or lightning, or a projectile)
acts on them, on a floor of stone, every second cell, with nothing else around:

```
z = 2, y = 1:   lamp
z = 1, y = 1:   C                                         H
z = 0, y = 1:   D  .  W  .  P  .  G  .  I  .  R  .  T  .  S       x = 0 .. 14
z = 0, y = 0:   S  S  S  S  S  S  S  S  S  S  S  S  S  S  S       (and S under C and lamp)
```

`D` detector rail, `W` oak (wooden) pressure plate, `P` stone pressure plate, `G` light
weighted (gold) plate, `I` heavy weighted (iron) plate, `R` lightning rod, `T` target, `H` a
tripwire hook on the south face of the stone block `S` at x = 14. `C` is a comparator that
reads the detector rail, with a lamp at its output.

A level without entities has nothing that presses a plate, rides a rail, pulls a string,
strikes a rod or hits a target. The theorem says that the row is at rest and stays as it is
for ever: every sensor off, no signal to the cell east of any of them, the comparator reading
zero and its lamp dark. For the plates and the detector rail, `Redstone/Lemmas/Plate.lean`
has the generic side of this: in any level without entities they measure nothing.

The level is loaded raw.
-/

set_option Elab.async false

namespace Redstone.Theorems.RailMisc.IdleSensors

/-- The position of the comparator that reads the detector rail. -/
def comparator : Pos := ⟨0, 1, 1⟩

/-- The position of the lamp at the comparator's output. -/
def lamp : Pos := ⟨0, 1, 2⟩

/-- The sensors, each in its off state. -/
def sensors : List (Pos × Block) :=
  [(⟨0, 1, 0⟩, blk% "minecraft:detector_rail[powered=false,shape=east_west,waterlogged=false]"),
    (⟨2, 1, 0⟩, blk% "minecraft:oak_pressure_plate[powered=false]"),
    (⟨4, 1, 0⟩, blk% "minecraft:stone_pressure_plate[powered=false]"),
    (⟨6, 1, 0⟩, blk% "minecraft:light_weighted_pressure_plate[power=0]"),
    (⟨8, 1, 0⟩, blk% "minecraft:heavy_weighted_pressure_plate[power=0]"),
    (⟨10, 1, 0⟩, blk% "minecraft:lightning_rod[facing=up,powered=false,waterlogged=false]"),
    (⟨12, 1, 0⟩, blk% "minecraft:target[power=0]"),
    (⟨14, 1, 1⟩, blk% "minecraft:tripwire_hook[attached=false,facing=south,powered=false]")]

/-- The comparator, facing the detector rail, off. -/
def comparatorOff : Block := blk% "minecraft:comparator[facing=north,mode=compare,powered=false]"

/-- The row of sensors on a floor of stone, with the comparator and its lamp. -/
def circuit : Level :=
  .ofCells ((List.range 15).map (fun i => ((⟨(i : ℤ), 0, 0⟩ : Pos), Block.plain .stone)) ++
    [(⟨0, 0, 1⟩, .plain .stone), (⟨0, 0, 2⟩, .plain .stone), (⟨14, 1, 0⟩, .plain .stone),
      (comparator, comparatorOff), (lamp, .redstoneLamp ⟨false⟩)] ++ sensors)

/-- The row is at rest, and it has no entity. -/
theorem circuit_quiescent : circuit.Quiescent ∧ circuit.entities = [] := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- No sensor gives a signal to the cell east of it, or to the cell above it, and the
comparator has read zero. -/
theorem no_signal :
    (sensors.map fun s => circuit.signalTo (s.1.step .east)) = List.replicate 8 0 ∧
      (sensors.map fun s => circuit.signalTo (s.1.step .up)) = List.replicate 8 0 ∧
      circuit.blockEntities comparator = some (.comparator ⟨0⟩) := by
  circuit_decide

assert_standard_axioms no_signal

/-- **With no entity every sensor stays off for ever**: after any number of game ticks the
sensors are as they were built, the comparator is off, its lamp is dark, and its reading is
zero. -/
theorem stay_off (n : ℕ) :
    (rules.steps n circuit).blocksAt (sensors.map (·.1)) = sensors.map (·.2) ∧
      (rules.steps n circuit).blocksAt [comparator, lamp] =
        [comparatorOff, .redstoneLamp ⟨false⟩] ∧
      (rules.steps n circuit).blockEntities comparator = some (.comparator ⟨0⟩) ∧
      (rules.steps n circuit).overflow = false := by
  rw [rules.steps_of_quiescent circuit_quiescent.1]
  simp only [Level.blocksAt_advance, Level.blockEntities_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stay_off

end Redstone.Theorems.RailMisc.IdleSensors
