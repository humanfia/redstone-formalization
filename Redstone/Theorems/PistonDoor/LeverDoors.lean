import Redstone.Proof.Circuit

/-!
# An iron door, an iron trapdoor and a fence gate on a lever

The doors that need no piston. A lever stands on a stone floor; west of it is an iron door
(two blocks high), east of it an iron trapdoor, south of it an oak fence gate. All three are
next to the lever, so each receives its signal directly.

```
y = 2     the upper half of the door, above the lower half

y = 1     door   lever   trapdoor         (west to east, at z = 0)
                 gate                     (at z = 1)

y = 0     stone under each of the four
```

What is proved:

* `opens_at_once`: in the game tick in which the lever is switched on, the door (both halves),
  the trapdoor and the gate open and remember that they are powered. Nothing is scheduled:
  the level after that game tick is at rest. The upper half of the door is not next to the
  lever; it follows the lower half through a shape update (`DoorBlock.updateShape`).
* `stays_open`: they stay open for ever while the lever is on.
* `closes_at_once`: in the game tick in which the lever is switched off they close, and the
  level is at rest with the blocks it started with.

Iron doors and iron trapdoors cannot be opened by hand (`Redstone/Lemmas/Door.lean`), so the
lever is the only way in.

The theorems evaluate one game tick each, directly: this level has no checkpoints, because
the command `checkpoints` (and `blk%`) cannot write a door, a trapdoor or a fence gate as a
term. Their property `open` is a keyword of Lean, and what `Repr` prints for it does not parse
(`Redstone.Proof.parseRepr`). The blocks are written with their constructors here.

Not proved: a pair of doors side by side (two doors that open away from each other need
hinges on opposite sides; that is a matter of how they look, not of how they switch), and
doors opened by a pressure plate, which needs an entity to stand on it.

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonDoor.LeverDoors

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The lower half of the door. -/
def doorLower : Pos := ⟨-1, 1, 0⟩

/-- The upper half of the door. -/
def doorUpper : Pos := ⟨-1, 2, 0⟩

/-- The trapdoor. -/
def trapdoor : Pos := ⟨1, 1, 0⟩

/-- The fence gate. -/
def gate : Pos := ⟨0, 1, 1⟩

/-- The four blocks that open and close. -/
def doors : List Pos := [doorLower, doorUpper, trapdoor, gate]

/-- The four blocks, each open and powered or neither. -/
def doorBlocks (on : Bool) : List Block :=
  [.door .iron_door ⟨.east, .lower, .left, on, on⟩,
    .door .iron_door ⟨.east, .upper, .left, on, on⟩,
    .trapDoor .iron_trapdoor ⟨.north, .bottom, on, on, false⟩,
    .fenceGate .oak_fence_gate ⟨.north, false, on, on⟩]

/-- A lever on a stone floor with an iron door, an iron trapdoor and a fence gate around it,
all closed. -/
def circuit : Level :=
  .ofCells ([(⟨0, 0, 0⟩, .plain .stone), (⟨-1, 0, 0⟩, .plain .stone), (⟨1, 0, 0⟩, .plain .stone),
    (⟨0, 0, 1⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩)] ++
    doors.zip (doorBlocks false))

/-- The level after the game tick in which the lever is switched on. -/
def opened : Level := rules.stepWith [.use lever .up] circuit

/-- The circuit as built is at rest, with the four blocks closed. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧ circuit.blocksAt doors = doorBlocks false := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **They open at once.** After the game tick in which the lever is switched on, both halves
of the door, the trapdoor and the gate are open and powered, and the level is at rest. -/
theorem opens_at_once :
    (rules.stepWith [.use lever .up] circuit).blocksAt doors = doorBlocks true ∧
      (rules.stepWith [.use lever .up] circuit).Quiescent ∧
      (rules.stepWith [.use lever .up] circuit).overflow = false := by
  circuit_decide

assert_standard_axioms opens_at_once

/-- With the lever on, they stay open for ever. -/
theorem stays_open (n : ℕ) :
    (rules.steps n (rules.stepWith [.use lever .up] circuit)).blocksAt doors = doorBlocks true ∧
      (rules.steps n (rules.stepWith [.use lever .up] circuit)).overflow = false := by
  rw [rules.steps_of_quiescent opens_at_once.2.1]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  exact ⟨opens_at_once.1, opens_at_once.2.2⟩

assert_standard_axioms stays_open

/-- **They close at once.** After the game tick in which the lever is switched off again, the
blocks are those the circuit started with, and the level is at rest. -/
theorem closes_at_once :
    (rules.stepWith [.use lever .up] opened).blocksAt doors = doorBlocks false ∧
      (rules.stepWith [.use lever .up] opened).world = circuit.world ∧
      (rules.stepWith [.use lever .up] opened).Quiescent ∧
      (rules.stepWith [.use lever .up] opened).overflow = false := by
  circuit_decide

assert_standard_axioms closes_at_once

end Redstone.Theorems.PistonDoor.LeverDoors
