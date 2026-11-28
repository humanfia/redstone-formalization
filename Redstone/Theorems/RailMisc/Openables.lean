import Redstone.Proof.Circuit

/-!
# Door, trapdoor and fence gate on one lever

A lever on a stone block with an iron door to its east, an iron trapdoor to its west and an
oak fence gate to its south. Top view at y = 1 (x to the right, z down); the door is two
blocks high:

```
z = 0:   T  L  D        T iron trapdoor (bottom half, closed)   L lever, on stone
z = 1:      G           D iron door, lower half on stone, upper half at y = 2
x =     -1  0  1        G oak fence gate, on stone
```

All three follow the signal: each stores in `powered` whether it had a signal the last time it
looked, and opens or closes when that changes (`DoorBlock`, `TrapDoorBlock`,
`FenceGateBlock.neighborChanged`). There is no delay: they open in the game tick in which the
lever is switched on and close in the game tick in which it is switched off. Both halves of
the door move together, although only the lower half touches the lever.

| lever | door (both halves) | trapdoor | fence gate |
|---|---|---|---|
| off | closed | closed | closed |
| on | open | open | open |

By hand (the lever is off again): the iron door and the iron trapdoor do not react to a
player; the wooden fence gate opens, without becoming `powered`.

The level is loaded raw with everything closed; `circuit_quiescent` shows that this is a state
of rest. Every opening and closing draws from the level's random generator for the pitch of
its sound; the theorems are about the blocks.

This file does not use `checkpoints`: the command cannot write out a level that has a door, a
trapdoor or a fence gate (their property `open` is printed without the quotes Lean needs to
read it back; see `Overview`). The runs are at most three game ticks long, and each statement
is evaluated by the kernel in one piece.
-/

set_option Elab.async false

namespace Redstone.Theorems.RailMisc.Openables

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The lower half of the door. -/
def doorLower : Pos := ⟨1, 1, 0⟩

/-- The upper half of the door. -/
def doorUpper : Pos := ⟨1, 2, 0⟩

/-- The position of the trapdoor. -/
def trapdoor : Pos := ⟨-1, 1, 0⟩

/-- The position of the fence gate. -/
def gate : Pos := ⟨0, 1, 1⟩

/-- The lever, on or off. -/
def leverState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- A half of the iron door, with `open` and `powered`. -/
def doorState (half : DoubleBlockHalf) («open» powered : Bool) : Block :=
  .door .iron_door { facing := .north, half := half, hinge := .left, «open» := «open»,
                     powered := powered }

/-- The iron trapdoor, with `open` and `powered`. -/
def trapdoorState («open» powered : Bool) : Block :=
  .trapDoor .iron_trapdoor { facing := .north, half := .bottom, «open» := «open»,
                             powered := powered, waterlogged := false }

/-- The oak fence gate, with `open` and `powered`. -/
def gateState («open» powered : Bool) : Block :=
  .fenceGate .oak_fence_gate { facing := .north, in_wall := false, «open» := «open»,
                               powered := powered }

/-- The observed blocks: lever, lower and upper half of the door, trapdoor, gate. -/
def cells : List Pos := [lever, doorLower, doorUpper, trapdoor, gate]

/-- The blocks of `cells` when the lever is `on` and all three follow it. -/
def following (on : Bool) : List Block :=
  [leverState on, doorState .lower on on, doorState .upper on on, trapdoorState on on,
    gateState on on]

/-- The lever with the door, the trapdoor and the gate, all closed. -/
def circuit : Level :=
  .ofCells ([(⟨0, 0, 0⟩, .plain .stone), (⟨1, 0, 0⟩, .plain .stone), (⟨0, 0, 1⟩, .plain .stone)] ++
    cells.zip (following false))

/-- The lever is switched on before the first game tick. -/
def switchOn : Schedule := .first [.use lever .up] 1

/-- The lever is switched on before game tick 1 and off again before game tick 3; three game
ticks. -/
def onAndOff : Schedule := .first [.use lever .up] 2 ++ .first [.use lever .up] 1

/-- A player uses the door, the trapdoor and the gate before the first game tick. -/
def byHand : Schedule := .first [.use doorLower .south, .use trapdoor .up, .use gate .south] 1

/-- With the lever off and everything closed the level is at rest. -/
theorem circuit_quiescent : circuit.Quiescent ∧ circuit.blocksAt cells = following false := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Lever on: all three open at once**, in the game tick in which the lever is used, both
halves of the door included; and they stay open for ever. -/
theorem on_opens (n : ℕ) :
    (rules.runSchedule switchOn circuit).blocksAt cells = following true ∧
      (rules.steps n (rules.runSchedule switchOn circuit)).blocksAt cells = following true ∧
      (rules.steps n (rules.runSchedule switchOn circuit)).overflow = false := by
  rw [rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms on_opens

/-- **Lever off: all three close at once**, in the game tick in which the lever is used (game
tick 3); the blocks are those the level started with, and they stay closed for ever. -/
theorem off_closes (n : ℕ) :
    (rules.runSchedule onAndOff circuit).blocksAt cells = following false ∧
      (rules.runSchedule onAndOff circuit).world = circuit.world ∧
      (rules.steps n (rules.runSchedule onAndOff circuit)).blocksAt cells = following false ∧
      (rules.steps n (rules.runSchedule onAndOff circuit)).overflow = false := by
  rw [rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms off_closes

/-- **By hand: iron stays shut, the wooden gate opens.** With the lever off, a player uses the
door, the trapdoor and the gate. The iron door and the iron trapdoor are as they were; the
fence gate is open and not `powered`. -/
theorem by_hand :
    (rules.runSchedule byHand circuit).blocksAt cells =
        [leverState false, doorState .lower false false, doorState .upper false false,
          trapdoorState false false, gateState true false] ∧
      (rules.runSchedule byHand circuit).overflow = false := by
  circuit_decide

assert_standard_axioms by_hand

end Redstone.Theorems.RailMisc.Openables
