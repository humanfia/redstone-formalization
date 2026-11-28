import Redstone.Proof.Circuit
-- Heavy chain: imported only so that the memory-heavy files of the repository are checked one
-- after the other; see "What it costs" in `Redstone/Proof/README.md`.
import Redstone.Theorems.Basics.RepeaterClock

/-!
# The two-torch RS latch

Two stone blocks `A` and `B`, each with a redstone torch on its side, cross-coupled through
redstone dust: the torch on `A` feeds a line of dust that runs into `B`, and the torch on `B`
feeds a piece of dust that runs into `A`. So each torch is lit exactly when the other one is
not, and the circuit has two states of rest. A lever on top of each block is an input: powering
`A` (*set*) puts out the torch on `A` and so lights the torch on `B`; powering `B` (*reset*)
does the opposite. The output is the torch on `B`.

```
z = -2:  w  w  w  w        w: redstone dust      y = 1, seen from above, x to the right
z = -1:  T1 .  .  w        T1: torch on the north side of A
z =  0:  A  d  T2 B        T2: torch on the west side of B, d: dust between T2 and A
```

What is proved: both states are states of rest and hold for ever (*hold*); a set pulse of four
game ticks moves the latch from the first to the second and it stays there after the lever is
released; a reset pulse moves it back, to the very blocks it started with. The switch takes
four game ticks, two for each torch.

The level is loaded raw, in the state in which the torch on `A` is lit: the blocks are those
the model itself settles in when the circuit is built block by block.
-/

set_option Elab.async false

namespace Redstone.Theorems.Basics.RSLatch

/-- The lever on top of the block `A`: the *set* input. -/
def setLever : Pos := ⟨0, 2, 0⟩

/-- The lever on top of the block `B`: the *reset* input. -/
def resetLever : Pos := ⟨3, 2, 0⟩

/-- The torch on the block `A`. It is lit in the *reset* state. -/
def torchA : Pos := ⟨0, 1, -1⟩

/-- The torch on the block `B`: the output. It is lit in the *set* state. -/
def torchB : Pos := ⟨2, 1, 0⟩

/-- The stone floor under the circuit. -/
def floor : List (Pos × Block) :=
  (List.range 4).flatMap fun x =>
    (List.range 3).map fun z => (⟨x, 0, (z : ℤ) - 2⟩, Block.plain .stone)

/-- The latch in its *reset* state: the torch on `A` is lit and powers the dust that runs into
`B`, so the torch on `B` is out. -/
def circuit : Level :=
  .ofCells (floor ++ [
    (⟨0, 1, 0⟩, .plain .stone), (⟨3, 1, 0⟩, .plain .stone),
    (setLever, .lever ⟨.floor, .north, false⟩), (resetLever, .lever ⟨.floor, .north, false⟩),
    (torchA, .redstoneWallTorch ⟨.north, true⟩), (torchB, .redstoneWallTorch ⟨.west, false⟩),
    (⟨1, 1, 0⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]"),
    (⟨0, 1, -2⟩,
      blk% "minecraft:redstone_wire[east=side,north=none,power=15,south=side,west=none]"),
    (⟨1, 1, -2⟩,
      blk% "minecraft:redstone_wire[east=side,north=none,power=14,south=none,west=side]"),
    (⟨2, 1, -2⟩,
      blk% "minecraft:redstone_wire[east=side,north=none,power=13,south=none,west=side]"),
    (⟨3, 1, -2⟩,
      blk% "minecraft:redstone_wire[east=none,north=none,power=12,south=side,west=side]"),
    (⟨3, 1, -1⟩,
      blk% "minecraft:redstone_wire[east=none,north=side,power=11,south=side,west=none]")])

/-- A set pulse (the set lever on before game tick 1, off before game tick 5), four game ticks
of rest, then a reset pulse (the reset lever on before game tick 9, off before game tick 13)
and four game ticks of rest. -/
def schedule : Schedule :=
  .first [.use setLever .up] 4 ++ .first [.use setLever .up] 4 ++
    .first [.use resetLever .up] 4 ++ .first [.use resetLever .up] 4

checkpoints state := schedule from circuit

/-- Which torches are lit: the one on `A`, the one on `B`. -/
def torches (l : Level) : Block × Block := (l.blockAt torchA, l.blockAt torchB)

/-- The *reset* state: the torch on `A` is lit, the output is off. -/
def isReset : Block × Block :=
  (.redstoneWallTorch ⟨.north, true⟩, .redstoneWallTorch ⟨.west, false⟩)

/-- The *set* state: the torch on `A` is out, the output is on. -/
def isSet : Block × Block :=
  (.redstoneWallTorch ⟨.north, false⟩, .redstoneWallTorch ⟨.west, true⟩)

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Hold, reset state.** With both levers off the latch stays in the reset state for
ever. -/
theorem holds_reset (n : ℕ) :
    torches (rules.steps n circuit) = isReset ∧ (rules.steps n circuit).overflow = false := by
  rw [rules.steps_of_quiescent circuit_quiescent]
  simp only [torches, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms holds_reset

/-- **Set.** The set lever is switched on before game tick 1. After game tick 2 the torch on
`A` is out and the output is not on yet; after game tick 4, four game ticks after the lever,
the output is on. -/
theorem set :
    torches (rules.runSchedule (schedule.take 1) circuit) = isReset ∧
      torches (rules.runSchedule (schedule.take 2) circuit) =
        (.redstoneWallTorch ⟨.north, false⟩, .redstoneWallTorch ⟨.west, false⟩) ∧
      torches (rules.runSchedule (schedule.take 3) circuit) =
        (.redstoneWallTorch ⟨.north, false⟩, .redstoneWallTorch ⟨.west, false⟩) ∧
      torches (rules.runSchedule (schedule.take 4) circuit) = isSet ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4]
  circuit_decide

assert_standard_axioms set

/-- **Hold, set state.** The set lever is switched off again before game tick 5. The latch is
then at rest in the set state, with both levers off, and stays in it for ever. -/
theorem holds_set (n : ℕ) :
    (rules.runSchedule (schedule.take 5) circuit).blocksAt [setLever, resetLever] =
        [.lever ⟨.floor, .north, false⟩, .lever ⟨.floor, .north, false⟩] ∧
      torches (rules.steps n (rules.runSchedule (schedule.take 5) circuit)) = isSet ∧
      (rules.steps n (rules.runSchedule (schedule.take 5) circuit)).overflow = false := by
  rw [state_run_5, rules.steps_of_quiescent (by circuit_decide)]
  simp only [torches, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms holds_set

/-- **Reset.** The reset lever is switched on before game tick 9. After game tick 10 the
output is off; after game tick 12 the torch on `A` is lit again. -/
theorem reset :
    torches (rules.runSchedule (schedule.take 8) circuit) = isSet ∧
      torches (rules.runSchedule (schedule.take 9) circuit) = isSet ∧
      torches (rules.runSchedule (schedule.take 10) circuit) =
        (.redstoneWallTorch ⟨.north, false⟩, .redstoneWallTorch ⟨.west, false⟩) ∧
      torches (rules.runSchedule (schedule.take 12) circuit) = isReset ∧
      (rules.runSchedule (schedule.take 12) circuit).overflow = false := by
  rw [state_run_8, state_run_9, state_run_10, state_run_12]
  circuit_decide

assert_standard_axioms reset

/-- **Back to the start.** After the reset lever is switched off again (before game tick 13)
the blocks are exactly those the circuit started with, the level is at rest, and the latch
stays in the reset state for ever. -/
theorem back_to_start (n : ℕ) :
    (rules.runSchedule (schedule.take 13) circuit).world = circuit.world ∧
      torches (rules.steps n (rules.runSchedule (schedule.take 13) circuit)) = isReset ∧
      (rules.steps n (rules.runSchedule (schedule.take 13) circuit)).overflow = false := by
  rw [state_run_13, rules.steps_of_quiescent (by circuit_decide)]
  simp only [torches, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Basics.RSLatch
