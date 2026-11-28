import Redstone.Mechanics.Dispatch
import Redstone.Mechanics.Input
import Redstone.Proof.Axioms

/-!
# Smoke test of the proof method

Four small circuits, each proved by letting the Lean kernel run the model (`decide +kernel`):
the statement is a decidable fact about the level after some inputs and game ticks, and the
kernel evaluates `Level.tick` on a concrete level to check it. Nothing is trusted but the
kernel: the check at the end of each theorem fails the build if the proof depends on anything
besides the three standard axioms.

This file is a regression guard for the model. Kernel evaluation only works while everything
on the path it takes can be reduced by the kernel in reasonable time: no `Float`, no opaque or
well-founded definitions, no string processing on the path of a block. A change to the model
that puts such a thing on the path of a lever, a lamp, a piston or a hopper makes this file
fail or slow down, long before the theorems about real contraptions do. The whole file is
meant to build in well under three minutes; if a change makes it slower, the change has made
every proof slower.

The measurements behind the method, and its limits, are in `docs/proof-feasibility.md`.

The levels are loaded raw, as the test harness loads a scenario: the blocks are put in place
without any reaction, and each theorem says what happens from there.
-/

/- Lean elaborates the theorems of a file on several threads at once by default. Kernel
evaluation is many times slower when several evaluations run side by side (measured: 80 s
instead of 2 s for four ticks of a piston), so the theorems of this file are checked one after
the other. Every file that proves things with `decide +kernel` should set this option. -/
set_option Elab.async false

namespace Redstone.Proof.Smoke

/-- The level with the given blocks and nothing else, at game time zero. -/
def level (cells : List (Pos × Block)) : Level :=
  let world := World.ofList cells
  { Level.empty with world, lightWorld := world }

/-- The level after the inputs of a schedule, under the rules of the game. -/
def run (s : Schedule) (l : Level) : Level := rules.runSchedule s l

/-! ### A lever lights a lamp -/

/-- A lever on a stone block, with a redstone lamp next to it. -/
def leverLamp : Level :=
  level [(⟨0, 0, 0⟩, .plain .stone), (⟨0, 1, 0⟩, .lever ⟨.floor, .north, false⟩),
    (⟨1, 1, 0⟩, .redstoneLamp ⟨false⟩)]

/-- The level after the lever is used and one game tick has run. -/
def leverLampOn : Level := run [[.use ⟨0, 1, 0⟩ .up]] leverLamp

/-- Using the lever switches it on and lights the lamp, in the same game tick. -/
theorem lever_lights_lamp :
    leverLampOn.blockAt ⟨0, 1, 0⟩ = .lever ⟨.floor, .north, true⟩ ∧
      leverLampOn.blockAt ⟨1, 1, 0⟩ = .redstoneLamp ⟨true⟩ ∧ leverLampOn.overflow = false := by
  decide +kernel

assert_standard_axioms lever_lights_lamp

/-! ### A lever loses its support -/

/-- A lever on a stone block. -/
def leverOnStone : Level :=
  level [(⟨0, 0, 0⟩, .plain .stone), (⟨0, 1, 0⟩, .lever ⟨.floor, .north, false⟩)]

/-- The level after the stone block is destroyed and one game tick has run. -/
def leverPopped : Level := run [[.destroy ⟨0, 0, 0⟩]] leverOnStone

/-- When the block under a lever is destroyed, the lever breaks: its cell is air after the
tick. Breaking it draws from the level's random number generator, for the item that would
drop. -/
theorem lever_pops_off :
    leverPopped.blockAt ⟨0, 0, 0⟩ = .AIR ∧ leverPopped.blockAt ⟨0, 1, 0⟩ = .AIR ∧
      leverPopped.overflow = false ∧ leverPopped.random ≠ leverOnStone.random := by
  decide +kernel

assert_standard_axioms lever_pops_off

/-! ### A sticky piston pushes a block -/

/-- A sticky piston facing east with a stone block in front of it, and behind it a stone block
with a lever on top. -/
def stickyPiston : Level :=
  level [(⟨-1, 1, 0⟩, .plain .stone), (⟨-1, 2, 0⟩, .lever ⟨.floor, .north, false⟩),
    (⟨0, 1, 0⟩, .pistonBase .sticky_piston ⟨false, .east⟩), (⟨1, 1, 0⟩, .plain .stone)]

/-- The level after the lever is used and three game ticks have run. -/
def stickyPistonOut : Level := run (.first [.use ⟨-1, 2, 0⟩ .up] 3) stickyPiston

/-- The lever powers the block behind the piston. Three game ticks later the piston is
extended, its head is where the stone block was, and the stone block is one cell further
east; nothing is left moving. -/
theorem sticky_piston_extends :
    stickyPistonOut.blockAt ⟨0, 1, 0⟩ = .pistonBase .sticky_piston ⟨true, .east⟩ ∧
      stickyPistonOut.blockAt ⟨1, 1, 0⟩ = .pistonHead ⟨.east, false, .sticky⟩ ∧
      stickyPistonOut.blockAt ⟨2, 1, 0⟩ = .plain .stone ∧
      stickyPistonOut.blockEntityTickers = [] ∧ stickyPistonOut.blockEvents = [] ∧
      stickyPistonOut.overflow = false := by
  decide +kernel

assert_standard_axioms sticky_piston_extends

/-! ### An item moves between two hoppers -/

/-- The number of items in the hopper at `p`. -/
def hopperCount (l : Level) (p : Pos) : ℕ :=
  match l.blockEntities p with
  | some (.hopper d) => (d.items.map (·.count)).sum
  | _ => 0

/-- Two hoppers, one on top of the other, both pointing down. The upper one holds one piece of
redstone. -/
def hopperPair : Level :=
  let l := level [(⟨0, 2, 0⟩, .hopper ⟨true, .down⟩), (⟨0, 1, 0⟩, .hopper ⟨true, .down⟩)]
  let upper : BlockEntity :=
    .hopper { items := (Inventory.empty 5).setItem 0 (.of "minecraft:redstone") }
  { l with
    blockEntities := PosMap.ofList [(⟨0, 2, 0⟩, upper), (⟨0, 1, 0⟩, .hopper {})]
    blockEntityTickers := [⟨0, 2, 0⟩, ⟨0, 1, 0⟩] }

/-- The level after one game tick. -/
def hopperPairMoved : Level := run (.idle 1) hopperPair

/-- After one game tick the piece of redstone is in the lower hopper. -/
theorem hopper_moves_item :
    hopperCount hopperPair ⟨0, 2, 0⟩ = 1 ∧ hopperCount hopperPair ⟨0, 1, 0⟩ = 0 ∧
      hopperCount hopperPairMoved ⟨0, 2, 0⟩ = 0 ∧ hopperCount hopperPairMoved ⟨0, 1, 0⟩ = 1 ∧
      hopperPairMoved.overflow = false := by
  decide +kernel

assert_standard_axioms hopper_moves_item

end Redstone.Proof.Smoke
