import Redstone.Proof.Circuit

/-!
# What the analog circuits share

The circuits of `Redstone/Theorems/Analog` are built on a stone floor at `y = 0`, with the
components at `y = 1`. This file has the floor, the two straight pieces of redstone dust, and
the observation of a comparator.

A comparator is observed by its `powered` property together with the output stored in its
block entity (`comparator`): `(true, 11)` is a comparator that emits 11 at its front;
`emitted` is that strength alone, 0 for a comparator that is off. Most
circuits also have one piece of redstone dust in front of the comparator, whose power is the
signal the comparator gives to the world.

Coordinates: east is `+x`, up `+y`, south `+z`. The `facing` of a comparator points from the
comparator to the block it reads, as in the game; a comparator `facing = west` reads the block
to its west and emits to the east.
-/

namespace Redstone.Theorems.Analog

/-- A stone floor at `y = 0` under the given columns. -/
def floor (xs zs : List ℤ) : List (Pos × Block) :=
  xs.flatMap fun x => zs.map fun z => (⟨x, 0, z⟩, Block.plain .stone)

/-- Redstone dust without power that runs east and west. -/
def wireEW : Block := .redstoneWire ⟨.side, .none, 0, .none, .side⟩

/-- Redstone dust without power that runs north and south. -/
def wireNS : Block := .redstoneWire ⟨.none, .side, 0, .side, .none⟩

/-- The comparator at `p`: whether it is powered, and the output stored in its block entity.
`(false, 0)` if there is no comparator at `p`. -/
def comparator (l : Level) (p : Pos) : Bool × ℕ :=
  match l.blockAt p, l.blockEntities p with
  | .comparator s, some (.comparator d) => (s.powered, d.output)
  | _, _ => (false, 0)

/-- Moving the clock on does not change what a comparator shows. -/
theorem comparator_advance (l : Level) (n : ℕ) : comparator (l.advance n) = comparator l := rfl

assert_standard_axioms comparator_advance

/-- What the comparator at `p` emits at its front: the stored output while it is powered, and 0
while it is not. -/
def emitted (l : Level) (p : Pos) : ℕ :=
  match comparator l p with
  | (true, n) => n
  | _ => 0

/-- Moving the clock on does not change what a comparator emits. -/
theorem emitted_advance (l : Level) (n : ℕ) : emitted (l.advance n) = emitted l := rfl

assert_standard_axioms emitted_advance

end Redstone.Theorems.Analog
