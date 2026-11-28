import Redstone.Theorems.PistonDoor.Door3x3

/-!
# The smallest 3×3 piston door

The goal this repository started from: determine the least volume of a working 3×3 piston
door, by exhibiting a door of that volume and proving that no smaller one exists.

What a working door is, and what its volume is, is defined in
`Redstone/Contraption/PistonDoor.lean` (`Contraption.PistonDoor.IsPistonDoor`,
`Contraption.PistonDoor.volume`, `Contraption.minVolume`).

**What is proved** is the first half, for one door: `Redstone/Theorems/PistonDoor/Door3x3.lean`
has a concrete level that is a working 3 by 3 door, proved game tick by game tick on the full
tick semantics, and the cells it ever occupies fill a box of 462 blocks. So

* `exists_door`: there is a working 3 by 3 door of volume 462, and
* `minVolume_le`: the least volume of a working 3 by 3 door is at most 462.

**What is not proved** is everything else about the minimum:

* 462 is the volume of a door laid out to be cheap for the kernel to check, with repeaters
  for every delay. It makes no attempt to be small, and the doors the community builds for
  size are many times smaller. Proving one of those correct is the same work as here, on a
  different level; none is proved.
* A lower bound, that no working 3 by 3 door has a volume below some number, is a statement
  about every level and every schedule of its mechanism. Evaluation proves facts about one
  level; it gives no such bound, and no other argument is formalized. So the least volume is
  not determined, and `minVolume 3 3 ≤ 462` is all that is known here.
-/

namespace Redstone.Theorems.PistonDoor3x3

open Contraption

/-- There is a working 3 by 3 piston door whose volume is 462. -/
theorem exists_door : ∃ d : PistonDoor, d.IsPistonDoor 3 3 ∧ d.volume = 462 :=
  ⟨_, PistonDoor.Door3x3.isPistonDoor, PistonDoor.Door3x3.volume⟩

assert_standard_axioms exists_door

/-- The least volume of a working 3 by 3 piston door is at most 462. -/
theorem minVolume_le : minVolume 3 3 ≤ 462 := PistonDoor.Door3x3.minVolume_le

assert_standard_axioms minVolume_le

end Redstone.Theorems.PistonDoor3x3
