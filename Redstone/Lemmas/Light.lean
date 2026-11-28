import Redstone.World.Light
import Redstone.Proof.Axioms

/-!
# Light, evaluated by the kernel

A few facts about the light of small worlds, each proved by letting the Lean kernel run
`Redstone.Light` (`decide +kernel`). They say what the definitions give in the plainest cases,
and they guard the way theorems about circuits are proved: light must stay something the kernel
can evaluate, and the brightness of a cell that the sky does not reach must not depend on the
`float` arithmetic of the time of day.
-/

set_option Elab.async false

namespace Redstone.Lemmas.Light

open Redstone

/-- Stone. -/
def stone : Block := .plain .stone

/-! ### Block light -/

/-- A torch on a block of stone, and nothing else. -/
def torchWorld : World := World.ofList [(⟨0, 0, 0⟩, stone), (⟨0, 1, 0⟩, Block.default .torch)]

/-- A torch has block light 14. A cell `n` steps away has `14 - n`, the stone below the torch
has none, and neither has a cell that is 14 steps away. -/
theorem torch_blockLight :
    Light.blockLight torchWorld ⟨0, 1, 0⟩ = 14 ∧ Light.blockLight torchWorld ⟨3, 1, 0⟩ = 11 ∧
      Light.blockLight torchWorld ⟨2, 3, -1⟩ = 9 ∧ Light.blockLight torchWorld ⟨0, 0, 0⟩ = 0 ∧
      Light.blockLight torchWorld ⟨7, 8, 0⟩ = 0 := by
  decide +kernel

assert_standard_axioms torch_blockLight

/-- A lit redstone lamp with a wall of stone two cells to its east, three cells wide and
high. -/
def lampWorld : World :=
  World.ofList ((⟨0, 0, 0⟩, .redstoneLamp ⟨true⟩) ::
    ([-1, 0, 1].flatMap fun y => [-1, 0, 1].map fun z => ((⟨2, y, z⟩ : Pos), stone)))

/-- A lit lamp has block light 15 and lights the cell next to it with 14. Behind the wall the
light has gone around it: the cell behind the middle of the wall is 7 steps from the lamp, not
3. -/
theorem lamp_blockLight :
    Light.blockLight lampWorld ⟨0, 0, 0⟩ = 15 ∧ Light.blockLight lampWorld ⟨1, 0, 0⟩ = 14 ∧
      Light.blockLight lampWorld ⟨2, 0, 0⟩ = 0 ∧ Light.blockLight lampWorld ⟨3, 0, 0⟩ = 8 := by
  decide +kernel

assert_standard_axioms lamp_blockLight

/-! ### Sky light -/

/-- A pit: the cell at the origin has stone below it and on its four sides, and the cell above
it, which holds `roof`, has stone on its four sides. -/
def pit (roof : Block) : World :=
  World.ofList [(⟨0, -1, 0⟩, stone), (⟨1, 0, 0⟩, stone), (⟨-1, 0, 0⟩, stone), (⟨0, 0, 1⟩, stone),
    (⟨0, 0, -1⟩, stone), (⟨1, 1, 0⟩, stone), (⟨-1, 1, 0⟩, stone), (⟨0, 1, 1⟩, stone),
    (⟨0, 1, -1⟩, stone), (⟨0, 1, 0⟩, roof)]

/-- The sky light at the bottom of the pit: 15 when the pit is open or roofed with glass, 13
under leaves or water, which take one level and stop the light from going straight down, and
none under tinted glass or stone. -/
theorem pit_skyLight :
    Light.skyLight (pit .AIR) ⟨0, 0, 0⟩ = 15 ∧ Light.skyLight (pit (.plain .glass)) ⟨0, 0, 0⟩ = 15 ∧
      Light.skyLight (pit (Block.default .oak_leaves)) ⟨0, 0, 0⟩ = 13 ∧
      Light.skyLight (pit (Block.default .water)) ⟨0, 0, 0⟩ = 13 ∧
      Light.skyLight (pit (Block.default .tinted_glass)) ⟨0, 0, 0⟩ = 0 ∧
      Light.skyLight (pit stone) ⟨0, 0, 0⟩ = 0 := by
  decide +kernel

assert_standard_axioms pit_skyLight

/-- A slab closes the pit whichever half it is: the top of a top slab and the bottom of a bottom
slab are full faces, and light does not pass a full face. -/
theorem pit_slab_skyLight :
    Light.skyLight (pit (.slab .oak_slab ⟨.top, false⟩)) ⟨0, 0, 0⟩ = 0 ∧
      Light.skyLight (pit (.slab .oak_slab ⟨.bottom, false⟩)) ⟨0, 0, 0⟩ = 0 ∧
      Light.skyLight (pit (.slab .oak_slab ⟨.bottom, false⟩)) ⟨0, 1, 0⟩ = 15 ∧
      Light.skyLight (pit (.slab .oak_slab ⟨.top, false⟩)) ⟨0, 1, 0⟩ = 0 := by
  decide +kernel

assert_standard_axioms pit_slab_skyLight

/-! ### Brightness -/

/-- The level with the given blocks, as the light engine sees them, at midnight. -/
def level (cells : List (Pos × Block)) : Level :=
  let world := World.ofList cells
  { Level.empty with world, lightWorld := world, dayTime := 18000 }

/-- Two cells closed in by stone, with a torch in the western one. -/
def closedRoom : Level :=
  level [(⟨0, 0, 0⟩, Block.default .torch), (⟨-1, 0, 0⟩, stone), (⟨2, 0, 0⟩, stone),
    (⟨0, -1, 0⟩, stone), (⟨0, 1, 0⟩, stone), (⟨0, 0, -1⟩, stone), (⟨0, 0, 1⟩, stone),
    (⟨1, -1, 0⟩, stone), (⟨1, 1, 0⟩, stone), (⟨1, 0, -1⟩, stone), (⟨1, 0, 1⟩, stone)]

/-- Where the sky does not reach, the brightness of a cell is its block light, and finding it
takes no arithmetic on `float`s: the darkening of the sky is not looked at. -/
theorem closedRoom_brightness :
    closedRoom.maxLocalRawBrightness ⟨1, 0, 0⟩ = 13 ∧ closedRoom.skyLight ⟨1, 0, 0⟩ = 0 ∧
      closedRoom.maxLocalRawBrightness ⟨2, 0, 0⟩ = 0 := by
  decide +kernel

assert_standard_axioms closedRoom_brightness

end Redstone.Lemmas.Light
