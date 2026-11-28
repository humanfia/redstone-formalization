module

public import Redstone.World.Level

/-!
# Light

Java classes: `LevelLightEngine`, `BlockAndLightGetter`, `LevelReader`.

This is a stub: every cell is as bright as can be, 15. That is what the model has assumed so
far wherever the game asks for the light of a cell and the model did not ask (the plants and
mushrooms that need or shun light never break for lack or excess of it, ice and snow never
melt): none of those places calls these definitions yet, so nothing changes by them.

They are here so that a block whose behaviour depends on light can be written against the
game's own questions now, and gets the right answers once light is modelled, without its file
being edited again.

What belongs here: block light (the light that blocks emit, spread through the cells that let
it pass, `BlockLightEngine`), sky light, which `Redstone.Component.Sensor.Light` computes for
the daylight detector from `Level.lightWorld`, and the dampening and face occlusion of blocks.
Light is to be computed where it is asked for, not maintained by `setBlock`.
-/

@[expose] public section

namespace Redstone

namespace Level

/-- `getBrightness(LightLayer.BLOCK, pos)`: the block light of the cell `p`. A stub: 15. -/
def blockLight (_l : Level) (_p : Pos) : ℕ := 15

/-- `BlockAndLightGetter.getRawBrightness(pos, darkening)`: the larger of the block light of the
cell `p` and its sky light less `skyDarken`. A stub: 15. -/
def rawBrightness (_l : Level) (_p : Pos) (_skyDarken : ℕ := 0) : ℕ := 15

/-- `LevelReader.getMaxLocalRawBrightness(pos)`: `rawBrightness` with the darkening of the sky
at this time and in this weather (`Level.getSkyDarken`). A stub: 15. -/
def maxLocalRawBrightness (_l : Level) (_p : Pos) : ℕ := 15

end Level

end Redstone
