module

public import Redstone.Mechanics.Tick

/-!
# Decorations that hang on another block

Java classes: `LadderBlock`, `LanternBlock`, `SignBlock`, `CeilingHangingSignBlock`,
`WallHangingSignBlock`, `AbstractBannerBlock`, `FlowerPotBlock`, `CandleBlock`,
`AmethystClusterBlock`, `CocoaBlock`, `HangingRootsBlock`, `SporeBlossomBlock`,
`HangingMossBlock`, `MossyCarpetBlock`, `EndRodBlock`, `GrindstoneBlock`, `ShelfMushroomBlock`.

This is a stub: the blocks of these classes are registered with this component
(`tools/gen/components.json`), and their behaviour is still `Behaviour.inert`, exactly as before
they were registered.

What belongs here: `canSurvive` and `updateShape` of each (the block breaks when what it
hangs on goes away), and the candle's interactions.
-/

@[expose] public section

namespace Redstone.Component.Attached

/-- The behaviour of the blocks of this component: nothing yet. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Attached
