module

public import Redstone.Mechanics.Tick

/-!
# Blocks that only change on random ticks

Java classes: `WeatheringCopperFullBlock`, `IceBlock`, `BuddingAmethystBlock`.

This is a stub: the blocks of these classes are registered with this component
(`tools/gen/components.json`), and their behaviour is still `Behaviour.inert`, exactly as before
they were registered.

What belongs here: the `randomTick` of each (copper weathering through
`Block.Weathering.next?`, ice melting, amethyst buds growing). The random-tick engine is
`Redstone.Mechanics.RandomTick`.
-/

@[expose] public section

namespace Redstone.Component.RandomTicked

/-- The behaviour of the blocks of this component: nothing yet. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.RandomTicked
