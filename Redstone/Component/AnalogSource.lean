module

public import Redstone.Mechanics.Tick

/-!
# Other blocks a comparator reads

Java classes: `LecternBlock`, `JukeboxBlock`, `CakeBlock`, `CandleCakeBlock`,
`AbstractCauldronBlock`, `ComposterBlock`, `EndPortalFrameBlock`, `BeehiveBlock`,
`ChiseledBookShelfBlock`, `DecoratedPotBlock`, `RespawnAnchorBlock`, `CopperGolemStatueBlock`,
`CreakingHeartBlock`, `ShelfBlock`.

To be formalized: lecterns, jukeboxes, cakes, cauldrons, composters, end portal frames, beehives,
chiseled bookshelves, decorated pots, respawn anchors, copper golem statues, creaking hearts and
shelves.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.AnalogSource

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.AnalogSource
