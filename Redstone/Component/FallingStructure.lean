module

public import Redstone.Mechanics.Tick

/-!
# Structures that fall apart

Java classes: `ScaffoldingBlock`, `PointedDripstoneBlock`, `SulfurSpikeBlock`,
`BrushableBlock`.

This is a stub: the blocks of these classes are registered with this component
(`tools/gen/components.json`), and their behaviour is still `Behaviour.inert`, exactly as before
they were registered.

What belongs here: the distance ticks of scaffolding and its fall, the thickness of pointed
dripstone and the fall of a stalactite, the fall of suspicious sand and gravel.
-/

@[expose] public section

namespace Redstone.Component.FallingStructure

/-- The behaviour of the blocks of this component: nothing yet. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.FallingStructure
