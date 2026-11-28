module

public import Redstone.Mechanics.Tick

/-!
# Fire

Java classes: `BaseFireBlock` (`FireBlock`, `SoulFireBlock`).

This is a stub: the blocks of these classes are registered with this component
(`tools/gen/components.json`), and their behaviour is still `Behaviour.inert`, exactly as before
they were registered.

What belongs here: the scheduled tick through which fire spreads and burns out, and what it
does to the blocks next to it (TNT).
-/

@[expose] public section

namespace Redstone.Component.Fire

/-- The behaviour of the blocks of this component: nothing yet. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Fire
