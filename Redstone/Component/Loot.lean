module

public import Redstone.Mechanics.Tick

/-!
# Blocks that drop more than themselves

Java classes: `DropExperienceBlock`, `InfestedBlock`, `SpawnerBlock`.

This is a stub: the blocks of these classes are registered with this component
(`tools/gen/components.json`), and their behaviour is still `Behaviour.inert`, exactly as before
they were registered.

What belongs here: `spawnAfterBreak` (experience, silverfish), together with the loot of
every block, which `Level.getDrops` is the place for.
-/

@[expose] public section

namespace Redstone.Component.Loot

/-- The behaviour of the blocks of this component: nothing yet. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Loot
