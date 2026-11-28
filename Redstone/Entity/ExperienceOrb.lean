module

public import Redstone.Entity.Physics

/-!
# Experience orbs

Java class: `ExperienceOrb`.

This is a stub: the behaviour does nothing. No entity is an
`EntityData.experienceOrb` yet (`Entities.ExperienceOrb.ofNbt?` reads nothing), so the dispatch
arm that leads here is never taken: an experience orb is still an `EntityData.other`, which
`Redstone.Entity.Still` handles.

What belongs here: the orb's motion, its merging with other orbs and its age.
-/

@[expose] public section

namespace Redstone.Entity.ExperienceOrb

/-- The behaviour of the entity: nothing yet. -/
def behaviour : EntityBehaviour := .inert

end Redstone.Entity.ExperienceOrb
