module

public import Redstone.Entity.Physics

/-!
# Item frames

Java class: `ItemFrame`, `GlowItemFrame` (with `HangingEntity`).

This is a stub: the behaviour does nothing. No entity is an
`EntityData.itemFrame` yet (`Entities.ItemFrame.ofNbt?` reads nothing), so the dispatch arm that
leads here is never taken: an item frame is still an `EntityData.other`, which
`Redstone.Entity.Still` handles.

What belongs here: the frame's survival check (`HangingEntity.survives`), and the item and its
rotation, which a comparator behind the frame reads (`ItemFrame.getAnalogOutput`).
-/

@[expose] public section

namespace Redstone.Entity.Hanging

/-- The behaviour of the entity: nothing yet. -/
def behaviour : EntityBehaviour := .inert

end Redstone.Entity.Hanging
