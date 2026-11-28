module

public import Redstone.Entity.Physics

/-!
# Lightning bolts

Java class: `LightningBolt`.

This is a stub: the behaviour does nothing. No entity is an `EntityData.lightning` yet
(`Entities.Lightning.ofNbt?` reads nothing), so the dispatch arm that leads here is never taken:
a lightning bolt is still an `EntityData.other`, which `Redstone.Entity.Still` handles.

What belongs here: the bolt's life (`life`, `flashes`, drawn from the bolt's own random source,
`Level.createRandomSource`), the strike of a lightning rod (`Component.Sensor.strike`), the
cleaning of copper (`Block.Weathering`) and the fire it lights.
-/

@[expose] public section

namespace Redstone.Entity.Lightning

/-- The behaviour of the entity: nothing yet. -/
def behaviour : EntityBehaviour := .inert

end Redstone.Entity.Lightning
