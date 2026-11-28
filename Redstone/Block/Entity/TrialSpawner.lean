module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:trial_spawner`

The data that the model keeps of the block entity `TrialSpawnerBlockEntity`: whether the
spawner has been given anything to spawn.

A trial spawner as it is placed has the default configuration, whose list of mobs is empty, and
no spawn data. Such a spawner stays `inactive` for ever (`TrialSpawnerState.tickAndGetNext`),
and that is all the model follows (`Redstone.Component.Ground.trialSpawner`). A spawner with a
configuration (`normal_config`, `ominous_config`) or with spawn data that names an entity
(`spawn_data.entity.id`) wakes up, looks for players and spawns mobs. The first tick of an
inactive spawner without a mob writes spawn data with an empty entity, which is why the entity
id is what is looked at.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:trial_spawner` block entity. -/
structure TrialSpawner where
  /-- The saved data has a configuration or names an entity to spawn. -/
  hasSpawnData : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace TrialSpawner

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (nbt : Nbt) : Option TrialSpawner :=
  let entityId := ((nbt.get? "spawn_data").bind (·.get? "entity")).bind (·.get? "id")
  some { hasSpawnData :=
    entityId.isSome || (nbt.get? "normal_config").isSome || (nbt.get? "ominous_config").isSome }

end TrialSpawner

end Redstone.BlockEntities
