module

public import Redstone.Entity.Data.Item
public import Redstone.Entity.Data.FallingBlock
public import Redstone.Entity.Data.Tnt
public import Redstone.Entity.Data.Minecart
public import Redstone.Entity.Data.Projectile

/-!
# Entities

The entities that take part in redstone: dropped items, falling blocks, primed TNT, minecarts
and projectiles. Every other entity (players, mobs, ...) is kept as `other`: it has a position
and can be detected, but the model does not move it.
-/

@[expose] public section

namespace Redstone

/-- The kinds of minecart, by entity type. -/
inductive MinecartKind
  | minecart
  | chest
  | furnace
  | tnt
  | hopper
  | spawner
  | commandBlock
  deriving DecidableEq, Repr

/-- The registry name of the entity type. -/
def MinecartKind.typeName : MinecartKind → String
  | .minecart => "minecraft:minecart"
  | .chest => "minecraft:chest_minecart"
  | .furnace => "minecraft:furnace_minecart"
  | .tnt => "minecraft:tnt_minecart"
  | .hopper => "minecraft:hopper_minecart"
  | .spawner => "minecraft:spawner_minecart"
  | .commandBlock => "minecraft:command_block_minecart"

/-- What the model keeps of an entity it does not move, besides its type: the flags that decide
whether and how it touches blocks. -/
structure Entities.Other where
  /-- `Entity.isNoGravity()` (`NoGravity`). -/
  noGravity : Bool := false
  /-- `ArmorStand.isMarker()` (`Marker`). -/
  marker : Bool := false
  /-- `ArmorStand.isSmall()` (`Small`). -/
  small : Bool := false
  deriving Repr, Inhabited

/-- The flags are not compared with the server: the model reads them once and never changes
them, while the game does change some (a vex gives itself `NoGravity`). -/
instance : BEq Entities.Other := ⟨fun _ _ => true⟩

/-- Reads the flags from the entity's saved NBT. -/
def Entities.Other.ofNbt (nbt : Nbt) : Entities.Other :=
  ⟨nbt.boolD "NoGravity" false, nbt.boolD "Marker" false, nbt.boolD "Small" false⟩

/-- What an entity is, with the data particular to its kind. -/
inductive EntityData
  | item (d : Entities.Item)
  | fallingBlock (d : Entities.FallingBlock)
  | tnt (d : Entities.Tnt)
  | minecart (kind : MinecartKind) (d : Entities.Minecart)
  /-- A projectile of the entity type named `type`. -/
  | projectile (type : String) (d : Entities.Projectile)
  /-- Any other entity, of the entity type named `type`. -/
  | other (type : String) (d : Entities.Other := {})
  deriving BEq, Repr

/-- The registry name of the entity type. -/
def EntityData.typeName : EntityData → String
  | .item _ => "minecraft:item"
  | .fallingBlock _ => "minecraft:falling_block"
  | .tnt _ => "minecraft:tnt"
  | .minecart kind _ => kind.typeName
  | .projectile type _ => type
  | .other type _ => type

/-- The entity types kept as `EntityData.projectile`. -/
def projectileTypes : List String :=
  ["minecraft:arrow", "minecraft:spectral_arrow", "minecraft:trident", "minecraft:snowball",
    "minecraft:egg", "minecraft:ender_pearl", "minecraft:wind_charge", "minecraft:firework_rocket",
    "minecraft:small_fireball", "minecraft:fireball", "minecraft:splash_potion",
    "minecraft:lingering_potion", "minecraft:experience_bottle"]

/-- Reads the kind-specific data of an entity of the type named `type` from its saved NBT. -/
def EntityData.ofNbt? (type : String) (nbt : Nbt) : Option EntityData :=
  match type with
  | "minecraft:item" => .item <$> Entities.Item.ofNbt? nbt
  | "minecraft:falling_block" => .fallingBlock <$> Entities.FallingBlock.ofNbt? nbt
  | "minecraft:tnt" => .tnt <$> Entities.Tnt.ofNbt? nbt
  | "minecraft:minecart" => .minecart .minecart <$> Entities.Minecart.ofNbt? nbt
  | "minecraft:chest_minecart" => .minecart .chest <$> Entities.Minecart.ofNbt? nbt
  | "minecraft:furnace_minecart" => .minecart .furnace <$> Entities.Minecart.ofNbt? nbt
  | "minecraft:tnt_minecart" => .minecart .tnt <$> Entities.Minecart.ofNbt? nbt
  | "minecraft:hopper_minecart" => .minecart .hopper <$> Entities.Minecart.ofNbt? nbt
  | "minecraft:spawner_minecart" => .minecart .spawner <$> Entities.Minecart.ofNbt? nbt
  | "minecraft:command_block_minecart" => .minecart .commandBlock <$> Entities.Minecart.ofNbt? nbt
  | _ =>
    if projectileTypes.contains type then .projectile type <$> Entities.Projectile.ofNbt? nbt
    else some (.other type (.ofNbt nbt))

/-- An entity of the world. -/
structure Entity where
  /-- Entities are numbered in the order in which they are created; this is also the order in
  which they are ticked. -/
  index : ℕ
  /-- The state every entity has. -/
  base : Entities.Base
  /-- What the entity is. -/
  data : EntityData
  deriving BEq, Repr

/-- `Entity.resetFallDistance()`: sets `Entity.fallDistance` to zero, for the kinds of entity
that keep it. -/
def Entity.resetFallDistance (e : Entity) : Entity :=
  match e.data with
  | .item d => { e with data := .item { d with phys := { d.phys with fallDistance := 0 } } }
  | .fallingBlock d =>
    { e with data := .fallingBlock { d with phys := { d.phys with fallDistance := 0 } } }
  | .tnt d => { e with data := .tnt { d with fallDistance := 0 } }
  | .minecart kind d => { e with data := .minecart kind { d with fallDistance := 0 } }
  | _ => e

end Redstone
