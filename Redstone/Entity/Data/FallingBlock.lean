module

public import Redstone.Entity.Data.Base

/-!
# Entity data: falling block

A falling block (`FallingBlockEntity`): the block state it carries, how long it has been falling,
what it does when it lands, and the state `Entity.move` works with.

The block entity data a falling block can carry (`TileEntityData`) is not kept, only whether
there is any.
-/

@[expose] public section

namespace Redstone.Entities

/-- The data of the entity besides `Base`. -/
structure FallingBlock where
  /-- `FallingBlockEntity.blockState`, saved as `BlockState`. -/
  blockState : Block := .default .sand
  /-- `FallingBlockEntity.time`, saved as `Time`. -/
  time : ℤ := 0
  /-- `FallingBlockEntity.dropItem`, saved as `DropItem`. -/
  dropItem : Bool := true
  /-- `FallingBlockEntity.cancelDrop`, saved as `CancelDrop`. -/
  cancelDrop : Bool := false
  /-- `FallingBlockEntity.hurtEntities`, saved as `HurtEntities`. -/
  hurtEntities : Bool := false
  /-- `FallingBlockEntity.fallDamagePerDistance` as the bits of a `float`, saved as
  `FallHurtAmount`. -/
  fallDamagePerDistance : ℕ := 0
  /-- `FallingBlockEntity.fallDamageMax`, saved as `FallHurtMax`. -/
  fallDamageMax : ℤ := 40
  /-- `FallingBlockEntity.blockData` is present (saved as `TileEntityData`). -/
  hasBlockData : Bool := false
  /-- The state `Entity.move` works with. -/
  phys : Physics := {}
  deriving BEq, Repr, Inhabited

namespace FallingBlock

/-- Reads a block state as `BlockState.CODEC` writes it when some property differs from the
default state of the block: a compound with the block's `id` and its `properties`, each a
string. (A default state is written as a string, the name of the block.) Properties that are
missing take the value of the default state. -/
def blockOfNbt? (nbt : Nbt) : Option Block := do
  let id ← BlockId.ofName? (← (← nbt.get? "id").toString?)
  let default := (Block.default id).toProps
  let props := nbt.get? "properties"
  Block.ofProps? id fun k =>
    match (props.bind (·.get? k)).bind Nbt.toString? with
    | some v => some v
    | none => (default.find? (·.1 == k)).map (·.2)

/-- Reads the data from the entity's saved NBT. Fields the model does not keep are ignored. -/
def ofNbt? (nbt : Nbt) : Option FallingBlock := do
  let blockState ←
    match nbt.get? "BlockState" with
    | some (.string s) => (BlockId.ofName? s).map Block.default
    | some t => blockOfNbt? t
    | none => some (.default .sand)
  let hurtDefault := blockState.is .anvil || blockState.is .chipped_anvil ||
    blockState.is .damaged_anvil
  let amount :=
    match nbt.get? "FallHurtAmount" with
    | some (.float bits) => bits
    | _ => 0
  return {
    blockState := blockState
    time := nbt.intD "Time" 0
    dropItem := nbt.boolD "DropItem" true
    cancelDrop := nbt.boolD "CancelDrop" false
    hurtEntities := nbt.boolD "HurtEntities" hurtDefault
    fallDamagePerDistance := amount
    fallDamageMax := nbt.intD "FallHurtMax" 40
    hasBlockData := (nbt.get? "TileEntityData").isSome
    phys := ← Physics.ofNbt? nbt }

end FallingBlock

end Redstone.Entities
