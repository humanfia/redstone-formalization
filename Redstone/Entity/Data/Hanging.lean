module

public import Redstone.Entity.Data.Base

/-!
# Entity data: item frame

An item frame or a glow item frame (`ItemFrame`, `GlowItemFrame`, with `HangingEntity` and
`BlockAttachedEntity`): the block it is in, the direction it faces, the item it shows and how
far the item is turned.

A frame hangs in a block (`BlockAttachedEntity.pos`, saved as `block_pos`) on the face of the
neighbour behind it: a frame that faces east is in the block east of its support. Its position
and its bounding box are computed from that block and the direction
(`HangingEntity.recalculateBoundingBox`), so the position in `Base` says nothing more; the model
takes it from the trace and never changes it.

Of the item only the name and whether it carries data components are kept, as for a dropped
item (`Entities.Item`). A frame always holds a single item (`ItemFrame.setItem`).

## What is not read

A frame whose saved data the model cannot represent is not decoded (`ofNbt?` gives `none`) and
stays an `EntityData.other`, which a comparator that looks for frames treats as unknown
(`Component.Comparator.inputSignal`):

* a frame without `block_pos`, which is what a scenario's `summon` gives unless it writes the
  tag itself, since the game only computes it when the entity is loaded;
* a negative `ItemRotation` that is not a multiple of 8: the game keeps `rotation % 8`, which is
  then negative, and so is the signal a comparator reads;
* a `Facing` outside 0 to 5;
* a frame with a custom name, which the frame's own item would carry when it drops;
* an `Item` whose count is not from 1 to 99, which the game does not accept
  (`ItemStack.CODEC`) and replaces by no item.

What is read is taken as the game would have saved it. The game also drops an `Item` whose
name is not that of an item, and a `block_pos` more than 16 blocks from the position; the
model does not check the name, and a frame whose position is not the one its block and
direction give sets `Level.overflow` when it is ticked (`Entity.Hanging.tick`).
-/

@[expose] public section

namespace Redstone.Entities

/-- The data of the entity besides `Base`. Two values are equal (`==`) when the fields that the
game saves agree; `ticksSinceLastCheck` is not saved. -/
structure ItemFrame where
  /-- `BlockAttachedEntity.pos`, saved as `block_pos`: the block the frame is in. -/
  pos : Pos
  /-- `HangingEntity.getDirection()`, saved as `Facing`: the direction the frame looks in, away
  from the block it hangs on. -/
  facing : Direction
  /-- The registry name of the item in the frame (`ItemFrame.getItem`, saved as `Item`), or
  `minecraft:air` for an empty frame. -/
  item : String := "minecraft:air"
  /-- The item has data components that differ from those of the item. -/
  hasComponents : Bool := false
  /-- `ItemFrame.getRotation()`, saved as `ItemRotation`: from 0 to 7. -/
  rotation : ℕ := 0
  /-- `ItemFrame.dropChance`, saved as `ItemDropChance`, as the bits of a `float`. -/
  dropChance : ℕ := 0x3f800000
  /-- `ItemFrame.fixed`, saved as `Fixed`: the frame never falls off. -/
  fixed : Bool := false
  /-- `BlockAttachedEntity.ticksSinceLastCheck`: the game ticks since the frame last checked
  that it can stay. Not saved; a frame that is loaded starts from 0. -/
  ticksSinceLastCheck : ℕ := 0
  deriving Repr

instance : Inhabited ItemFrame := ⟨{ pos := ⟨0, 0, 0⟩, facing := .south }⟩

instance : BEq ItemFrame :=
  ⟨fun a b => a.pos == b.pos && a.facing == b.facing && a.item == b.item &&
    a.hasComponents == b.hasComponents && a.rotation == b.rotation &&
    a.dropChance == b.dropChance && a.fixed == b.fixed⟩

namespace ItemFrame

/-- `Direction.from3DDataValue`, for the values 0 to 5 (`Direction.LEGACY_ID_CODEC`). -/
def directionOfId? : ℤ → Option Direction
  | 0 => some .down
  | 1 => some .up
  | 2 => some .north
  | 3 => some .south
  | 4 => some .west
  | 5 => some .east
  | _ => none

/-- Reads the data from the entity's saved NBT (`readAdditionalSaveData` of `ItemFrame` and of
`BlockAttachedEntity`). `none` for a frame the model cannot represent (see the module
docstring), which then stays an `EntityData.other`. -/
def ofNbt? (nbt : Nbt) : Option ItemFrame := do
  let pos ←
    match nbt.get? "block_pos" with
    | some (.intArray [x, y, z]) => some (⟨x, y, z⟩ : Pos)
    | _ => none
  let facing ← directionOfId? (nbt.intD "Facing" 0)
  let rotation := nbt.intD "ItemRotation" 0
  if rotation < 0 ∧ rotation % 8 ≠ 0 then none
  if (nbt.get? "CustomName").isSome then none
  let stack := nbt.get? "Item"
  let count := (stack.map fun (t : Nbt) => t.intD "count" 1).getD 0
  let id := ((stack.bind (·.get? "id")).bind Nbt.toString?).getD "minecraft:air"
  if stack.isSome ∧ (count < 1 ∨ 99 < count) then none
  let empty := id == "minecraft:air"
  let dropChance :=
    match nbt.get? "ItemDropChance" with
    | some (.float bits) => bits
    | _ => 0x3f800000
  return {
    pos, facing
    item := if empty then "minecraft:air" else id
    hasComponents := !empty && (stack.bind (·.get? "components")).isSome
    rotation := (rotation % 8).toNat
    dropChance
    fixed := nbt.boolD "Fixed" false }

/-- `ItemFrame.getItem().isEmpty()`. -/
def isEmpty (d : ItemFrame) : Bool := d.item == "minecraft:air"

/-- `ItemFrame.getAnalogOutput()`: what a comparator reads from the frame, nothing if it is
empty and otherwise one more than the rotation of the item. -/
def analogOutput (d : ItemFrame) : ℕ := if d.isEmpty then 0 else d.rotation % 8 + 1

/-- The size (width, height) of an item frame as `float` bits, which is what
`Component.Tripwire.entitySize` asks for. `none`: the box of a frame is not the box of a width
and a height around its position (`ItemFrame.calculateBoundingBox`: a slab a sixteenth of a
block thick against the face it hangs on, around the position in all three directions), so
tripwire that looks for entities while a frame exists sets `Level.overflow`. -/
def sizeBits (_d : ItemFrame) : Option (UInt32 × UInt32) := none

/-- Whether a minecart and an item frame whose boxes meet act on each other, which is what
`Entity.Minecart.contact` asks for. They never do: a frame cannot be pushed (`Entity.isPushable`)
and does not stop a minecart (`Entity.canBeCollidedWith`), and it pushes nothing itself. -/
def touchesMinecart (_d : ItemFrame) : Option Bool := some false

end ItemFrame

end Redstone.Entities
