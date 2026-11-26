module

public import Redstone.Entity.Data.Base

/-!
# Entity data: item

A dropped item (`ItemEntity`): the stack it holds, its age, the delay before it can be picked
up, its health, and the state `Entity.move` works with.

Of the item stack only the item, the count and whether it carries data components are kept.
The owner and the thrower are not kept.
-/

@[expose] public section

namespace Redstone.Entities

/-- The data of the entity besides `Base`. -/
structure Item where
  /-- The registry name of the item of the stack (`ItemStack.getItem`). -/
  item : String := "minecraft:air"
  /-- `ItemStack.getCount`. -/
  count : ℕ := 0
  /-- The stack has data components that differ from those of the item. -/
  hasComponents : Bool := false
  /-- `ItemEntity.age`, saved as `Age`. -/
  age : ℤ := 0
  /-- `ItemEntity.pickupDelay`, saved as `PickupDelay`. -/
  pickupDelay : ℤ := 0
  /-- `ItemEntity.health`, saved as `Health`. -/
  health : ℤ := 5
  /-- `Entity.getYRot()` as the bits of a `float`, saved in `Rotation`. The constructor of the
  entity draws it at random. -/
  yRot : ℕ := 0
  /-- The state `Entity.move` works with. -/
  phys : Physics := {}
  deriving BEq, Repr, Inhabited

namespace Item

/-- Reads the data from the entity's saved NBT. Fields the model does not keep are ignored. -/
def ofNbt? (nbt : Nbt) : Option Item := do
  let stack := nbt.get? "Item"
  let yRot :=
    match nbt.get? "Rotation" with
    | some (.list (.float bits :: _)) => bits
    | _ => 0
  return {
    item := ((stack.bind (·.get? "id")).bind Nbt.toString?).getD "minecraft:air"
    count := ((stack.map fun (t : Nbt) => t.intD "count" 1).getD 0).toNat
    hasComponents := (stack.bind (·.get? "components")).isSome
    age := nbt.intD "Age" 0
    pickupDelay := nbt.intD "PickupDelay" 0
    health := nbt.intD "Health" 5
    yRot := yRot
    phys := ← Physics.ofNbt? nbt }

end Item

end Redstone.Entities
