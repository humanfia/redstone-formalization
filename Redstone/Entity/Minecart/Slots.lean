module

public import Redstone.Entity.Item

/-!
# The slots of a minecart with a container

Java classes: `ContainerEntity`, `AbstractMinecartContainer`, with `EntitySelector` and
`HopperBlockEntity.getEntityContainer`.

A minecart with a chest has 27 slots and a minecart with a hopper has five. This file is the
view of such a minecart as a `Container`: reading and writing its slots, and finding the
minecarts whose box meets a given box, as hoppers and droppers look for them. The operations of
`Container` that hoppers use are built on it in `Redstone.Component.Container`
(`ContainerRef.entity`); what the minecarts themselves do with their slots is in
`Redstone.Entity.Minecart.Container`.

## What is left out

* Loot tables. A minecart whose container still has a loot table fills its slots from it the
  first time a slot is read (`unpackChestVehicleLootTable`); the model sets `Level.overflow`
  then.
* Boats with a chest, which are containers as well and are not modelled: finding one sets
  `Level.overflow`.
* The order in which `Level.getEntities` returns several entities. When more than one container
  entity is found, the game takes one of them at random; the model draws the random number, but
  it does not know which of them the number stands for, and sets `Level.overflow`.
-/

@[expose] public section

namespace Redstone.Entity.MinecartContainer

/-- `getContainerSize()` of a minecart: 27 with a chest, five with a hopper; the other kinds are
no containers. -/
def size : MinecartKind → Option ℕ
  | .chest => some 27
  | .hopper => some 5
  | _ => none

/-- `EntityType.getDimensions` of a minecart, which is `0.98F` wide and `0.7F` high. -/
def dims : Dimensions := .ofBits 0x3f7ae148 0x3f333333

/-- `ContainerEntity.getItemStacks()`: the slots of an entity that is a minecart with a
container. -/
def slots? (e : Entity) : Option Inventory :=
  match e.data with
  | .minecart kind d => (size kind).map fun n => d.items.take n
  | _ => none

/-- The entity is a minecart with a container (`entity instanceof Container`, for the entities
that are modelled). -/
def isContainer (e : Entity) : Bool := (slots? e).isSome

/-- The entity is a `Container` that the model has no slots for: a boat or a raft with a
chest. -/
def isUnmodelledContainer (e : Entity) : Bool :=
  match e.data with
  | .other type _ => type.endsWith "chest_boat" || type.endsWith "chest_raft"
  | _ => false

/-- The slots of the minecart with index `i`; none if it is not a container. -/
def getItems (i : ℕ) : M Inventory :=
  return (((← get).entity? i).bind slots?).getD []

/-- Replaces the slots of the minecart with index `i`. -/
def setItems (i : ℕ) (inv : Inventory) : M Unit :=
  Level.modifyEntity i fun e =>
    match e.data with
    | .minecart kind d =>
      { e with data := .minecart kind { d with items := inv ++ d.items.drop inv.length } }
    | _ => e

/-- `unpackChestVehicleLootTable(null)`: a container that still has a loot table is filled from
it. Loot tables are not modelled: this sets `Level.overflow`. -/
def unpackLootTable (i : ℕ) : M Unit := do
  if let some e := (← get).entity? i then
    if let .minecart _ d := e.data then
      if d.hasLootTable then Level.setOverflow

/-- `getContainerSize()` of the minecart with index `i`. -/
def containerSize (i : ℕ) : M ℕ := return (← getItems i).length

/-- `isChestVehicleEmpty()`: every slot is empty. -/
def isEmpty (i : ℕ) : M Bool := return (← getItems i).isEmpty

/-- `getChestVehicleItem(slot)`. -/
def getItem (i slot : ℕ) : M ItemStack := do
  unpackLootTable i
  return (← getItems i).getItem slot

/-- `removeChestVehicleItem(slot, 1)`, which is `ContainerHelper.removeItem`: takes one item out
of a slot and returns it. -/
def removeItem (i slot : ℕ) : M ItemStack := do
  unpackLootTable i
  let inv ← getItems i
  let s := inv.getItem slot
  if s.isEmpty then return .empty
  setItems i (inv.setItem slot (s.withCount (s.count - 1)))
  return s.withCount 1

/-- `setChestVehicleItem(slot, itemStack)`: the stack is put into the slot, cut down to what a
slot holds. -/
def setItem (i slot : ℕ) (s : ItemStack) : M Unit := do
  unpackLootTable i
  setItems i ((← getItems i).setItem slot (s.limitSize s.containerMaxStackSize))

/-- Writes a stack into a slot as it is: what the game does when it changes the count of the
stack that is in the slot (`ItemStack.grow`, `setCount`). -/
def putItem (i slot : ℕ) (s : ItemStack) : M Unit := do
  setItems i ((← getItems i).setItem slot s)

/-- The entities of `l` that pass `test` and whose box meets `box`, in the order of the game's
entity sections (`Entity.Item.sectionKey`), as `Level.getEntities` returns them. An entity
without a box in the model is taken to meet every box. -/
def entitiesIn (l : Level) (box : AABB) (test : Entity → Bool) (boxOf : Entity → Option AABB) :
    List Entity :=
  let found := l.entities.filter fun e =>
    test e &&
      match boxOf e with
      | some b => b.intersects box
      | none => true
  found.foldl (fun acc e => Entity.Item.insertBySection e acc) []

/-- The minecarts with a container whose box meets `box`. -/
def containersIn (l : Level) (box : AABB) : List Entity :=
  entitiesIn l box isContainer fun e => some (dims.box e.base.pos)

/-- A container entity that is not modelled may be within `box`: such an entity lies within two
blocks of the box, which is more than the size of any boat. -/
def unmodelledContainerNear (l : Level) (box : AABB) : Bool :=
  l.entities.any fun e =>
    isUnmodelledContainer e && (AABB.of e.base.pos.x e.base.pos.y e.base.pos.z e.base.pos.x
      e.base.pos.y e.base.pos.z).intersects (box.inflate 2.0 2.0 2.0)

/-- `HopperBlockEntity.getEntityContainer`: one of the container entities whose box meets `box`,
by index, chosen with the level's random numbers (`nextInt(entities.size())`, which is drawn
for a single entity as well). With more than one entity the model cannot tell which one the
game takes, and with a boat it has no container to give: both set `Level.overflow`. -/
def getEntityContainer (box : AABB) : M (Option ℕ) := do
  let l ← get
  if unmodelledContainerNear l box then Level.setOverflow
  match containersIn l box with
  | [] => return none
  | found@(first :: rest) =>
    let (k, random) := l.random.nextInt found.length
    modify fun l => { l with random }
    if !rest.isEmpty then Level.setOverflow
    return some ((found.getD k first).index)

end Redstone.Entity.MinecartContainer
