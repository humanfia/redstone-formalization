module

public import Redstone.Component.Hopper
public import Redstone.Component.CommandBlock

/-!
# Minecarts with a load that acts: containers and commands

Java classes: `AbstractMinecartContainer`, `MinecartChest`, `MinecartHopper`,
`MinecartCommandBlock`, with the parts of `HopperBlockEntity`, `BaseCommandBlock` and
`DetectorRailBlock` that work on them.

* A minecart with a chest or a hopper is a `Container`. Hoppers push items into it and pull
  items out of it, droppers and crafters push items into it; all of that goes through
  `Redstone.Component.Container.ContainerRef.entity`, whose slots are in
  `Redstone.Entity.Minecart.Slots`. Its fullness is what a comparator reads behind a detector
  rail (`detectorSignal`), and it sets the friction of the minecart on rails (`signal`).
* A hopper minecart that is enabled takes in an item after every tick of its own
  (`tryConsumeItems`): out of the container above it, a block or another minecart; else from an
  item entity in or above its bowl; else from an item entity next to it.
* A command block minecart runs its command when it is on an active activator rail, at most
  once in four ticks (`activateCommandBlock`). The command itself is an oracle, as for the
  command blocks (`Redstone.Component.CommandBlock.Oracle`), run at the block the minecart is
  in; a comparator behind a detector rail reads how often it succeeded.

## What is left out

* Loot tables, boats with a chest and the choice between several container entities: see
  `Redstone.Entity.Minecart.Slots`.
* What a comparator reads behind a detector rail in two cases (`detectorUnknown`, which the
  tick of the minecart turns into `Level.overflow`): a minecart on the rail whose container still
  has a loot table, which the game fills when the comparator reads it; and two command block
  minecarts, or two minecarts with a container, on one rail, of which the game reads the first in
  the order of its entity sections, which the model does not keep for minecarts.
* A negative success count of a command block minecart, which reads as zero behind a detector
  rail (the signals of the model are natural numbers, as for command blocks).
* The components of the stack of an item entity (`Entities.Item`), as for hoppers: a hopper
  minecart that would take in an item entity whose stack has components sets `Level.overflow`.
* The menu of a minecart with a container (`interact`), and the contents a minecart drops when
  it is destroyed: the model never destroys a minecart.
* The output of a command (`LastOutput`), and the entity as the source of the command: the
  oracle is given the position only.

Scenarios that wait in `tests/pending/scenarios/minecart`:

* `container-hopper-cart-under-two-carts`: two minecarts with a chest above a hopper minecart, of
  which the game takes one at random (`Redstone.Entity.Minecart.Slots`).
* `container-unload-loot-table`: a hopper under a minecart whose chest has a loot table.
* `container-detector-chest-cart-loot-table` and `container-detector-two-chest-carts`: the two
  cases of `detectorUnknown`.
* `fuzz-minecart-container-s21-015`, `-022`, `-039`, `s22-030`, `-038` and `-058`: a rail or
  another block that loses its support is removed, and the game draws the place of its drops from
  the level's random numbers even when nothing is dropped; `Redstone.Component.Rail` leaves the
  drops out, so what a dropper throws out later differs. They fail in the same way without their
  minecart.
-/

@[expose] public section

namespace Redstone.Entity.MinecartContainer

open Redstone.Component
open Redstone.Component.Container (ContainerRef)

/-! ### The fullness of a container -/

/-- `AbstractContainerMenu.getRedstoneSignalFromContainer(minecart)` for a minecart of the given
kind with the given data; none for a minecart that is no container. -/
def signal (kind : MinecartKind) (d : Entities.Minecart) : Option ℕ :=
  (size kind).map fun n => Container.redstoneSignal (d.items.take n)

/-! ### `MinecartHopper` -/

/-- The item entities whose box meets `box`, by index, in the order of the game's entity
sections (`getEntitiesOfClass(ItemEntity.class, box, ENTITY_STILL_ALIVE)`). -/
def itemsIn (l : Level) (box : AABB) : List ℕ :=
  (entitiesIn l box (fun e => e.data matches .item _)
    fun e => some (Entity.Item.kind.dims.box e.base.pos)).map (·.index)

/-- `HopperBlockEntity.tryTakeInItemFromSlot(hopper, container, slot, DOWN)` for the hopper
minecart with index `i`: pulls one item out of a slot of the container above into the
minecart. -/
def tryTakeInItemFromSlot (i : ℕ) (c : ContainerRef) (slot : ℕ) : M Bool := do
  let stack ← c.getItem slot
  if stack.isEmpty then return false
  if !(← c.canTakeItemFromContainer (← getItems i) stack slot .down) then return false
  let removed ← c.removeItem slot
  let rest ← Container.addItem none (.entity i) removed none
  if rest.isEmpty then
    c.setChanged
    return true
  c.restoreItem slot stack
  return false

/-- `HopperBlockEntity.suckInItems(level, hopper)` for the hopper minecart with index `i`, whose
place as a hopper is half a block above its position (`getLevelY`). It pulls one item out of
the container in the block above that place, or else out of a container entity around the
point one block above it. Without a container it takes in the first item entity, among those
in the space a hopper picks up items from, that it has room for; a block above does not keep it
from that, since a minecart is not aligned with the blocks (`isGridAligned`). -/
def hopperSuckInItems (i : ℕ) : M Bool := do
  let some e := (← get).entity? i | return false
  let x := e.base.pos.x
  let y := e.base.pos.y + 0.5
  let z := e.base.pos.z
  let above : Pos := Vec3.blockPos ⟨x, y + 1.0, z⟩
  let source ←
    match ← Container.getBlockContainer above with
    | some c => pure (some c)
    | none =>
      let cy := y + 1.0
      let box := AABB.of (x - 0.5) (cy - 0.5) (z - 0.5) (x + 0.5) (cy + 0.5) (z + 0.5)
      pure ((← getEntityContainer box).map ContainerRef.entity)
  match source with
  | some c =>
    for slot in ← c.slots .down do
      if ← tryTakeInItemFromSlot i c slot then return true
    return false
  | none =>
    -- `getItemsAtAndAbove`: `Hopper.SUCK_AABB`, moved to the hopper.
    let suck := (AABB.of 0.0 0.6875 0.0 1.0 2.0 1.0).move ⟨x - 0.5, y - 0.5, z - 0.5⟩
    for j in itemsIn (← get) suck do
      if ← Hopper.addItemEntityTo (.entity i) j then return true
    return false

/-- `MinecartHopper.suckInItems`: what a hopper does, and failing that, the first item entity
within a quarter of a block of the minecart's sides that the minecart has room for. -/
def suckInItems (i : ℕ) : M Bool := do
  if ← hopperSuckInItems i then return true
  let some e := (← get).entity? i | return false
  for j in itemsIn (← get) ((dims.box e.base.pos).inflate 0.25 0.0 0.25) do
    if ← Hopper.addItemEntityTo (.entity i) j then return true
  return false

/-- `MinecartHopper.tryConsumeItems`, called at the end of the minecart's tick: a hopper minecart
that is enabled looks for an item to take in. -/
def tryConsumeItems (i : ℕ) : M Unit := do
  if let some e := (← get).entity? i then
    if let .minecart .hopper d := e.data then
      if d.enabled then discard <| suckInItems i

/-! ### `MinecartCommandBlock` -/

/-- The data of the command block minecart with index `i`. -/
def commandData? (i : ℕ) : M (Option (Entity × Entities.Minecart)) := do
  match (← get).entity? i with
  | some e =>
    match e.data with
    | .minecart .commandBlock d => return some (e, d)
    | _ => return none
  | none => return none

/-- Changes the data of the minecart with index `i`. -/
def modifyData (i : ℕ) (f : Entities.Minecart → Entities.Minecart) : M Unit :=
  Level.modifyEntity i fun e =>
    match e.data with
    | .minecart kind d => { e with data := .minecart kind (f d) }
    | _ => e

/-- `BaseCommandBlock.performCommand` for the command block minecart with index `i`: executes
its command at the block the minecart is in. Returns false, and does nothing, if the minecart
already executed in this game tick. -/
def performCommand (oracle : CommandBlock.Oracle) (i : ℕ) : M Bool := do
  let some (e, d) ← commandData? i | return false
  let now : ℤ := (← get).gameTime
  if now = d.lastExecution then return false
  if CommandBlock.isSearge d.command then
    modifyData i ({ · with successCount := 1 })
    return true
  modifyData i ({ · with successCount := 0 })
  if d.command ≠ "" then
    let successes ← oracle e.base.pos.blockPos d.command
    modifyData i fun d => { d with successCount := d.successCount + successes }
  modifyData i fun d => { d with lastExecution := if d.updateLastExecution then now else -1 }
  return true

/-- `MinecartCommandBlock.activateMinecart(level, x, y, z, true)`: an active activator rail runs
the command of the minecart on it, unless it did so less than four ticks of the minecart
ago. -/
def activateCommandBlockWith (oracle : CommandBlock.Oracle) (i : ℕ) : M Unit := do
  let some (_, d) ← commandData? i | return
  if d.tickCount ≥ d.lastActivated + 4 then
    discard <| performCommand oracle i
    modifyData i ({ · with lastActivated := d.tickCount })

/-- `activateCommandBlockWith` for the commands `CommandBlock.Oracle.default` knows. -/
def activateCommandBlock (i : ℕ) : M Unit := activateCommandBlockWith CommandBlock.Oracle.default i

/-! ### `DetectorRailBlock.getAnalogOutputSignal` -/

/-- `DetectorRailBlock.getSearchBB(pos)`. -/
def searchBB (p : Pos) : AABB :=
  ⟨Float.ofInt p.x + 0.2, Float.ofInt p.y, Float.ofInt p.z + 0.2, Float.ofInt (p.x + 1) - 0.2,
    Float.ofInt (p.y + 1) - 0.2, Float.ofInt (p.z + 1) - 0.2⟩

/-- `DetectorRailBlock.getAnalogOutputSignal` of a detector rail at `p` that is on: the success
count of the first command block minecart on the rail, or else the fullness of the first
minecart with a container; zero without either. -/
def detectorSignal (l : Level) (p : Pos) : ℕ :=
  let carts := entitiesIn l (searchBB p) (fun e => e.data matches .minecart _ _)
    fun e => some (dims.box e.base.pos)
  let commands := carts.filterMap fun e =>
    match e.data with
    | .minecart .commandBlock d => some d.successCount.toNat
    | _ => none
  let containers := carts.filterMap fun e =>
    match e.data with
    | .minecart kind d => signal kind d
    | _ => none
  (commands.head?.orElse fun _ => containers.head?).getD 0

/-- The model cannot tell what a comparator reads behind a detector rail on which the minecart
with index `i`, of the given kind and data, at `pos`, is: the minecart has a container with a
loot table, which reading would fill, or another minecart of its sort (with a command block, or
with a container) is on the same rail, and the model does not know which of the two the game
finds first. -/
def detectorUnknown (l : Level) (i : ℕ) (kind : MinecartKind) (d : Entities.Minecart)
    (pos : Vec3) : Bool :=
  let isCommand := kind == .commandBlock
  if !isCommand && (size kind).isNone then false
  else
    let box := dims.box pos
    box.blocks.any fun p =>
      (l.blockAt p matches .detectorRail _) && box.intersects (searchBB p) &&
        ((!isCommand && d.hasLootTable) ||
          l.entities.any fun o =>
            o.index != i && (dims.box o.base.pos).intersects (searchBB p) &&
              match o.data with
              | .minecart k _ => if isCommand then k == .commandBlock else (size k).isSome
              | _ => false)

end Redstone.Entity.MinecartContainer
