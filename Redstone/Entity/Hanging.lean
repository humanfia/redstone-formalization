module

public import Redstone.Entity.Physics
public import Redstone.Entity.ItemDrop

/-!
# Item frames

Java classes: `ItemFrame`, `GlowItemFrame`, with `HangingEntity` and `BlockAttachedEntity`.

An item frame hangs in a block on a face of the neighbour behind it. It shows one item, which
can be turned in eight steps; a comparator behind the block the frame hangs on reads the step
(`ItemFrame.getAnalogOutput`, in `Component.Comparator.inputSignal`). The frame does not move.
Every 101st game tick it checks that it can stay (`BlockAttachedEntity.tick`), and if it cannot
it is removed, tells the comparators, and drops itself and its item
(`ItemFrame.dropItem`).

A frame can stay (`ItemFrame.survives`) if no block collides with its box, the block behind it
is solid, or is a repeater or comparator when the frame hangs on a wall, and no other frame in
the same block faces the same way.

## What is left out

* Players: putting an item into a frame, turning it and taking it out (`ItemFrame.interact`,
  `hurtServer`) are what a player does, and the player is not an entity of the model. The item
  and its rotation therefore only change when the frame falls off.
* What moves or damages a frame. A frame that is moved (`BlockAttachedEntity.move`: a piston
  pushes a block into it) or pushed, or hurt by an explosion, falls off at once. Pistons move no
  entities in the model (`Component.Piston`), so there the frame stays until its next check;
  an explosion near a frame sets `Level.overflow` (`Entity.Tnt.hurtEntities`).
* Maps. A frame that shows a map has a larger bounding box, which only matters to what looks
  for entities; the box that decides whether the frame can stay is the same
  (`ItemFrame.getPopBox`). The map's record of its frames (`removeFramedMap`) is not kept.
* The drop of the item when `ItemDropChance` is strictly between 0 and 1: it depends on the
  frame's own random numbers, which the model does not follow. The frame then sets
  `Level.overflow`.
* Paintings, and frames whose data the model could not read (`Entities.ItemFrame.ofNbt?`): they
  are hanging entities too, and one of them in the box of a frame facing the same way makes the
  frame fall off (`HangingEntity.canCoexist`). The model does not know their boxes, so a frame
  that checks whether it can stay while one exists sets `Level.overflow`.
* Frames pressing things. Block triggers do not find frames
  (`Entity.Still.getTriggeringEntities`), although the game's search does: a frame in the block
  of a pressure plate keeps the plate down once something pressed it. Tripwire that looks for
  entities while a frame exists sets `Level.overflow` (`Entities.ItemFrame.sizeBits`).
* The world border, and the void (`Entity.checkBelowWorld`).
* Sounds.

Two of these gaps are silent, in that the model goes on without setting `Level.overflow`: a
piston that pushes a block into a frame, after which a comparator may keep reading a frame that
the game has dropped, and a frame in the block of a pressure plate. The pending scenarios
`comparator/frame-negative-rotation-*` and `comparator/frame-summon-raw-*` hold frames the
model cannot read (`Entities.ItemFrame.ofNbt?`).
-/

@[expose] public section

namespace Redstone.Entity.Hanging

/-- The position of a frame, the centre of its bounding box
(`HangingEntity.recalculateBoundingBox`): the centre of the face it hangs on, moved a
thirty-second of a block into the block the frame is in. -/
def position (d : Entities.ItemFrame) : Vec3 := ItemDrop.centerRelative d.pos d.facing (-0.46875)

/-- `ItemFrame.getPopBox()`, which is `createBoundingBox(pos, direction, false)`: a slab three
quarters of a block wide and high and a sixteenth thick, against the face the frame hangs
on. -/
def popBox (d : Entities.ItemFrame) : AABB :=
  let c := position d
  let size (ax : Axis) : Float := if d.facing.axis = ax then 0.0625 else 0.75
  AABB.of (c.x - size .x / 2.0) (c.y - size .y / 2.0) (c.z - size .z / 2.0)
    (c.x + size .x / 2.0) (c.y + size .y / 2.0) (c.z + size .z / 2.0)

/-- `HangingEntity.canCoexist(true)` for the frame with the given index: no other hanging
entity that faces the same way has a box that meets the frame's. The box of a frame lies inside
its block, so another frame is in the way exactly when it is in the same block. A hanging
entity whose box the model does not know (a painting, a frame it could not read) sets
`Level.overflow` and is taken not to be in the way. -/
def canCoexist (index : ℕ) (d : Entities.ItemFrame) : M Bool := do
  let others := (← get).entities.filter (·.index != index)
  let unknown := others.any fun e =>
    match e.data with
    | .other type _ =>
      type == "minecraft:painting" || type == "minecraft:item_frame" ||
        type == "minecraft:glow_item_frame"
    | _ => false
  if unknown then Level.setOverflow
  return !others.any fun e =>
    match e.data with
    | .itemFrame _ o => o.pos == d.pos && o.facing == d.facing
    | _ => false

/-- `ItemFrame.survives()`: the frame can stay where it is. A block near the frame whose
collision shape is not modelled sets `Level.overflow`. -/
def survives (index : ℕ) (d : Entities.ItemFrame) : M Bool := do
  if d.fixed then return true
  let l ← get
  let (shapes, unmodelled) := l.blockCollisions (popBox d)
  if unmodelled then Level.setOverflow
  if !shapes.isEmpty then return false
  let state := l.blockAt (d.pos.step d.facing.opposite)
  if state.attrs.solid || (d.facing.axis ≠ .y && (state.is .repeater || state.is .comparator)) then
    canCoexist index d
  else return false

/-- `BlockAttachedEntity.discard()` followed by `ItemFrame.dropItem(level, null)`, for a frame
that is not fixed: the frame leaves the world and gives up its item, which the comparators
that could read it are told (`setItem(ItemStack.EMPTY)`); then the frame and the item it held
appear as item entities in front of where it hung (`HangingEntity.spawnAtLocation`), and the
change is announced (`GameEvent.BLOCK_CHANGE`). The game rule `entity_drops` is on. -/
def dropItem (e : Entity) (glow : Bool) (d : Entities.ItemFrame) : M Unit := do
  Level.removeEntity e.index
  Level.updateNeighbourForOutputSignal d.pos .air
  let n := ItemDrop.stepVec d.facing
  let reach := Phys.f 0x3e19999a
  let pos : Vec3 := ⟨e.base.pos.x + n.x * reach, e.base.pos.y, e.base.pos.z + n.z * reach⟩
  discard <| Entity.Item.spawnAtLocation pos
    (if glow then "minecraft:glow_item_frame" else "minecraft:item_frame") (e.index + 1)
  if !d.isEmpty then
    let chance := Float32.ofBits (UInt32.ofNat d.dropChance)
    if chance ≥ 1.0 then
      discard <| Entity.Item.spawnAtLocation pos d.item (e.index + 1) 1 d.hasComponents
    else if !(chance ≤ 0.0) then Level.setOverflow
  Level.gameEvent "minecraft:block_change" d.pos

/-- `BlockAttachedEntity.tick()`: every 101st tick the frame checks that it can stay, and falls
off if it cannot. A frame that is not where its block and its direction put it, which the game
never has, sets `Level.overflow`: the model looks for frames by their block. -/
def tick (index : ℕ) : M Unit := do
  let some e := (← get).entity? index | return
  let .itemFrame glow d := e.data | return
  if !(e.base.pos == position d) then Level.setOverflow
  if d.ticksSinceLastCheck < 100 then
    Level.modifyEntity index fun e =>
      { e with data := .itemFrame glow { d with ticksSinceLastCheck := d.ticksSinceLastCheck + 1 } }
  else
    Level.modifyEntity index fun e =>
      { e with data := .itemFrame glow { d with ticksSinceLastCheck := 0 } }
    if !(← survives index d) then dropItem e glow d

/-- The behaviour of the entity. -/
def behaviour : EntityBehaviour := ⟨tick⟩

end Redstone.Entity.Hanging
