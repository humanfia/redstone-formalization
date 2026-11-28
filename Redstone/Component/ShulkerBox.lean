module

public import Redstone.Mechanics.Power
public import Redstone.Block.FaceShape

/-!
# The lid of a shulker box

Java classes: `ShulkerBoxBlock` (`canOpen`, `getBlockSupportShape`, `getShape`) and
`ShulkerBoxBlockEntity` (`startOpen`, `stopOpen`, `triggerEvent`, `updateAnimation`), with
`Shulker.getProgressDeltaAabb` for the boxes of the lid.

A player who opens the menu of a shulker box raises its `openCount` and sends the block event
`1` with the new count. The event sets the lid moving (`AnimationStatus`), and the ticker of
the block entity moves it by `0.1F` a tick. In the tick in which the lid leaves an end and in
the tick in which it arrives at one, the box sends shape updates and neighbour updates around
(`doNeighborUpdates`). The lid is not saved, and none of it shows in a block state: what a
circuit sees of it are these updates, and what the box supports while its lid is not closed.

While the lid is not closed, only the face of the box opposite to the lid is sturdy
(`getBlockSupportShape`). While the lid is up the box has the collision shape of its block
entity, which is larger than a block, so it is no redstone conductor. The two are not quite the
same time: between the block event and the first step of the lid, and when the lid has stopped
a few rounding errors short of closed, the box has the shape of a block but is not closed
(`ShulkerBox.isFullBlock`). `Level.supportAttrs` says both, and the blocks that ask through it
(torches,
levers, buttons, rails, pressure plates, bells, tripwire hooks, the blocks of
`Component.Supported`, chests under the box) see the box as the game does. The behaviour of the
block itself, with the menu of the player, is `Component.Container.shulkerBox`.

## What is left out

* Blocks that read the attributes of the block state instead of `Level.supportAttrs`. For them
  a box whose lid is not closed still looks like a full block that conducts. `checkLid`, which
  runs when a block event sets the lid moving and in every tick of a box that is not closed
  (after the lid has moved, before the box updates its neighbours), sets `Level.overflow` when
  that could matter:
  * a neighbour that would not survive next to a block with the sturdy faces of the open box,
    while it does survive next to the box as the model shows it (found by asking its
    `canSurvive` in a level where a trapdoor with the same sturdy face stands in for the box:
    `standIn`);
  * redstone wire next to a box that does not conduct, whose connections depend on that;
  * a direct signal into a box that does not conduct, which a conductor would pass on
    (`Level.signalAt`).

  Not caught: a change of this kind that comes and goes between two of these checks; a
  comparator that reads the box from the far side of a container next to it and is told of a
  change of that container although the box does not conduct
  (`Level.updateNeighbourForOutputSignal`), which only shows if that comparator had missed an
  update before; the conductor test of `Entity.Minecart`.
* Entities and the lid. The lid pushes the entities in its way (`moveCollidedEntities`), and a
  boat or a shulker in its way keeps the box shut (`canOpen`). Neither is modelled: an entity
  that may reach into the block in front of the lid when the box is used or while the lid
  opens sets `Level.overflow`. The box assumed for an entity other than an item is three
  blocks wide and three high. The collision shape of the open box for entities is not
  modelled either: `Entity.Physics` gives up on any shulker box.
* `canOpen` and blocks whose collision shape the model does not have: a moving piston,
  scaffolding, powder snow, bamboo, pointed dripstone, or another shulker box whose lid is not
  closed, in or next to the block in front of the lid, sets `Level.overflow`.
* Loot tables and locks (see `Redstone.ItemStack`), the statistics of the player, and the
  piglins that a player who opens a box angers.
-/

@[expose] public section

namespace Redstone.Component.ShulkerBox

open BlockEntities (ShulkerBoxAnimationStatus)

/-- `state.getValue(ShulkerBoxBlock.FACING)`: the side the lid opens to. -/
def facing? : Block → Option Direction
  | .shulkerBox _ s => some s.facing
  | _ => none

/-- The data of the shulker box at `p`. -/
def getData (p : Pos) : M (Option BlockEntities.ShulkerBox) := do
  match ← Level.getBlockEntity p with
  | some (.shulkerBox d) => return some d
  | _ => return none

/-! ### What stands in the way of the lid -/

/-- The box `Shulker.getProgressDeltaAabb(1.0F, facing, 0.0F, 0.5F, bottomCenter)
.deflate(1.0E-6)` of `ShulkerBoxBlock.canOpen`: the half of the block in front of the lid that
the open lid fills, a little smaller, in the coordinates of that block. -/
def lidOpenBox (facing : Direction) : RatBox :=
  let e : ℚ := 1 / 1000000
  let b : RatBox := ⟨e, e, e, 1 - e, 1 - e, 1 - e⟩
  match facing with
  | .west => { b with minX := 1 / 2 + e }
  | .east => { b with maxX := 1 / 2 - e }
  | .down => { b with minY := 1 / 2 + e }
  | .up => { b with maxY := 1 / 2 - e }
  | .north => { b with minZ := 1 / 2 + e }
  | .south => { b with maxZ := 1 / 2 - e }

/-- `AABB.intersects`: the interior of `a` meets that of `b` moved by `(dx, dy, dz)`. -/
def meets (a b : RatBox) (dx dy dz : ℤ) : Bool :=
  a.minX < b.maxX + dx && a.maxX > b.minX + dx && a.minY < b.maxY + dy && a.maxY > b.minY + dy
    && a.minZ < b.maxZ + dz && a.maxZ > b.minZ + dz

/-- The blocks, other than shulker boxes, whose collision shape depends on the position, on who
asks or on a block entity: the model does not have their shape. -/
def collisionUnmodelled (b : Block) : Bool :=
  b.is .moving_piston || b.is .scaffolding || b.is .powder_snow || b.is .bamboo ||
    b.is .pointed_dripstone

/-- What `level.noCollision(lidOpenBoundingBox)` finds among the blocks, for the box at `p`
whose lid opens to `facing`: whether a collision shape reaches into the half block in front of
the lid, and whether a shape the model does not have may.

`BlockCollisions` looks at the block in front of the lid, at the blocks next to that one if
their shape may be larger than a block (the box itself is one of them, and is closed here: it
stays inside its own block), and at the blocks one step further along an edge if they are
moving pistons. -/
def lidBlocked (l : Level) (p : Pos) (facing : Direction) : Bool × Bool :=
  let q := p.step facing
  let lid := lidOpenBox facing
  let cells := q :: (Direction.values.map q.step).filter (· != p)
  let edges : List Pos :=
    Direction.values.flatMap fun d =>
      (Direction.values.filter fun d' => d' != d && d' != d.opposite).map fun d' =>
        (q.step d).step d'
  let blocked := cells.any fun r =>
    let b := l.blockAt r
    if b.isAir then false
    else if (facing? b).isSome then r == q
    else
      (FaceShape.ofIndex b.attrs.collision).boxes.any fun box =>
        meets lid box (r.x - q.x) (r.y - q.y) (r.z - q.z)
  let unmodelled :=
    (cells.any fun r =>
        let b := l.blockAt r
        collisionUnmodelled b ||
          ((facing? b).isSome &&
            match l.blockEntities r with
            | some (.shulkerBox d) => !d.isClosed
            | _ => false))
      || edges.any fun r => (l.blockAt r).is .moving_piston
  (blocked, unmodelled)

/-- An entity may reach into the block at `q`. The box assumed for an item is its own; for any
other entity it is three blocks wide and three high. -/
def entityNear (l : Level) (q : Pos) : Bool :=
  l.entities.any fun e =>
    let (halfWidth, height) : Float × Float :=
      match e.data with
      | .item _ => (0.125, 0.25)
      | _ => (1.5, 3.0)
    let within (a : Float) (b : ℤ) : Bool :=
      a - halfWidth < Float.ofInt b + 1 && a + halfWidth > Float.ofInt b
    within e.base.pos.x q.x && within e.base.pos.z q.z
      && e.base.pos.y < Float.ofInt q.y + 1 && e.base.pos.y + height > Float.ofInt q.y

/-- `ShulkerBoxBlock.canOpen(state, level, pos, blockEntity)`: a box whose lid is closed opens
only if nothing is in the way of the lid. -/
def canOpen (self : Block) (p : Pos) (d : BlockEntities.ShulkerBox) : M Bool := do
  if !d.isClosed then return true
  let some facing := facing? self | return true
  let l ← get
  let (blocked, unmodelled) := lidBlocked l p facing
  if unmodelled || entityNear l (p.step facing) then Level.setOverflow
  return !blocked

/-! ### What the model cannot show of an open box -/

/-- A block with the sturdy faces of a shulker box whose lid, opening to `facing`, is not
closed: a trapdoor that covers the face opposite to the lid. It is no conductor, and like the
plate under the open box (`ShulkerBoxBlock.SHAPES_OPEN_SUPPORT`) it supports nothing on its
other faces, whatever the kind of support asked for. -/
def standIn (facing : Direction) : Block :=
  let s : Blocks.TrapDoor :=
    { facing := .north, half := .bottom, «open» := false, powered := false, waterlogged := false }
  .trapDoor .iron_trapdoor <|
    match facing with
    | .up => s
    | .down => { s with half := .top }
    | .north => { s with «open» := true, facing := .north }
    | .south => { s with «open» := true, facing := .south }
    | .west => { s with «open» := true, facing := .west }
    | .east => { s with «open» := true, facing := .east }

/-- Sets `Level.overflow` when something around the box `self` at `p` reads it in a way that
does not go through `Level.supportAttrs`, and so takes it for a closed box, while its lid is
not closed or it does not conduct. See the head of the file. -/
def checkLid (self : Block) (p : Pos) : M Unit := do
  let some facing := facing? self | return
  let some d ← getData p | return
  let l ← get
  let env ← read
  let unsupported :=
    !d.isClosed &&
      let other := l.setBlockRaw p (standIn facing)
      Direction.values.any fun dir =>
        let q := p.step dir
        let b := l.blockAt q
        !b.isAir && (env.block b).canSurvive l q && !(env.block b).canSurvive other q
  let conductor :=
    !d.isFullBlock &&
      ((Direction.values.any fun dir => (l.blockAt (p.step dir)).is .redstone_wire)
        || l.directSignalTo env p > 0)
  if unsupported || conductor then Level.setOverflow

/-! ### The block entity -/

/-- `level.playSound(..., level.getRandom().nextFloat() * 0.1F + 0.9F)`: the pitch of the sound
is drawn from the level's random numbers. -/
def playSound : M Unit := modify fun l => { l with random := l.random.nextFloat24.2 }

/-- `ShulkerBoxBlockEntity.startOpen(containerUser)`. -/
def startOpen (p : Pos) : M Unit := do
  let some d ← getData p | return
  let openCount := (if d.openCount < 0 then 0 else d.openCount) + 1
  Level.setBlockEntity p (.shulkerBox { d with openCount })
  Level.blockEvent p (← Level.getBlock p).id 1 openCount
  if openCount = 1 then
    Level.gameEvent "minecraft:container_open" p
    playSound

/-- `ShulkerBoxBlockEntity.stopOpen(containerUser)`. -/
def stopOpen (p : Pos) : M Unit := do
  let some d ← getData p | return
  let openCount := d.openCount - 1
  Level.setBlockEntity p (.shulkerBox { d with openCount })
  Level.blockEvent p (← Level.getBlock p).id 1 openCount
  if openCount ≤ 0 then
    Level.gameEvent "minecraft:container_close" p
    playSound

/-- `ShulkerBoxBlockEntity.triggerEvent(b0, b1)`, through `BaseEntityBlock.triggerEvent`: the
event `1` carries the new `openCount` and sets the lid moving. -/
def triggerEvent (self : Block) (p : Pos) (b0 b1 : ℤ) : M Bool := do
  let some d ← getData p | return false
  if b0 ≠ 1 then return false
  let animationStatus : ShulkerBoxAnimationStatus :=
    if b1 = 1 then .opening else if b1 = 0 then .closing else d.animationStatus
  Level.setBlockEntity p (.shulkerBox { d with openCount := b1, animationStatus })
  checkLid self p
  return true

/-- `ShulkerBoxBlockEntity.doNeighborUpdates`. -/
def doNeighborUpdates (self : Block) (p : Pos) : M Unit := do
  Level.updateNeighbourShapes self p 3
  Level.updateNeighborsAt p self.id

/-- What `updateAnimation` makes of the lid in one tick: the new status and progress, and
whether the box calls `doNeighborUpdates`. It does so when the lid leaves an end (`progressOld`
is 0 when opening, 1 when closing) and when it arrives at one; the two never fall into the same
tick, the step being a tenth of the way. -/
def stepLid (status : ShulkerBoxAnimationStatus) (progressOld : ℚ) :
    ShulkerBoxAnimationStatus × ℚ × Bool :=
  match status with
  | .closed => (.closed, 0, false)
  | .opening =>
    let progress := F32.roundFloat (progressOld + BlockEntities.ShulkerBox.lidStep)
    if progress ≥ 1 then (.opened, 1, true) else (.opening, progress, progressOld = 0)
  | .opened => (.opened, 1, false)
  | .closing =>
    let progress := F32.roundFloat (progressOld - BlockEntities.ShulkerBox.lidStep)
    if progress ≤ 0 then (.closed, 0, true) else (.closing, progress, progressOld = 1)

/-- `ShulkerBoxBlockEntity.tick`, that is `updateAnimation(level, pos, state)`: the lid moves a
step. The entities that `moveCollidedEntities` would push are not moved: one that may be in the
way of the opening lid sets `Level.overflow`. A box that stays closed is left untouched. -/
def tick (self : Block) (p : Pos) : M Unit := do
  let some d ← getData p | return
  if d.animationStatus = .closed && d.progress = 0 && d.progressOld = 0 then return
  let (animationStatus, progress, updates) := stepLid d.animationStatus d.progress
  let d' := { d with animationStatus, progress, progressOld := d.progress }
  if d' ≠ d then Level.setBlockEntity p (.shulkerBox d')
  checkLid self p
  if updates then doNeighborUpdates self p
  if d.animationStatus = .opening then
    if let some facing := facing? self then
      if entityNear (← get) (p.step facing) then Level.setOverflow

end Redstone.Component.ShulkerBox
