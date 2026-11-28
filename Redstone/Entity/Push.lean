module

public import Redstone.Mechanics.Tick
public import Redstone.Entity.Geometry
public import Redstone.Entity.Tnt.JavaMath

/-!
# Entities that meet entities

Java classes: `Entity` (`push`, `collide`, `canCollideWith`, `canBeCollidedWith`, `isPushable`),
`EntityGetter.getEntityCollisions`, `EntitySectionStorage` and `EntitySection` (the order of
`Level.getEntities`), `AbstractMinecart` (`push`, `pushOtherMinecart`, `canCollideWith`),
`OldMinecartBehavior.pushAndPickupEntities`, `AbstractBoat.canVehicleCollide`, `Mth.sin`.

Two things happen between entities here.

* An entity that moves is stopped by the boxes of the entities it can collide with
  (`entityColliders`), exactly as by the collision shapes of blocks: `Entity.collide` puts the
  boxes of these entities in front of the shapes of the blocks. An entity that is no vehicle
  (an item, a falling block) collides with the entities that say `canBeCollidedWith`: boats and
  rafts, shulkers and grown happy ghasts. A minecart collides with these and with every entity
  that is pushable, which includes the other minecarts.
* At the end of its tick a minecart pushes the minecarts within a fifth of a block of its box
  (`pushAndPickupEntities`, `minecartPush`, `pushOtherMinecart`): two minecarts in line share
  their velocities, and a furnace minecart drives the one in front of it.

The search for entities goes through the entity sections in the order of the game, and through
the entities of a section in the order in which they entered it (`sectionKey`), so that pushes
and collisions happen in the order of the server.

## What is assumed

* A shulker is closed and a happy ghast cannot be told from its young: the model keeps neither
  the peek of a shulker nor the age of a mob. A closed shulker is the cube around its position;
  a happy ghast in the way sets `Level.overflow`.
* A boat or a raft has the box of its type at its position, which is so as long as it is at rest
  (boats that move are not modelled).

## What is left out

* Passengers. A minecart that is fast enough picks up the mob or the boat it touches, and
  entities that ride each other do not collide. The model has no passengers: the minecart
  module sets `Level.overflow` when an entity that could be picked up is within reach
  (`Redstone.Entity.Minecart.entityGuard`).
* Living entities and boats as actors: a mob pushes the minecart in its box and is pushed back,
  a boat pushes what is next to it, and both are obstacles to a minecart. None of them has a
  modelled motion, so the minecart module sets `Level.overflow` for them; here they are neither
  pushed nor, the boats and shulkers apart, obstacles.
* The box of an entity that lies in the unit cube at the origin of the world on the grid of
  eighths (`Shapes.create` snaps such a box to the grid, with a tolerance): `Level.overflow`,
  unless it is the cube itself.
* Scoreboard teams (`EntitySelector.pushableBy`) and spectators: there are none.
* Primed TNT does not look for entities in its way yet (`Redstone.Entity.PrimedTnt` has its own
  copy of `Entity.collide`).

Scenarios that wait in `tests/pending/scenarios/entity-collisions` for one of these:
`cart-picks-up-mob` (a passenger), `chest-cart-stops-at-mob` (a mob as an obstacle: whether a
mob is pushable depends on its species and state), `cart-meets-boat` (the boat is pushed and
moves), `stand-pushes-cart` (the armour stand is pushed back and moves) and
`item-meets-happy-ghast`.
-/

@[expose] public section

namespace Redstone.Entity.Push

/-! ### `Mth.sin` -/

/-- `Mth.SIN[index]`: the table of 65536 sines of the game, `(float)Math.sin(i /
10430.378350470453)`, with the `Math.sin` of the virtual machine. -/
def sinTable (index : ℕ) : Float32 :=
  (Tnt.JavaMath.sin (Float.ofNat index / Float.ofBits 0x40c45f306dc9c883)).toFloat32

/-- The index of the table for an angle that was scaled: `(int)((long)v & 65535L)`. -/
def sinIndex (v : Float) : ℕ := (v.toInt64.toInt % 65536).toNat

/-- `Mth.sin(double)`. -/
def mthSin (x : Float) : Float32 := sinTable (sinIndex (x * Float.ofBits 0x40c45f306dc9c883))

/-- `Mth.cos(double)`. -/
def mthCos (x : Float) : Float32 :=
  sinTable (sinIndex (x * Float.ofBits 0x40c45f306dc9c883 + 16384.0))

/-! ### The entities in a box -/

/-- `EntityType.getDimensions` of a minecart of any kind: `0.98F` wide and `0.7F` high. -/
def minecartDims : Dimensions := .ofBits 0x3f7ae148 0x3f333333

/-- `EntityType.getDimensions` of a boat or a raft: `1.375F` wide and `0.5625F` high. -/
def boatDims : Dimensions := .ofBits 0x3fb00000 0x3f100000

/-- The size of a closed shulker (`Shulker.makeBoundingBox` with no peek): a cube. -/
def shulkerDims : Dimensions := ⟨0.5, 1.0⟩

/-- `EntityType.getDimensions` of a happy ghast: four blocks wide and high. -/
def happyGhastDims : Dimensions := ⟨2.0, 4.0⟩

/-- The entity is a boat or a raft, with or without a chest (`AbstractBoat`). -/
def isBoat (e : Entity) : Bool :=
  match e.data with
  | .other type _ => type.endsWith "_boat" || type.endsWith "_raft"
  | _ => false

/-- `Entity.getBoundingBox()` of a minecart. -/
def minecartBox? (e : Entity) : Option AABB :=
  match e.data with
  | .minecart _ _ => some (minecartDims.box e.base.pos)
  | _ => none

/-- When the entity was last put into the entity section it is in
(`Entities.Physics.sectionEntry`), for the kinds of entity that keep it. An entity of another
kind counts as having been in its section from the start. -/
def sectionEntry (e : Entity) : ℕ × ℕ :=
  match e.data with
  | .item d => d.phys.sectionEntry
  | .fallingBlock d => d.phys.sectionEntry
  | .minecart _ d => d.sectionEntry
  | _ => (0, 0)

/-- `SectionPos.posToSectionCoord(double)`: the coordinate of the 16-block section of `v`. -/
def sectionCoord (v : Float) : ℤ := (Phys.floor v).fdiv 16

/-- The entity section a point lies in (`SectionPos.of(BlockPos.containing(p))`). -/
def sectionOf (p : Vec3) : ℤ × ℤ × ℤ := (sectionCoord p.x, sectionCoord p.y, sectionCoord p.z)

/-- The place of an entity in the order in which `EntitySectionStorage` goes through the
entities of a region: sections by x, then by z and y, the last two as the unsigned numbers that
`SectionPos.asLong` packs (sections with a negative coordinate come last); inside a section the
entities in the order in which they entered it (`EntitySection.storage` is a list; entities that
entered at the same moment are in the order of their creation). -/
def sectionKey (e : Entity) : List ℤ :=
  let p := e.base.pos
  let entry := sectionEntry e
  [sectionCoord p.x, sectionCoord p.z % 2 ^ 22, sectionCoord p.y % 2 ^ 20, entry.1, entry.2,
    e.index]

/-- `EntitySectionStorage.forEachAccessibleNonEmptySection(box, ...)`: the entity search only
looks at the sections that the box, grown by 2 blocks horizontally and by 4 blocks downwards,
reaches; an entity is stored in the section of its position. -/
def inSearchedSections (pos : Vec3) (box : AABB) : Bool :=
  let within (lo v hi : Float) : Bool :=
    sectionCoord lo ≤ sectionCoord v && sectionCoord v ≤ sectionCoord hi
  within (box.minX - 2.0) pos.x (box.maxX + 2.0) &&
    within (box.minY - 4.0) pos.y (box.maxY + 0.0) &&
    within (box.minZ - 2.0) pos.z (box.maxZ + 2.0)

/-- Inserts an entity into a list ordered by `sectionKey`. -/
def insertBySection (e : Entity × AABB) : List (Entity × AABB) → List (Entity × AABB)
  | [] => [e]
  | o :: os => if sectionKey e.1 < sectionKey o.1 then e :: o :: os else o :: insertBySection e os

/-- `Level.getEntities(except, box, predicate)`: the entities other than the one with index
`except` whose bounding box meets `box`, in the order in which the game finds them, each with
its box. `boxOf` is the predicate and the bounding box in one: it gives the box of an entity that
passes. -/
def getEntities (l : Level) (except : ℕ) (box : AABB) (boxOf : Entity → Option AABB) :
    List (Entity × AABB) :=
  let found := l.entities.filterMap fun e =>
    if e.index == except then none
    else
      match boxOf e with
      | some b =>
        if inSearchedSections e.base.pos box && b.intersects box then some (e, b) else none
      | none => none
  found.foldl (fun acc e => insertBySection e acc) []

/-! ### Entities as obstacles -/

/-- An entity that stands in the way of the one that asks, with its box. `known` is false when
the model cannot tell whether the entity is an obstacle, or what its box is. -/
structure Obstacle where
  box : AABB
  known : Bool := true

/-- `source.canCollideWith(e)` with the box of `e`, for a source that is a vehicle (a minecart:
`AbstractBoat.canVehicleCollide`, which also takes the pushable entities) or not
(`e.canBeCollidedWith(source)`). Boats, rafts and shulkers can be collided with, and so can a
happy ghast that is grown; minecarts are pushable. The living entities, which a minecart
collides with as well when they are pushable, are left to the minecart module. -/
def obstacle? (vehicle : Bool) (e : Entity) : Option Obstacle :=
  match e.data with
  | .minecart _ _ => if vehicle then some ⟨minecartDims.box e.base.pos, true⟩ else none
  | .other type _ =>
    if isBoat e then some ⟨boatDims.box e.base.pos, true⟩
    else if type == "minecraft:shulker" then some ⟨shulkerDims.box e.base.pos, true⟩
    else if type == "minecraft:happy_ghast" then some ⟨happyGhastDims.box e.base.pos, false⟩
    else none
  | _ => none

/-- `Shapes.create(box)` may snap the box to the grid of a block: the box lies in the unit cube
at the origin, within the tolerance of `Shapes.findBits`, and is not that cube. -/
def snapsToGrid (b : AABB) : Bool :=
  let inUnit (lo hi : Float) : Bool :=
    !(lo < -Phys.eps7) && !(hi > Float.ofBits 0x3ff000001ad7f29b)
  inUnit b.minX b.maxX && inUnit b.minY b.maxY && inUnit b.minZ b.maxZ &&
    !(b.minX == 0 && b.minY == 0 && b.minZ == 0 && b.maxX == 1 && b.maxY == 1 && b.maxZ == 1)

/-- `Level.getEntityCollisions(source, area)`: the boxes of the entities that the entity with
index `source` can collide with and that meet `area`, grown by `1.0E-7`, in the order in which
the game finds them. The flag tells that one of them is not modelled. -/
def entityColliders (l : Level) (source : ℕ) (vehicle : Bool) (area : AABB) : List AABB × Bool :=
  -- `AABB.getSize()`
  if (area.size .x + area.size .y + area.size .z) / 3.0 < Phys.eps7 then ([], false)
  else
    let found := getEntities l source (area.inflate Phys.eps7 Phys.eps7 Phys.eps7)
      fun e => (obstacle? vehicle e).map (·.box)
    (found.map (·.2),
      found.any fun (e, b) => snapsToGrid b || !((obstacle? vehicle e).any (·.known)))

/-! ### Pushing -/

/-- `Vec3.normalize()`. -/
def normalize (v : Vec3) : Vec3 :=
  let dist := v.lengthSqr.sqrt
  if dist < Phys.eps5f then .zero else ⟨v.x / dist, v.y / dist, v.z / dist⟩

/-- `Entity.setDeltaMovement` for the entity with the given index. -/
def setMotion (index : ℕ) (v : Vec3) : M Unit :=
  Level.modifyEntity index fun e => { e with base := { e.base with motion := v } }

/-- `Entity.push(xa, ya, za)` for the entity with the given index: the push is added to its
velocity, unless it is not finite. -/
def pushBy (index : ℕ) (xa ya za : Float) : M Unit :=
  if xa.isFinite && ya.isFinite && za.isFinite then
    Level.modifyEntity index fun e =>
      { e with base := { e.base with motion := e.base.motion.add ⟨xa, ya, za⟩ } }
  else pure ()

/-- `AbstractMinecart.pushOtherMinecart(otherMinecart, xa, za)`, called on the minecart with
index `this`. Nothing happens unless the other minecart lies along the way this one faces (the
cosine of the angle is `0.8F` or more). Then two minecarts of which neither or both are furnace
minecarts share the mean of their velocities and are pushed apart; a furnace minecart keeps
`0.95` of its velocity and gives it to the other one. -/
def pushOtherMinecart (this other : ℕ) (xa za : Float) : M Unit := do
  let l ← get
  let some t := l.entity? this | return
  let some o := l.entity? other | return
  let .minecart tKind td := t.data | return
  let .minecart oKind _ := o.data | return
  let xo := o.base.pos.x - t.base.pos.x
  let zo := o.base.pos.z - t.base.pos.z
  let dir := normalize ⟨xo, 0.0, zo⟩
  -- `getYRot() * (float)(Math.PI / 180.0)`
  let angle := (td.yRot * Float32.ofBits 0x3c8efa35).toFloat
  let facing := normalize ⟨(mthCos angle).toFloat, 0.0, (mthSin angle).toFloat⟩
  let dot := (dir.x * facing.x + dir.y * facing.y + dir.z * facing.z).abs
  if !(dot < Phys.f 0x3f4ccccd) then
    let movement := t.base.motion
    let entityMovement := o.base.motion
    let slow := Phys.d 0x3fc999999999999a
    let keep := Phys.d 0x3fee666666666666
    if oKind == .furnace && tKind != .furnace then
      setMotion this (movement.mul slow 1.0 slow)
      pushBy this (entityMovement.x - xa) 0.0 (entityMovement.z - za)
      setMotion other (entityMovement.mul keep 1.0 keep)
    else if oKind != .furnace && tKind == .furnace then
      setMotion other (entityMovement.mul slow 1.0 slow)
      pushBy other (movement.x + xa) 0.0 (movement.z + za)
      setMotion this (movement.mul keep 1.0 keep)
    else
      let xdd := (entityMovement.x + movement.x) / 2.0
      let zdd := (entityMovement.z + movement.z) / 2.0
      setMotion this (movement.mul slow 1.0 slow)
      pushBy this (xdd - xa) 0.0 (zdd - za)
      setMotion other (entityMovement.mul slow 1.0 slow)
      pushBy other (xdd + xa) 0.0 (zdd + za)

/-- `AbstractMinecart.push(entity)`, called on the minecart with index `this`: the two are
pushed apart along the line between them, the harder the nearer they are, unless they are in
the same place. Only another minecart is modelled as the entity that pushes; anything else
(`this.push(-xa, 0.0, -za)` and `entity.push(xa / 4.0, 0.0, za / 4.0)`) moves an entity whose
motion the model does not follow, and sets `Level.overflow`. -/
def minecartPush (this entity : ℕ) : M Unit := do
  let l ← get
  let some t := l.entity? this | return
  let some e := l.entity? entity | return
  let xa := e.base.pos.x - t.base.pos.x
  let za := e.base.pos.z - t.base.pos.z
  let dd := xa * xa + za * za
  if dd ≥ Phys.f 0x38d1b717 then
    let dd := dd.sqrt
    let xa := xa / dd
    let za := za / dd
    let pow := 1.0 / dd
    let pow := if pow > 1.0 then 1.0 else pow
    let xa := xa * pow * Phys.f 0x3dcccccd * 0.5
    let za := za * pow * Phys.f 0x3dcccccd * 0.5
    match e.data with
    | .minecart _ _ => pushOtherMinecart this entity xa za
    | _ =>
      pushBy this (-xa) 0.0 (-za)
      pushBy entity (xa / 4.0) 0.0 (za / 4.0)
      Level.setOverflow

/-- The box in which a minecart looks for entities to push or to pick up
(`getBoundingBox().inflate(0.2F, 0.0, 0.2F)`). -/
def hitbox (pos : Vec3) : AABB :=
  (minecartDims.box pos).inflate (Phys.f 0x3e4ccccd) 0.0 (Phys.f 0x3e4ccccd)

/-- `OldMinecartBehavior.pushAndPickupEntities()` for the minecart with index `index`, as far
as minecarts go: every minecart whose box meets the hit box of this one pushes it
(`entity.push(this.minecart)`), in the order in which the game finds them. Both branches of the
game do this to a minecart. What they do to the other entities (a plain minecart that is fast
picks up the mobs and boats it reaches, and is pushed by an iron golem) is not modelled; the
minecart module looks for such entities itself. -/
def pushAndPickupEntities (index : ℕ) : M Unit := do
  let l ← get
  let some c := l.entity? index | return
  for (other, _) in getEntities l index (hitbox c.base.pos) minecartBox? do
    minecartPush other.index index

end Redstone.Entity.Push
