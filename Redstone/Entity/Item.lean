module

public import Redstone.Entity.Physics
public import Redstone.Block.Generated.Items

/-!
# Dropped items

Java class: `ItemEntity`.

An item falls under gravity, comes to rest on blocks, slides with the friction of the block
under it, and merges with other items of the same kind nearby. After 6000 game ticks it
disappears.

## What is left out

* Fluids: an item that touches water or lava sets `Level.overflow`.
* Fire, damage, portals, and being picked up by players. (Hoppers pick items up: see
  `Redstone.Component.Hopper`.)
* Data components: two stacks of the same item of which one has components are not compared;
  the model sets `Level.overflow` instead of deciding whether they merge.
* The owner of an item (`Owner`), which the game compares before merging.
* The order in which an item meets the items it could merge with is that of the game's entity
  sections, and inside a section the order in which the entities entered it. The model knows
  that order for the entities whose motion it models (`Entities.Physics.sectionEntry`); an item
  that another part of the model creates or moves counts as having been in its section from the
  start.
-/

@[expose] public section

namespace Redstone.Entity.Item

/-- The kind of entity an item is: 0.25 wide and high, gravity 0.04, and the block that affects
its movement is the one `0.999999F` under it. -/
def kind : Entity.Kind where
  dims := ⟨Phys.f 0x3e000000, Phys.f 0x3e800000⟩
  gravity := Phys.d 0x3fa47ae147ae147b
  movementOffset := Phys.f 0x3f7fffef

/-- The item entity with index `i`, with its data. -/
def get? (i : ℕ) : M (Option (Entity × Entities.Item)) := do
  match (← get).entity? i with
  | some e =>
    match e.data with
    | .item dt => return some (e, dt)
    | _ => return none
  | none => return none

/-- Changes the data of the item entity with index `i`. -/
def modifyData (i : ℕ) (g : Entities.Item → Entities.Item) : M Unit :=
  Level.modifyEntity i fun e =>
    match e.data with
    | .item dt => { e with data := .item (g dt) }
    | _ => e

/-- The generator of an item entity after its constructor, which draws `bobOffs` and the
rotation. -/
def initialRandom (id : ℕ) : JavaRandom :=
  let r := Entity.randomAfterUuid id
  let r := r.nextFloat24.2
  r.nextFloat24.2

/-- `RandomSource.nextFloat()` as a `float`. -/
def toFloat32 (n : ℕ) : Float32 := Float32.ofNat n / 16777216

/-- `RandomSource.nextDouble()` as a `double`. -/
def toDouble (n : ℕ) : Float := Float.ofNat n * Phys.d 0x3ca0000000000000

/-- `new ItemEntity(level, x, y, z, stack)` followed by `setDefaultPickUpDelay` and
`addFreshEntity`, as `Entity.spawnAtLocation` does: `count` items of the kind named `item`
appear at `pos` with a random horizontal velocity and cannot be picked up for 10 ticks. `actor`
tells what makes the item, as in `Entities.Physics.sectionEntry`: `0` before the entities are
ticked, `i + 1` in the tick of the entity with index `i`. Returns the index of the new entity. -/
def spawnAtLocation (pos : Vec3) (item : String) (actor : ℕ) (count : ℕ := 1)
    (hasComponents : Bool := false) : M ℕ := do
  let id := (← get).nextEntityIndex + 2
  let r := Entity.randomAfterUuid id
  let r := r.nextFloat24.2
  let (yaw, r) := r.nextFloat24
  let (dx, r) := r.nextDouble53
  let (dz, r) := r.nextDouble53
  let now := (← get).gameTime
  let scale := Phys.d 0x3fc999999999999a
  let shift := Phys.d 0x3fb999999999999a
  let motion : Vec3 := ⟨toDouble dx * scale - shift, scale, toDouble dz * scale - shift⟩
  let data : Entities.Item :=
    { item := item, count := count, hasComponents := hasComponents, pickupDelay := 10
      yRot := (toFloat32 yaw * 360).toBits.toNat
      phys := { random := some r, sectionEntry := (now, actor) } }
  Level.addEntity ⟨pos, motion, false⟩ (.item data)

/-- `new ItemEntity(level, x, y, z, stack)` followed by `setDeltaMovement(motion)` and
`addFreshEntity`, as `DefaultDispenseItemBehavior.spawnItem` and `Containers.dropItemStack` do:
`count` items of the kind named `item` appear at `pos` with the given velocity and can be
picked up at once. The constructor draws the bobbing offset, the rotation and a velocity that
is then replaced from the entity's own generator. `actor` is as in `spawnAtLocation`. Returns
the index of the new entity. -/
def spawnStack (pos motion : Vec3) (item : String) (count : ℕ) (hasComponents : Bool)
    (actor : ℕ := 0) : M ℕ := do
  let id := (← get).nextEntityIndex + 2
  let r := Entity.randomAfterUuid id
  let r := r.nextFloat24.2
  let (yaw, r) := r.nextFloat24
  let r := r.nextDouble53.2
  let r := r.nextDouble53.2
  let now := (← get).gameTime
  let data : Entities.Item :=
    { item := item, count := count, hasComponents := hasComponents
      yRot := (toFloat32 yaw * 360).toBits.toNat
      phys := { random := some r, sectionEntry := (now, actor) } }
  Level.addEntity ⟨pos, motion, false⟩ (.item data)

/-- `Entity.moveTowardsClosestSpace(x, y, z)`: an item stuck inside blocks is pushed towards
the nearest side that is not a full block, at a random speed. -/
def moveTowardsClosestSpace (i : ℕ) (x y z : Float) : M Unit := do
  let some (e, dt) ← get? i | return
  let l ← get
  let pos : Pos := ⟨Phys.floor x, Phys.floor y, Phys.floor z⟩
  let delta : Vec3 := ⟨x - Phys.ofInt pos.x, y - Phys.ofInt pos.y, z - Phys.ofInt pos.z⟩
  let step (best : Direction × Float) (dir : Direction) : Direction × Float :=
    if !l.isCollisionShapeFullBlock (pos.step dir) then
      let dd := delta.get dir.axis
      let positive := dir == .south || dir == .east || dir == .up
      let oriented := if positive then 1.0 - dd else dd
      if oriented < best.2 then (dir, oriented) else best
    else best
  let (closest, _) := [Direction.north, .south, .west, .east, .up].foldl step
    (Direction.up, Phys.d 0x7fefffffffffffff)
  let (n, r) := (dt.phys.random.getD (initialRandom e.id)).nextFloat24
  let speed : Float32 := toFloat32 n * Float32.ofBits 0x3e4ccccd + Float32.ofBits 0x3dcccccd
  let sign : Float32 := if closest == .south || closest == .east || closest == .up then 1 else -1
  let scaled := e.base.motion.mul 0.75 0.75 0.75
  let motion := scaled.set closest.axis (sign * speed).toFloat
  Level.setEntity
    ({ e with base := { e.base with motion := motion } }.modifyPhys fun p =>
      { p with random := some r })

/-- `ItemEntity.isMergable`. -/
def isMergable (dt : Entities.Item) : Bool :=
  dt.pickupDelay != 32767 && dt.age != -32768 && dt.age < 6000 &&
    dt.count < itemMaxStackSize dt.item

/-- `ItemEntity.tryToMerge(other)` for the item entities with indices `i` and `j`: if the two
stacks fit into one, the smaller one is added to the larger one and disappears. -/
def tryToMerge (i j : ℕ) : M Unit := do
  let some (_, a) ← get? i | return
  let some (_, b) ← get? j | return
  if b.count + a.count > itemMaxStackSize b.item then return
  if a.item != b.item then return
  if a.hasComponents || b.hasComponents then
    Level.setOverflow
    return
  -- `merge(to, toStack, from, fromStack)`
  let (dst, toData, src, srcData) := if b.count < a.count then (i, a, j, b) else (j, b, i, a)
  let moved := min (min (itemMaxStackSize toData.item) 64 - toData.count) srcData.count
  modifyData dst fun dt => { dt with
    count := dt.count + moved
    pickupDelay := max toData.pickupDelay srcData.pickupDelay
    age := min toData.age srcData.age }
  modifyData src fun dt => { dt with count := dt.count - moved }
  if srcData.count - moved == 0 then Level.removeEntity src

/-- The place of an entity in the order in which `EntitySectionStorage` goes through the
entities of a region: sections by x, then by z and y, the last two as the unsigned numbers that
`SectionPos.asLong` packs (sections with a negative coordinate come last); inside a section the
entities in the order in which they entered it (see `Entities.Physics.sectionEntry`; entities
that entered at the same moment are in the order of their creation). -/
def sectionKey (e : Entity) : List ℤ :=
  let p := e.base.pos
  let entry := e.phys.sectionEntry
  [Phys.floor p.x / 16, (Phys.floor p.z / 16) % 2 ^ 22, (Phys.floor p.y / 16) % 2 ^ 20,
    entry.1, entry.2, e.index]

/-- Inserts an entity into a list ordered by `sectionKey`. -/
def insertBySection (e : Entity) : List Entity → List Entity
  | [] => [e]
  | o :: os => if sectionKey e < sectionKey o then e :: o :: os else o :: insertBySection e os

/-- `ItemEntity.mergeWithNeighbours`: the item tries to merge with every mergable item whose
box meets its own, widened by half a block on each side. -/
def mergeWithNeighbours (i : ℕ) : M Unit := do
  let some (e, dt) ← get? i | return
  if !isMergable dt then return
  let area := (kind.dims.box e.base.pos).inflate 0.5 0.0 0.5
  let others := (← get).entities.filter fun o =>
    match o.data with
    | .item od => o.index != i && isMergable od && (kind.dims.box o.base.pos).intersects area
    | _ => false
  for o in others.foldl (fun acc o => insertBySection o acc) [] do
    if let some (_, od) ← get? o.index then
      if ((← get? i).isSome) && isMergable od then tryToMerge i o.index

/-- `ItemEntity.tick`. -/
def tick (i : ℕ) : M Unit := do
  let some (e, dt) ← get? i | return
  if dt.count == 0 || dt.item == "minecraft:air" then
    Level.removeEntity i
    return
  -- `Entity.baseTick`: fluids are not modelled; below the world the entity is removed
  Level.checkNoFluid kind i
  if e.base.pos.y < -128 then
    Level.removeEntity i
    return
  let tickCount := e.phys.tickCount + 1
  Level.modifyEntity i fun e => e.modifyPhys fun p => { p with tickCount := tickCount }
  if dt.pickupDelay > 0 && dt.pickupDelay != 32767 then
    modifyData i fun dt => { dt with pickupDelay := dt.pickupDelay - 1 }
  let old := e.base.pos
  Level.applyGravity kind i
  -- `noPhysics`: the item is inside a block
  let some (e, _) ← get? i | return
  let box := kind.dims.box e.base.pos
  let (inside, unmodelled) := (← get).blockCollisions (box.deflate Phys.eps7)
  if unmodelled then Level.setOverflow
  Level.modifyEntity i fun e => e.modifyPhys fun p => { p with noPhysics := !inside.isEmpty }
  if !inside.isEmpty then
    moveTowardsClosestSpace i e.base.pos.x ((box.minY + box.maxY) / 2.0) e.base.pos.z
  let some (e, _) ← get? i | return
  if e.base.onGround && !(e.base.motion.horizontalDistanceSqr > Phys.eps5f) &&
      (tickCount + e.id) % 4 != 0 then
    Level.applyEffectsFromBlocksForLastMovements kind i
  else
    Level.moveEntity kind i e.base.motion
    Level.applyEffectsFromBlocks kind i old
    let some (e, _) ← get? i | return
    let airDrag : Float32 := Float32.ofBits 0x3f7ae148
    let l ← get
    let groundFriction : Float32 :=
      if e.base.onGround then
        airDrag * Float32.ofBits (l.blockAt (Entity.getOnPos l e kind.movementOffset)).frictionBits
      else airDrag
    let motion := e.base.motion.mul groundFriction.toFloat airDrag.toFloat groundFriction.toFloat
    let motion := if e.base.onGround && motion.y < 0 then motion.mul 1.0 (-0.5) 1.0 else motion
    Level.setEntity { e with base := { e.base with motion := motion } }
  let some (e, dt) ← get? i | return
  let moved := Phys.floor old.x != Phys.floor e.base.pos.x ||
    Phys.floor old.y != Phys.floor e.base.pos.y || Phys.floor old.z != Phys.floor e.base.pos.z
  let rate := if moved then 2 else 40
  if tickCount % rate == 0 && isMergable dt then mergeWithNeighbours i
  let some (_, dt) ← get? i | return
  let age := if dt.age != -32768 then dt.age + 1 else dt.age
  modifyData i fun dt => { dt with age := age }
  if age ≥ 6000 then Level.removeEntity i

/-- The behaviour of the entity. -/
def behaviour : EntityBehaviour := ⟨tick⟩

end Redstone.Entity.Item
