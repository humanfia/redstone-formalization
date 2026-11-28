module

public import Redstone.Entity.Physics
public import Redstone.Entity.Item

/-!
# Experience orbs

Java class: `ExperienceOrb`.

An orb falls under gravity, comes to rest on blocks, slides with the friction of the block under
it, is pushed out of a block it is stuck in, and every second takes in the orbs of the same
value around it whose entity id differs from its own by a multiple of 40. After 6000 game ticks
it disappears.

Where orbs come from is not decided here: a broken block and a furnace that is removed release
them through `Level.awardExperience` (`ExperienceOrb.award`), which is in
`Redstone.Mechanics.Update` because breaking a block is.

## What is left out

* Players: an orb follows no player and is picked up by none (`followNearbyPlayer`,
  `playerTouch`). The player of the `use` actions is not in the world.
* Fluids: an orb that touches water or lava sets `Level.overflow`.
* Fire and damage (`hurtServer`): the health of an orb never changes.
* Entities an orb can be stuck in. `Level.noCollision(box)` also looks for entities that can be
  collided with (boats, shulkers); the model only looks at blocks.
* The order in which an orb meets the orbs it merges with is that of the game's entity sections
  (see `Redstone.Entity.Item`, which has the same gap).
-/

@[expose] public section

namespace Redstone.Entity.ExperienceOrb

/-- The kind of entity an orb is: 0.5 wide and high, gravity 0.03, and the block that affects
its movement is the one `0.999999F` under it. -/
def kind : Entity.Kind where
  dims := .ofBits 0x3f000000 0x3f000000
  gravity := Phys.d 0x3f9eb851eb851eb8
  movementOffset := Phys.f 0x3f7fffef

/-- The orb with index `i`, with its data. -/
def get? (i : ℕ) : M (Option (Entity × Entities.ExperienceOrb)) := do
  match (← get).entity? i with
  | some e =>
    match e.data with
    | .experienceOrb dt => return some (e, dt)
    | _ => return none
  | none => return none

/-- Changes the data of the orb with index `i`. -/
def modifyData (i : ℕ) (g : Entities.ExperienceOrb → Entities.ExperienceOrb) : M Unit :=
  Level.modifyEntity i fun e =>
    match e.data with
    | .experienceOrb dt => { e with data := .experienceOrb (g dt) }
    | _ => e

/-- `Entity.moveTowardsClosestSpace(x, y, z)`: an orb stuck inside blocks is pushed towards the
nearest side that is not a full block, at a random speed drawn from its own generator. An orb
that was read from saved data has drawn nothing from it but its UUID. -/
def moveTowardsClosestSpace (i : ℕ) (x y z : Float) : M Unit := do
  let some (e, dt) ← get? i | return
  let l ← get
  let pos : Pos := ⟨Phys.floor x, Phys.floor y, Phys.floor z⟩
  let delta : Vec3 := ⟨x - Phys.ofInt pos.x, y - Phys.ofInt pos.y, z - Phys.ofInt pos.z⟩
  let step (best : Direction × Float) (dir : Direction) : Direction × Float :=
    if !(l.blockAt (pos.step dir)).isCollisionShapeFullBlock then
      let dd := delta.get dir.axis
      let positive := dir == .south || dir == .east || dir == .up
      let oriented := if positive then 1.0 - dd else dd
      if oriented < best.2 then (dir, oriented) else best
    else best
  let (closest, _) := [Direction.north, .south, .west, .east, .up].foldl step
    (Direction.up, Phys.d 0x7fefffffffffffff)
  let (n, r) := (dt.phys.random.getD (Entity.randomAfterUuid e.id)).nextFloat24
  let speed : Float32 :=
    Entity.Item.toFloat32 n * Float32.ofBits 0x3e4ccccd + Float32.ofBits 0x3dcccccd
  let sign : Float32 := if closest == .south || closest == .east || closest == .up then 1 else -1
  let scaled := e.base.motion.mul 0.75 0.75 0.75
  let motion := scaled.set closest.axis (sign * speed).toFloat
  Level.setEntity
    ({ e with base := { e.base with motion := motion } }.modifyPhys fun p =>
      { p with random := some r })

/-- `ExperienceOrb.canMerge(orb, id, value)`, for an orb that is alive: its id differs from `id`
by a multiple of 40, and it has the value `value`. -/
def canMerge (o : Entity) (od : Entities.ExperienceOrb) (id : ℕ) (value : ℤ) : Bool :=
  ((o.id : ℤ) - id) % 40 == 0 && od.value == value

/-- `ExperienceOrb.scanForMerges`: the orb takes in every orb it can merge with whose box meets
its own, widened by half a block on every side. The orbs are found first and merged then, in
the order of the entity sections. -/
def scanForMerges (i : ℕ) : M Unit := do
  let some (e, dt) ← get? i | return
  let area := (kind.dims.box e.base.pos).inflate 0.5 0.5 0.5
  let others := (← get).entities.filter fun o =>
    match o.data with
    | .experienceOrb od =>
      o.index != i && canMerge o od e.id dt.value && (kind.dims.box o.base.pos).intersects area
    | _ => false
  for o in others.foldl (fun acc o => Entity.Item.insertBySection o acc) [] do
    -- `merge(orb)`
    if let some (_, od) ← get? o.index then
      modifyData i fun dt => { dt with count := dt.count + od.count, age := min dt.age od.age }
      Level.removeEntity o.index

/-- `ExperienceOrb.tick`. -/
def tick (i : ℕ) : M Unit := do
  let some (e, _) ← get? i | return
  -- `Entity.baseTick`: fluids are not modelled; below the world the entity is removed
  Level.checkNoFluid kind i
  if e.base.pos.y < -128 then
    Level.removeEntity i
    return
  let tickCount := e.phys.tickCount + 1
  Level.modifyEntity i fun e => e.modifyPhys fun p => { p with tickCount := tickCount }
  let old := e.base.pos
  let box := kind.dims.box e.base.pos
  let (inside, unmodelled) := (← get).blockCollisions box
  if unmodelled then Level.setOverflow
  let colliding := !inside.isEmpty
  if !colliding then Level.applyGravity kind i
  if tickCount % 20 == 1 then scanForMerges i
  -- `followNearbyPlayer`: there is no player
  if colliding then
    let some (e, _) ← get? i | return
    let (next, unmodelled) := (← get).blockCollisions (box.move e.base.motion)
    if unmodelled then Level.setOverflow
    if !next.isEmpty then
      moveTowardsClosestSpace i e.base.pos.x ((box.minY + box.maxY) / 2.0) e.base.pos.z
  let some (e, _) ← get? i | return
  let fallSpeed := e.base.motion.y
  Level.moveEntity kind i e.base.motion
  Level.applyEffectsFromBlocks kind i old
  let some (e, _) ← get? i | return
  let airDrag : Float32 := Float32.ofBits 0x3f7ae148
  let l ← get
  let friction : Float32 :=
    if e.base.onGround then
      airDrag * Float32.ofBits (l.blockAt (Entity.getOnPos l e kind.movementOffset)).frictionBits
    else airDrag
  let motion := e.base.motion.mul friction.toFloat friction.toFloat friction.toFloat
  let gravity := if e.phys.noGravity then 0.0 else kind.gravity
  let motion : Vec3 :=
    if e.phys.verticalCollisionBelow && fallSpeed < -gravity then
      ⟨motion.x, -fallSpeed * Phys.d 0x3fd999999999999a, motion.z⟩
    else motion
  Level.setEntity { e with base := { e.base with motion := motion } }
  let some (_, dt) ← get? i | return
  let age := dt.age + 1
  modifyData i fun dt => { dt with age := age }
  if age ≥ 6000 then Level.removeEntity i

/-- The behaviour of the entity. -/
def behaviour : EntityBehaviour := ⟨tick⟩

end Redstone.Entity.ExperienceOrb
