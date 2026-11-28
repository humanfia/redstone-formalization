module

public import Redstone.Entity.Physics

/-!
# Projectiles

Java classes: `AbstractArrow` (`tick`, `shouldFall`, `tickDespawn`), `Arrow`, `SpectralArrow`.

Only an arrow that is stuck in a block is formalized. Such an arrow does not move; in every
game tick it grows older, and disappears after 1200 ticks, and it tells the blocks its box
reaches that it is inside them (`Redstone.Entity.Touch`), which is how an arrow keeps a wooden
button pressed. An arrow whose position lies inside the collision shape of a block gets stuck
there.

## What is left out

* Flight: an arrow that is not in a block does nothing in the model, and neither does any other
  projectile, so the scenarios in which one flies wait in `tests/pending`. An arrow that lies
  in a block and finds nothing to hold it any more (`shouldFall`) would start to fall
  (`startFalling`): the model sets `Level.overflow`.
* Tridents, whose tick does more (`ThrownTrident`).
* The shaking of an arrow that has just hit (`shakeTime`), fire, and the potion of a tipped
  arrow, which wears off after 600 ticks in the ground.
-/

@[expose] public section

namespace Redstone.Entity.Projectile

/-- The entity types whose tick is that of `AbstractArrow`. -/
def arrowTypes : List String := ["minecraft:arrow", "minecraft:spectral_arrow"]

/-- `EntityType.getDimensions` of an arrow, which is `0.5F` wide and `0.5F` high. -/
def arrowDims : Dimensions := .ofBits 0x3f000000 0x3f000000

/-- `AbstractArrow.shouldFall` for an arrow in the ground: no block collides with the small box
around its position (`new AABB(position, position).inflate(0.06)`). The flag tells that a block
whose collision shape is not modelled was near. -/
def shouldFall (l : Level) (pos : Vec3) : Bool × Bool :=
  let box := (AABB.of pos.x pos.y pos.z pos.x pos.y pos.z).inflate 0.06 0.06 0.06
  let (shapes, unmodelled) := l.blockCollisions box
  (shapes.isEmpty, unmodelled)

/-- `AbstractArrow.tick` for the entity with index `i`, as far as it is modelled. -/
def tick (i : ℕ) : M Unit := do
  let some e := (← get).entity? i | return
  let .projectile type d := e.data | return
  if !arrowTypes.contains type then return
  let l ← get
  let pos := e.base.pos
  let blockPos := pos.blockPos
  let state := l.blockAt blockPos
  -- an arrow inside the collision shape of a block is stuck in it
  if !state.isAir && state.collisionUnmodelled then Level.setOverflow
  let stuck := !state.isAir && !state.collisionUnmodelled &&
    state.collisionShape.boxes.any fun box => (box.atBlock blockPos).contains pos
  let inGround := d.inGround || stuck
  if !inGround then return
  let motion := if stuck then Vec3.zero else e.base.motion
  let (falls, unmodelled) := shouldFall l pos
  if unmodelled then Level.setOverflow
  if falls then
    -- `startFalling`: the arrow flies again
    Level.setOverflow
    return
  -- `tickDespawn`
  let life := d.life + 1
  if life ≥ 1200 then
    Level.removeEntity i
    return
  Level.modifyEntity i fun e =>
    { e with base := { e.base with motion := motion }
             data := .projectile type { d with inGround := true, life := life } }
  -- `applyEffectsFromBlocks`: the arrow made no movement
  Touch.applyEffectsFromBlocks arrowDims i none [⟨pos, pos, none⟩]

/-- The behaviour of the entity. -/
def behaviour : EntityBehaviour := ⟨tick⟩

end Redstone.Entity.Projectile
