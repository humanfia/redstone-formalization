module

public import Redstone.Entity.Clip
public import Redstone.Entity.Still

/-!
# Projectiles

Java classes: `Projectile` (`tick`, `hitTargetOrDeflectSelf`, `onHit`, `onHitBlock`),
`AbstractArrow` (`tick`, `stepMoveAndHit`, `onHitBlock`, `shouldFall`, `startFalling`,
`tickDespawn`), `Arrow`, `SpectralArrow`, `ThrownTrident`, `ThrowableProjectile` (`tick`),
`Snowball`, `ThrownEgg`, `ProjectileUtil` (`getHitResultOnMoveVector`), `Entity` (`baseTick`).

Arrows, spectral arrows, tridents, snowballs and eggs fly. In every game tick a projectile
follows the segment of its velocity through the blocks (`Level.clip`, `Redstone.Entity.Clip`),
tells the blocks on its way that it is inside them (`Redstone.Entity.Touch`, which is how a
flying arrow presses a wooden button, a wooden pressure plate or a tripwire), slows down by the
drag of the air and speeds up by gravity. When the segment meets the collision shape of a block,
the block is told where and on which face it was hit (`Behaviour.onProjectileHit`), and the game
event `projectile_land` is sent. An arrow then stays in the block: it is put a twentieth of a
block back from the point of the hit, stops, and from then on grows older until it disappears
after 1200 ticks. When the block that holds it is gone (`shouldFall`), the arrow starts to fall
again (`startFalling`). A snowball or an egg disappears when it hits.

An arrow whose position lies inside the collision shape of a block gets stuck there.

The numbers a projectile draws come from its own generator (`Entity.random`), which the test
harness seeds from the id of the entity (`Entity.randomAfterUuid`): an arrow draws one for the
pitch of the sound of every hit and three when it starts to fall, an egg draws one to decide
whether it hatches.

## What is left out

* Hits on entities. Whenever the way of a projectile meets the box of an entity it could hit
  (`Entity.canBeHitByProjectile`: minecarts, falling blocks, primed TNT, item frames, mobs,
  fireballs), the model sets `Level.overflow`.
* A trident is an arrow here: its owner (loyalty) and its enchantments (channeling, which calls
  lightning on a rod) are not modelled.
* Every other projectile: ender pearls, potions, experience bottles, fireworks, fireballs and
  wind charges do nothing in the model. One that has a velocity sets
  `Level.overflow`; one without is left where it is, which is right for a fireball at rest and
  wrong for whatever gravity pulls.
* Fluids: a projectile whose box touches a fluid sets `Level.overflow` (water slows it down and
  puts out its fire, bubble columns push it). So does a burning projectile while it rains.
* An egg that hatches (one in eight): the chicken is a mob, and the model sets
  `Level.overflow`.
* The owner of a projectile (`leftOwner`, statistics, advancements, the sender of vibrations),
  the rotation, critical arrows, the pierce level and enchanted weapons, the world border
  (`clipIncludingBorder`), portals, and `noPhysics` (a trident coming back).
* A block of amethyst chimes when it is hit, at a pitch drawn from the generator of the level
  (`AmethystBlock.onProjectileHit`): the draw is made here, since the block has no behaviour of
  its own.
* Blocks that set an entity on fire as it passes (fire, lava) do not light a projectile.

## Scenarios that wait in `tests/pending/scenarios/projectile`

* `egg-hatches-*`: the egg hatches, and the chicken is a mob.
* `pot-*`: a projectile shatters a decorated pot. The pot does what the game does
  (`Component.AnalogSource.decoratedPot`), but the loot of a pot is not evaluated yet
  (`Level.getDrops`), so the model stops at `Level.overflow`.
* `sculk-*`: a sculk sensor hears the shot or the landing. A game event of the model has the
  centre of a block as its origin, where the game has the position of the projectile, and the
  vibration of the game records the UUID of the projectile, which the model does not have.
-/

@[expose] public section

namespace Redstone.Entity.Projectile

/-- The entity types whose tick is that of `AbstractArrow`. A trident is one of them as long as
it has no owner to return to and no enchantment, which is all the model knows of a trident. -/
def arrowTypes : List String :=
  ["minecraft:arrow", "minecraft:spectral_arrow", "minecraft:trident"]

/-- The entity types whose tick is that of `ThrowableProjectile` and that disappear on a hit
without doing more to blocks. -/
def throwableTypes : List String := ["minecraft:snowball", "minecraft:egg"]

/-- `EntityType.getDimensions` of an arrow, which is `0.5F` wide and `0.5F` high. -/
def arrowDims : Dimensions := .ofBits 0x3f000000 0x3f000000

/-- `EntityType.getDimensions` of a snowball or an egg: `0.25F` wide and `0.25F` high. -/
def throwableDims : Dimensions := .ofBits 0x3e800000 0x3e800000

/-- `0.99F`, the drag of the air on a projectile (`getAirDrag`), as a `double`. -/
def airDrag : Float := Phys.f 0x3f7d70a4

/-- The projectile with index `i`: the entity, its type and its data. -/
def get? (i : ℕ) : M (Option (Entity × String × Entities.Projectile)) := do
  match (← get).entity? i with
  | some e =>
    match e.data with
    | .projectile type d => return some (e, type, d)
    | _ => return none
  | none => return none

/-- Changes the data of the projectile with index `i`. -/
def modifyData (i : ℕ) (g : Entities.Projectile → Entities.Projectile) : M Unit :=
  Level.modifyEntity i fun e =>
    match e.data with
    | .projectile type d => { e with data := .projectile type (g d) }
    | _ => e

/-- `Entity.setPos(pos)` for the entity with index `i`. -/
def setPos (i : ℕ) (pos : Vec3) : M Unit :=
  Level.modifyEntity i fun e => { e with base := { e.base with pos := pos } }

/-- `Entity.setDeltaMovement(motion)` for the entity with index `i`. -/
def setMotion (i : ℕ) (motion : Vec3) : M Unit :=
  Level.modifyEntity i fun e => { e with base := { e.base with motion := motion } }

/-- The projectile's own generator (`Entity.random`). -/
def random (e : Entity) (d : Entities.Projectile) : JavaRandom :=
  d.random.getD (Entity.randomAfterUuid e.id)

/-- `RandomSource.nextFloat()` of the generator of the projectile with index `i`, as the
numerator of a fraction with denominator `2 ^ 24`. -/
def nextFloat (i : ℕ) : M ℕ := do
  let some (e, _, d) ← get? i | return 0
  let (n, r) := (random e d).nextFloat24
  modifyData i fun d => { d with random := some r }
  return n

/-- `Entity.isPickable()` as far as the model can tell: what a projectile can hit. Items,
experience orbs, lightning and the projectiles that cannot be redirected are not pickable. -/
def isPickable (e : Entity) : Bool :=
  match e.data with
  | .item _ | .experienceOrb _ | .lightning _ => false
  | .projectile type _ =>
    type ∈ ["minecraft:fireball", "minecraft:small_fireball", "minecraft:wind_charge",
      "minecraft:breeze_wind_charge", "minecraft:dragon_fireball", "minecraft:wither_skull"]
  | .other type d => !(type == "minecraft:marker" || type == "minecraft:area_effect_cloud" ||
      type == "minecraft:interaction" || type.endsWith "_display" ||
      (type == "minecraft:armor_stand" && d.marker))
  | _ => true

/-- `ProjectileUtil.computeMargin(source)`: how much the box of an entity is widened for a
projectile that has been ticked `tickCount` times, as a `double`. -/
def computeMargin (tickCount : ℕ) : Float :=
  let m : Float32 := (Float32.ofNat tickCount - 2) / 20
  let m := if m ≤ Float32.ofBits 0x3e99999a then m else Float32.ofBits 0x3e99999a
  (if m ≥ 0 then m else 0).toFloat

/-- The entity search of `ProjectileUtil.getEntityHitResult` (for a thrown projectile) and of
`ProjectileUtil.getManyEntityHitResult` (for an arrow, if `arrow`) for the projectile with
index `i`, whose way goes from `start` to `stop`: an entity that can be hit lies in `area`, and
the way enters its box, or its box widened by `margin`. An entity of unknown size counts as
met. For an arrow the game then looks whether the entity can be reached from the point on the
widened box; here it always can. Hits on entities are not modelled; the caller sets
`Level.overflow`. -/
def meetsEntity (l : Level) (i : ℕ) (area : AABB) (start stop : Vec3) (margin : Float)
    (arrow : Bool) : Bool :=
  l.entities.any fun o =>
    o.index != i && isPickable o &&
      match Still.boundingBox? o with
      | none => true
      | some box =>
        box.intersects area &&
          ((arrow && (box.clip start stop).isSome) ||
            ((!arrow || margin > 0.0) &&
              ((box.inflate margin margin margin).clip start stop).isSome))

/-- The block the entity with index `i` steps on (`getOnPosLegacy`), if it is on the ground. -/
def effectPos (i : ℕ) : M (Option Pos) := do
  let l ← get
  let some e := l.entity? i | return none
  return if e.base.onGround then some (Entity.getOnPosLegacy l e) else none

/-- `Projectile.tick`, after the subclass has moved the projectile: the game event of the shot,
once, and then `Entity.baseTick`, in which a burning projectile burns down and a projectile
that fell out of the world is removed. -/
def baseTick (dims : Dimensions) (i : ℕ) : M Unit := do
  let some (e, _, d) ← get? i | return
  if !d.hasBeenShot then
    Level.gameEvent "minecraft:projectile_shoot" e.base.pos.blockPos
    modifyData i fun d => { d with hasBeenShot := true }
  if (← get).touchesFluid (dims.box e.base.pos) then Level.setOverflow
  modifyData i fun d =>
    { d with fire := if d.fire > 0 then d.fire - 1 else d.fire, firstTick := false }
  -- `checkBelowWorld`
  if e.base.pos.y < -128 then Level.removeEntity i

/-- `Projectile.onHitBlock(hitResult)`: the block that was hit is told. -/
def onHitBlock (i : ℕ) (hit : BlockHitResult) : M Unit := do
  let state ← Level.getBlock hit.blockPos
  if state.is .amethyst_block || state.is .budding_amethyst then
    -- `AmethystBlock.onProjectileHit`: the pitch of the chime
    modify fun l => { l with random := l.random.nextFloat24.2 }
  (← Level.behaviour state).onProjectileHit hit.blockPos hit.direction hit.location i

/-- The end of `Projectile.onHit(hitResult)` for a block: the game event of the landing. -/
def landed (i : ℕ) (hit : BlockHitResult) : M Unit := do
  Level.gameEvent "minecraft:projectile_land" hit.blockPos
    { sourceEntity := some (.entity i), affectedState := some (← Level.getBlock hit.blockPos) }

/-! ### Arrows -/

/-- `AbstractArrow.shouldFall` for an arrow in the ground: no block collides with the small box
around its position (`new AABB(position, position).inflate(0.06)`). The flag tells that a block
whose collision shape is not modelled was near. -/
def shouldFall (l : Level) (pos : Vec3) : Bool × Bool :=
  let box := (AABB.of pos.x pos.y pos.z pos.x pos.y pos.z).inflate 0.06 0.06 0.06
  let (shapes, unmodelled) := l.blockCollisions box
  (shapes.isEmpty, unmodelled)

/-- `RandomSource.nextFloat() * 0.2F`, as a `double`. -/
def fallFactor (n : ℕ) : Float := (Float32.ofNat n / 16777216 * Float32.ofBits 0x3e4ccccd).toFloat

/-- `AbstractArrow.startFalling`: the arrow is no longer in the ground, keeps a random part of
its velocity, and is young again. -/
def startFalling (i : ℕ) : M Unit := do
  let x ← nextFloat i
  let y ← nextFloat i
  let z ← nextFloat i
  Level.modifyEntity i fun e =>
    { e with base := { e.base with
        motion := e.base.motion.mul (fallFactor x) (fallFactor y) (fallFactor z) } }
  modifyData i fun d => { d with inGround := false, life := 0 }

/-- `AbstractArrow.onHitBlock(hitResult)` and the rest of `Projectile.onHit`: the block is told,
then the arrow backs out a twentieth of a block against its velocity, stops and is in the
ground. -/
def arrowOnHit (i : ℕ) (hit : BlockHitResult) : M Unit := do
  let lastState ← Level.getBlock hit.blockPos
  modifyData i fun d => { d with lastState := some lastState }
  onHitBlock i hit
  let some (e, _, _) ← get? i | return
  let movement := e.base.motion
  -- `new Vec3(signum(x), signum(y), signum(z)).scale(0.05F)`
  let back (v : Float) : Float :=
    if v > 0.0 then Phys.f 0x3d4ccccd else if v < 0.0 then -Phys.f 0x3d4ccccd else 0.0
  setPos i (e.base.pos.sub ⟨back movement.x, back movement.y, back movement.z⟩)
  setMotion i .zero
  -- the pitch of the sound
  discard <| nextFloat i
  modifyData i fun d => { d with inGround := true, shake := 7 }
  landed i hit

/-- The part of `AbstractArrow.tick` for an arrow that flies: `stepMoveAndHit` along the
velocity, the drag of the air, gravity, and `Projectile.tick`. -/
def arrowFly (i : ℕ) : M Unit := do
  let some (e, _, d) ← get? i | return
  let l ← get
  let start := e.base.pos
  let movement := e.base.motion
  if l.touchesFluid (arrowDims.box start) then Level.setOverflow
  let (hit, unmodelled) := l.clip start (start.add movement)
  if unmodelled then Level.setOverflow
  -- `stepMoveAndHit`
  let area := ((arrowDims.box start).expandTowards movement).inflate 1.0 1.0 1.0
  if meetsEntity l i area start hit.location (computeMargin d.tickCount) true then
    Level.setOverflow
  setPos i hit.location
  Touch.applyEffectsFromBlocks arrowDims i (← effectPos i) [⟨start, hit.location, none⟩]
  if ((← get? i).isSome) && !hit.miss then
    -- `hitTargetOrDeflectSelf`
    if !(← Level.getBlock hit.blockPos).isAir then arrowOnHit i hit
  let some (e, _, d) ← get? i | return
  setMotion i (e.base.motion.mul airDrag airDrag airDrag)
  if !d.inGround && !d.noGravity then
    Level.modifyEntity i fun e =>
      { e with base := { e.base with motion := e.base.motion.add ⟨0.0, -0.05, 0.0⟩ } }
  baseTick arrowDims i

/-- `AbstractArrow.tick` for the entity with index `i`. -/
def arrowTick (i : ℕ) : M Unit := do
  let some (e, _, d) ← get? i | return
  let l ← get
  let pos := e.base.pos
  let blockPos := pos.blockPos
  let blockState := l.blockAt blockPos
  -- an arrow inside the collision shape of a block is stuck in it
  if !blockState.isAir && blockState.collisionUnmodelled then Level.setOverflow
  let stuck := !blockState.isAir && !blockState.collisionUnmodelled &&
    blockState.collisionShape.boxes.any fun box => (box.atBlock blockPos).contains pos
  if stuck then
    setMotion i .zero
    -- `onSyncedDataUpdated`: an arrow that has been ticked before starts to shake
    let shakes := !d.inGround && !d.firstTick && d.shake ≤ 0
    modifyData i fun d => { d with inGround := true, shake := if shakes then 7 else d.shake }
  modifyData i fun d =>
    { d with shake := if d.shake > 0 then d.shake - 1 else d.shake, tickCount := d.tickCount + 1 }
  -- `isInWaterOrRain`: water or rain would put out the fire
  if d.fire > 0 && (l.weather != .clear || l.touchesFluid (arrowDims.box pos)) then
    Level.setOverflow
  if d.inGround || stuck then
    let falls ←
      if d.lastState == some blockState then pure false
      else
        let (falls, unmodelled) := shouldFall l pos
        if unmodelled then Level.setOverflow
        pure falls
    if falls then startFalling i
    else
      -- `tickDespawn`
      if d.life + 1 ≥ 1200 then
        Level.removeEntity i
        return
      modifyData i fun d => { d with life := d.life + 1 }
    -- `applyEffectsFromBlocks`: the arrow made no movement
    Touch.applyEffectsFromBlocks arrowDims i (← effectPos i) [⟨pos, pos, none⟩]
  else arrowFly i

/-! ### Snowballs and eggs -/

/-- `ThrowableProjectile.tick` for the entity with index `i`, with `Snowball.onHit` and
`ThrownEgg.onHit`. -/
def throwableTick (i : ℕ) : M Unit := do
  let some (e, type, d) ← get? i | return
  let l ← get
  let start := e.base.pos
  -- `handleFirstTickBubbleColumn`, and the water of `applyInertia`
  if l.touchesFluid (throwableDims.box start) then Level.setOverflow
  if d.fire > 0 && l.weather != .clear then Level.setOverflow
  -- `applyGravity`, `applyInertia`
  let movement := if d.noGravity then e.base.motion else e.base.motion.add ⟨0.0, -0.03, 0.0⟩
  let movement := movement.mul airDrag airDrag airDrag
  setMotion i movement
  modifyData i fun d => { d with tickCount := d.tickCount + 1 }
  -- `ProjectileUtil.getHitResultOnMoveVector`
  let (hit, unmodelled) := l.clip start (start.add movement)
  if unmodelled then Level.setOverflow
  let area := ((throwableDims.box start).expandTowards movement).inflate 1.0 1.0 1.0
  if meetsEntity l i area start hit.location (computeMargin (d.tickCount + 1)) false then
    Level.setOverflow
  let stop := if hit.miss then start.add movement else hit.location
  setPos i stop
  Touch.applyEffectsFromBlocks throwableDims i (← effectPos i) [⟨start, stop, none⟩]
  baseTick throwableDims i
  if hit.miss then return
  let some (e, _, d) ← get? i | return
  -- `hitTargetOrDeflectSelf`
  if (← Level.getBlock hit.blockPos).isAir then return
  onHitBlock i hit
  landed i hit
  if type == "minecraft:egg" then
    -- one egg in eight hatches
    if ((random e d).nextInt 8).1 == 0 then Level.setOverflow
  Level.removeEntity i

/-- The tick of a projectile. -/
def tick (i : ℕ) : M Unit := do
  let some (e, type, d) ← get? i | return
  if arrowTypes.contains type then arrowTick i
  else if throwableTypes.contains type then throwableTick i
  else if d.inGround || e.base.motion == .zero then pure ()
  else Level.setOverflow

/-- The behaviour of the entity. -/
def behaviour : EntityBehaviour := ⟨tick⟩

end Redstone.Entity.Projectile
