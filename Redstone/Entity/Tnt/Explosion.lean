module

public import Redstone.Entity.Tnt.Physics
public import Redstone.Entity.Tnt.JavaMath
public import Redstone.Entity.Tnt.HashSet
public import Redstone.Block.Generated.Items
public import Redstone.Entity.Still
public import Redstone.Entity.ItemDrop

/-!
# Explosions

Java classes: `ServerExplosion`, `ExplosionDamageCalculator`,
`EntityBasedExplosionDamageCalculator`, `ServerLevel.explode`, `BlockBehaviour.onExplosionHit`,
the constructor of `PrimedTnt`, and what an explosion does to the entities it reaches
(`ItemEntity.hurtServer`, `VehicleEntity.hurtServer`, `MinecartTNT.destroy`,
`ArmorStand.hurtServer`, `Entity.push`).

An explosion (`ServerExplosion.explode`) does four things, in this order:

1. `calculateExplodedPositions`: 1352 rays leave the centre, each with a random strength
   drawn from the level's random number generator. A ray loses strength with every step and
   with the explosion resistance of the blocks it crosses; every position it reaches with
   strength left is collected, air included. Who explodes may change the resistance of a block
   and keep a block out of it (`DamageCalculator`): a primed TNT minecart spares rails and what
   they lie on, a respawn anchor in water blows up nothing.
2. `hurtEntities`: the entities within twice the power are hurt and pushed away, in proportion
   to how much of them the centre can see (`getSeenPercent`).
3. `interactWithBlocks`, unless the explosion keeps the blocks: the collected positions are
   shuffled with the level's random number generator and every block is told that the explosion
   hit it (`onExplosionHit`). A block that is not air is replaced by air; a TNT block becomes a
   primed TNT with a short random fuse (`TntBlock.wasExploded`).
4. `createFire`, if the explosion makes fire: one position in three, if it is air above a solid
   block, is set on fire.

The positions are collected in a `java.util.HashSet` and shuffled afterwards, so the order in
which blocks are removed depends on the iteration order of that hash set, which `JHashSet`
reproduces (`Redstone.Entity.Tnt.HashSet`).

## Entities

What `hurtEntities` does to an entity depends on its kind:

* primed TNT and falling blocks are pushed;
* an item loses health and disappears when it has none left (a nether star is not hurt);
* a minecart takes damage, which wears off again (`Entities.Minecart.damage`); with more than
  40 it breaks and drops itself as an item, and a minecart with a chest or a hopper first drops
  what it holds. A TNT minecart never breaks: it is primed with a fuse of 0 to 38 ticks, drawn from
  its own generator;
* an arrow is pushed unless it is stuck in a block;
* an armour stand breaks.

The entities are gone through in the order of the entity sections (`sectionKey`), which
matters when more than one of them drops something.

## Blocks: the hook

`BlockBehaviour.onExplosionHit` is overridden by the blocks an explosion can trigger (doors,
trapdoors, fence gates, buttons, levers, bells, candles). Every override has the form
"if `explosion.canTriggerBlocks()` then react; then the method of `BlockBehaviour`", and the
method of `BlockBehaviour` does nothing for an explosion that triggers blocks. The hook
`Behaviour.onExplosionHit` therefore stands for the reaction alone: `onExplosionHit` here calls
it for an explosion that triggers blocks (`ExplosionInteraction.trigger`) and does the work of
`BlockBehaviour` for every other.

## What is left out

* Living entities: damage needs health, which the model does not keep. A mob, a boat, an end
  crystal or any other entity not listed above within reach sets `Level.overflow`; so do
  projectiles other than arrows, item frames, experience orbs and lightning bolts.
* An armour stand is taken to be visible and to carry nothing (the model keeps neither the flag
  `Invisible` nor the equipment): it breaks and drops nothing. A marker armour stand, which is
  not hurt but pushed, sets `Level.overflow`.
* An item whose stack has data components sets `Level.overflow`: the components may make it
  resistant, or make it drop what it holds when it is destroyed.
* The flag `Invulnerable` of an entity, custom names of minecarts (the dropped item carries the
  name), passengers, and the components of the items in a minecart that breaks.
* Explosions caused by wind charges, which leave items and armour stands alone
  (`shouldAffectBlocklikeEntities`) and push with another strength: the calculator has the
  fields for it, but nothing makes such an explosion yet.
* The collision context of a falling block in powder snow (`Level.overflow` when the line of
  sight to one crosses powder snow).
* Drops: an exploded block drops nothing, as in a world where the game rule `block_drops` is
  off, which is how the tests run. The game still evaluates the loot table of every exploded
  block and draws the position of every stack from the level's generator, so the number of
  stacks is modelled (`Level.getExplosionDrops`, `addOrAppendStack`, `Level.popResource`). With
  the game rule on, `Level.popResource` sets `Level.overflow`. A block whose drops depend on
  chance, on its block entity or on its neighbours (leaves, glowstone, some ores, banners,
  shulker boxes, heads, ...) sets `Level.overflow` when it explodes. Experience and silverfish
  (`spawnAfterBreak`) are not modelled.
* Decay: an explosion of a block or of a mob (`ExplosionInteraction.block`, `mob`) lets only
  some of the drops survive, by the generator of each loot table. `Level.getExplosionDrops` does
  not evaluate that, so a block that would drop something sets `Level.overflow` there.
* The overrides of `onExplosionHit` of the beehive and the creaking heart, which act on mobs.
* Game events (`explode`, `entity_damage`, `entity_die`) are announced at the block the
  explosion or the entity is in, without the entity that caused them: what a sculk sensor keeps
  of them differs from the game.
* Two exploded positions with the same hash in a tree bucket of the hash set, which Java orders
  by identity hash code, set `Level.overflow`; this needs positions 31 blocks apart.
* The build limits are those of the overworld (y from -64 to 319). The game rules that decide
  what an explosion does to blocks have their default values.

## Scenarios that wait

In `tests/pending/scenarios`:

* `analog/anchor-explode-soul`, `anchor-explode-stone-floor` and the `analog/adv-fuzz-*`
  scenarios in which a respawn anchor explodes: the explosion of a respawn anchor lets the
  drops decay, and the floor it destroys drops something, so the model sets `Level.overflow`
  (see Decay above); the draws the game makes for the decay also move the fires that
  `createFire` lights afterwards. What a fire does once it is placed is
  `Redstone.Component.Fire`.
* `minecart/tnt-chain-rails`: the explosion of one TNT minecart pushes the next into a third,
  and minecarts that meet are not modelled (`Redstone.Entity.Minecart`).
* `minecart/tnt-fall-sculk` and `minecart/tnt-fuse-sculk`: a sculk sensor hears the explosion
  and the damage of the entities. The game announces these events at the exact position of the
  explosion or of the entity and with the entity that exploded, while the model's game events
  are heard at the centre of a block and these carry no entity (`Redstone.Component.Sculk`).
-/

@[expose] public section

namespace Redstone.Entity.Tnt

/-! ### The level's random number generator -/

/-- `RandomSource.nextFloat()` on the level's generator. -/
def nextFloat (r : JavaRandom) : Float32 × JavaRandom :=
  let (n, r) := r.nextFloat24
  (Float32.ofNat n * Float32.ofBits 0x33800000, r)

/-- `RandomSource.nextDouble()` on the level's generator. -/
def nextDouble (r : JavaRandom) : Float × JavaRandom :=
  let (n, r) := r.nextDouble53
  (Float.ofNat n * wide 0x25000000, r)

/-- Draws from `Level.random` with `f`. -/
def drawRandom {α : Type} (f : JavaRandom → α × JavaRandom) : M α :=
  modifyGet fun l =>
    let (a, r) := f l.random
    (a, { l with random := r })

/-! ### Primed TNT -/

/-- The constructor `PrimedTnt(level, x, y, z, owner)` followed by `addFreshEntity`: a primed
TNT at the bottom centre of the block position `p`, moving up and slightly sideways in a random
direction, with the given fuse. Returns the index of the entity. -/
def addPrimedTnt (p : Pos) (fuse : JavaRandom → ℤ × JavaRandom) : M ℕ := do
  let position : Vec3 := ⟨Float.ofInt p.x + 0.5, Float.ofInt p.y, Float.ofInt p.z + 0.5⟩
  let rot := (← drawRandom nextDouble) * wide 0x40c90fdb
  let motion : Vec3 := ⟨-(JavaMath.sin rot) * 0.02, wide 0x3e4ccccd, -(JavaMath.cos rot) * 0.02⟩
  let fuse ← drawRandom fuse
  Level.addEntity ⟨position, motion, false⟩ (.tnt { (default : Entities.Tnt) with fuse := fuse })

/-- `PrimedTnt.getRandomShortFuse(80, random)`: between 10 and 29 ticks. -/
def randomShortFuse (r : JavaRandom) : ℤ × JavaRandom :=
  let (n, r) := r.nextInt 20
  ((n : ℤ) + 10, r)

/-! ### The rays -/

/-- `ExplosionDamageCalculator.getBlockExplosionResistance`: nothing for air without fluid,
otherwise the larger of the resistances of the block and of its fluid (100 for water and
lava). -/
def blockExplosionResistance (b : Block) : Option Float32 :=
  if b.isAir && b.attrs.fluid.isEmpty then none
  else
    let block := explosionResistance b.id
    let fluid : Float32 := if b.attrs.fluid.isEmpty then 0.0 else 100.0
    some (if block ≥ fluid then block else fluid)

/-- `Level.isInWorldBounds` for the overworld. -/
def isInWorldBounds (p : Pos) : Bool :=
  -64 ≤ p.y && p.y < 320 && -30000000 ≤ p.x && p.x < 30000000 && -30000000 ≤ p.z &&
    p.z < 30000000

/-- `ExplosionDamageCalculator`, with the methods that who explodes can change
(`EntityBasedExplosionDamageCalculator` asks the exploding entity; a respawn anchor and a wind
charge bring a calculator of their own). The default is the calculator of the class itself. -/
structure DamageCalculator where
  /-- `getBlockExplosionResistance(explosion, level, pos, block, fluid)`. -/
  getBlockExplosionResistance : Level → Pos → Block → Option Float32 :=
    fun _ _ b => blockExplosionResistance b
  /-- `shouldBlockExplode(explosion, level, pos, state, power)`. -/
  shouldBlockExplode : Level → Pos → Block → Bool := fun _ _ _ => true
  /-- `shouldDamageEntity(explosion, entity)`, which no calculator makes depend on the
  entity. -/
  shouldDamageEntity : Bool := true
  /-- `getKnockbackMultiplier(entity)`, for an entity that is not a flying player. -/
  knockbackMultiplier : Float32 := 1.0

/-- The calculator of an explosion whose source is a TNT minecart
(`MinecartTNT.getBlockExplosionResistance` and `shouldBlockExplode`): while the minecart is
primed, a rail and the block under a rail have no resistance and do not explode. -/
def minecartTntCalculator (primed : Bool) : DamageCalculator where
  getBlockExplosionResistance l p b :=
    (blockExplosionResistance b).map fun r =>
      if primed && (b.isRail || (l.blockAt (p.step .up)).isRail) then 0.0 else r
  shouldBlockExplode l p b := !(primed && (b.isRail || (l.blockAt (p.step .up)).isRail))

/-- The inner loop of `calculateExplodedPositions`, bounded by `fuel` steps: follows one ray
from `pos` in steps of 0.3 along `dir` while it has power left, and collects what it reaches. -/
def rayLoop (l : Level) (rules : DamageCalculator) (dir : Vec3) :
    ℕ → Float32 → Vec3 → JHashSet → JHashSet × Bool
  | 0, _, _, set => (set, true)
  | fuel + 1, power, pos, set =>
    if power > 0.0 then
      let p := blockPos pos
      if !isInWorldBounds p then (set, false)
      else
        let b := l.blockAt p
        let power :=
          match rules.getBlockExplosionResistance l p b with
          | some r => power - (r + Float32.ofBits 0x3e99999a) * Float32.ofBits 0x3e99999a
          | none => power
        let set := if power > 0.0 && rules.shouldBlockExplode l p b then set.insert p else set
        let step := wide 0x3e99999a
        rayLoop l rules dir fuel (power - Float32.ofBits 0x3e666667)
          ⟨pos.x + dir.x * step, pos.y + dir.y * step, pos.z + dir.z * step⟩ set
    else (set, false)

/-- The coordinate `i / 15.0F * 2.0F - 1.0F` of a ray's direction before normalization. -/
def rayCoord (i : ℕ) : Float :=
  (Float32.ofNat i / 15.0 * 2.0 - 1.0).toFloat

/-- `ServerExplosion.calculateExplodedPositions`: the positions the explosion reaches, in the
iteration order of the hash set, the generator after the 1352 draws, and whether a bound of the
model was hit. -/
def calculateExplodedPositions (l : Level) (center : Vec3) (radius : Float32)
    (rules : DamageCalculator := {}) : List Pos × JavaRandom × Bool := Id.run do
  let mut set := JHashSet.empty
  let mut random := l.random
  let mut bad := false
  for xx in List.range 16 do
    for yy in List.range 16 do
      for zz in List.range 16 do
        if xx == 0 || xx == 15 || yy == 0 || yy == 15 || zz == 0 || zz == 15 then
          let xd := rayCoord xx
          let yd := rayCoord yy
          let zd := rayCoord zz
          let d := Float.sqrt (xd * xd + yd * yd + zd * zd)
          let (f, r) := nextFloat random
          random := r
          let power := radius * (Float32.ofBits 0x3f333333 + f * Float32.ofBits 0x3f19999a)
          let (s, b) := rayLoop l rules ⟨xd / d, yd / d, zd / d⟩ 4096 power center set
          set := s
          if b then bad := true
  return (set.toList, random, bad || set.unordered)

/-! ### Entities -/

/-- `ServerExplosion.getSeenPercent(center, entity)` for an entity with the bounding box `bb`:
the share of a grid of points of the box from which the centre can be seen. `clip a b` tells
whether a block lies between two points for this entity, and whether the model could not decide
it; the second component of the result tells the latter for any of the points. -/
def getSeenPercent (center : Vec3) (bb : AABB) (clip : Vec3 → Vec3 → Bool × Bool) :
    Float32 × Bool :=
  Id.run do
  let xs := 1.0 / ((bb.maxX - bb.minX) * 2.0 + 1.0)
  let ys := 1.0 / ((bb.maxY - bb.minY) * 2.0 + 1.0)
  let zs := 1.0 / ((bb.maxZ - bb.minZ) * 2.0 + 1.0)
  let xOffset := (1.0 - Float.floor (1.0 / xs) * xs) / 2.0
  let zOffset := (1.0 - Float.floor (1.0 / zs) * zs) / 2.0
  if xs < 0.0 || ys < 0.0 || zs < 0.0 then return (0.0, false)
  let mut hits := 0
  let mut count := 0
  let mut bad := false
  -- the three loops `for (double v = 0.0; v <= 1.0; v += step)`, at most 64 steps each
  let steps (step : Float) : List Float × Bool :=
    let vs := (List.range 65).map fun i => i.repeat (· + step) 0.0
    ((vs.take 64).takeWhile (· ≤ 1.0), vs.all (· ≤ 1.0))
  let (xxs, bx) := steps xs
  let (yys, by') := steps ys
  let (zzs, bz) := steps zs
  if bx || by' || bz then bad := true
  for xx in xxs do
    for yy in yys do
      for zz in zzs do
        let x := lerp xx bb.minX bb.maxX
        let y := lerp yy bb.minY bb.maxY
        let z := lerp zz bb.minZ bb.maxZ
        let (hit, unmodelled) := clip ⟨x + xOffset, y, z + zOffset⟩ center
        if unmodelled then bad := true
        if !hit then hits := hits + 1
        count := count + 1
  return (Float32.ofNat hits / Float32.ofNat count, bad)

/-- What `hurtEntities` needs to know of an entity before it looks at its kind. -/
structure Target where
  /-- `Entity.getBoundingBox()`. -/
  box : AABB
  /-- The point the explosion pushes the entity away from, above its position: nothing for a
  primed TNT (`position()`), the eye height for every other entity (`getEyePosition()`). -/
  originHeight : Float
  /-- `Entity.fallDistance`, on which the collision shape of powder snow depends. -/
  fall : Float
  /-- The entity is a falling block, for which powder snow is solid. -/
  fallingBlock : Bool

/-- `EntityDimensions.eyeHeight` of an entity type with the height `height`: 85 hundredths of
the height, unless the type says otherwise, as the arrows do. Only the types that an explosion
pushes matter. -/
def eyeHeight (type : String) (height : Float32) : Float :=
  if type == "minecraft:arrow" || type == "minecraft:spectral_arrow" then
    (0.13 : Float32).toFloat
  else (height * (0.85 : Float32)).toFloat

/-- The `Target` of an entity; `none` for an entity of a type whose size the model does not
know. -/
def target? (e : Entity) : Option Target :=
  match e.data with
  | .tnt d => some ⟨entityBox e.base.pos, 0.0, d.fallDistance, false⟩
  | data =>
    (Still.info? e).map fun info =>
      let fall :=
        match data with
        | .item d => d.phys.fallDistance
        | .fallingBlock d => d.phys.fallDistance
        | .minecart _ d => d.fallDistance
        | _ => 0.0
      let fallingBlock := match data with | .fallingBlock _ => true | _ => false
      ⟨Still.makeBoundingBox info e.base.pos, eyeHeight data.typeName info.height, fall,
        fallingBlock⟩

/-- `Level.clip` with `ClipContext.Block.COLLIDER` for the entity `t`: `clipCollider`, which
takes powder snow as a primed TNT does. A falling block stands on powder snow whatever its fall
distance, which is not modelled. -/
def Target.clip (l : Level) (t : Target) (a b : Vec3) : Bool × Bool :=
  let (hit, unmodelled) := clipCollider l t.fall a b
  let snow := t.fallingBlock && traverseBlocks (fun p => (l.blockAt p).id == .powder_snow) a b
  (hit, unmodelled || snow)

/-- `ExplosionDamageCalculator.getEntityDamageAmount(explosion, entity, exposure)`, for an
entity at `dist` times twice the radius from the centre. -/
def entityDamageAmount (doubleRadius : Float32) (dist : Float) (exposure : Float32) : Float32 :=
  let pow := (1.0 - dist) * exposure.toFloat
  ((pow * pow + pow) / 2.0 * 7.0 * doubleRadius.toFloat + 1.0).toFloat32

/-- The conversion `(int) x` of a `float`: towards zero. -/
def truncInt (x : Float32) : ℤ :=
  if x < 0.0 then -((-x).floor.toInt64.toInt) else x.floor.toInt64.toInt

/-- `ItemEntity.hurtServer` for the damage of an explosion: the item loses health, announces
the damage and is discarded when no health is left. A nether star is resistant to explosions
(`ItemStack.canBeHurtBy`, component `damage_resistant`). -/
def hurtItem (e : Entity) (d : Entities.Item) (damage : Float32) : M Unit := do
  if d.item == "minecraft:nether_star" then return
  if d.hasComponents then Level.setOverflow
  let health := truncInt (Float32.ofInt d.health - damage)
  Level.modifyEntity e.index fun e => { e with data := .item { d with health := health } }
  Level.gameEvent "minecraft:entity_damage" (blockPos e.base.pos)
  if health ≤ 0 then Level.removeEntity e.index

/-- `Containers.dropItemStack(level, x, y, z, itemStack)` for a stack that an entity at the
block position `p` drops: `ItemDrop.dropItemStack`, with the items entering their entity
section in the tick of `actor` (`Entities.Physics.sectionEntry`). The position is drawn even
for an empty stack; `fuel` bounds the number of item entities. -/
def dropItemStack (p : Pos) (stack : ItemStack) (actor : ℕ) : M Unit := do
  let x := Float.ofInt p.x + (← ItemDrop.nextDouble) * 0.75 + 0.125
  let y := Float.ofInt p.y + (← ItemDrop.nextDouble) * 0.75
  let z := Float.ofInt p.z + (← ItemDrop.nextDouble) * 0.75 + 0.125
  let rec loop : ℕ → ItemStack → M Unit
    | 0, stack => if stack.isEmpty then pure () else Level.setOverflow
    | fuel + 1, stack => do
      if stack.isEmpty then return
      let n := min ((← ItemDrop.nextInt 21) + 10) stack.count
      let vx ← ItemDrop.triangle 0.0 0.11485000171139836
      let vy ← ItemDrop.triangle 0.2 0.11485000171139836
      let vz ← ItemDrop.triangle 0.0 0.11485000171139836
      discard <| Item.spawnStack ⟨x, y, z⟩ ⟨vx, vy, vz⟩ stack.id n stack.hasComponents actor
      loop fuel (stack.withCount (stack.count - n))
  loop stack.count stack

/-- `VehicleEntity.getDropItem()` of the kinds of minecart. -/
def minecartDropItem : MinecartKind → String
  | .minecart | .spawner | .commandBlock => "minecraft:minecart"
  | .chest => "minecraft:chest_minecart"
  | .furnace => "minecraft:furnace_minecart"
  | .tnt => "minecraft:tnt_minecart"
  | .hopper => "minecraft:hopper_minecart"

/-- `VehicleEntity.hurtServer` for the damage of an explosion. The damage is added up
(`setDamage`) and announced. A TNT minecart is destroyed by any explosion
(`shouldSourceDestroy`), which for it means that it is primed, with a fuse of two draws from its
own generator, unless it is primed already (`MinecartTNT.destroy`). Another minecart is
destroyed when its damage exceeds 40 (`VehicleEntity.destroy`): it is killed and drops its item
(the game rule `entity_drops` is on).

A minecart with a container drops what it holds when it is removed
(`AbstractMinecartContainer.remove`), which is before it drops itself, and once more afterwards
(`ContainerEntity.chestVehicleDestroyed`), when the container is empty. `Containers.dropContents`
draws a position for every slot, empty or not, so the second time only moves the level's
generator on. `actor` is as in `Entity.Item.spawnAtLocation`. -/
def hurtMinecart (e : Entity) (kind : MinecartKind) (d : Entities.Minecart) (damage : Float32)
    (actor : ℕ) : M Unit := do
  let pos := e.base.pos
  let d := { d with damage := d.damage + damage * 10.0 }
  let setData (d : Entities.Minecart) : M Unit :=
    Level.modifyEntity e.index fun e => { e with data := .minecart kind d }
  Level.gameEvent "minecraft:entity_damage" (blockPos pos)
  if kind == .tnt then
    if d.fuse < 0 then
      let r := d.random.getD (Entity.randomAfterUuid e.id)
      let (a, r) := r.nextInt 20
      let (b, r) := r.nextInt 20
      setData { d with fuse := (a : ℤ) + (b : ℤ), random := some r }
    else setData d
  else if d.damage > 40.0 then
    let slots := if kind == .chest then 27 else if kind == .hopper then 5 else 0
    if slots != 0 && d.hasLootTable then Level.setOverflow
    for slot in List.range slots do
      let stack : ItemStack :=
        match d.items.find? (·.1 == slot) with
        | some (_, item, count) => ⟨item, count, []⟩
        | none => .empty
      dropItemStack (blockPos pos) stack actor
    Level.removeEntity e.index
    Level.gameEvent "minecraft:entity_die" (blockPos pos)
    discard <| Item.spawnAtLocation pos (minecartDropItem kind) actor
    for _ in List.range slots do
      dropItemStack (blockPos pos) .empty actor
  else setData d

/-- The place of an entity in the order in which `EntitySectionStorage` goes through the
entities of a region: `Entity.Item.sectionKey`, which knows when an item or a falling block
entered its section, with what a minecart knows about itself. The other kinds of entity count
as having been in their section since the level was loaded. -/
def sectionKey (e : Entity) : List ℤ :=
  let p := e.base.pos
  let entry :=
    match e.data with
    | .minecart _ d => d.sectionEntry
    | _ => e.phys.sectionEntry
  [Phys.floor p.x / 16, (Phys.floor p.z / 16) % 2 ^ 22, (Phys.floor p.y / 16) % 2 ^ 20,
    entry.1, entry.2, e.index]

/-- Inserts an entity into a list ordered by `sectionKey`. -/
def insertBySection (e : Entity) : List Entity → List Entity
  | [] => [e]
  | o :: os => if sectionKey e < sectionKey o then e :: o :: os else o :: insertBySection e os

/-- `ServerExplosion.hurtEntities`: every entity within twice the power of the centre, except
the one that explodes (`source`), is hurt (`Entity.hurtServer`) and then pushed away from the
centre (`Entity.pushFromExplosion`), both in proportion to the share of it that the centre can
see. What being hurt means depends on the kind of entity; see the module docstring. An entity
of a kind for which it is not modelled sets `Level.overflow`. `actor` is as in
`Entity.Item.spawnAtLocation`. -/
def hurtEntities (center : Vec3) (radius : Float32) (rules : DamageCalculator := {})
    (source : Option ℕ := none) (actor : ℕ := 0) : M Unit := do
  if radius < Float32.ofBits 0x3727c5ac then return
  let doubleRadius := radius * 2.0
  let distOf (pos : Vec3) : Float :=
    let delta := vsub pos center
    Float.sqrt (delta.x * delta.x + delta.y * delta.y + delta.z * delta.z) / doubleRadius.toFloat
  let found := (← get).entities.filter fun e =>
    some e.index != source && !(distOf e.base.pos > 1.0)
  for found in found.foldl (fun acc e => insertBySection e acc) [] do
    let l ← get
    let some e := l.entity? found.index | continue
    let some t := target? e
      | Level.setOverflow
    let pos := e.base.pos
    let dist := distOf pos
    let direction := normalize (vsub ⟨pos.x, pos.y + t.originHeight, pos.z⟩ center)
    let (exposure, bad) :=
      if !rules.shouldDamageEntity && rules.knockbackMultiplier == 0.0 then (0.0, false)
      else getSeenPercent center t.box (t.clip l)
    if bad then Level.setOverflow
    let damage := entityDamageAmount doubleRadius dist exposure
    let knockbackPower :=
      (1.0 - dist) * exposure.toFloat * rules.knockbackMultiplier.toFloat * (1.0 - 0.0)
    let knockback := vscale direction knockbackPower
    -- `Entity.push(impulse)`, for an entity that is still there
    let push : M Unit :=
      if visFinite knockback then
        Level.modifyEntity e.index fun e =>
          { e with base := { e.base with motion := vadd e.base.motion knockback } }
      else pure ()
    match e.data with
    | .tnt _ | .fallingBlock _ => push
    | .item d =>
      if rules.shouldDamageEntity then hurtItem e d damage
      push
    | .minecart kind d =>
      if rules.shouldDamageEntity then hurtMinecart e kind d damage actor
      push
    | .projectile type d =>
      if type == "minecraft:arrow" || type == "minecraft:spectral_arrow" then
        -- `AbstractArrow.push`
        if !d.inGround then push
      else Level.setOverflow
    | .other "minecraft:armor_stand" d =>
      if d.marker || !rules.shouldDamageEntity then Level.setOverflow
      else
        -- `ArmorStand.hurtServer`: `brokenByAnything` and `kill`
        Level.removeEntity e.index
        Level.gameEvent "minecraft:entity_die" (blockPos pos)
    | _ => Level.setOverflow

/-! ### Blocks -/

/-- `Util.shuffle(list, random)`. -/
def shuffle (ps : Array Pos) (r : JavaRandom) : Array Pos × JavaRandom :=
  (List.range (ps.size - 1)).foldl
    (fun (ps, r) k =>
      let i := ps.size - k
      let (swapTo, r) := r.nextInt i
      (ps.swapIfInBounds (i - 1) swapTo, r))
    (ps, r)

/-- `ServerExplosion.addOrAppendStack`: adds a stack of `count` of `item`, dropped by the block at
`p`, to the ones collected so far (`ServerExplosion.StackCollector`: where the stack will be
dropped, the item, the count). It is merged into the collected ones of the same item, which
take up to 16 and keep their position (`StackCollector.tryMerge`, `ItemEntity.merge`), and what
is left becomes a new stack at `p`. An empty stack is kept only if it is the first. -/
def addOrAppendStack (collected : Array (Pos × String × ℕ)) (p : Pos) (item : String)
    (count : ℕ) : Array (Pos × String × ℕ) :=
  if count == 0 then (if collected.isEmpty then collected.push (p, item, 0) else collected)
  else
    let size : ℤ := itemMaxStackSize item
    let (collected, rest) := collected.foldl
      (fun ((acc, n) : Array (Pos × String × ℕ) × ℤ) (q, it, c) =>
        if n > 0 && c > 0 && it == item && n + c ≤ size then
          let delta := min (min size 16 - c) n
          (acc.push (q, it, (c + delta).toNat), n - delta)
        else (acc.push (q, it, c), n))
      (#[], (count : ℤ))
    if rest > 0 then collected.push (p, item, rest.toNat) else collected

/-- `Explosion.BlockInteraction`: what an explosion does to the blocks it reaches. -/
inductive BlockInteraction
  | keep
  | destroy
  | destroyWithDecay
  | triggerBlock
  deriving DecidableEq, Repr

/-- `Level.ExplosionInteraction`: the kind of thing that explodes. -/
inductive ExplosionInteraction
  | none
  | block
  | mob
  | tnt
  | trigger
  deriving DecidableEq, Repr

/-- The switch of `ServerLevel.explode`, with the default game rules: the drops of what a block
or a mob blows up decay (`block_explosion_drop_decay`, `mob_explosion_drop_decay`), those of
what TNT blows up do not (`tnt_explosion_drop_decay`), and mobs may destroy blocks
(`mob_griefing`). -/
def ExplosionInteraction.blockInteraction : ExplosionInteraction → BlockInteraction
  | .none => .keep
  | .block | .mob => .destroyWithDecay
  | .tnt => .destroy
  | .trigger => .triggerBlock

/-- `BlockState.onExplosionHit(level, pos, explosion, onHit)`.

An explosion that triggers blocks runs the block's own reaction, the hook
`Behaviour.onExplosionHit`, and nothing else. For every other explosion this is the method of
`BlockBehaviour`: the drops of a block that is not air (`Level.getExplosionDrops`) are added to
`collected`, the block is replaced by air, and then told so (`Block.wasExploded`). Only TNT
reacts to that, and it drops nothing (`dropFromExplosion`): it becomes a primed TNT with a short
fuse (`TntBlock.wasExploded`). Drops that decay are not evaluated: a block that would drop
something then sets `Level.overflow`. -/
def onExplosionHit (interaction : BlockInteraction) (collected : Array (Pos × String × ℕ))
    (p : Pos) : M (Array (Pos × String × ℕ)) := do
  let state ← Level.getBlock p
  if interaction == .triggerBlock then
    (← Level.behaviour state).onExplosionHit p
    return collected
  if state.isAir then return collected
  let mut collected := collected
  if !state.is .tnt then
    let drops ← Level.getExplosionDrops state p (← Level.peekBlockEntity p)
    if interaction == .destroyWithDecay && !drops.isEmpty then Level.setOverflow
    collected := drops.foldl (fun s (item, count) => addOrAppendStack s p item count) collected
  discard <| Level.setBlock p .AIR 3
  if state.is .tnt then discard <| addPrimedTnt p randomShortFuse
  return collected

/-- `ServerExplosion.interactWithBlocks`: shuffles the positions, tells each block that the
explosion hit it, and drops what was collected, every stack where the first block that dropped
that item was (`Level.popResource`). What the blocks drop and what dropping a stack does are not
decided here: both are in `Redstone.Mechanics.Update`, next to `Level.getDrops`. Returns the
positions as shuffled. -/
def interactWithBlocks (ps : List Pos) (interaction : BlockInteraction := .destroy) :
    M (List Pos) := do
  let ps := (← drawRandom (shuffle ps.toArray)).toList
  let collected ← ps.foldlM (onExplosionHit interaction) #[]
  collected.forM fun (p, item, count) => Level.popResource p item count
  return ps

/-- `BaseFireBlock.getState(level, pos)` above a block that is solid all through
(`isSolidRender`, which makes its top face sturdy): soul fire on soul sand and soul soil
(`SoulFireBlock.canSurviveOnBlock`), and otherwise the fire that burns on the floor
(`FireBlock.getStateForPlacement`). -/
def fireState (below : Block) : Block :=
  if below.id == .soul_sand || below.id == .soul_soil then .default .soul_fire
  else .default .fire

/-- `ServerExplosion.createFire`: for every position a draw; one in three is set on fire if
it is air above a block that is solid all through. -/
def createFire (ps : List Pos) : M Unit := do
  for p in ps do
    let n ← drawRandom (·.nextInt 3)
    if n == 0 && (← Level.getBlock p).isAir then
      let below ← Level.getBlock (p.step .down)
      if below.attrs.solidRender then discard <| Level.setBlock p (fireState below) 3

/-- `ServerLevel.explode(source, damageSource, damageCalculator, x, y, z, r, fire,
interactionType)` and `ServerExplosion.explode`: an explosion of the given power at `center`.
`source` is the index of the entity that explodes, which the explosion leaves alone, and
`calculator` what that entity or the caller has to say about blocks; `actor` is as in
`Entity.Item.spawnAtLocation`. -/
def explode (center : Vec3) (radius : Float32) (fire : Bool) (interaction : ExplosionInteraction)
    (calculator : DamageCalculator := {}) (source : Option ℕ := none) (actor : ℕ := 0) :
    M Unit := do
  Level.gameEvent "minecraft:explode" (blockPos center)
  let (toBlow, random, bad) := calculateExplodedPositions (← get) center radius calculator
  modify fun l => { l with random := random }
  if bad then Level.setOverflow
  hurtEntities center radius calculator source actor
  let blockInteraction := interaction.blockInteraction
  let toBlow ←
    if blockInteraction != .keep then interactWithBlocks toBlow blockInteraction
    else pure toBlow
  if fire then createFire toBlow

end Redstone.Entity.Tnt
