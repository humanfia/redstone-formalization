module

public import Redstone.Entity.Tnt.Physics
public import Redstone.Entity.Tnt.JavaMath
public import Redstone.Entity.Tnt.HashSet
public import Redstone.Block.Generated.Items

/-!
# Explosions

Java classes: `ServerExplosion`, `ExplosionDamageCalculator`, and the constructor of
`PrimedTnt`.

An explosion (`ServerExplosion.explode`) does three things, in this order:

1. `calculateExplodedPositions`: 1352 rays leave the centre, each with a random strength
   drawn from the level's random number generator. A ray loses strength with every step and
   with the explosion resistance of the blocks it crosses; every position it reaches with
   strength left is collected, air included.
2. `hurtEntities`: entities within twice the power are pushed away, in proportion to how
   much of them the centre can see (`getSeenPercent`).
3. `interactWithBlocks`: the collected positions are shuffled with the level's random number
   generator and every block that is not air is replaced by air; a TNT block becomes a primed
   TNT with a short random fuse (`TntBlock.wasExploded`).

The positions are collected in a `java.util.HashSet` and shuffled afterwards, so the order in
which blocks are removed depends on the iteration order of that hash set, which `JHashSet`
reproduces (`Redstone.Entity.Tnt.HashSet`).

## What is left out

* Only primed TNT is pushed. An entity of another kind in range (items and other
  entities are pushed, damaged or destroyed in the game) sets `Level.overflow`.
* Drops: an exploded block drops nothing, as in a world where the game rule `block_drops` is
  off, which is how the tests run. The game still evaluates the loot table of every exploded
  block and draws the position of every stack from the level's generator, so the number of
  stacks is modelled (`explosionDrops`, `addOrAppendStack`). A block whose drops depend on
  chance, on its block entity or on its neighbours (leaves, glowstone, some ores, banners,
  shulker boxes, heads, ...) sets `Level.overflow` when it explodes. Experience and silverfish
  (`spawnAfterBreak`) are not modelled.
* `BlockBehaviour.onExplosionHit` is taken to be the method of `BlockBehaviour` for every
  block. The overrides in the game differ only for explosions that trigger blocks (wind
  charges) and for the beehive and the creaking heart, which act on mobs.
* Fire: explosions of TNT make none.
* Two exploded positions with the same hash in a tree bucket of the hash set, which Java orders
  by identity hash code, set `Level.overflow`; this needs positions 31 blocks apart.
* The build limits are those of the overworld (y from -64 to 319).
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

/-- The inner loop of `calculateExplodedPositions`, bounded by `fuel` steps: follows one ray
from `pos` in steps of 0.3 along `dir` while it has power left, and collects what it reaches. -/
def rayLoop (l : Level) (dir : Vec3) : ℕ → Float32 → Vec3 → JHashSet → JHashSet × Bool
  | 0, _, _, set => (set, true)
  | fuel + 1, power, pos, set =>
    if power > 0.0 then
      let p := blockPos pos
      if !isInWorldBounds p then (set, false)
      else
        let power :=
          match blockExplosionResistance (l.blockAt p) with
          | some r => power - (r + Float32.ofBits 0x3e99999a) * Float32.ofBits 0x3e99999a
          | none => power
        let set := if power > 0.0 then set.insert p else set
        let step := wide 0x3e99999a
        rayLoop l dir fuel (power - Float32.ofBits 0x3e666667)
          ⟨pos.x + dir.x * step, pos.y + dir.y * step, pos.z + dir.z * step⟩ set
    else (set, false)

/-- The coordinate `i / 15.0F * 2.0F - 1.0F` of a ray's direction before normalization. -/
def rayCoord (i : ℕ) : Float :=
  (Float32.ofNat i / 15.0 * 2.0 - 1.0).toFloat

/-- `ServerExplosion.calculateExplodedPositions`: the positions the explosion reaches, in the
iteration order of the hash set, the generator after the 1352 draws, and whether a bound of the
model was hit. -/
def calculateExplodedPositions (l : Level) (center : Vec3) (radius : Float32) :
    List Pos × JavaRandom × Bool := Id.run do
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
          let (s, b) := rayLoop l ⟨xd / d, yd / d, zd / d⟩ 4096 power center set
          set := s
          if b then bad := true
  return (set.toList, random, bad || set.unordered)

/-! ### Entities -/

/-- `ServerExplosion.getSeenPercent(center, entity)` for a primed TNT at `position` with fall
distance `fall`: the share of a grid of points of its bounding box from which the centre can be
seen. The second component tells whether the model could not decide it. -/
def getSeenPercent (l : Level) (center position : Vec3) (fall : Float) : Float32 × Bool :=
  Id.run do
  let bb := entityBox position
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
        let (hit, unmodelled) := clipCollider l fall ⟨x + xOffset, y, z + zOffset⟩ center
        if unmodelled then bad := true
        if !hit then hits := hits + 1
        count := count + 1
  return (Float32.ofNat hits / Float32.ofNat count, bad)

/-- `ServerExplosion.hurtEntities`, for primed TNT only: every primed TNT within twice the
power of the centre is pushed away from it (`Entity.pushFromExplosion`). The exploding entity
has been removed before. An entity of another kind within that distance, which the game would
push, hurt or destroy, sets `Level.overflow`. -/
def hurtEntities (center : Vec3) (radius : Float32) : M Unit := do
  if radius < Float32.ofBits 0x3727c5ac then return
  let doubleRadius := (radius * 2.0).toFloat
  let l ← get
  for e in l.entities do
    let pos := e.base.pos
    let delta := vsub pos center
    let dist := Float.sqrt (delta.x * delta.x + delta.y * delta.y + delta.z * delta.z) /
      doubleRadius
    if let .tnt d := e.data then
      if !(dist > 1.0) then
        let direction := normalize delta
        let (exposure, bad) := getSeenPercent l center pos d.fallDistance
        if bad then Level.setOverflow
        let knockbackMultiplier := (1.0 : Float32).toFloat
        let knockbackPower := (1.0 - dist) * exposure.toFloat * knockbackMultiplier * (1.0 - 0.0)
        let knockback := vscale direction knockbackPower
        if visFinite knockback then
          Level.modifyEntity e.index fun e =>
            { e with base := { e.base with motion := vadd e.base.motion knockback } }
    else if !(dist > 1.0) then Level.setOverflow

/-! ### Blocks -/

/-- `Util.shuffle(list, random)`. -/
def shuffle (ps : Array Pos) (r : JavaRandom) : Array Pos × JavaRandom :=
  (List.range (ps.size - 1)).foldl
    (fun (ps, r) k =>
      let i := ps.size - k
      let (swapTo, r) := r.nextInt i
      (ps.swapIfInBounds (i - 1) swapTo, r))
    (ps, r)

/-- `ServerExplosion.addOrAppendStack`: adds a dropped stack of `count` of `item` to the ones
collected so far. It is merged into the collected ones of the same item, which take up to 16
(`StackCollector.tryMerge`, `ItemEntity.merge`), and what is left becomes a new stack. An empty
stack is kept only if it is the first. -/
def addOrAppendStack (collected : Array (String × ℕ)) (item : String) (count : ℕ) :
    Array (String × ℕ) :=
  if count == 0 then (if collected.isEmpty then collected.push (item, 0) else collected)
  else
    let size : ℤ := itemMaxStackSize item
    let (collected, rest) := collected.foldl
      (fun ((acc, n) : Array (String × ℕ) × ℤ) (it, c) =>
        if n > 0 && c > 0 && it == item && n + c ≤ size then
          let delta := min (min size 16 - c) n
          (acc.push (it, (c + delta).toNat), n - delta)
        else (acc.push (it, c), n))
      (#[], (count : ℤ))
    if rest > 0 then collected.push (item, rest.toNat) else collected

/-- `BlockBehaviour.onExplosionHit` for an explosion that destroys blocks: the drops of a block
that is not air are added to `collected`, the block is replaced by air, and then told so
(`Block.wasExploded`). Only TNT reacts, and it drops nothing (`dropFromExplosion`): it becomes a
primed TNT with a short fuse (`TntBlock.wasExploded`). -/
def onExplosionHit (collected : Array (String × ℕ)) (p : Pos) : M (Array (String × ℕ)) := do
  let state ← Level.getBlock p
  if state.isAir then return collected
  let mut collected := collected
  if !state.is .tnt then
    match explosionDrops state with
    | some drops =>
      collected := drops.foldl (fun s (item, count) => addOrAppendStack s item count) collected
    | none => Level.setOverflow
  discard <| Level.setBlock p .AIR 3
  if state.is .tnt then discard <| addPrimedTnt p randomShortFuse
  return collected

/-- `ServerExplosion.interactWithBlocks`: shuffles the positions, blows up each block, and
drops what was collected. Nothing is dropped in the model, but `Block.popResource` draws the
three coordinates of each stack from the level's generator before it finds that out. -/
def interactWithBlocks (ps : List Pos) : M Unit := do
  let ps ← drawRandom (shuffle ps.toArray)
  let collected ← ps.toList.foldlM onExplosionHit #[]
  collected.forM fun _ => do
    discard <| drawRandom nextDouble
    discard <| drawRandom nextDouble
    discard <| drawRandom nextDouble

/-- `ServerLevel.explode` with `ExplosionInteraction.TNT`, no fire and the default damage
calculator of an entity: `ServerExplosion.explode`. -/
def explode (center : Vec3) (radius : Float32) : M Unit := do
  Level.gameEvent "minecraft:explode" (blockPos center)
  let (toBlow, random, bad) := calculateExplodedPositions (← get) center radius
  modify fun l => { l with random := random }
  if bad then Level.setOverflow
  hurtEntities center radius
  interactWithBlocks toBlow

end Redstone.Entity.Tnt
