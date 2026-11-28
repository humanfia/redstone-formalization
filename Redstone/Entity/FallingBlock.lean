module

public import Redstone.Entity.Item

/-!
# Falling blocks

Java class: `FallingBlockEntity` (with `Fallable`, `AnvilBlock` and `ConcretePowderBlock` for
what happens on landing).

A falling block falls under gravity. When it lands it becomes a block again if the block it
landed in can be replaced and the block below is not free; otherwise it breaks and drops as an
item. A falling anvil can be damaged by its fall.

A falling block never updates its fluid interaction, so fluids neither push it nor slow it
down: it falls through water and lava as through air (lava sets it on fire, which shows in
nothing). Falling concrete powder that is in water (`isStuckInWater`) lands there and then turns
to concrete, and a block with the property `waterlogged` that lands in a water source is
waterlogged.

## What is left out

* The ray that a falling concrete powder faster than one block per tick casts for a water
  source it passed (`ClipContext.Fluid.SOURCE_ONLY`): such an entity with water on its way sets
  `Level.overflow`. So does any falling block that falls fast with a fluid on its way
  (`Redstone.Entity.Physics`).
* The damage a falling anvil does to living entities.
* The block entity data a falling block can carry: landing with such data sets
  `Level.overflow`.
* Dropping a block that is not one of the game's falling blocks (a falling block summoned with
  an arbitrary block state): the item of such a block is not known to the model, which sets
  `Level.overflow`.
* Portals, and the game rule `entity_drops`, taken to be true.
-/

@[expose] public section

namespace Redstone.Entity.FallingBlock

/-- The falling block entity with index `i`, with its data. -/
def get? (i : ℕ) : M (Option (Entity × Entities.FallingBlock)) := do
  match (← get).entity? i with
  | some e =>
    match e.data with
    | .fallingBlock dt => return some (e, dt)
    | _ => return none
  | none => return none

/-- Changes the data of the falling block entity with index `i`. -/
def modifyData (i : ℕ) (g : Entities.FallingBlock → Entities.FallingBlock) : M Unit :=
  Level.modifyEntity i fun e =>
    match e.data with
    | .fallingBlock dt => { e with data := .fallingBlock (g dt) }
    | _ => e

/-- The block is in the tag `minecraft:anvil`. -/
def isAnvil (b : Block) : Bool := b.is .anvil || b.is .chipped_anvil || b.is .damaged_anvil

/-- The block is a `ConcretePowderBlock`. -/
def isConcretePowder (b : Block) : Bool := b.id.name.endsWith "_concrete_powder"

/-- The blocks of the game that fall (`Fallable` blocks that have an item of the same name). -/
def isFallable (b : Block) : Bool :=
  b.is .sand || b.is .red_sand || b.is .gravel || b.is .dragon_egg || isAnvil b ||
    isConcretePowder b || b.is .suspicious_sand || b.is .suspicious_gravel

/-- `AnvilBlock.damage(state)`: the next more damaged anvil with the same facing, if any. -/
def damageAnvil (b : Block) : Option Block :=
  let next : Option BlockId :=
    if b.is .anvil then some .chipped_anvil
    else if b.is .chipped_anvil then some .damaged_anvil else none
  next.bind fun id => Block.ofProps? id fun k => (b.toProps.find? (·.1 == k)).map (·.2)

/-- `FallingBlockEntity.causeFallDamage(fallDistance, ...)`: a falling block that hurts entities
(an anvil) may be damaged by a fall of more than one block. The damage to living entities is
not modelled. -/
def causeFallDamage (i : ℕ) (fallDistance : Float) : M Unit := do
  let some (e, dt) ← get? i | return
  if !dt.hurtEntities then return
  let fallDistanceInt := Phys.ceil (fallDistance - 1.0)
  if fallDistanceInt < 0 then return
  let n : Float32 := Float32.ofInt fallDistanceInt
  let damage :=
    min (Phys.floor (n * Float32.ofBits (UInt32.ofNat dt.fallDamagePerDistance)).toFloat)
      dt.fallDamageMax
  if isAnvil dt.blockState && damage > 0 then
    let (draw, r) := (dt.phys.random.getD (Entity.randomAfterUuid e.id)).nextFloat24
    Level.modifyEntity i fun e => e.modifyPhys fun p => { p with random := some r }
    let chance : Float32 := Float32.ofBits 0x3d4ccccd + n * Float32.ofBits 0x3d4ccccd
    if Item.toFloat32 draw < chance then
      match damageAnvil dt.blockState with
      | some b => modifyData i fun dt => { dt with blockState := b }
      | none => modifyData i fun dt => { dt with cancelDrop := true }

/-- The kind of entity a falling block is: 0.98 wide and high, gravity 0.04. -/
def kind : Entity.Kind where
  dims := ⟨Phys.f 0x3efae148, Phys.f 0x3f7ae148⟩
  gravity := Phys.d 0x3fa47ae147ae147b
  causeFallDamage := causeFallDamage

/-- `FallingBlock.isFree(state)`: a falling block can fall into the block. The game also names
fire and liquids, which are replaceable. -/
def isFree (b : Block) : Bool := b.isAir || b.attrs.replaceable

/-- `BlockState.canBeReplaced(context)` for the placement of a block without an item in hand
(`DirectionalPlaceContext` with `ItemStack.EMPTY`), which is how a landing block asks. -/
def canBeReplaced (b : Block) : Bool :=
  let name := b.id.name
  let prop (k : String) := (b.toProps.find? (·.1 == k)).map (·.2)
  if name.endsWith "_slab" || b.is .pitcher_crop || b.is .scaffolding then false
  else if b.is .snow then prop "layers" == some "1"
  else if b.is .glow_lichen || b.is .sculk_vein || b.is .resin_clump then true
  else if b.is .vine then
    (["up", "north", "east", "south", "west"].filter fun k => prop k == some "true").length < 5
  else b.attrs.replaceable

/-- `ConcretePowderBlock.canSolidify(state)`: the block holds water. -/
def canSolidify (b : Block) : Bool := b.fluidState.fluid.isWater

/-- `ConcretePowderBlock.touchesLiquid(level, pos)`: a neighbour other than the one below holds
water and does not turn a sturdy face towards the block. -/
def touchesLiquid (l : Level) (p : Pos) : Bool :=
  [Direction.up, .north, .south, .west, .east].any fun dir =>
    let b := l.blockAt (p.step dir)
    canSolidify b && !b.attrs.isFaceSturdy dir.opposite

/-- The concrete that a concrete powder turns into. -/
def concreteOf (b : Block) : Option Block :=
  let name := b.id.name
  (BlockId.ofName? (String.ofList (name.toList.take (name.length - 7)))).map Block.default

/-- `Fallable.onLand(level, pos, state, replacedBlock, entity)`: concrete powder that lands in or
next to water turns to concrete. -/
def onLand (p : Pos) (state replaced : Block) : M Unit := do
  if isConcretePowder state && (canSolidify replaced || touchesLiquid (← get) p) then
    if let some concrete := concreteOf state then discard <| Level.setBlock p concrete

/-- `spawnAtLocation(level, block)`: the falling block with index `i` drops as an item where it
is. -/
def dropItem (i : ℕ) (pos : Vec3) (b : Block) : M Unit := do
  if isFallable b then discard <| Item.spawnAtLocation pos b.id.name (i + 1)
  else Level.setOverflow

/-- `blockState.setValue(WATERLOGGED, true)` for a block that has the property. -/
def waterlog (b : Block) : Block :=
  if b.toProps.any (·.1 == "waterlogged") then
    (Block.ofProps? b.id fun k =>
      if k == "waterlogged" then some "true" else (b.toProps.find? (·.1 == k)).map (·.2)).getD b
  else b

/-- The part of `FallingBlockEntity.tick` that runs when the entity is on the ground, or is
concrete powder in water (`isStuckInWater`): it turns into a block at `pos`, or breaks. `block`
is the block state the entity had at the start of the tick: the game drops the item of that
block, even if the fall has damaged an anvil since. -/
def land (i : ℕ) (block : Block) (pos : Pos) (isStuckInWater : Bool) : M Unit := do
  let some (e, dt) ← get? i | return
  let l ← get
  let currentState := l.blockAt pos
  Level.setEntity { e with base := { e.base with motion := e.base.motion.mul 0.7 (-0.5) 0.7 } }
  if currentState.is .moving_piston then return
  if dt.cancelDrop then
    Level.removeEntity i
    return
  let mayReplace := canBeReplaced currentState
  let wouldContinueFalling := isFree (l.blockAt (pos.step .down)) && !isStuckInWater
  let wouldSurvive :=
    (← Level.behaviour dt.blockState).canSurvive l pos && !wouldContinueFalling
  if mayReplace && wouldSurvive then
    -- a block that can be waterlogged takes the water source it lands in
    let placed :=
      if (l.fluidStateAt pos).fluid == .water then waterlog dt.blockState else dt.blockState
    if placed != dt.blockState then modifyData i fun dt => { dt with blockState := placed }
    if ← Level.setBlock pos placed then
      Level.removeEntity i
      onLand pos placed currentState
      if dt.hasBlockData && dt.blockState.hasBlockEntity then Level.setOverflow
    else if dt.dropItem then
      Level.removeEntity i
      dropItem i e.base.pos block
  else
    Level.removeEntity i
    if dt.dropItem then dropItem i e.base.pos block

/-- A block that holds water lies in the box spanned by the points `a` and `b`. -/
def waterBetween (l : Level) (a b : Vec3) : Bool :=
  let box := AABB.of a.x a.y a.z b.x b.y b.z
  box.blocks.any fun p => (l.fluidStateAt p).fluid.isWater

/-- `FallingBlockEntity.tick`. -/
def tick (i : ℕ) : M Unit := do
  let some (_, dt) ← get? i | return
  if dt.blockState.isAir then
    Level.removeEntity i
    return
  let block := dt.blockState
  modifyData i fun dt => { dt with time := dt.time + 1 }
  Level.modifyEntity i fun e => e.modifyPhys fun p => { p with tickCount := p.tickCount + 1 }
  Level.applyGravity kind i
  let some (e, _) ← get? i | return
  let old := e.base.pos
  Level.moveEntity kind i e.base.motion
  Level.applyEffectsFromBlocks kind i old
  let some (e, dt) ← get? i | return
  let l ← get
  let pos := e.base.pos.blockPos
  let isConcrete := isConcretePowder dt.blockState
  let isStuckInWater := isConcrete && (l.fluidStateAt pos).fluid.isWater
  -- fast concrete powder looks back for a water source it went through; the ray is not modelled
  if isConcrete && e.base.motion.lengthSqr > 1.0 && waterBetween l old e.base.pos then
    Level.setOverflow
  if !e.base.onGround && !isStuckInWater then
    let y := pos.y
    if (dt.time > 100 && (y ≤ -64 || y > 319)) || dt.time > 600 then
      Level.removeEntity i
      if dt.dropItem then dropItem i e.base.pos block
  else land i block pos isStuckInWater
  Level.modifyEntity i fun e =>
    let drag := kind.airDrag
    { e with base := { e.base with motion := e.base.motion.mul drag drag drag } }

/-- The behaviour of the entity. -/
def behaviour : EntityBehaviour := ⟨tick⟩

end Redstone.Entity.FallingBlock
