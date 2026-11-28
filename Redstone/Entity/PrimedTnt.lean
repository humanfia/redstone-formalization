module

public import Redstone.Entity.Tnt.Explosion

/-!
# Primed TNT

Java class: `PrimedTnt`, with the parts of `Entity` it uses (`move`, `collide`,
`checkSupportingBlock`, `checkFallDamage`, `restituteMovementAfterCollisions`,
`getBlockSpeedFactor`).

Every game tick a primed TNT is pulled down by gravity, moves and collides with blocks, loses
speed, and counts its fuse down. When the fuse runs out it disappears and explodes at one
sixteenth of its height above its position (`Redstone.Entity.Tnt.explode`).

## What is left out

* Blocks whose `entityInside` would change the entity itself in a way no component models
  (cobweb, sweet berry bush, powder snow, bubble column, the portals), and fluids, which push it
  (`updateFluidInteraction`): when the entity comes near one of them the model sets
  `Level.overflow`.
* Portals (`handlePortal`), the world border, and collisions with other entities (boats,
  shulkers).
* Collision shapes that do not depend on the block state alone; see
  `Redstone.Entity.Tnt.Physics`.
* Of `Block.fallOn` only the draw from the level's random number generator that farmland makes;
  the other overrides do nothing to an entity that takes no fall damage.
-/

@[expose] public section

namespace Redstone.Entity.PrimedTnt

open Redstone.Entity.Tnt

/-- `Entity.getOnPos(offset)`: the position of the block the entity counts as standing on,
`offset` below its feet; fences, walls and fence gates count although they are higher. -/
def getOnPos (l : Level) (pos : Vec3) (support : Option Pos) (offset : Float) : Pos :=
  match support with
  | some sp =>
    let below := (l.blockAt sp).id
    if (!(offset ≤ 0.5) || !isFence below) && !isWall below && !isFenceGate below then
      { sp with y := floorInt (pos.y - offset) }
    else sp
  | none => ⟨floorInt pos.x, floorInt (pos.y - offset), floorInt pos.z⟩

/-- `Entity.getOnPosLegacy()`. -/
def getOnPosLegacy (l : Level) (pos : Vec3) (support : Option Pos) : Pos :=
  getOnPos l pos support (wide 0x3e4ccccd)

/-- `Entity.getBlockPosBelowThatAffectsMyMovement()`. -/
def getBlockPosBelowThatAffectsMyMovement (l : Level) (pos : Vec3) (support : Option Pos) : Pos :=
  getOnPos l pos support (wide 0x3f000011)

/-- `Entity.getBlockSpeedFactor()`: the speed factor of the block the entity is in or, if that
is 1, of the block below (soul sand and honey slow entities down). -/
def getBlockSpeedFactor (l : Level) (pos : Vec3) (support : Option Pos) : Float :=
  let here := (l.blockAt (blockPos pos)).id
  let factor := (speedFactor here).toFloat
  if here != .water && here != .bubble_column && factor == 1.0 then
    (speedFactor (l.blockAt (getBlockPosBelowThatAffectsMyMovement l pos support)).id).toFloat
  else factor

/-- `Entity.collide(movement)` without entities and without stepping up: the part of
`movement` the entity can make, and whether a block shape the model does not have was met. -/
def collide (l : Level) (pos movement : Vec3) (fall : Float) : Vec3 × Bool :=
  if lengthSqr movement == 0.0 then (movement, false)
  else
    let box := entityBox pos
    let (shapes, unmodelled) := blockCollisions l fall (box.expandTowards movement)
    (collideWithShapes movement box shapes, unmodelled)

/-- The ray cast of `Entity.move` that resets the fall distance of a fast entity
(`ClipContext.Block.FALLDAMAGE_RESETTING`, `ClipContext.Fluid.WATER`): whether a block of the
tag `fall_damage_resetting` lies between `a` and `b`, and whether water does, whose shape the
model does not have. -/
def clipFallDamageResetting (l : Level) (a b : Vec3) : Bool × Bool :=
  let block : VoxelGrid := collisionGrid 1
  let hit := traverseBlocks
    (fun p => fallDamageResetting (l.blockAt p).id && clipHits block p a b) a b
  let water := traverseBlocks (fun p => (l.blockAt p).attrs.fluid.startsWith "minecraft:water") a b
  (hit, water)

/-- `Entity.checkSupportingBlock(onGround, movement)` for an entity at `pos`: the new values of
`mainSupportingBlockPos` and `onGroundNoBlocks`, and whether a block shape the model does not
have was met. -/
def checkSupportingBlock (l : Level) (pos movement : Vec3) (d : Entities.Tnt) (onGround : Bool) :
    Option Pos × Bool × Bool :=
  if onGround then
    let box := entityBox pos
    let testArea : AABB := ⟨box.minX, box.minY - 1.0e-6, box.minZ, box.maxX, box.minY, box.maxZ⟩
    let (support, bad) := findSupportingBlock l d.fallDistance pos testArea
    if support.isSome || d.onGroundNoBlocks then (support, support.isNone, bad)
    else
      let (support, bad') := findSupportingBlock l d.fallDistance pos
        (testArea.move ⟨-movement.x, 0.0, -movement.z⟩)
      (support, support.isNone, bad || bad')
  else (none, false, false)

/-- `Entity.restituteMovementAfterCollisions`: the velocity after a collision. The components
along which the entity was stopped become zero, unless it landed fast enough on a block that
bounces (slime, beds), in which case it is thrown back up. Returns the velocity and whether the
entity bounced. -/
def restituteMovementAfterCollisions (effectState : Block) (xCollision zCollision
    verticalCollision verticalCollisionBelow : Bool) (movement current : Vec3) : Vec3 × Bool :=
  let restitution : Float := 0.0
  let after := if xCollision then vset current .x (-current.x * restitution) else current
  let after := if zCollision then vset after .z (-current.z * restitution) else after
  if verticalCollision then
    let restitution :=
      if verticalCollisionBelow then
        if !(-current.y ≤ 0.04) && !suppressesBounce effectState.id then
          jmax restitution
            ((bounceRestitution effectState.id) * Float32.ofBits 0x3f4ccccd).toFloat
        else 0.0
      else restitution
    if restitution > 0.0 then
      let portionWithMovement := movement.y / current.y
      let gravityCompensation := portionWithMovement * 0.04
      let effectiveDrag := lerp portionWithMovement 1.0 (wide 0x3f7ae148)
      (vset after .y ((gravityCompensation - current.y) * effectiveDrag * restitution), true)
    else (vset after .y ((0.0 - current.y) * 1.0 * restitution), false)
  else (after, false)

/-- `Entity.move(MoverType.SELF, delta)` for a primed TNT with position, velocity and data as
given, on the server: collides the movement with the blocks, moves, finds out whether the
entity is on the ground and on which block, counts the fall, and changes the velocity for the
collision and for the block below. Returns the new common state and data, and the movement made
if the entity moved (`addMovementThisTick`). -/
def move (base : Entities.Base) (d : Entities.Tnt) :
    M (Entities.Base × Entities.Tnt × Option Entities.Movement) := do
  let l ← get
  let delta := base.motion
  let pos := base.pos
  let (movement, unmodelled) := collide l pos delta d.fallDistance
  if unmodelled then Level.setOverflow
  let movementLength := lengthSqr movement
  let moved := movementLength > 1.0e-7 || lengthSqr delta - movementLength < 1.0e-7
  let mut fall := d.fallDistance
  if moved && fall != 0.0 && movementLength ≥ 1.0 then
    let checkDistance := jmin (Float.sqrt movementLength) 8.0
    let (hit, water) :=
      clipFallDamageResetting l pos (vadd pos (vscale (normalize movement) checkDistance))
    if water then Level.setOverflow
    if hit then fall := 0.0
  let made : Option Entities.Movement :=
    if moved then some ⟨pos, vadd pos movement, some delta⟩ else none
  let pos := if moved then vadd pos movement else pos
  let xCollision := !((movement.x - delta.x).abs < wide 0x3727c5ac)
  let zCollision := !((movement.z - delta.z).abs < wide 0x3727c5ac)
  let horizontalCollision := xCollision || zCollision
  let movedVertically := delta.y.abs > 0.0
  let verticalCollision := delta.y != movement.y
  let verticalCollisionBelow := verticalCollision && delta.y < 0.0
  let onGround := verticalCollisionBelow
  let (support, noBlocks, unmodelled) :=
    checkSupportingBlock l pos movement { d with fallDistance := fall } onGround
  if unmodelled then Level.setOverflow
  let effectPos := getOnPosLegacy l pos support
  let effectState := l.blockAt effectPos
  -- `checkFallDamage`
  if movement.y < 0.0 then fall := fall - movement.y.toFloat32.toFloat
  if onGround then
    if fall > 0.0 then
      -- `FarmlandBlock.fallOn` draws a number before it looks at the entity
      if effectState.is .farmland then discard <| drawRandom nextFloat
      Level.gameEvent "minecraft:hit_ground" (blockPos pos)
    fall := 0.0
  let mut motion := delta
  if (movedVertically && verticalCollision) || horizontalCollision then
    let (after, bounced) := restituteMovementAfterCollisions effectState xCollision zCollision
      verticalCollision verticalCollisionBelow movement motion
    if bounced then Level.gameEvent "minecraft:bounce" (blockPos pos)
    motion := after
  let factor := getBlockSpeedFactor (← get) pos support
  motion := vmul motion factor 1.0 factor
  return (⟨pos, motion, onGround⟩,
    { d with fallDistance := fall, supportingBlock := support, onGroundNoBlocks := noBlocks },
    made)

/-- Whether the entity, moving from `old` to `new`, comes near a block that would act on it in
a way the model does not have: a fluid, or a block whose `entityInside` changes the entity. -/
def touchesUnmodelled (l : Level) (old new : Vec3) : Bool :=
  let a := entityBox old
  let b := entityBox new
  (intRange (floorInt (jmin a.minX b.minX)) (floorInt (jmax a.maxX b.maxX) + 1)).any fun x =>
    (intRange (floorInt (jmin a.minY b.minY)) (floorInt (jmax a.maxY b.maxY) + 1)).any fun y =>
      (intRange (floorInt (jmin a.minZ b.minZ)) (floorInt (jmax a.maxZ b.maxZ) + 1)).any fun z =>
        let block := l.blockAt ⟨x, y, z⟩
        !block.attrs.fluid.isEmpty ||
          [BlockId.cobweb, .sweet_berry_bush, .powder_snow, .bubble_column, .nether_portal,
            .end_portal, .end_gateway].contains block.id

/-- `PrimedTnt.tick()`. -/
def tick (index : ℕ) : M Unit := do
  let some e := (← get).entity? index | return
  let .tnt d := e.data | return
  -- `applyGravity`
  let m := e.base.motion
  let (base, d, made) ← move { e.base with motion := ⟨m.x + 0.0, m.y + -0.04, m.z + 0.0⟩ } d
  Level.modifyEntity index fun e => { e with base := base, data := .tnt d }
  if touchesUnmodelled (← get) e.base.pos base.pos then Level.setOverflow
  -- `applyEffectsFromBlocks`: the block below is stepped on, the blocks on the way are told
  let l ← get
  let effectPos :=
    if base.onGround then some (getOnPosLegacy l base.pos d.supportingBlock) else none
  Touch.applyEffectsFromBlocks dims index effectPos
    (Touch.finalMovements made.toList e.base.pos base.pos)
  let some e := (← get).entity? index | return
  let .tnt d := e.data | return
  let motion := vscale e.base.motion (wide 0x3f7ae148)
  let motion := if e.base.onGround then vmul motion 0.7 (-0.5) 0.7 else motion
  let fuse := d.fuse - 1
  if fuse ≤ 0 then
    -- `discard()` and `explode()`
    Level.removeEntity index
    let pos := e.base.pos
    explode ⟨pos.x, pos.y + wide 0x3f7ae148 * 0.0625, pos.z⟩ (Float32.ofBits d.explosionPower)
  else
    Level.modifyEntity index fun e =>
      { e with base := { e.base with motion := motion }, data := .tnt { d with fuse := fuse } }

/-- The behaviour of the entity. -/
def behaviour : EntityBehaviour := ⟨tick⟩

end Redstone.Entity.PrimedTnt
