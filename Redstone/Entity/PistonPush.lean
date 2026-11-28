module

public import Redstone.Entity.FallingBlock
public import Redstone.Entity.Still

/-!
# Entities moved by pistons

Java classes: `PistonMovingBlockEntity` (`moveCollidedEntities`, `moveStuckEntities`,
`moveEntityByPiston`, `fixEntityWithinPistonBase`), `PistonMath`, and `Entity.move` with
`MoverType.PISTON` (`Redstone.Level.moveEntity`).

A block that a piston moves takes half a block in each of its two ticks. Before it does, it
pushes the entities that are in the space it is about to take (`moveCollidedEntities`): each
is moved just far enough to be out of the way, and 0.01 further. A slime block also sets the
velocity of these entities to one block per tick along the movement, which is what launches
them. A honey block that moves sideways takes along the entities that stand on it
(`moveStuckEntities`). The base of a retracting piston pulls the entities that are in the way
of its head back out of the base (`fixEntityWithinPistonBase`).

While an entity is moved by a piston, the blocks that are moving in the direction of that
piston and have not arrived are not in its way (`NOCLIP`, see `Level.movingPistonShape`).

## What is left out

* Only dropped items and falling blocks are moved, the entities whose motion goes through
  `Level.moveEntity`. Primed TNT and minecarts have a motion of their own in the model, which
  does not know the shape of a moving block, and the other entities are not moved at all: when
  a piston would move one of these the model sets `Level.overflow`. Entities that pistons
  ignore (`PushReaction.IGNORE_ENTITY`: markers, marker armour stands, displays, interactions,
  area effect clouds, ominous item spawners) are left alone, as in the game.
* An entity of a type the model has no size for is not found.
* While a piston moves an entity, the game takes the blocks that move the same way out of
  every question about collision shapes (`NOCLIP` is a thread-local). The model does so for
  the collisions of the entity that is moved; a block that asks for the support of such a
  moving block during the reactions to that movement (an item pushed onto a pressure plate,
  say) gets the answer it would get outside the push.
* A moved block whose collision shape is not modelled (`Block.collisionUnmodelled`) sets
  `Level.overflow` if an entity is within two blocks of it.
* The order in which the entities are pushed is that of the game's entity sections, known for
  the entities whose motion is modelled (`Entity.Item.sectionKey`).
-/

@[expose] public section

namespace Redstone.Entity.PistonPush

open BlockEntities (Piston)

/-- `0.01`, the `PUSH_OFFSET`. -/
def pushOffset : Float := Phys.d 0x3f847ae147ae147b

/-- The kind of an entity that the model can move by a piston. -/
def kind? (e : Entity) : Option Entity.Kind :=
  match e.data with
  | .item _ => some Item.kind
  | .fallingBlock _ => some FallingBlock.kind
  | _ => none

/-- `Entity.getPistonPushReaction() == PushReaction.IGNORE_ENTITY`. -/
def ignoresPistons (e : Entity) : Bool :=
  match e.data with
  | .other type d =>
    (type == "minecraft:armor_stand" && d.marker) ||
      ["minecraft:marker", "minecraft:area_effect_cloud", "minecraft:interaction",
        "minecraft:block_display", "minecraft:item_display", "minecraft:text_display",
        "minecraft:ominous_item_spawner"].contains type
  | _ => false

/-- `Entity.getBoundingBox()`. -/
def boundingBox? (e : Entity) : Option AABB :=
  match kind? e with
  | some k => some (k.dims.box e.base.pos)
  | none => Still.boundingBox? e

/-- `Level.getEntities(null, box)`: the entities whose box meets `box` and whose position is in
a section the search looks at, in the order of the entity sections. -/
def getEntities (l : Level) (box : AABB) : List Entity :=
  let found := l.entities.filter fun e =>
    Still.inSearchedSections e.base.pos box && (boundingBox? e).any (·.intersects box)
  found.foldl (fun acc e => Item.insertBySection e acc) []

/-- `PistonMath.getMovementArea(aabb, direction, amount)`: the space that the face `direction`
of the box sweeps when the box moves by `amount`. -/
def getMovementArea (aabb : AABB) (direction : Direction) (amount : Float) : AABB :=
  let positive := direction = .up || direction = .south || direction = .east
  let delta := amount * (if positive then 1.0 else -1.0)
  let lo := Phys.min delta 0.0
  let hi := Phys.max delta 0.0
  match direction with
  | .west => .of (aabb.minX + lo) aabb.minY aabb.minZ (aabb.minX + hi) aabb.maxY aabb.maxZ
  | .east => .of (aabb.maxX + lo) aabb.minY aabb.minZ (aabb.maxX + hi) aabb.maxY aabb.maxZ
  | .down => .of aabb.minX (aabb.minY + lo) aabb.minZ aabb.maxX (aabb.minY + hi) aabb.maxZ
  | .up => .of aabb.minX (aabb.maxY + lo) aabb.minZ aabb.maxX (aabb.maxY + hi) aabb.maxZ
  | .north => .of aabb.minX aabb.minY (aabb.minZ + lo) aabb.maxX aabb.maxY (aabb.minZ + hi)
  | .south => .of aabb.minX aabb.minY (aabb.maxZ + lo) aabb.maxX aabb.maxY (aabb.maxZ + hi)

/-- `AABB.minmax(other)`: the smallest box that holds both. -/
def minmax (a b : AABB) : AABB :=
  ⟨Phys.min a.minX b.minX, Phys.min a.minY b.minY, Phys.min a.minZ b.minZ,
    Phys.max a.maxX b.maxX, Phys.max a.maxY b.maxY, Phys.max a.maxZ b.maxZ⟩

/-- `AABB.intersect(other)`: the common part of two boxes. -/
def intersect (a b : AABB) : AABB :=
  .of (Phys.max a.minX b.minX) (Phys.max a.minY b.minY) (Phys.max a.minZ b.minZ)
    (Phys.min a.maxX b.maxX) (Phys.min a.maxY b.maxY) (Phys.min a.maxZ b.maxZ)

/-- `PistonMovingBlockEntity.getMovement(aabbToBeOutsideOf, movement, aabb)`: how far `aabb`
has to go in the direction `movement` to be out of the other box. -/
def getMovement (aabbToBeOutsideOf : AABB) (movement : Direction) (aabb : AABB) : Float :=
  match movement with
  | .east => aabbToBeOutsideOf.maxX - aabb.minX
  | .west => aabb.maxX - aabbToBeOutsideOf.minX
  | .up => aabbToBeOutsideOf.maxY - aabb.minY
  | .down => aabb.maxY - aabbToBeOutsideOf.minY
  | .south => aabbToBeOutsideOf.maxZ - aabb.minZ
  | .north => aabb.maxZ - aabbToBeOutsideOf.minZ

/-- `PistonMovingBlockEntity.moveByPositionAndProgress(pos, aabb, entity)`: a box of the moved
block, given relative to the block, where the block is now. -/
def moveByPositionAndProgress (pos : Pos) (aabb : AABB) (self : Piston) : AABB :=
  let currentPosition := Level.pistonExtendedProgress self
  let step := self.direction.stepVec
  aabb.move ⟨Phys.ofInt pos.x + currentPosition * step.x,
    Phys.ofInt pos.y + currentPosition * step.y,
    Phys.ofInt pos.z + currentPosition * step.z⟩

/-- `PistonMovingBlockEntity.getCollisionRelatedBlockState()`: the block whose shape pushes the
entities. For the base of a retracting piston it is the head that moves back. -/
def collisionRelatedBlockState (self : Piston) : Block :=
  match self.movedState with
  | .pistonBase id s =>
    if !self.extending && self.isSourcePiston then
      let type : PistonType :=
        match id with
        | .sticky_piston => .sticky
        | .piston => .normal
      .pistonHead ⟨s.facing, decide (self.progress > 1 / 4), type⟩
    else self.movedState
  | _ => self.movedState

/-- `VoxelShape.bounds()` of a shape that is not empty. -/
def bounds (s : Shape) : AABB :=
  ⟨s.min .x, s.min .y, s.min .z, s.max .x, s.max .y, s.max .z⟩

/-- `PistonMovingBlockEntity.moveEntityByPiston(pistonDirection, entity, delta, movement)` for
the entity with index `i`: the entity is moved by `delta` in the direction `movement`
(`Entity.move(MoverType.PISTON, ...)`) while the blocks that move in `pistonDirection` are not
in its way, the effects of the blocks on this way are applied, and the movement is taken off
the record of the movements of this tick (`removeLatestMovementRecording`). An entity whose
motion the model does not have sets `Level.overflow`. -/
def moveEntityByPiston (pistonDirection : Direction) (i : ℕ) (delta : Float)
    (movement : Direction) : M Unit := do
  let some e ← Level.getEntity i | return
  let some k := kind? e
    | Level.setOverflow
  let previousPos := e.base.pos
  let step := movement.stepVec
  Level.moveEntity k i ⟨delta * step.x, delta * step.y, delta * step.z⟩ (some pistonDirection)
  -- `applyEffectsFromBlocks(previousPos, position())`
  if let some e ← Level.getEntity i then
    if !e.phys.noPhysics then
      let l ← get
      let effectPos := if e.base.onGround then some (Entity.getOnPosLegacy l e) else none
      Touch.applyEffectsFromBlocks k.dims i effectPos [⟨previousPos, e.base.pos, none⟩]
  Level.modifyEntity i fun e =>
    e.modifyPhys fun p => { p with movementThisTick := p.movementThisTick.dropLast }

/-- `PistonMovingBlockEntity.fixEntityWithinPistonBase(pos, entity, direction, deltaProgress)`:
an entity that the head of a retracting piston pushed into the base at `pos` is moved back out
of the base, against the movement. -/
def fixEntityWithinPistonBase (pos : Pos) (i : ℕ) (direction : Direction)
    (deltaProgress : Float) : M Unit := do
  let some e ← Level.getEntity i | return
  let some entityAabb := boundingBox? e | return
  let box := AABB.ofBlock pos
  if entityAabb.intersects box then
    let opposite := direction.opposite
    let delta := getMovement box opposite entityAabb + pushOffset
    let deltaIntersected := getMovement box opposite (intersect entityAabb box) + pushOffset
    if (delta - deltaIntersected).abs < pushOffset then
      let delta := Phys.min delta deltaProgress + pushOffset
      moveEntityByPiston direction i delta opposite

/-- `PistonMovingBlockEntity.moveCollidedEntities(level, pos, newProgress, self)` for the block
entity `self` at `pos`, before its progress becomes `newProgress`: the entities in the space
the moved block is about to take are pushed out of it. -/
def moveCollidedEntities (pos : Pos) (newProgress : ℚ) (self : Piston) : M Unit := do
  let movement := self.movementDirection
  let deltaProgress := Phys.ofRat (newProgress - self.progress)
  let state := collisionRelatedBlockState self
  let l ← get
  if state.collisionUnmodelled then
    if !(getEntities l ((AABB.ofBlock pos).inflate 2.0 2.0 2.0)).isEmpty then Level.setOverflow
    return
  let shape := state.collisionShape
  if shape.isEmpty then return
  let aabb := moveByPositionAndProgress pos (bounds shape) self
  let entities := getEntities l (minmax (getMovementArea aabb movement deltaProgress) aabb)
  let causeBounce := self.movedState.is .slime_block
  for found in entities do
    let i := found.index
    let some e ← Level.getEntity i | continue
    if ignoresPistons e then continue
    let some entityAabb := boundingBox? e | continue
    let delta := shape.boxes.foldl (init := (0.0 : Float)) fun delta shapeAabb =>
      let movingAABB :=
        getMovementArea (moveByPositionAndProgress pos shapeAabb self) movement deltaProgress
      if movingAABB.intersects entityAabb then
        Phys.max delta (getMovement movingAABB movement entityAabb)
      else delta
    if (kind? e).isNone then
      -- an entity whose motion the model does not have, and that the game would change
      if causeBounce || !(delta ≤ 0.0) then Level.setOverflow
      continue
    if causeBounce then
      let step := movement.stepVec
      let motion :=
        match movement.axis with
        | .x => e.base.motion.set .x step.x
        | .y => e.base.motion.set .y step.y
        | .z => e.base.motion.set .z step.z
      Level.modifyEntity i fun e => { e with base := { e.base with motion := motion } }
    if !(delta ≤ 0.0) then
      let delta := Phys.min delta deltaProgress + pushOffset
      moveEntityByPiston movement i delta movement
      if !self.extending && self.isSourcePiston then
        fixEntityWithinPistonBase pos i movement deltaProgress

/-- `PistonMovingBlockEntity.moveStuckEntities(level, pos, newProgress, self)`: a honey block
that moves sideways takes along the entities that stand on it. -/
def moveStuckEntities (pos : Pos) (newProgress : ℚ) (self : Piston) : M Unit := do
  if !self.movedState.is .honey_block then return
  let movement := self.movementDirection
  if movement.axis = .y then return
  let stickyTop := self.movedState.collisionShape.max .y
  let aabb := moveByPositionAndProgress pos
    (.of 0.0 stickyTop 0.0 1.0 (Phys.d 0x3ff800010c6f7a0c) 1.0) self
  let deltaProgress := Phys.ofRat (newProgress - self.progress)
  let l ← get
  -- `matchesStickyCritera(aabb, entity, pos)`
  let stuck := (getEntities l aabb).filter fun e =>
    !ignoresPistons e && e.base.onGround &&
      ((kind? e).isNone || e.phys.mainSupportingBlockPos == some pos ||
        (e.base.pos.x ≥ aabb.minX && e.base.pos.x ≤ aabb.maxX &&
          e.base.pos.z ≥ aabb.minZ && e.base.pos.z ≤ aabb.maxZ))
  for found in stuck do moveEntityByPiston movement found.index deltaProgress movement

/-- The part of `PistonMovingBlockEntity.tick` that moves entities, for the block entity
`self` at `pos`, before its progress becomes `newProgress`. -/
def moveEntities (pos : Pos) (newProgress : ℚ) (self : Piston) : M Unit := do
  moveCollidedEntities pos newProgress self
  moveStuckEntities pos newProgress self

end Redstone.Entity.PistonPush
