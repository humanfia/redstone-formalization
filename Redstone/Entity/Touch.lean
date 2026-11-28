module

public import Redstone.Mechanics.Tick
public import Redstone.Block.Generated.Shapes
public import Redstone.Entity.Geometry

/-!
# How an entity touches blocks

Java classes: `Entity` (`applyEffectsFromBlocks`, `checkInsideBlocks`,
`collidedWithShapeMovingFrom`), `BlockGetter` (`forEachBlockIntersectedBetween`,
`addCollisionsAlongTravel`, `getFurthestCorner`), `BlockPos` (`betweenClosed`,
`betweenCornersInDirection`), `BlockBehaviour.getEntityInsideCollisionShape`.

Once per tick, or more often, an entity tells the blocks that it touches them. The block it
stands on is stepped on (`Block.stepOn`). Then every movement the entity made since the last
time is gone through again: a movement made by `Entity.move` one axis after the other, any
other in a straight line. Along each stretch the game visits the blocks that the box of the
entity sweeps over, in a fixed order, and each of them whose shape the entity meets on the way
is told that the entity is inside it (`BlockBehaviour.entityInside`), once.

This is the one implementation of that for every entity unit of the model. A unit says what
its entity is like (`Dimensions`), which block it stands on and which movements it made; the
rest is here.

The shape a block is touched by (`getEntityInsideCollisionShape`) is the full cube for every
block but a few: tripwire and the end portal are touched by their outline, a filled cauldron by
its hollow shape, powder snow by its collision shape if it has one.

## What is left out

* Fluids (`FluidState.entityInside`, `Entity.collidedWithFluid`): the entity units set
  `Level.overflow` when their entity comes near a fluid.
* The effects that blocks ask for through the `InsideBlockEffectApplier` (fire, freezing,
  extinguishing), and rain putting out a burning entity.
* The shapes of filled cauldrons and of powder snow. No reaction of these blocks is modelled,
  so they are taken as full cubes, which changes nothing.
-/

@[expose] public section

namespace Redstone

namespace Entity.Touch

open Entities (Movement)

/-! ### The order of the blocks -/

/-- `BlockPos.betweenCornersInDirection(x1, y1, z1, x2, y2, z2, direction)`: the block positions
of the box between two corners. The vertical axis changes slowest, then the horizontal axis
along which `direction` is larger, then the other one; along each axis the positions are gone
through in the sense of `direction`. -/
def betweenCornersInDirection (a b : Pos) (direction : Vec3) : List Pos :=
  let lo : Pos := ⟨min a.x b.x, min a.y b.y, min a.z b.z⟩
  let hi : Pos := ⟨max a.x b.x, max a.y b.y, max a.z b.z⟩
  let line (ax : Axis) : List ℤ :=
    let (l, h) : ℤ × ℤ :=
      match ax with
      | .x => (lo.x, hi.x)
      | .y => (lo.y, hi.y)
      | .z => (lo.z, hi.z)
    let count := (h - l + 1).toNat
    if direction.get ax ≥ 0.0 then (List.range count).map fun i => l + i
    else (List.range count).map fun i => h - i
  let pos (ax1 : Axis) (v1 : ℤ) (ax2 : Axis) (v2 : ℤ) (ax3 : Axis) (v3 : ℤ) : Pos :=
    let set (p : Pos) (ax : Axis) (v : ℤ) : Pos :=
      match ax with
      | .x => { p with x := v }
      | .y => { p with y := v }
      | .z => { p with z := v }
    set (set (set ⟨0, 0, 0⟩ ax1 v1) ax2 v2) ax3 v3
  match Phys.axisStepOrder direction with
  | [first, second, third] =>
    (line first).flatMap fun v1 => (line second).flatMap fun v2 =>
      (line third).map fun v3 => pos first v1 second v2 third v3
  | _ => []

/-- `BlockPos.betweenCornersInDirection(aabb, direction)`. -/
def betweenBoxCornersInDirection (box : AABB) (direction : Vec3) : List Pos :=
  betweenCornersInDirection ⟨Phys.floor box.minX, Phys.floor box.minY, Phys.floor box.minZ⟩
    ⟨Phys.floor box.maxX, Phys.floor box.maxY, Phys.floor box.maxZ⟩ direction

/-- `BlockGetter.getFurthestCorner(direction)`: the corner of the box that
`addCollisionsAlongTravel` follows, as three signs. -/
def furthestCorner (direction : Vec3) : ℤ × ℤ × ℤ :=
  let xDot := direction.x.abs
  let yDot := direction.y.abs
  let zDot := direction.z.abs
  let xSign : ℤ := if direction.x ≥ 0.0 then 1 else -1
  let ySign : ℤ := if direction.y ≥ 0.0 then 1 else -1
  let zSign : ℤ := if direction.z ≥ 0.0 then 1 else -1
  if xDot ≤ yDot && xDot ≤ zDot then (-xSign, -zSign, ySign)
  else if yDot ≤ zDot then (zSign, -ySign, -xSign)
  else (-ySign, xSign, -zSign)

/-- `Mth.frac`. -/
def frac (v : Float) : Float := v - Phys.ofInt (Phys.floor v)

/-- `Mth.sign`. -/
def sign (v : Float) : ℤ := if v == 0.0 then 0 else if v > 0.0 then 1 else -1

/-- `Mth.clamp` on doubles. -/
def clamp (v lo hi : Float) : Float := if v < lo then lo else Phys.min v hi

/-- The lower bound `block + 1.0E-5F` of `addCollisionsAlongTravel`, which the game computes in
`float`. -/
def lowerEdge (block : ℤ) : Float :=
  ((Phys.ofInt block).toFloat32 + Float32.ofBits 0x3727c5ac).toFloat

/-- The state of the walk of `addCollisionsAlongTravel`. -/
structure Walk where
  /-- The block the followed corner is in. -/
  corner : Pos
  tX : Float
  tY : Float
  tZ : Float
  /-- The number of blocks the corner has entered. -/
  iterations : ℕ := 0
  /-- The blocks found so far, last first, each with the iteration that found it. -/
  found : List (Pos × ℕ) := []
  /-- The blocks found by the caller before the walk. -/
  visited : List Pos

/-- `BlockGetter.addCollisionsAlongTravel`: one corner of the box is followed along the
movement `delta` to its place in `box`, the box at the end. Each time the corner enters a block,
the blocks between that block and the one the opposite corner is in at that moment are found, in
the order of `betweenCornersInDirection`. Returns the blocks that are not in `visited`, each
with the number of the step that found it, and the number of steps. -/
def collisionsAlongTravel (visited : List Pos) (delta : Vec3) (box : AABB) :
    List (Pos × ℕ) × ℕ :=
  let sizeX := box.size .x
  let sizeY := box.size .y
  let sizeZ := box.size .z
  let (cx, cy, cz) := furthestCorner delta
  let centre := box.center
  let toCorner : Vec3 := ⟨centre.x + sizeX * 0.5 * Phys.ofInt cx,
    centre.y + sizeY * 0.5 * Phys.ofInt cy, centre.z + sizeZ * 0.5 * Phys.ofInt cz⟩
  let fromCorner := toCorner.sub delta
  let signX := sign delta.x
  let signY := sign delta.y
  let signZ := sign delta.z
  let maxValue := Phys.d 0x7fefffffffffffff
  let tDeltaX := if signX == 0 then maxValue else Phys.ofInt signX / delta.x
  let tDeltaY := if signY == 0 then maxValue else Phys.ofInt signY / delta.y
  let tDeltaZ := if signZ == 0 then maxValue else Phys.ofInt signZ / delta.z
  let start : Walk :=
    { corner := fromCorner.blockPos
      tX := tDeltaX * (if signX > 0 then 1.0 - frac fromCorner.x else frac fromCorner.x)
      tY := tDeltaY * (if signY > 0 then 1.0 - frac fromCorner.y else frac fromCorner.y)
      tZ := tDeltaZ * (if signZ > 0 then 1.0 - frac fromCorner.z else frac fromCorner.z)
      visited := visited }
  let step (w : Walk) : Walk :=
    let w :=
      if w.tX < w.tY then
        if w.tX < w.tZ then
          { w with corner := { w.corner with x := w.corner.x + signX }, tX := w.tX + tDeltaX }
        else { w with corner := { w.corner with z := w.corner.z + signZ }, tZ := w.tZ + tDeltaZ }
      else if w.tY < w.tZ then
        { w with corner := { w.corner with y := w.corner.y + signY }, tY := w.tY + tDeltaY }
      else { w with corner := { w.corner with z := w.corner.z + signZ }, tZ := w.tZ + tDeltaZ }
    let c := w.corner
    match (AABB.ofBlock c).clip fromCorner toCorner with
    | none => w
    | some hit =>
      let iterations := w.iterations + 1
      let hitX := clamp hit.x (lowerEdge c.x) (Phys.ofInt c.x + 1.0 - Phys.eps5f)
      let hitY := clamp hit.y (lowerEdge c.y) (Phys.ofInt c.y + 1.0 - Phys.eps5f)
      let hitZ := clamp hit.z (lowerEdge c.z) (Phys.ofInt c.z + 1.0 - Phys.eps5f)
      let opposite : Pos := ⟨Phys.floor (hitX - sizeX * Phys.ofInt cx),
        Phys.floor (hitY - sizeY * Phys.ofInt cy), Phys.floor (hitZ - sizeZ * Phys.ofInt cz)⟩
      (betweenCornersInDirection c opposite delta).foldl (init := { w with iterations }) fun w p =>
        if w.visited.contains p then w
        else { w with visited := p :: w.visited, found := (p, iterations) :: w.found }
  -- every step takes the corner one block further, and it ends within the movement
  let fuel := (Phys.floor delta.x.abs + Phys.floor delta.y.abs + Phys.floor delta.z.abs).toNat + 8
  let rec loop : ℕ → Walk → Walk
    | 0, w => w
    | n + 1, w => if w.tX ≤ 1.0 || w.tY ≤ 1.0 || w.tZ ≤ 1.0 then loop n (step w) else w
  let w := loop fuel start
  (w.found.reverse, w.iterations)

/-- `BlockGetter.forEachBlockIntersectedBetween(from, to, aabbAtTarget, visitor)`: the blocks
that the box `box`, which is where the entity ends, went over on its way from `start` to
`stop`, in the order in which the game visits them, each with the number of its step. An entity
that hardly moved visits the blocks of its box (`BlockPos.betweenClosed`). Otherwise the blocks
of the box at the start come first, then those on the way, then those of the box at the end. -/
def blocksIntersectedBetween (start stop : Vec3) (box : AABB) : List (Pos × ℕ) :=
  let travel := stop.sub start
  let small := Float32.ofBits 0x3727c5ac
  if travel.lengthSqr < (small * small).toFloat then box.blocks.map (·, 0)
  else
    let first := betweenBoxCornersInDirection (box.move (travel.mul (-1.0) (-1.0) (-1.0))) travel
    let (along, iterations) := collisionsAlongTravel first.reverse travel box
    let seen := first ++ along.map (·.1)
    let last := (betweenBoxCornersInDirection box travel).filter fun p => !seen.contains p
    first.map (·, 0) ++ along ++ last.map (·, iterations + 1)

/-! ### The shape a block is touched by -/

/-- `BlockState.getEntityInsideCollisionShape`: the boxes of the shape by which an entity
touches the block, in the coordinates of the block; `none` stands for the full cube
(`Shapes.block()`), which every entity that visits the block touches. Tripwire and the end
portal are touched by their outline. -/
def insideShape (b : Block) : Option (List AABB) :=
  if b.is .tripwire || b.is .end_portal then
    some (AABB.listOfBits (Block.shapeBits.getD b.attrs.outline #[]).toList)
  else none

/-- `Entity.collidedWithShapeMovingFrom(from, to, aabbs)` for the shape of the block at `p`: the
entity of size `dims`, going from `start` to `stop`, meets the block. -/
def collidedWithBlock (dims : Dimensions) (b : Block) (p : Pos) (start stop : Vec3) : Bool :=
  match insideShape b with
  | none => true
  | some parts =>
    (dims.box start).collidedAlongVector (stop.sub start) (parts.map (·.atBlock p))

/-! ### Telling the blocks -/

/-- `Entity.checkInsideBlocks(from, to, effectCollector, visitedBlocks, maxMovementIterations)`
for the entity with index `i`: the blocks on the way from `start` to `stop` that the entity
meets, and that are not in `visited` yet, are told that the entity is inside them. The walk ends
when the entity is gone, or at step `maxIterations`. Returns the blocks told so far and the
number of steps made. -/
def checkInsideBlocksBetween (dims : Dimensions) (i : ℕ) (start stop : Vec3) (visited : List Pos)
    (maxIterations : ℤ) : M (List Pos × ℤ) := do
  let box := (dims.box stop).deflate Phys.eps5f
  let mut visited := visited
  let mut iterations : ℕ := 0
  for (p, iteration) in blocksIntersectedBetween start stop box do
    if ((← get).entity? i).isNone then break
    if (iteration : ℤ) ≥ maxIterations then break
    iterations := iteration
    let state ← Level.getBlock p
    if !state.isAir && collidedWithBlock dims state p start stop && !visited.contains p then
      visited := p :: visited
      (← Level.behaviour state).entityInside p i
  return (visited, (iterations : ℤ) + 1)

/-- `Entity.checkInsideBlocks(movements, effectCollector)` for the entity with index `i`. A
movement that `Entity.move` made is gone through one axis after the other, in the order in which
the movement that was asked for is resolved; any other movement in a straight line. At most 16
steps are made for one movement; if they are used up, the blocks at its end are visited. -/
def checkInsideBlocks (dims : Dimensions) (i : ℕ) (movements : List Movement) : M Unit := do
  let mut visited : List Pos := []
  for movement in movements do
    let delta := movement.stop.sub movement.start
    let mut left : ℤ := 16
    match movement.original with
    | some original =>
      if delta.lengthSqr > 0.0 then
        let mut pos := movement.start
        for ax in Phys.axisStepOrder original do
          let axisMove := delta.get ax
          if axisMove != 0.0 then
            -- `Vec3.relative(axis.getPositive(), axisMove)`
            let target : Vec3 :=
              match ax with
              | .x => ⟨pos.x + axisMove * 1.0, pos.y + axisMove * 0.0, pos.z + axisMove * 0.0⟩
              | .y => ⟨pos.x + axisMove * 0.0, pos.y + axisMove * 1.0, pos.z + axisMove * 0.0⟩
              | .z => ⟨pos.x + axisMove * 0.0, pos.y + axisMove * 0.0, pos.z + axisMove * 1.0⟩
            let (v, used) ← checkInsideBlocksBetween dims i pos target visited left
            visited := v
            left := left - used
            pos := target
      else
        let (v, used) ← checkInsideBlocksBetween dims i movement.start movement.stop visited 16
        visited := v
        left := left - used
    | none =>
      let (v, used) ← checkInsideBlocksBetween dims i movement.start movement.stop visited 16
      visited := v
      left := left - used
    if left ≤ 0 then
      let (v, _) ← checkInsideBlocksBetween dims i movement.stop movement.stop visited 1
      visited := v

/-- `Entity.applyEffectsFromBlocks(movements)` for the entity with index `i`, which is of size
`dims` and is affected by blocks (it is alive and has physics). `effectPos` is the block the
entity stands on (`getOnPosLegacy`) if it is on the ground: that block is stepped on
(`Block.stepOn`). Then the blocks met during the movements are told that the entity is inside
them. -/
def applyEffectsFromBlocks (dims : Dimensions) (i : ℕ) (effectPos : Option Pos)
    (movements : List Movement) : M Unit := do
  if ((← get).entity? i).isNone then return
  if let some p := effectPos then
    (← Level.behaviour (← Level.getBlock p)).stepOn p i
  checkInsideBlocks dims i movements

/-- The movements for which `Entity.applyEffectsFromBlocks()` applies the effects of blocks:
those made since the last time, followed by the way from the end of the last one to where the
entity is now if it is not there; with no movement made, the way from `old`, where the entity
was when its tick began (`oldPosition`), to where it is. -/
def finalMovements (made : List Movement) (old pos : Vec3) : List Movement :=
  match made.getLast? with
  | none => [⟨old, pos, none⟩]
  | some last =>
    let d := last.stop.sub pos
    if d.lengthSqr > (Float32.ofBits 0x2edbe6fe).toFloat then made ++ [⟨last.stop, pos, none⟩]
    else made

end Entity.Touch

end Redstone
