module

public import Redstone.Entity.Physics

/-!
# Rays through the blocks of the world

Java classes: `BlockGetter` (`clip`, `traverseBlocks`), `VoxelShape` (`clip`), `AABB` (`clip`,
`getDirection`, `clipPoint`), `BlockHitResult`, `ClipContext`.

`Level.clip` follows a segment from block to block and returns the first point where it meets
the collision shape of a block, with the face that was met: this is how a projectile finds the
block it hits. The arithmetic is that of the game, operation for operation.

## What is left out

* The ray is the one of `ClipContext.Block.COLLIDER` with `ClipContext.Fluid.NONE`: collision
  shapes, no fluids. A block whose collision shape the model does not have
  (`Block.collisionUnmodelled`) on the way is reported by a flag and passed through.
* `clipWithInteractionOverride`: a block with an interaction shape (cauldron, composter, hopper)
  can replace the face of the hit. Nothing in the model reads the face of a hit on such a block.
* The world border (`CollisionGetter.clipIncludingBorder`).
-/

@[expose] public section

namespace Redstone

/-- `BlockHitResult`: where a ray ends. -/
structure BlockHitResult where
  /-- `getLocation()`: the point of the hit; for a miss, the end of the ray. -/
  location : Vec3
  /-- `getDirection()`: the face of the block that was hit. -/
  direction : Direction
  /-- `getBlockPos()`. -/
  blockPos : Pos
  /-- `getType() == MISS`. -/
  miss : Bool := false
  /-- `isInside()`: the ray starts inside the shape. -/
  inside : Bool := false

namespace Phys

/-- `Direction.getApproximateNearest(dx, dy, dz)`: the direction whose normal has the largest
product with the vector, computed in `float`; `north` if no product is positive. -/
def approximateNearest (v : Vec3) : Direction :=
  let x := v.x.toFloat32
  let y := v.y.toFloat32
  let z := v.z.toFloat32
  let step (acc : Direction × Float32) (d : Direction) (dot : Float32) : Direction × Float32 :=
    if dot > acc.2 then (d, dot) else acc
  -- `Float.MIN_VALUE`
  let acc : Direction × Float32 := (.north, Float32.ofBits 1)
  let acc := step acc .down (x * 0 + y * (-1) + z * 0)
  let acc := step acc .up (x * 0 + y * 1 + z * 0)
  let acc := step acc .north (x * 0 + y * 0 + z * (-1))
  let acc := step acc .south (x * 0 + y * 0 + z * 1)
  let acc := step acc .west (x * (-1) + y * 0 + z * 0)
  let acc := step acc .east (x * 1 + y * 0 + z * 0)
  acc.1

/-- `Mth.lerp(alpha, p0, p1)` on doubles. -/
def lerp (alpha p0 p1 : Float) : Float := p0 + alpha * (p1 - p0)

end Phys

namespace AABB

/-- `AABB.getDirection(aabb, from, scaleReference, direction, dx, dy, dz)`: the faces of the box
that the ray from `start` along `(dx, dy, dz)` can enter are tried along x, then y, then z. A
face that the ray crosses nearer than the best hit so far (`acc.1`, a fraction of the ray)
becomes the best hit. -/
def getDirection (bx : AABB) (start : Vec3) (dx dy dz : Float)
    (acc : Float × Option Direction) : Float × Option Direction :=
  let step (acc : Float × Option Direction) (d : Direction) (hit : Float → Option Float) :
      Float × Option Direction :=
    match hit acc.1 with
    | some s => (s, some d)
    | none => acc
  let acc :=
    if dx > Phys.eps7 then
      step acc .west fun scale =>
        clipPoint scale dx dy dz bx.minX bx.minY bx.maxY bx.minZ bx.maxZ start.x start.y start.z
    else if dx < -Phys.eps7 then
      step acc .east fun scale =>
        clipPoint scale dx dy dz bx.maxX bx.minY bx.maxY bx.minZ bx.maxZ start.x start.y start.z
    else acc
  let acc :=
    if dy > Phys.eps7 then
      step acc .down fun scale =>
        clipPoint scale dy dz dx bx.minY bx.minZ bx.maxZ bx.minX bx.maxX start.y start.z start.x
    else if dy < -Phys.eps7 then
      step acc .up fun scale =>
        clipPoint scale dy dz dx bx.maxY bx.minZ bx.maxZ bx.minX bx.maxX start.y start.z start.x
    else acc
  if dz > Phys.eps7 then
    step acc .north fun scale =>
      clipPoint scale dz dx dy bx.minZ bx.minX bx.maxX bx.minY bx.maxY start.z start.x start.y
  else if dz < -Phys.eps7 then
    step acc .south fun scale =>
      clipPoint scale dz dx dy bx.maxZ bx.minX bx.maxX bx.minY bx.maxY start.z start.x start.y
  else acc

/-- `AABB.clip(aabbs, from, to, pos)`: the first point where the segment from `start` to `stop`
enters one of the boxes, which are given relative to the block at `p`. -/
def clipBoxes (boxes : List AABB) (start stop : Vec3) (p : Pos) : Option BlockHitResult :=
  let dx := stop.x - start.x
  let dy := stop.y - start.y
  let dz := stop.z - start.z
  let acc := boxes.foldl (fun acc bx => (bx.atBlock p).getDirection start dx dy dz acc) (1.0, none)
  acc.2.map fun d =>
    { location := ⟨start.x + acc.1 * dx, start.y + acc.1 * dy, start.z + acc.1 * dz⟩
      direction := d, blockPos := p }

end AABB

namespace Shape

/-- `VoxelShape.findIndex(axis, coord)` of the shape where it is, relative to its block. -/
def findIndex (s : Shape) (ax : Axis) (coord : Float) : ℤ :=
  (((s.coords ax).toList.takeWhile fun c => !(coord < c)).length : ℤ) - 1

/-- `VoxelShape.clip(from, to, pos)`: the hit of the segment from `start` to `stop` on the shape
placed at the block `p`. A segment that starts inside the shape hits at once, a thousandth of
its length from its start, on the face it comes from. -/
def clip (s : Shape) (start stop : Vec3) (p : Pos) : Option BlockHitResult :=
  if s.isEmpty then none
  else
    let diff := stop.sub start
    if diff.lengthSqr < Phys.eps7 then none
    else
      let testPoint := start.add (diff.mul 0.001 0.001 0.001)
      if s.isFullWide (s.findIndex .x (testPoint.x - Phys.ofInt p.x))
          (s.findIndex .y (testPoint.y - Phys.ofInt p.y))
          (s.findIndex .z (testPoint.z - Phys.ofInt p.z)) then
        some { location := testPoint, direction := (Phys.approximateNearest diff).opposite
               blockPos := p, inside := true }
      else AABB.clipBoxes s.boxes start stop p

end Shape

namespace Level

/-- What `BlockGetter.clip` does at one block: the hit on the collision shape of the block at
`p`. The flag tells that the shape of the block is not modelled. -/
def clipBlock (l : Level) (start stop : Vec3) (p : Pos) : Option BlockHitResult × Bool :=
  let state := l.blockAt p
  if state.isAir then (none, false)
  else if state.collisionUnmodelled then (none, true)
  else if state.attrs.collision == 0 then (none, false)
  else (state.collisionShape.clip start stop p, false)

/-- The loop of `BlockGetter.traverseBlocks`: from the block `p` the ray goes on to the next
block as long as one of the parameters `tX`, `tY`, `tZ`, at which it crosses the next block
boundary along each axis, is at most 1. `fuel` bounds the number of blocks. -/
def traverseLoop (l : Level) (start stop : Vec3) (signX signY signZ : ℤ)
    (tDeltaX tDeltaY tDeltaZ : Float) :
    ℕ → Pos → Float → Float → Float → Bool → Option BlockHitResult × Bool
  | 0, _, _, _, _, unmodelled => (none, unmodelled)
  | fuel + 1, p, tX, tY, tZ, unmodelled =>
    if tX ≤ 1.0 || tY ≤ 1.0 || tZ ≤ 1.0 then
      let (p, tX, tY, tZ) :=
        if tX < tY then
          if tX < tZ then ({ p with x := p.x + signX }, tX + tDeltaX, tY, tZ)
          else ({ p with z := p.z + signZ }, tX, tY, tZ + tDeltaZ)
        else if tY < tZ then ({ p with y := p.y + signY }, tX, tY + tDeltaY, tZ)
        else ({ p with z := p.z + signZ }, tX, tY, tZ + tDeltaZ)
      match l.clipBlock start stop p with
      | (some hit, u) => (some hit, unmodelled || u)
      | (none, u) =>
        traverseLoop l start stop signX signY signZ tDeltaX tDeltaY tDeltaZ fuel p tX tY tZ
          (unmodelled || u)
    else (none, unmodelled)

/-- `BlockGetter.clip(new ClipContext(from, to, COLLIDER, NONE, entity))`: the first hit of the
segment from `start` to `stop` on the collision shape of a block, or a miss at `stop`. The flag
tells that a block whose collision shape is not modelled lay on the way. -/
def clip (l : Level) (start stop : Vec3) : BlockHitResult × Bool :=
  let missed : BlockHitResult :=
    { location := stop, direction := Phys.approximateNearest (start.sub stop)
      blockPos := stop.blockPos, miss := true }
  if start == stop then (missed, false)
  else
    let alpha := -Phys.eps7
    let toX := Phys.lerp alpha stop.x start.x
    let toY := Phys.lerp alpha stop.y start.y
    let toZ := Phys.lerp alpha stop.z start.z
    let fromX := Phys.lerp alpha start.x stop.x
    let fromY := Phys.lerp alpha start.y stop.y
    let fromZ := Phys.lerp alpha start.z stop.z
    let p : Pos := ⟨Phys.floor fromX, Phys.floor fromY, Phys.floor fromZ⟩
    match l.clipBlock start stop p with
    | (some hit, u) => (hit, u)
    | (none, u) =>
      let dx := toX - fromX
      let dy := toY - fromY
      let dz := toZ - fromZ
      let signX := Entity.Touch.sign dx
      let signY := Entity.Touch.sign dy
      let signZ := Entity.Touch.sign dz
      let huge := Phys.d 0x7fefffffffffffff
      let tDeltaX := if signX == 0 then huge else Phys.ofInt signX / dx
      let tDeltaY := if signY == 0 then huge else Phys.ofInt signY / dy
      let tDeltaZ := if signZ == 0 then huge else Phys.ofInt signZ / dz
      let frac := Entity.Touch.frac
      let tX := tDeltaX * (if signX > 0 then 1.0 - frac fromX else frac fromX)
      let tY := tDeltaY * (if signY > 0 then 1.0 - frac fromY else frac fromY)
      let tZ := tDeltaZ * (if signZ > 0 then 1.0 - frac fromZ else frac fromZ)
      -- every step goes one block further along one axis, towards the block of the end
      let fuel := ((Phys.floor toX - p.x).natAbs + (Phys.floor toY - p.y).natAbs +
        (Phys.floor toZ - p.z).natAbs + 3)
      match traverseLoop l start stop signX signY signZ tDeltaX tDeltaY tDeltaZ fuel p tX tY tZ u
        with
      | (some hit, u) => (hit, u)
      | (none, u) => (missed, u)

end Level

end Redstone
