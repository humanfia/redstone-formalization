module

public import Redstone.Entity.Basic

/-!
# Geometry of entities

The numbers, vectors and boxes that every entity unit works with: the arithmetic of the game on
`double` and `float` (`Mth`, `Math.min`, `Math.max`), `Vec3`, the axis-aligned box `AABB`, and
the size of an entity (`EntityDimensions`).

`Float` is the game's `double` and `Float32` its `float`. Every operation is done in the order
of the Java source, so results agree bit for bit; constants that are not exactly representable
are given by their bits.
-/

@[expose] public section

namespace Redstone

/-! ### Numbers -/

namespace Phys

/-- The `double` with the given bits. -/
def d (bits : UInt64) : Float := Float.ofBits bits

/-- The `float` with the given bits, widened to `double`. -/
def f (bits : UInt32) : Float := (Float32.ofBits bits).toFloat

/-- `(double)(float)v`: a `double` rounded to `float`. -/
def toFloat32 (v : Float) : Float := v.toFloat32.toFloat

/-- `1.0E-7`, the tolerance of shape collisions (`Shapes.EPSILON`). -/
def eps7 : Float := d 0x3e7ad7f29abcaf48

/-- `1.0E-6`. -/
def eps6 : Float := d 0x3eb0c6f7a0b5ed8d

/-- `1.0E-5F`. -/
def eps5f : Float := f 0x3727c5ac

/-- `Math.min` on doubles. -/
def min (a b : Float) : Float :=
  if a.isNaN then a
  else if a == 0 && b == 0 && b.toBits == 0x8000000000000000 then b
  else if a ≤ b then a else b

/-- `Math.max` on doubles. -/
def max (a b : Float) : Float :=
  if a.isNaN then a
  else if a == 0 && b == 0 && a.toBits == 0x8000000000000000 then b
  else if a ≥ b then a else b

/-- `Mth.floor`: the largest integer not above `v`. -/
def floor (v : Float) : ℤ :=
  let w := v.floor
  if w < 0 then -((0 - w).toUInt64.toNat : ℤ) else (w.toUInt64.toNat : ℤ)

/-- `Mth.ceil`: the smallest integer not below `v`. -/
def ceil (v : Float) : ℤ := -floor (-v)

/-- An integer as a `double`. -/
def ofInt (n : ℤ) : Float := Float.ofInt n

/-- `Mth.equal`: the two numbers differ by less than `1.0E-5F`. -/
def equal (a b : Float) : Bool := (b - a).abs < eps5f

/-- `Direction.axisStepOrder(movement)`: the order in which a movement is resolved. -/
def axisStepOrder (movement : Vec3) : List Axis :=
  if movement.x.abs < movement.z.abs then [.y, .z, .x] else [.y, .x, .z]

end Phys

namespace Vec3

/-- The zero vector (`Vec3.ZERO`). -/
def zero : Vec3 := ⟨0, 0, 0⟩

/-- `Vec3.add`. -/
def add (a b : Vec3) : Vec3 := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

/-- `Vec3.subtract`. -/
def sub (a b : Vec3) : Vec3 := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

/-- `Vec3.multiply(x, y, z)`. -/
def mul (a : Vec3) (x y z : Float) : Vec3 := ⟨a.x * x, a.y * y, a.z * z⟩

/-- `Vec3.lengthSqr`. -/
def lengthSqr (a : Vec3) : Float := a.x * a.x + a.y * a.y + a.z * a.z

/-- `Vec3.horizontalDistanceSqr`. -/
def horizontalDistanceSqr (a : Vec3) : Float := a.x * a.x + a.z * a.z

/-- `Vec3.get(axis)`. -/
def get (a : Vec3) : Axis → Float
  | .x => a.x
  | .y => a.y
  | .z => a.z

/-- `Vec3.with(axis, value)`. -/
def set (a : Vec3) (ax : Axis) (v : Float) : Vec3 :=
  match ax with
  | .x => { a with x := v }
  | .y => { a with y := v }
  | .z => { a with z := v }

/-- `BlockPos.containing`: the block the point lies in. -/
def blockPos (a : Vec3) : Pos := ⟨Phys.floor a.x, Phys.floor a.y, Phys.floor a.z⟩

end Vec3

/-! ### Boxes -/

/-- An axis-aligned box in space (`AABB`). -/
structure AABB where
  minX : Float
  minY : Float
  minZ : Float
  maxX : Float
  maxY : Float
  maxZ : Float
  deriving Repr, Inhabited

namespace AABB

/-- The constructor of `AABB`, which orders the two corners. -/
def of (x1 y1 z1 x2 y2 z2 : Float) : AABB :=
  ⟨Phys.min x1 x2, Phys.min y1 y2, Phys.min z1 z2, Phys.max x1 x2, Phys.max y1 y2, Phys.max z1 z2⟩

/-- `AABB.min(axis)`. -/
def min (b : AABB) : Axis → Float
  | .x => b.minX
  | .y => b.minY
  | .z => b.minZ

/-- `AABB.max(axis)`. -/
def max (b : AABB) : Axis → Float
  | .x => b.maxX
  | .y => b.maxY
  | .z => b.maxZ

/-- `AABB.move`. -/
def move (b : AABB) (v : Vec3) : AABB :=
  of (b.minX + v.x) (b.minY + v.y) (b.minZ + v.z) (b.maxX + v.x) (b.maxY + v.y) (b.maxZ + v.z)

/-- `AABB.expandTowards`: the box stretched by a movement. -/
def expandTowards (b : AABB) (v : Vec3) : AABB :=
  of (if v.x < 0 then b.minX + v.x else b.minX) (if v.y < 0 then b.minY + v.y else b.minY)
    (if v.z < 0 then b.minZ + v.z else b.minZ) (if v.x > 0 then b.maxX + v.x else b.maxX)
    (if v.y > 0 then b.maxY + v.y else b.maxY) (if v.z > 0 then b.maxZ + v.z else b.maxZ)

/-- `AABB.inflate(x, y, z)`. -/
def inflate (b : AABB) (x y z : Float) : AABB :=
  of (b.minX - x) (b.minY - y) (b.minZ - z) (b.maxX + x) (b.maxY + y) (b.maxZ + z)

/-- `AABB.deflate(amount)`. -/
def deflate (b : AABB) (v : Float) : AABB := b.inflate (-v) (-v) (-v)

/-- `AABB.intersects(minX, ..., maxZ)`: the interiors of the boxes meet. -/
def intersects (b c : AABB) : Bool :=
  b.minX < c.maxX && b.maxX > c.minX && b.minY < c.maxY && b.maxY > c.minY &&
    b.minZ < c.maxZ && b.maxZ > c.minZ

/-- The box of the block at `p`, as `BlockCollisions` passes it to `AABB.intersects`. -/
def ofBlock (p : Pos) : AABB :=
  let x := Phys.ofInt p.x
  let y := Phys.ofInt p.y
  let z := Phys.ofInt p.z
  ⟨x, y, z, x + 1.0, y + 1.0, z + 1.0⟩

end AABB

namespace AABB

/-- Reads a list of boxes from the bits of their coordinates, six for each box. -/
def listOfBits : List UInt64 → List AABB
  | a :: b :: c :: d :: e :: g :: rest =>
    ⟨.ofBits a, .ofBits b, .ofBits c, .ofBits d, .ofBits e, .ofBits g⟩ :: listOfBits rest
  | _ => []

/-- `AABB.contains(x, y, z)`. -/
def contains (b : AABB) (v : Vec3) : Bool :=
  v.x ≥ b.minX && v.x < b.maxX && v.y ≥ b.minY && v.y < b.maxY && v.z ≥ b.minZ && v.z < b.maxZ

/-- `AABB.getXsize`, `getYsize`, `getZsize`: the length of the box along an axis. -/
def size (b : AABB) (ax : Axis) : Float := b.max ax - b.min ax

/-- `AABB.getCenter()`. -/
def center (b : AABB) : Vec3 :=
  ⟨b.minX + 0.5 * (b.maxX - b.minX), b.minY + 0.5 * (b.maxY - b.minY),
    b.minZ + 0.5 * (b.maxZ - b.minZ)⟩

/-- `AABB.intersects` with the cube of the block at `p`. -/
def intersectsBlock (b : AABB) (p : Pos) : Bool := b.intersects (ofBlock p)

/-- `AABB.move(BlockPos)`: the box moved by the coordinates of a block position. -/
def atBlock (b : AABB) (p : Pos) : AABB :=
  b.move ⟨Phys.ofInt p.x, Phys.ofInt p.y, Phys.ofInt p.z⟩

/-- `BlockPos.betweenClosed(aabb)`: the block positions the box reaches, in the order of the
game's iterator: x runs fastest, then y, then z. -/
def blocks (b : AABB) : List Pos :=
  let x0 := Phys.floor b.minX
  let y0 := Phys.floor b.minY
  let z0 := Phys.floor b.minZ
  let width := (Phys.floor b.maxX - x0 + 1).toNat
  let height := (Phys.floor b.maxY - y0 + 1).toNat
  let depth := (Phys.floor b.maxZ - z0 + 1).toNat
  (List.range depth).flatMap fun z => (List.range height).flatMap fun y =>
    (List.range width).map fun x => ⟨x0 + x, y0 + y, z0 + z⟩

/-- `AABB.clipPoint`: the ray from `(fromA, fromB, fromC)` along `(da, db, dc)` crosses the
plane `a = point` at a parameter between zero and `scale`, within the rectangle of the face.
Returns the new, smaller parameter. -/
def clipPoint (scale da db dc point minB maxB minC maxC fromA fromB fromC : Float) :
    Option Float :=
  let s := (point - fromA) / da
  let pb := fromB + s * db
  let pc := fromC + s * dc
  if 0.0 < s && s < scale && minB - Phys.eps7 < pb && pb < maxB + Phys.eps7 &&
      minC - Phys.eps7 < pc && pc < maxC + Phys.eps7 then some s
  else none

/-- `AABB.clip(from, to)`: the point where the segment from `a` to `b` first enters the box
through one of the faces it meets from outside, if it does. -/
def clip (bx : AABB) (a b : Vec3) : Option Vec3 :=
  let dx := b.x - a.x
  let dy := b.y - a.y
  let dz := b.z - a.z
  -- `getDirection`: the faces are tried along x, then y, then z; each hit shortens the ray
  let step (acc : Float × Bool) (hit : Float → Option Float) : Float × Bool :=
    match hit acc.1 with
    | some s => (s, true)
    | none => acc
  let acc : Float × Bool := (1.0, false)
  let acc := step acc fun scale =>
    if dx > Phys.eps7 then
      clipPoint scale dx dy dz bx.minX bx.minY bx.maxY bx.minZ bx.maxZ a.x a.y a.z
    else if dx < -Phys.eps7 then
      clipPoint scale dx dy dz bx.maxX bx.minY bx.maxY bx.minZ bx.maxZ a.x a.y a.z
    else none
  let acc := step acc fun scale =>
    if dy > Phys.eps7 then
      clipPoint scale dy dz dx bx.minY bx.minZ bx.maxZ bx.minX bx.maxX a.y a.z a.x
    else if dy < -Phys.eps7 then
      clipPoint scale dy dz dx bx.maxY bx.minZ bx.maxZ bx.minX bx.maxX a.y a.z a.x
    else none
  let acc := step acc fun scale =>
    if dz > Phys.eps7 then
      clipPoint scale dz dx dy bx.minZ bx.minX bx.maxX bx.minY bx.maxY a.z a.x a.y
    else if dz < -Phys.eps7 then
      clipPoint scale dz dx dy bx.maxZ bx.minX bx.maxX bx.minY bx.maxY a.z a.x a.y
    else none
  if acc.2 then some ⟨a.x + acc.1 * dx, a.y + acc.1 * dy, a.z + acc.1 * dz⟩ else none

/-- `AABB.collidedAlongVector(vector, aabbs)`: the box, moved along `vector`, meets one of the
boxes `parts` on the way. Each part is grown by half the size of the box, less `1.0E-7`, and
the centre of the box is followed. -/
def collidedAlongVector (b : AABB) (vector : Vec3) (parts : List AABB) : Bool :=
  let start := b.center
  let stop := start.add vector
  parts.any fun part =>
    let inflated := part.inflate (b.size .x * 0.5 - Phys.eps7) (b.size .y * 0.5 - Phys.eps7)
      (b.size .z * 0.5 - Phys.eps7)
    inflated.contains stop || inflated.contains start || (inflated.clip start stop).isSome

end AABB

/-- The size of an entity (`EntityDimensions`): half its width and its height, as doubles. -/
structure Dimensions where
  halfWidth : Float
  height : Float

namespace Dimensions

/-- The dimensions of an entity type from the bits of its width and height, which are `float`:
half the width is computed in `float`, as `EntityDimensions.makeBoundingBox` does. -/
def ofBits (width height : UInt32) : Dimensions :=
  ⟨(Float32.ofBits width / 2.0).toFloat, (Float32.ofBits height).toFloat⟩

/-- `EntityDimensions.makeBoundingBox`: the box of an entity at `p`. -/
def box (dm : Dimensions) (p : Vec3) : AABB :=
  AABB.of (p.x - dm.halfWidth) p.y (p.z - dm.halfWidth) (p.x + dm.halfWidth) (p.y + dm.height)
    (p.z + dm.halfWidth)

end Dimensions

/-! ### Shapes that are shifted by the position of the block -/

/-- The shift of the shapes of a block whose shapes depend on where it is
(`BlockBehaviour.OffsetType.XZ`, `BlockState.getOffset(pos)`): bamboo, pointed dripstone and
sulfur spikes stand a little off the middle of their block, by an amount that the game derives
from the x and z of the position. -/
structure ShapeOffset where
  /-- `getOffset(BlockPos.ZERO)`, along x and along z: the shift that the shapes of the server's
  shape table already carry, since they were taken from the block at the origin. -/
  origin : Float
  /-- The x of `getOffset(pos)`. -/
  x : Float
  /-- The z of `getOffset(pos)`. -/
  z : Float

namespace ShapeOffset

/-- A coordinate of a shape of the shape table, as `VoxelShape.move(getOffset(pos))` gives it for
the block at the position of the offset: the coordinate of the shape as the block defines it,
which the shift of the table is taken off to get back (exactly: the coordinates of these shapes
and the shift are small multiples of a power of two), plus the offset. -/
def apply (o : ShapeOffset) (ax : Axis) (c : Float) : Float :=
  match ax with
  | .x => (c - o.origin) + o.x
  | .y => c + 0.0
  | .z => (c - o.origin) + o.z

/-- A box of a shape of the shape table, shifted to where the block has it. -/
def box (o : ShapeOffset) (b : AABB) : AABB :=
  ⟨o.apply .x b.minX, o.apply .y b.minY, o.apply .z b.minZ,
    o.apply .x b.maxX, o.apply .y b.maxY, o.apply .z b.maxZ⟩

end ShapeOffset

namespace Block

/-- `Block.getMaxHorizontalOffset()` of the blocks with `OffsetType.XZ` that have a collision
shape: a quarter of a block for bamboo (the default), an eighth for pointed dripstone and sulfur
spikes (`SpeleothemBlock.MAX_HORIZONTAL_OFFSET`, the margin of their widest shape). The other
blocks with an offset (flowers, grass, ...) have no collision shape. -/
def maxHorizontalOffset? (b : Block) : Option Float :=
  if b.is .bamboo then some 0.25
  else if b.is .pointed_dripstone || b.is .sulfur_spike then some 0.125
  else none

/-- `Mth.getSeed(x, 0, z)`, in the arithmetic of `int` and `long`. -/
def offsetSeed (p : Pos) : Int64 :=
  let seed : Int64 := (Int32.ofInt p.x * 3129871).toInt64 ^^^ (Int64.ofInt p.z * 116129781)
  let seed := seed * seed * 42317861 + seed * 11
  seed >>> 16

/-- One horizontal component of `getOffset(pos)` for `OffsetType.XZ`:
`Mth.clamp(((float)bits / 15.0F - 0.5) * 0.5, -max, max)`, where `bits` are four bits of the
seed. -/
def offsetComponent (bits : Int64) (max : Float) : Float :=
  let v := ((Float32.ofNat (bits &&& 15).toInt.toNat / 15.0).toFloat - 0.5) * 0.5
  if v < -max then -max else Phys.min v max

/-- `BlockState.getOffset(pos)` for a block whose collision shape is shifted by it, with the
shift at the origin that the shape table carries. -/
def shapeOffset? (b : Block) (p : Pos) : Option ShapeOffset :=
  b.maxHorizontalOffset?.map fun max =>
    let seed := offsetSeed p
    { origin := offsetComponent (offsetSeed ⟨0, 0, 0⟩) max
      x := offsetComponent seed max
      z := offsetComponent (seed >>> 8) max }

end Block

end Redstone
