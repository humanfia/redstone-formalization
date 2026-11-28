module

public import Redstone.Mechanics.Tick
public import Redstone.Entity.Tnt.Tables
public import Redstone.Entity.Touch

/-!
# Geometry for primed TNT

The parts of the game's entity physics that primed TNT and explosions use, in the game's own
floating point arithmetic: collision shapes placed in the world
(`VoxelShape.move`), the collision of a moving box with shapes (`VoxelShape.collide`,
`Shapes.collide`), the block collisions around a box (`BlockCollisions`), and ray casts
through blocks (`BlockGetter.clip`), of which only "hit or miss" is needed.

`Float` is the game's `double` and `Float32` its `float`; every operation is written in the
order of the Java source, so that the results agree bit for bit.

## What is left out

The collision shape of a block is taken from its state alone (`collisionGrid`). Powder snow,
whose shape depends on the fall distance of the entity, is handled. The other blocks whose
collision shape depends on the position, the block entity or the entity are not: scaffolding,
bamboo, pointed dripstone, sulfur spikes, shulker boxes and moving pistons. When such a block
is examined the result carries the flag `unmodelled`, and the callers set `Level.overflow`.
-/

@[expose] public section

namespace Redstone.Entity.Tnt

/-! ### Numbers -/

/-- The Java `float` with the given bits, widened to `double`. -/
def wide (bits : UInt32) : Float := (Float32.ofBits bits).toFloat

/-- `Mth.floor`: the largest integer not above `x`. -/
def floorInt (x : Float) : ℤ := x.floor.toInt64.toInt

/-- `Mth.frac`: the fractional part of `x`. -/
def frac (x : Float) : Float := x - x.floor

/-- `Mth.lerp(alpha, p0, p1)`. -/
def lerp (alpha p0 p1 : Float) : Float := p0 + alpha * (p1 - p0)

/-- `Math.min` on `double`: of two zeros the negative one is the smaller. -/
def jmin (a b : Float) : Float :=
  if a == 0.0 && b == 0.0 && b.toBits == 0x8000000000000000 then b else if a ≤ b then a else b

/-- `Math.max` on `double`: of two zeros the positive one is the larger. -/
def jmax (a b : Float) : Float :=
  if a == 0.0 && b == 0.0 && a.toBits == 0x8000000000000000 then b else if a ≥ b then a else b

/-- `Double.MAX_VALUE`. -/
def maxDouble : Float := Float.ofBits 0x7fefffffffffffff

/-- The integers from `lo` up to, but not including, `hi`. -/
def intRange (lo hi : ℤ) : List ℤ := (List.range (hi - lo).toNat).map (lo + ·)

/-! ### Vectors -/

/-- `Vec3.get(axis)`. -/
def vget (v : Vec3) : Axis → Float
  | .x => v.x
  | .y => v.y
  | .z => v.z

/-- `Vec3.with(axis, value)`. -/
def vset (v : Vec3) (a : Axis) (value : Float) : Vec3 :=
  match a with
  | .x => { v with x := value }
  | .y => { v with y := value }
  | .z => { v with z := value }

/-- `Vec3.add`. -/
def vadd (a b : Vec3) : Vec3 := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

/-- `Vec3.subtract`. -/
def vsub (a b : Vec3) : Vec3 := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

/-- `Vec3.multiply(x, y, z)`. -/
def vmul (a : Vec3) (x y z : Float) : Vec3 := ⟨a.x * x, a.y * y, a.z * z⟩

/-- `Vec3.scale`. -/
def vscale (a : Vec3) (s : Float) : Vec3 := vmul a s s s

/-- `Vec3.lengthSqr`. -/
def lengthSqr (a : Vec3) : Float := a.x * a.x + a.y * a.y + a.z * a.z

/-- `Vec3.normalize`. -/
def normalize (a : Vec3) : Vec3 :=
  let dist := Float.sqrt (a.x * a.x + a.y * a.y + a.z * a.z)
  if dist < wide 0x3727c5ac then ⟨0.0, 0.0, 0.0⟩ else ⟨a.x / dist, a.y / dist, a.z / dist⟩

/-- `Vec3.isFinite`. -/
def visFinite (a : Vec3) : Bool := a.x.isFinite && a.y.isFinite && a.z.isFinite

/-- `BlockPos.containing(x, y, z)`. -/
def blockPos (a : Vec3) : Pos := ⟨floorInt a.x, floorInt a.y, floorInt a.z⟩

/-! ### Boxes -/

/-- `EntityType.getDimensions` of primed TNT, which is `0.98F` wide and `0.98F` high. -/
def dims : Dimensions := ⟨wide 0x3efae148, wide 0x3f7ae148⟩

/-- `EntityDimensions.makeBoundingBox` for primed TNT: the box of an entity at `p`. -/
def entityBox (p : Vec3) : AABB := dims.box p

/-! ### Shapes -/

/-- The two other axes, in the order in which `VoxelShape.collideX` goes through them. -/
def otherAxes : Axis → Axis × Axis
  | .x => (.y, .z)
  | .y => (.z, .x)
  | .z => (.x, .y)

/-- The cell `(x, y, z)` whose index along `a` is `i` and whose indices along the two other
axes are `j` and `k`. -/
def cellOf (a : Axis) (i j k : ℤ) : ℤ × ℤ × ℤ :=
  match a with
  | .x => (i, j, k)
  | .y => (k, i, j)
  | .z => (j, k, i)

namespace VoxelGrid

/-- `getCoords(axis)`. -/
def coords (g : VoxelGrid) : Axis → Array Float
  | .x => g.xs
  | .y => g.ys
  | .z => g.zs

/-- `shape.getSize(axis)`: the number of cells along the axis. -/
def size (g : VoxelGrid) (a : Axis) : ℕ := (g.coords a).size - 1

/-- `VoxelShape.isEmpty`: no cell is full. -/
def isEmpty (g : VoxelGrid) : Bool := g.full == 0

/-- `DiscreteVoxelShape.isFullWide`: the cell exists and is full. -/
def isFullWide (g : VoxelGrid) (x y z : ℤ) : Bool :=
  0 ≤ x && 0 ≤ y && 0 ≤ z && x < g.size .x && y < g.size .y && z < g.size .z &&
    g.full.testBit ((x.toNat * g.size .y + y.toNat) * g.size .z + z.toNat)

/-- The cell with index `i` along `a` and `j`, `k` along the two other axes is full. -/
def isFullAt (g : VoxelGrid) (a : Axis) (i j k : ℤ) : Bool :=
  let (x, y, z) := cellOf a i j k
  g.isFullWide x y z

/-- Some cell with index `i` along `a` is full. -/
def anyFullAt (g : VoxelGrid) (a : Axis) (i : ℤ) : Bool :=
  let (b, c) := otherAxes a
  (intRange 0 (g.size b)).any fun j => (intRange 0 (g.size c)).any fun k => g.isFullAt a i j k

/-- `shape.firstFull(axis)`: the least index along the axis of a full cell. -/
def firstFull (g : VoxelGrid) (a : Axis) : ℕ :=
  (((intRange 0 (g.size a)).find? (g.anyFullAt a)).getD (g.size a)).toNat

/-- `shape.lastFull(axis)`: one more than the greatest index along the axis of a full cell. -/
def lastFull (g : VoxelGrid) (a : Axis) : ℕ :=
  ((((intRange 0 (g.size a)).reverse.find? (g.anyFullAt a)).map (· + 1)).getD 0).toNat

/-- `hasLargeCollisionShape` for a block without dynamic shape: the shape reaches outside the
cube of its block. -/
def isLarge (g : VoxelGrid) : Bool :=
  g.boxes.any fun (x0, y0, z0, x1, y1, z1) =>
    x0 < 0.0 || y0 < 0.0 || z0 < 0.0 || x1 > 1.0 || y1 > 1.0 || z1 > 1.0

/-- `PowderSnowBlock.FALLING_COLLISION_SHAPE`: `Shapes.box(0, 0, 0, 1, 0.9F, 1)`. -/
def powderSnowFalling : VoxelGrid :=
  let h := wide 0x3f666666
  ⟨false, #[0.0, 1.0], #[0.0, h], #[0.0, 1.0], 1, [(0.0, 0.0, 0.0, 1.0, h, 1.0)]⟩

end VoxelGrid

/-- A collision shape at the position of its block (`VoxelShape.move(pos)`). -/
structure Shape where
  grid : VoxelGrid
  pos : Pos

namespace Shape

/-- The offset along an axis. -/
def off (s : Shape) : Axis → Float
  | .x => Float.ofInt s.pos.x
  | .y => Float.ofInt s.pos.y
  | .z => Float.ofInt s.pos.z

/-- `get(axis, i)`: the `i`-th coordinate along the axis. -/
def get (s : Shape) (a : Axis) (i : ℕ) : Float := ((s.grid.coords a).getD i 0.0) + s.off a

/-- `getCoords(axis)` of the moved shape. -/
def coords (s : Shape) (a : Axis) : Array Float := (s.grid.coords a).map (· + s.off a)

/-- `findIndex(axis, coord)`: the index of the cell that contains `coord`; `-1` below the
shape and the number of cells above it. -/
def findIndex (s : Shape) (a : Axis) (coord : Float) : ℤ :=
  ((s.coords a).toList.takeWhile fun c => !(coord < c)).length - 1

/-- `min(axis)`. -/
def min (s : Shape) (a : Axis) : Float := s.get a (s.grid.firstFull a)

/-- `max(axis)`. -/
def max (s : Shape) (a : Axis) : Float := s.get a (s.grid.lastFull a)

/-- `VoxelShape.collide(axis, moving, distance)`: how far the box `moving` can go along `a`,
at most `distance`, before it meets the shape. -/
def collide (s : Shape) (a : Axis) (moving : AABB) (distance : Float) : Float :=
  if s.grid.isEmpty then distance
  else if distance.abs < 1.0e-7 then 0.0
  else
    let (b, c) := otherAxes a
    let maxA := moving.max a
    let minA := moving.min a
    let aMin := s.findIndex a (minA + 1.0e-7)
    let aMax := s.findIndex a (maxA - 1.0e-7)
    let bMin := Max.max 0 (s.findIndex b (moving.min b + 1.0e-7))
    let bMax := Min.min (s.grid.size b : ℤ) (s.findIndex b (moving.max b - 1.0e-7) + 1)
    let cMin := Max.max 0 (s.findIndex c (moving.min c + 1.0e-7))
    let cMax := Min.min (s.grid.size c : ℤ) (s.findIndex c (moving.max c - 1.0e-7) + 1)
    let fullAt (i : ℤ) : Bool :=
      (intRange bMin bMax).any fun j => (intRange cMin cMax).any fun k => s.grid.isFullAt a i j k
    if distance > 0.0 then
      match (intRange (aMax + 1) (s.grid.size a)).find? fullAt with
      | some i =>
        let newDistance := s.get a i.toNat - maxA
        if newDistance ≥ -1.0e-7 then jmin distance newDistance else distance
      | none => distance
    else if distance < 0.0 then
      match (intRange 0 aMin).reverse.find? fullAt with
      | some i =>
        let newDistance := s.get a (i.toNat + 1) - minA
        if newDistance ≤ 1.0e-7 then jmax distance newDistance else distance
      | none => distance
    else distance

end Shape

/-- `Shapes.collide(axis, moving, shapes, distance)`. -/
def collideShapes (a : Axis) (moving : AABB) (shapes : List Shape) (distance : Float) : Float :=
  match shapes with
  | [] => distance
  | s :: rest =>
    if distance.abs < 1.0e-7 then 0.0 else collideShapes a moving rest (s.collide a moving distance)

/-- `Entity.collideWithShapes`: the part of `movement` the box can make, one axis after the
other (`Direction.axisStepOrder`). -/
def collideWithShapes (movement : Vec3) (box : AABB) (shapes : List Shape) : Vec3 :=
  if shapes.isEmpty then movement
  else
    let order : List Axis := if movement.x.abs < movement.z.abs then [.y, .z, .x] else [.y, .x, .z]
    order.foldl
      (fun resolved a =>
        let m := vget movement a
        if m != 0.0 then vset resolved a (collideShapes a (box.move resolved) shapes m)
        else resolved)
      ⟨0.0, 0.0, 0.0⟩

/-! ### Whether a shape meets a box

`Shapes.joinIsNotEmpty(shape, Shapes.create(box), BooleanOp.AND)`, with the index mergers the
game uses for it. The shape of a box is a single cell between its two corners. -/

/-- `IndirectMerger` with neither side mattering alone: the pairs of cell indices of the
merged cells. Coordinates closer than `1e-7` to the previous one do not start a new cell. -/
def indirectMergeLoop (first second : Array Float) :
    ℕ → ℕ → ℕ → Array (ℤ × ℤ) → Float → Array (ℤ × ℤ)
  | 0, _, _, result, _ => result
  | fuel + 1, fi, si, result, last =>
    let ranOutOfFirst := fi ≥ first.size
    let ranOutOfSecond := si ≥ second.size
    if ranOutOfFirst && ranOutOfSecond then result
    else
      let choseFirst := !ranOutOfFirst &&
        (ranOutOfSecond || first.getD fi 0.0 < second.getD si 0.0 + 1.0e-7)
      let fi' := if choseFirst then fi + 1 else fi
      let si' := if choseFirst then si else si + 1
      let skip := if choseFirst then si == 0 || ranOutOfSecond else fi == 0 || ranOutOfFirst
      if skip then indirectMergeLoop first second fuel fi' si' result last
      else
        let cur : ℤ × ℤ := ((fi' : ℤ) - 1, (si' : ℤ) - 1)
        let next := if choseFirst then first.getD (fi' - 1) 0.0 else second.getD (si' - 1) 0.0
        if !(last ≥ next - 1.0e-7) then
          indirectMergeLoop first second fuel fi' si' (result.push cur) next
        else
          indirectMergeLoop first second fuel fi' si' (result.set! (result.size - 1) cur) last

/-- `Shapes.createIndexMerger(first, second)` followed by `forMergedIndexes`: the pairs of cell
indices, in `first` and in `second`, of the cells of the merged coordinate list. -/
def mergedIndexes (first second : Array Float) : List (ℤ × ℤ) :=
  let firstSize := first.size - 1
  let secondSize := second.size - 1
  if first.getD firstSize 0.0 < second.getD 0 0.0 - 1.0e-7 then
    -- `NonOverlappingMerger(first, second, false)`
    (intRange 0 first.size).map (·, -1) ++ (intRange 0 secondSize).map ((firstSize : ℤ), ·)
  else if second.getD secondSize 0.0 < first.getD 0 0.0 - 1.0e-7 then
    -- `NonOverlappingMerger(second, first, true)`
    (intRange 0 second.size).map (-1, ·) ++ (intRange 0 firstSize).map (·, (secondSize : ℤ))
  else if firstSize == secondSize && first.map Float.toBits == second.map Float.toBits then
    -- `IdenticalMerger`
    (intRange 0 firstSize).map fun i => (i, i)
  else
    let result :=
      indirectMergeLoop first second (first.size + second.size + 1) 0 0 #[] (0.0 / 0.0)
    (result.toList.take (Max.max 1 result.size - 1))

/-- `Shapes.joinIsNotEmpty(shape, Shapes.create(box), BooleanOp.AND)`: the shape and the box
overlap. -/
def Shape.meets (s : Shape) (box : AABB) : Bool :=
  if s.grid.isEmpty then false
  else if box.maxX - box.minX < 1.0e-7 || box.maxY - box.minY < 1.0e-7 ||
      box.maxZ - box.minZ < 1.0e-7 then false
  else if [Axis.x, Axis.y, Axis.z].any fun a =>
      s.max a < box.min a - 1.0e-7 || box.max a < s.min a - 1.0e-7 then false
  else
    let merged (a : Axis) := mergedIndexes (s.coords a) #[box.min a, box.max a]
    (merged .x).any fun (x1, x2) => (merged .y).any fun (y1, y2) => (merged .z).any fun (z1, z2) =>
      s.grid.isFullWide x1 y1 z1 && x2 == 0 && y2 == 0 && z2 == 0

/-! ### Block collisions -/

/-- The collision shape of the block at `p` for a primed TNT whose fall distance is `fall`
(`BlockState.getCollisionShape(level, pos, CollisionContext.of(entity))`), and whether the
shape of that block is one the model does not have. -/
def collisionShapeAt (l : Level) (fall : Float) (p : Pos) : VoxelGrid × Bool :=
  let b := l.blockAt p
  if b.id == .powder_snow then (if fall > 2.5 then .powderSnowFalling else .empty, false)
  else if hasDynamicCollision b.id || b.id == .scaffolding then (.empty, true)
  else (collisionGrid b.attrs.collision, false)

/-- `BlockState.hasLargeCollisionShape`. -/
def hasLargeCollisionShape (b : Block) : Bool :=
  hasDynamicShape b.id || (collisionGrid b.attrs.collision).isLarge

/-- `BlockCollisions`: the collision shapes of the blocks that meet `box`, in the order of the
game's cursor (x fastest, then y, then z), and whether a shape the model does not have was
among the blocks examined. Blocks on an edge of the searched region count only if their shape
is larger than a cube, and blocks on a corner never. -/
def blockCollisions (l : Level) (fall : Float) (box : AABB) : List Shape × Bool := Id.run do
  let x0 := floorInt (box.minX - 1.0e-7) - 1
  let x1 := floorInt (box.maxX + 1.0e-7) + 1
  let y0 := floorInt (box.minY - 1.0e-7) - 1
  let y1 := floorInt (box.maxY + 1.0e-7) + 1
  let z0 := floorInt (box.minZ - 1.0e-7) - 1
  let z1 := floorInt (box.maxZ + 1.0e-7) + 1
  let mut out : Array Shape := #[]
  let mut unmodelled := false
  for z in intRange z0 (z1 + 1) do
    for y in intRange y0 (y1 + 1) do
      for x in intRange x0 (x1 + 1) do
        let type := (if x == x0 || x == x1 then 1 else 0) + (if y == y0 || y == y1 then 1 else 0) +
          (if z == z0 || z == z1 then 1 else 0)
        if type != 3 then
          let p : Pos := ⟨x, y, z⟩
          let b := l.blockAt p
          if (type != 1 || hasLargeCollisionShape b) && (type != 2 || b.id == .moving_piston) then
            let (grid, bad) := collisionShapeAt l fall p
            if bad then unmodelled := true
            if grid.isBlock then
              if box.intersectsBlock p then out := out.push ⟨grid, p⟩
            else if (Shape.mk grid p).meets box then out := out.push ⟨grid, p⟩
  return (out.toList, unmodelled)

/-- `Vec3i.distToCenterSqr`. -/
def distToCenterSqr (p : Pos) (v : Vec3) : Float :=
  let dx := Float.ofInt p.x + 0.5 - v.x
  let dy := Float.ofInt p.y + 0.5 - v.y
  let dz := Float.ofInt p.z + 0.5 - v.z
  dx * dx + dy * dy + dz * dz

/-- `Vec3i.compareTo` is negative: `p` comes before `q` by y, then z, then x. -/
def posLT (p q : Pos) : Bool :=
  if p.y == q.y then (if p.z == q.z then p.x < q.x else p.z < q.z) else p.y < q.y

/-- `CollisionGetter.findSupportingBlock(entity, box)`: among the blocks that meet `box`, the
one whose centre is closest to `position`; of two equally close, the later in `posLT`. -/
def findSupportingBlock (l : Level) (fall : Float) (position : Vec3) (box : AABB) :
    Option Pos × Bool :=
  let (shapes, unmodelled) := blockCollisions l fall box
  let best := shapes.foldl
    (fun (best : Option (Pos × Float)) s =>
      let distance := distToCenterSqr s.pos position
      match best with
      | none => some (s.pos, distance)
      | some (q, d) =>
        if distance < d || (distance == d && posLT q s.pos) then some (s.pos, distance) else best)
    none
  (best.map (·.1), unmodelled)

/-! ### Ray casts -/

/-- `AABB.clipPoint` succeeds: the ray from `from` along `(da, db, dc)` crosses the plane
`a = point` strictly inside the segment and within the rectangle of the face. -/
def clipPoint (da db dc point minB maxB minC maxC fromA fromB fromC : Float) : Bool :=
  let s := (point - fromA) / da
  let pb := fromB + s * db
  let pc := fromC + s * dc
  0.0 < s && s < 1.0 && minB - 1.0e-7 < pb && pb < maxB + 1.0e-7 && minC - 1.0e-7 < pc &&
    pc < maxC + 1.0e-7

/-- `AABB.getDirection` finds a face: the segment from `a` along `d` enters the box. -/
def clipBox (b : AABB) (a d : Vec3) : Bool :=
  (if d.x > 1.0e-7 then clipPoint d.x d.y d.z b.minX b.minY b.maxY b.minZ b.maxZ a.x a.y a.z
    else if d.x < -1.0e-7 then
      clipPoint d.x d.y d.z b.maxX b.minY b.maxY b.minZ b.maxZ a.x a.y a.z
    else false) ||
  (if d.y > 1.0e-7 then clipPoint d.y d.z d.x b.minY b.minZ b.maxZ b.minX b.maxX a.y a.z a.x
    else if d.y < -1.0e-7 then
      clipPoint d.y d.z d.x b.maxY b.minZ b.maxZ b.minX b.maxX a.y a.z a.x
    else false) ||
  (if d.z > 1.0e-7 then clipPoint d.z d.x d.y b.minZ b.minX b.maxX b.minY b.maxY a.z a.x a.y
    else if d.z < -1.0e-7 then
      clipPoint d.z d.x d.y b.maxZ b.minX b.maxX b.minY b.maxY a.z a.x a.y
    else false)

/-- `VoxelShape.clip(from, to, pos)` is not null: the segment from `a` to `b` hits the shape
`grid` of the block at `p`. It does when it starts inside the shape or enters one of its
boxes. -/
def clipHits (grid : VoxelGrid) (p : Pos) (a b : Vec3) : Bool :=
  if grid.isEmpty then false
  else
    let diff := vsub b a
    if lengthSqr diff < 1.0e-7 then false
    else
      let test := vadd a (vscale diff 0.001)
      let s : Shape := ⟨grid, ⟨0, 0, 0⟩⟩
      let off := Vec3.mk (Float.ofInt p.x) (Float.ofInt p.y) (Float.ofInt p.z)
      grid.isFullWide (s.findIndex .x (test.x - off.x)) (s.findIndex .y (test.y - off.y))
          (s.findIndex .z (test.z - off.z)) ||
        grid.boxes.any fun (x0, y0, z0, x1, y1, z1) =>
          clipBox ⟨x0 + off.x, y0 + off.y, z0 + off.z, x1 + off.x, y1 + off.y, z1 + off.z⟩ a diff

/-- The loop of `BlockGetter.traverseBlocks`, bounded by `fuel` steps: walks from cell to cell
along the segment and returns whether `visit` holds at one of them. -/
def traverseLoop (visit : Pos → Bool) (signX signY signZ : ℤ) (tDeltaX tDeltaY tDeltaZ : Float) :
    ℕ → Pos → Float → Float → Float → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, cur, tX, tY, tZ =>
    if tX ≤ 1.0 || tY ≤ 1.0 || tZ ≤ 1.0 then
      let (cur, tX, tY, tZ) :=
        if tX < tY then
          if tX < tZ then ({ cur with x := cur.x + signX }, tX + tDeltaX, tY, tZ)
          else ({ cur with z := cur.z + signZ }, tX, tY, tZ + tDeltaZ)
        else if tY < tZ then ({ cur with y := cur.y + signY }, tX, tY + tDeltaY, tZ)
        else ({ cur with z := cur.z + signZ }, tX, tY, tZ + tDeltaZ)
      visit cur || traverseLoop visit signX signY signZ tDeltaX tDeltaY tDeltaZ fuel cur tX tY tZ
    else false

/-- `Mth.sign`. -/
def sign (x : Float) : ℤ := if x == 0.0 then 0 else if x > 0.0 then 1 else -1

/-- `BlockGetter.traverseBlocks(from, to, ...)` returns a hit: `visit` holds at one of the cells
the segment from `a` to `b` goes through. -/
def traverseBlocks (visit : Pos → Bool) (a b : Vec3) : Bool :=
  if a.x.toBits == b.x.toBits && a.y.toBits == b.y.toBits && a.z.toBits == b.z.toBits then false
  else
    let toX := lerp (-1.0e-7) b.x a.x
    let toY := lerp (-1.0e-7) b.y a.y
    let toZ := lerp (-1.0e-7) b.z a.z
    let fromX := lerp (-1.0e-7) a.x b.x
    let fromY := lerp (-1.0e-7) a.y b.y
    let fromZ := lerp (-1.0e-7) a.z b.z
    let cur : Pos := ⟨floorInt fromX, floorInt fromY, floorInt fromZ⟩
    if visit cur then true
    else
      let dx := toX - fromX
      let dy := toY - fromY
      let dz := toZ - fromZ
      let signX := sign dx
      let signY := sign dy
      let signZ := sign dz
      let tDeltaX := if signX == 0 then maxDouble else Float.ofInt signX / dx
      let tDeltaY := if signY == 0 then maxDouble else Float.ofInt signY / dy
      let tDeltaZ := if signZ == 0 then maxDouble else Float.ofInt signZ / dz
      let tX := tDeltaX * (if signX > 0 then 1.0 - frac fromX else frac fromX)
      let tY := tDeltaY * (if signY > 0 then 1.0 - frac fromY else frac fromY)
      let tZ := tDeltaZ * (if signZ > 0 then 1.0 - frac fromZ else frac fromZ)
      let fuel := ((floorInt toX - cur.x).natAbs + (floorInt toY - cur.y).natAbs +
        (floorInt toZ - cur.z).natAbs) + 8
      traverseLoop visit signX signY signZ tDeltaX tDeltaY tDeltaZ fuel cur tX tY tZ

/-- `Level.clip` with `ClipContext.Block.COLLIDER` and no fluids hits a block: something
solid lies between `a` and `b`, for a primed TNT whose fall distance is `fall`. The second
component tells whether a shape the model does not have was on the way. -/
def clipCollider (l : Level) (fall : Float) (a b : Vec3) : Bool × Bool :=
  let hit := traverseBlocks (fun p => clipHits (collisionShapeAt l fall p).1 p a b) a b
  let unmodelled := traverseBlocks (fun p => (collisionShapeAt l fall p).2) a b
  (hit, unmodelled)

end Redstone.Entity.Tnt
