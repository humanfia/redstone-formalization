module

public import Redstone.Block.Generated.Shapes
public import Redstone.Basic.Direction

/-!
# Faces of block shapes

Java classes: `VoxelShape` (`getFaceShape`), `SliceShape`, `Shapes` (`joinIsNotEmpty`), `Block`
(`isFaceFull`, `isShapeFullBlock`).

Some blocks look at the shape of a neighbour where it touches them: a snow layer needs the top
of the block below to be full, a wall is raised where the block above covers it. This file
gives these tests for the shapes of the generated table (`Block.shapeBits`), with exact
arithmetic: the coordinates of a shape are `double`s, which are rational numbers.

A shape is a set of cells of a grid. Here it is kept as the union of its boxes together with
the coordinates of its grid, and the joins of `Shapes` are computed on the set of points. The
game compares coordinates with a tolerance of `1.0E-7` (`IndexMerger`, `DoubleMath.fuzzyEquals`);
here they are compared exactly, which is the same for coordinates that are multiples of a
power of two not smaller than `2⁻²⁰`, as those of every block shape are.
-/

@[expose] public section

namespace Redstone

/-- The value of a finite `double`, given by its IEEE bits. -/
def ratOfDoubleBits (bits : UInt64) : ℚ :=
  let n : ℕ := bits.toNat
  let e : ℕ := (n >>> 52) &&& 0x7ff
  let m : ℕ := n &&& (2 ^ 52 - 1)
  let v : ℚ :=
    if e = 0 then mkRat m (2 ^ 1074) else ((m + 2 ^ 52 : ℕ) : ℚ) * (2 : ℚ) ^ ((e : ℤ) - 1075)
  if n.testBit 63 then -v else v

/-- An axis-aligned box with rational corners. -/
structure RatBox where
  minX : ℚ
  minY : ℚ
  minZ : ℚ
  maxX : ℚ
  maxY : ℚ
  maxZ : ℚ
  deriving DecidableEq, Repr

namespace RatBox

/-- `Block.box`: the box with the given corners, in sixteenths of a block. -/
def ofPixels (x0 y0 z0 x1 y1 z1 : ℚ) : RatBox :=
  ⟨x0 / 16, y0 / 16, z0 / 16, x1 / 16, y1 / 16, z1 / 16⟩

/-- The lower end of the box along an axis. -/
def min (b : RatBox) : Axis → ℚ
  | .x => b.minX
  | .y => b.minY
  | .z => b.minZ

/-- The upper end of the box along an axis. -/
def max (b : RatBox) : Axis → ℚ
  | .x => b.maxX
  | .y => b.maxY
  | .z => b.maxZ

/-- The box with its extent along `ax` replaced by `[lo, hi]`. -/
def setRange (b : RatBox) (ax : Axis) (lo hi : ℚ) : RatBox :=
  match ax with
  | .x => { b with minX := lo, maxX := hi }
  | .y => { b with minY := lo, maxY := hi }
  | .z => { b with minZ := lo, maxZ := hi }

/-- The point lies strictly inside the box. -/
def contains (b : RatBox) (x y z : ℚ) : Bool :=
  b.minX < x && x < b.maxX && b.minY < y && y < b.maxY && b.minZ < z && z < b.maxZ

end RatBox

/-- A block shape (`VoxelShape`), relative to its block: the boxes whose union it is, and the
coordinates of its grid along each axis, in increasing order (`getCoords`). -/
structure FaceShape where
  boxes : List RatBox
  xs : List ℚ
  ys : List ℚ
  zs : List ℚ
  deriving Repr

namespace FaceShape

/-- Inserts a coordinate into an increasing list, unless it is there. -/
def insertCoord (v : ℚ) : List ℚ → List ℚ
  | [] => [v]
  | c :: cs => if v < c then v :: c :: cs else if v = c then c :: cs else c :: insertCoord v cs

/-- The increasing list of the ends along `ax` of the given boxes, added to `init`. -/
def boxCoords (ax : Axis) (boxes : List RatBox) (init : List ℚ := []) : List ℚ :=
  boxes.foldl (fun cs b => insertCoord (b.max ax) (insertCoord (b.min ax) cs)) init

/-- Reads the boxes of a shape from the bits of their coordinates. -/
def boxesOfBits : List UInt64 → List RatBox
  | a :: b :: c :: d :: e :: g :: rest =>
    ⟨ratOfDoubleBits a, ratOfDoubleBits b, ratOfDoubleBits c, ratOfDoubleBits d,
      ratOfDoubleBits e, ratOfDoubleBits g⟩ :: boxesOfBits rest
  | _ => []

/-- The shape with the given boxes, on the grid made by the faces of the boxes. -/
def ofBoxes (boxes : List RatBox) : FaceShape :=
  ⟨boxes, boxCoords .x boxes, boxCoords .y boxes, boxCoords .z boxes⟩

/-- `Shapes.empty()`. -/
def empty : FaceShape := ⟨[], [], [], []⟩

/-- `Shapes.block()`: the full cube. -/
def block : FaceShape := ofBoxes [⟨0, 0, 0, 1, 1, 1⟩]

/-- The shape number `i` of the table generated from the server. A collision shape has the grid
that the game gives it; for any other shape the grid is made by the faces of its boxes. -/
def ofIndex (i : ℕ) : FaceShape :=
  let boxes := boxesOfBits (Block.shapeBits.getD i #[]).toList
  match Block.shapeGridBits.getD i #[] with
  | #[xs, ys, zs] =>
    ⟨boxes, xs.toList.map ratOfDoubleBits, ys.toList.map ratOfDoubleBits,
      zs.toList.map ratOfDoubleBits⟩
  | _ => ofBoxes boxes

/-- `VoxelShape.isEmpty`. -/
def isEmpty (s : FaceShape) : Bool := s.boxes.isEmpty

/-- `VoxelShape.getCoords(axis)`. -/
def coords (s : FaceShape) : Axis → List ℚ
  | .x => s.xs
  | .y => s.ys
  | .z => s.zs

/-- `VoxelShape.isCubeLikeAlong(axis)`: the grid has one cell along the axis, from 0 to 1. -/
def isCubeLikeAlong (s : FaceShape) (ax : Axis) : Bool := s.coords ax == [0, 1]

/-- The cell of an increasing list of coordinates that contains `c`: the consecutive
coordinates `lo ≤ c < hi` (`VoxelShape.findIndex`). -/
def cellAt (c : ℚ) : List ℚ → Option (ℚ × ℚ)
  | lo :: hi :: rest => if lo ≤ c && c < hi then some (lo, hi) else cellAt c (hi :: rest)
  | _ => none

/-- `VoxelShape.getFaceShape(direction)`: the part of the shape that touches the face
`direction` of its block, stretched over the whole block along the axis of the face. A shape
with a single cell from 0 to 1 along that axis is its own face shape. Otherwise the face shape
is the layer of cells at `0.9999999` (for a positive direction) or at `1.0E-7` (`SliceShape`),
and it is empty when the shape has no cell there. -/
def faceShape (s : FaceShape) (d : Direction) : FaceShape :=
  let ax := d.axis
  if s.isEmpty || s.isCubeLikeAlong ax then s else
  let c : ℚ := if d = .up || d = .south || d = .east then 9999999 / 10000000 else 1 / 10000000
  match cellAt c (s.coords ax) with
  | none => empty
  | some (lo, hi) =>
    let boxes := (s.boxes.filter fun b => b.min ax ≤ lo && hi ≤ b.max ax).map (·.setRange ax 0 1)
    if boxes.isEmpty then empty else
    match ax with
    | .x => ⟨boxes, [0, 1], s.ys, s.zs⟩
    | .y => ⟨boxes, s.xs, [0, 1], s.zs⟩
    | .z => ⟨boxes, s.xs, s.ys, [0, 1]⟩

/-- The point lies inside the shape. -/
def contains (s : FaceShape) (x y z : ℚ) : Bool := s.boxes.any (·.contains x y z)

/-- The middles of the cells of an increasing list of coordinates. -/
def mids : List ℚ → List ℚ
  | a :: b :: rest => (a + b) / 2 :: mids (b :: rest)
  | _ => []

/-- `!Shapes.joinIsNotEmpty(first, second, BooleanOp.ONLY_FIRST)`: every point of `first` lies
in `second`. It is enough to look at the middle of every cell of the grid made by the faces of
all the boxes. -/
def subset (first second : FaceShape) : Bool :=
  let all := first.boxes ++ second.boxes
  (mids (boxCoords .x all)).all fun x =>
    (mids (boxCoords .y all)).all fun y =>
      (mids (boxCoords .z all)).all fun z => !first.contains x y z || second.contains x y z

/-- `Block.isShapeFullBlock(shape)`: `!Shapes.joinIsNotEmpty(Shapes.block(), shape, NOT_SAME)`,
the shape is exactly the full cube. -/
def isFullBlock (s : FaceShape) : Bool := subset block s && subset s block

/-- `Block.isFaceFull(shape, direction)`: the shape covers the whole face `direction`. -/
def isFaceFull (s : FaceShape) (d : Direction) : Bool := (s.faceShape d).isFullBlock

end FaceShape

end Redstone
