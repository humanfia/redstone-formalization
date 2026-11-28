module

public import Redstone.Mechanics.Tick
public import Redstone.Block.Generated.Shapes
public import Redstone.Entity.Touch

/-!
# Entity physics

How an entity moves through the blocks of the world: `Entity.move` with `Entity.collide`,
`Shapes.collide` and `VoxelShape.collide`, the supporting block, fall distance, the bounce of
`restituteMovementAfterCollisions`, gravity, and the effects of the blocks an entity touches
(through `Redstone.Entity.Touch`).

The arithmetic is that of the game: every operation on `double` and `float` values is done in
the same order, so results agree bit for bit. Constants that are not exactly representable are
given by their bits.

## What is left out

* Fluids. An entity that touches a block holding a fluid sets `Level.overflow`.
* Collisions with other entities (boats, shulkers) and with the world border.
* Stepping up (`Entity.maxUpStep`), which is zero for the entities modelled here.
* Collision shapes that depend on the entity or on the position of the block (scaffolding,
  powder snow, bamboo, pointed dripstone, moving pistons, shulker boxes). Meeting one of these
  sets `Level.overflow`.
* The box of an entity is always taken as a shape with its own coordinates. The game snaps a
  box that lies in the unit cube on multiples of one eighth to that grid, with a tolerance.
* Blocks whose `fallOn` does more than pass the fall on to the entity (farmland, turtle eggs,
  powder snow, pointed dripstone) set `Level.overflow` when an entity lands on them.
-/

@[expose] public section

namespace Redstone


/-! ### Shapes -/

/-- The shape of a block (`VoxelShape`), relative to the block: its boxes, and the coordinates
of its grid along each axis, in increasing order. These coordinates cut space into cells; a
cell is full when it lies in one of the boxes. -/
structure Shape where
  boxes : List AABB
  xs : Array Float
  ys : Array Float
  zs : Array Float

namespace Shape

/-- Inserts a coordinate into an increasing list, unless it is there. -/
def insertCoord (v : Float) : List Float → List Float
  | [] => [v]
  | c :: cs => if v < c then v :: c :: cs else if v == c then c :: cs else c :: insertCoord v cs

/-- The shape with the given boxes, on the grid made by the faces of the boxes. -/
def ofBoxes (boxes : List AABB) : Shape where
  boxes := boxes
  xs := (boxes.foldl (fun cs b => insertCoord b.maxX (insertCoord b.minX cs)) []).toArray
  ys := (boxes.foldl (fun cs b => insertCoord b.maxY (insertCoord b.minY cs)) []).toArray
  zs := (boxes.foldl (fun cs b => insertCoord b.maxZ (insertCoord b.minZ cs)) []).toArray

/-- The shape number `i` of the table generated from the server. A collision shape has the grid
that the game gives it; for any other shape the grid is made by the faces of its boxes. -/
def ofIndex (i : ℕ) : Shape :=
  let boxes := AABB.listOfBits (Block.shapeBits.getD i #[]).toList
  match Block.shapeGridBits.getD i #[] with
  | #[xs, ys, zs] => ⟨boxes, xs.map .ofBits, ys.map .ofBits, zs.map .ofBits⟩
  | _ => ofBoxes boxes

/-- `VoxelShape.isEmpty`. -/
def isEmpty (s : Shape) : Bool := s.boxes.isEmpty

/-- The shape is `Shapes.block()`, the full cube. -/
def isBlock (s : Shape) : Bool :=
  match s.boxes with
  | [b] => b.minX.toBits == 0 && b.minY.toBits == 0 && b.minZ.toBits == 0 &&
    b.maxX == 1 && b.maxY == 1 && b.maxZ == 1
  | _ => false

/-- `VoxelShape.getCoords(axis)`. -/
def coords (s : Shape) : Axis → Array Float
  | .x => s.xs
  | .y => s.ys
  | .z => s.zs

/-- `DiscreteVoxelShape.getSize(axis)`: the number of cells along an axis. -/
def size (s : Shape) (ax : Axis) : ℤ := ((s.coords ax).size : ℤ) - 1

/-- `DiscreteVoxelShape.isFullWide(x, y, z)`: the cell with these indices exists and is full. -/
def isFullWide (s : Shape) (i j k : ℤ) : Bool :=
  if i < 0 || j < 0 || k < 0 then false else
  match s.xs[i.toNat]?, s.xs[i.toNat + 1]?, s.ys[j.toNat]?, s.ys[j.toNat + 1]?,
    s.zs[k.toNat]?, s.zs[k.toNat + 1]? with
  | some x0, some x1, some y0, some y1, some z0, some z1 =>
    s.boxes.any fun b =>
      b.minX ≤ x0 && x1 ≤ b.maxX && b.minY ≤ y0 && y1 ≤ b.maxY && b.minZ ≤ z0 && z1 ≤ b.maxZ
  | _, _, _, _, _, _ => false

/-- `isFullWide` with the first index along `ax` and the other two along the remaining axes. -/
def isFullAlong (s : Shape) (ax : Axis) (a b c : ℤ) : Bool :=
  match ax with
  | .x => s.isFullWide a b c
  | .y => s.isFullWide b a c
  | .z => s.isFullWide b c a

/-- `VoxelShape.min(axis)` of a shape that is not empty. -/
def min (s : Shape) (ax : Axis) : Float :=
  match s.boxes with
  | [] => 0
  | b :: bs => bs.foldl (fun m c => if c.min ax < m then c.min ax else m) (b.min ax)

/-- `VoxelShape.max(axis)` of a shape that is not empty. -/
def max (s : Shape) (ax : Axis) : Float :=
  match s.boxes with
  | [] => 0
  | b :: bs => bs.foldl (fun m c => if c.max ax > m then c.max ax else m) (b.max ax)

/-- `BlockState.hasLargeCollisionShape`: the shape reaches outside its block. -/
def isLarge (s : Shape) : Bool :=
  !s.isEmpty && [Axis.x, Axis.y, Axis.z].any fun ax => s.min ax < 0 || s.max ax > 1

end Shape

/-- The two axes other than `ax`. -/
def Axis.others : Axis → Axis × Axis
  | .x => (.y, .z)
  | .y => (.x, .z)
  | .z => (.x, .y)

/-- The coordinate of a block position along an axis, as a `double`. -/
def Pos.coord (p : Pos) : Axis → Float
  | .x => Phys.ofInt p.x
  | .y => Phys.ofInt p.y
  | .z => Phys.ofInt p.z

/-- A shape placed at a block position (`VoxelShape.move(pos)`). Its coordinates are those of
the shape plus the position. -/
structure PlacedShape where
  shape : Shape
  pos : Pos

namespace PlacedShape

/-- `VoxelShape.get(axis, i)` of the moved shape. -/
def get (s : PlacedShape) (ax : Axis) (i : ℤ) : Float :=
  ((s.shape.coords ax)[i.toNat]?).getD 0 + s.pos.coord ax

/-- `VoxelShape.findIndex(axis, coord)`: the index of the cell that contains `coord`, which is
`-1` below the shape and the number of cells above it. -/
def findIndex (s : PlacedShape) (ax : Axis) (coord : Float) : ℤ :=
  let off := s.pos.coord ax
  (((s.shape.coords ax).toList.takeWhile fun c => !(coord < c + off)).length : ℤ) - 1

/-- The integers from `lo` to `hi - 1`. -/
def range (lo hi : ℤ) : List ℤ := (List.range (hi - lo).toNat).map fun i => lo + i

/-- `VoxelShape.collide(axis, moving, distance)`: how far the box `moving` can travel along
`ax`, at most `distance`, before it meets the shape. -/
def collide (s : PlacedShape) (ax : Axis) (moving : AABB) (distance : Float) : Float :=
  if s.shape.isEmpty then distance
  else if distance.abs < Phys.eps7 then 0.0
  else
    let (bx, cx) := ax.others
    let maxA := moving.max ax
    let minA := moving.min ax
    let aMin := s.findIndex ax (minA + Phys.eps7)
    let aMax := s.findIndex ax (maxA - Phys.eps7)
    let bMin := Max.max 0 (s.findIndex bx (moving.min bx + Phys.eps7))
    let bMax := Min.min (s.shape.size bx) (s.findIndex bx (moving.max bx - Phys.eps7) + 1)
    let cMin := Max.max 0 (s.findIndex cx (moving.min cx + Phys.eps7))
    let cMax := Min.min (s.shape.size cx) (s.findIndex cx (moving.max cx - Phys.eps7) + 1)
    let full (a : ℤ) : Bool :=
      (range bMin bMax).any fun b => (range cMin cMax).any fun c => s.shape.isFullAlong ax a b c
    if distance > 0 then
      match (range (aMax + 1) (s.shape.size ax)).find? full with
      | some a =>
        let newDistance := s.get ax a - maxA
        if newDistance ≥ -Phys.eps7 then Phys.min distance newDistance else distance
      | none => distance
    else if distance < 0 then
      match (range 0 aMin).reverse.find? full with
      | some a =>
        let newDistance := s.get ax (a + 1) - minA
        if newDistance ≤ Phys.eps7 then Phys.max distance newDistance else distance
      | none => distance
    else distance

/-- The merged cells of an `IndirectMerger` for two coordinate lists, when neither list matters
on its own (the operation is `BooleanOp.AND`): for each merged cell, the cell of the first list
and the cell of the second list it lies in. The state is the next index in each list, the last
coordinate written, and the points written so far, last first. -/
def indirectLoop (first second : Array Float) :
    ℕ → ℕ → ℕ → Option Float → List (ℤ × ℤ) → List (ℤ × ℤ)
  | 0, _, _, _, out => out
  | fuel + 1, fi, si, last, out =>
    let ranOutOfFirst := fi ≥ first.size
    let ranOutOfSecond := si ≥ second.size
    if ranOutOfFirst && ranOutOfSecond then out
    else
      let choseFirst := !ranOutOfFirst &&
        (ranOutOfSecond || first[fi]?.getD 0 < second[si]?.getD 0 + Phys.eps7)
      if choseFirst && (si == 0 || ranOutOfSecond) then
        indirectLoop first second fuel (fi + 1) si last out
      else if !choseFirst && (fi == 0 || ranOutOfFirst) then
        indirectLoop first second fuel fi (si + 1) last out
      else
        let fi := if choseFirst then fi + 1 else fi
        let si := if choseFirst then si else si + 1
        let nextValue := if choseFirst then first[fi - 1]?.getD 0 else second[si - 1]?.getD 0
        let entry : ℤ × ℤ := ((fi : ℤ) - 1, (si : ℤ) - 1)
        if last.any (· ≥ nextValue - Phys.eps7) then
          indirectLoop first second fuel fi si last (entry :: out.tail)
        else indirectLoop first second fuel fi si (some nextValue) (entry :: out)

/-- `IndexMerger.forMergedIndexes` of the merger that `Shapes.createIndexMerger` builds for two
coordinate lists that overlap: the pairs of cells that the merged cells lie in. -/
def mergedCells (first second : Array Float) : List (ℤ × ℤ) :=
  if first.size == second.size &&
      (first.toList.zip second.toList).all (fun (a, b) => a.toBits == b.toBits) then
    (List.range (first.size - 1)).map fun i => ((i : ℤ), (i : ℤ))
  else
    let points := (indirectLoop first second (first.size + second.size + 1) 0 0 none []).reverse
    points.dropLast

/-- `Shapes.joinIsNotEmpty(shape, Shapes.create(box), BooleanOp.AND)`: the shape and the box
overlap. The box is taken with its own coordinates; the game snaps a box that lies in the unit
cube on multiples of one eighth to that grid. -/
def intersectsBox (s : PlacedShape) (box : AABB) : Bool :=
  let axes := [Axis.x, Axis.y, Axis.z]
  if s.shape.isEmpty then false
  else if axes.any fun ax => box.max ax - box.min ax < Phys.eps7 then false
  else if axes.any fun ax =>
      s.shape.max ax + s.pos.coord ax < box.min ax - Phys.eps7 ||
        box.max ax < s.shape.min ax + s.pos.coord ax - Phys.eps7 then false
  else
    let cells (ax : Axis) : List ℤ :=
      let moved := (s.shape.coords ax).map (· + s.pos.coord ax)
      (mergedCells moved #[box.min ax, box.max ax]).filterMap fun (i, j) =>
        if j == 0 then some i else none
    (cells .x).any fun i => (cells .y).any fun j => (cells .z).any fun k =>
      s.shape.isFullWide i j k

end PlacedShape

/-! ### The blocks an entity can collide with -/

namespace Block

/-- `BlockState.getCollisionShape` for a block whose collision shape depends neither on its
position nor on the entity. -/
def collisionShape (b : Block) : Shape := Shape.ofIndex b.attrs.collision

/-- The blocks whose collision shape depends on the position or on the entity that asks, or
comes from a block entity. They are not modelled. -/
def collisionUnmodelled (b : Block) : Bool :=
  b.is .scaffolding || b.is .powder_snow || b.is .bamboo || b.is .pointed_dripstone ||
    b.is .moving_piston || b.id.name.endsWith "shulker_box"

/-- `BlockState.isCollisionShapeFullBlock`. -/
def isCollisionShapeFullBlock (b : Block) : Bool := b.collisionShape.isBlock

/-- The block holds a fluid (`!getFluidState().isEmpty()`). -/
def hasFluid (b : Block) : Bool := b.attrs.fluid != ""

/-- The block is in the tag `minecraft:fences`. -/
def isFence (b : Block) : Bool := b.id.name.endsWith "_fence"

/-- The block is in the tag `minecraft:walls`. -/
def isWall (b : Block) : Bool := b.id.name.endsWith "_wall"

/-- The block is a `FenceGateBlock`. -/
def isFenceGate (b : Block) : Bool := b.id.name.endsWith "_fence_gate"

/-- `Block.getFriction` as the bits of a `float`. -/
def frictionBits (b : Block) : UInt32 :=
  if b.is .ice || b.is .packed_ice || b.is .frosted_ice then 0x3f7ae148
  else if b.is .blue_ice then 0x3f7d2f1b
  else if b.is .slime_block then 0x3f4ccccd
  else 0x3f19999a

/-- `Block.getSpeedFactor`. -/
def speedFactor (b : Block) : Float :=
  if b.is .soul_sand || b.is .honey_block then Phys.f 0x3ecccccd else 1.0

/-- `Block.getBounceRestitution` as the bits of a `float`. -/
def bounceRestitutionBits (b : Block) : UInt32 :=
  if b.is .slime_block then 0x3f800000
  else if b.id.name.endsWith "_bed" || b.is .shelf_mushroom then 0x3f400000
  else 0

/-- `Block.getFallDistanceReduction` as the bits of a `float`. -/
def fallDistanceReductionBits (b : Block) : UInt32 :=
  if b.id.name.endsWith "_bed" || b.is .shelf_mushroom then 0x3f000000 else 0

end Block

namespace Level

/-- `BlockCollisions`: the blocks whose collision shape overlaps `box`, in the order in which
the game finds them, each with its shape. The flag tells that a block whose collision shape is
not modelled was among the candidates. -/
def blockCollisions (l : Level) (box : AABB) : List PlacedShape × Bool := Id.run do
  let x0 := Phys.floor (box.minX - Phys.eps7) - 1
  let x1 := Phys.floor (box.maxX + Phys.eps7) + 1
  let y0 := Phys.floor (box.minY - Phys.eps7) - 1
  let y1 := Phys.floor (box.maxY + Phys.eps7) + 1
  let z0 := Phys.floor (box.minZ - Phys.eps7) - 1
  let z1 := Phys.floor (box.maxZ + Phys.eps7) + 1
  let width := (x1 - x0 + 1).toNat
  let height := (y1 - y0 + 1).toNat
  let depth := (z1 - z0 + 1).toNat
  let mut out : List PlacedShape := []
  let mut unmodelled := false
  for index in [0:width * height * depth] do
    let x := index % width
    let slice := index / width
    let y := slice % height
    let z := slice / height
    let type := (if x == 0 || x == width - 1 then 1 else 0) +
      (if y == 0 || y == height - 1 then 1 else 0) + (if z == 0 || z == depth - 1 then 1 else 0)
    if type != 3 then
      let p : Pos := ⟨x0 + x, y0 + y, z0 + z⟩
      let state := l.blockAt p
      if state.collisionUnmodelled then unmodelled := true
      else if state.attrs.collision != 0 then
        let shape := state.collisionShape
        if type == 0 || (type == 1 && shape.isLarge) then
          let placed : PlacedShape := ⟨shape, p⟩
          if shape.isBlock then
            if box.intersects (AABB.ofBlock p) then out := placed :: out
          else if placed.intersectsBox box then out := placed :: out
  return (out.reverse, unmodelled)

/-- `Level.noCollision(entity, box)`, for blocks only: no collision shape overlaps `box`. -/
def noBlockCollision (l : Level) (box : AABB) : Bool := (l.blockCollisions box).1.isEmpty

/-- A block that holds a fluid touches `box`. -/
def touchesFluid (l : Level) (box : AABB) : Bool :=
  (PlacedShape.range (Phys.floor box.minX) (Phys.floor box.maxX + 1)).any fun x =>
    (PlacedShape.range (Phys.floor box.minY) (Phys.floor box.maxY + 1)).any fun y =>
      (PlacedShape.range (Phys.floor box.minZ) (Phys.floor box.maxZ + 1)).any fun z =>
        (l.blockAt ⟨x, y, z⟩).hasFluid

/-- `CollisionGetter.findSupportingBlock(entity, box)`: among the blocks that collide with
`box`, the one whose centre is closest to the position `at` of the entity. -/
def findSupportingBlock (l : Level) (pos : Vec3) (box : AABB) : Option Pos :=
  let step (best : Option (Pos × Float)) (s : PlacedShape) : Option (Pos × Float) :=
    let p := s.pos
    let dx := Phys.ofInt p.x + 0.5 - pos.x
    let dy := Phys.ofInt p.y + 0.5 - pos.y
    let dz := Phys.ofInt p.z + 0.5 - pos.z
    let distance := dx * dx + dy * dy + dz * dz
    match best with
    | none => some (p, distance)
    | some (q, bestDistance) =>
      -- `Vec3i.compareTo` orders by y, then z, then x
      let before := q.y < p.y || (q.y == p.y && (q.z < p.z || (q.z == p.z && q.x < p.x)))
      if distance < bestDistance || (distance == bestDistance && before) then some (p, distance)
      else best
  ((l.blockCollisions box).1.foldl step none).map (·.1)

end Level

/-! ### Collision of a moving box -/

namespace Phys

/-- `Shapes.collide(axis, moving, shapes, distance)`. -/
def collideShapes (ax : Axis) (moving : AABB) (shapes : List PlacedShape) (distance : Float) :
    Float :=
  match shapes with
  | [] => distance
  | s :: rest =>
    if distance.abs < eps7 then 0.0 else collideShapes ax moving rest (s.collide ax moving distance)

/-- `Entity.collideWithShapes(movement, box, shapes)`: the part of `movement` the box can
make. -/
def collideWithShapes (movement : Vec3) (box : AABB) (shapes : List PlacedShape) : Vec3 :=
  if shapes.isEmpty then movement
  else
    (axisStepOrder movement).foldl (init := Vec3.zero) fun resolved ax =>
      let axisMovement := movement.get ax
      if axisMovement != 0 then
        resolved.set ax (collideShapes ax (box.move resolved) shapes axisMovement)
      else resolved

/-- `Entity.collide(movement)` for an entity that cannot step up, in a world without entities
to collide with. The flag tells that a block whose collision shape is not modelled was near. -/
def collide (l : Level) (box : AABB) (movement : Vec3) : Vec3 × Bool :=
  if movement.lengthSqr == 0 then (movement, false)
  else
    let (shapes, unmodelled) := l.blockCollisions (box.expandTowards movement)
    (collideWithShapes movement box shapes, unmodelled)

end Phys

/-! ### Entities -/

namespace Entity

/-- `Entity.getId()`. The harness resets the counter of entity ids, and the first id goes to the
player of the `use` actions, so the entity with index `i` has id `i + 2`, as long as every
entity that is created is in the world at the end of the tick. -/
def id (e : Entity) : ℕ := e.index + 2

/-- The seed of `Entity.random`: the harness seeds the generator of the entity with id `n` with
`n * 0x9E3779B97F4A7C15` (see `tests/FORMAT.md`), under the same assumption as `id`. -/
def randomOfId (n : ℕ) : JavaRandom := .ofSeed ((n * 0x9E3779B97F4A7C15) % 2 ^ 64)

/-- The generator after the constructor of `Entity`, which draws the UUID of the entity
(`Mth.createInsecureUUID`: two `nextLong`). -/
def randomAfterUuid (n : ℕ) : JavaRandom :=
  let r := randomOfId n
  let r := (r.next 32).2
  let r := (r.next 32).2
  let r := (r.next 32).2
  (r.next 32).2

/-- The state `Entity.move` works with, for the kinds of entity whose motion is modelled. -/
def phys (e : Entity) : Entities.Physics :=
  match e.data with
  | .item dt => dt.phys
  | .fallingBlock dt => dt.phys
  | _ => {}

/-- Replaces the state `Entity.move` works with. -/
def withPhys (e : Entity) (p : Entities.Physics) : Entity :=
  match e.data with
  | .item dt => { e with data := .item { dt with phys := p } }
  | .fallingBlock dt => { e with data := .fallingBlock { dt with phys := p } }
  | _ => e

/-- Changes the state `Entity.move` works with. -/
def modifyPhys (e : Entity) (g : Entities.Physics → Entities.Physics) : Entity :=
  e.withPhys (g e.phys)

/-- What `Entity.move` needs to know about the kind of an entity. -/
structure Kind where
  /-- `EntityType.getDimensions`. -/
  dims : Dimensions
  /-- `getDefaultGravity`. -/
  gravity : Float
  /-- `getAirDrag`. -/
  airDrag : Float := Phys.f 0x3f7ae148
  /-- The offset of `getBlockPosBelowThatAffectsMyMovement`. -/
  movementOffset : Float := Phys.f 0x3f000011
  /-- `causeFallDamage(fallDistance, ...)` for the entity with the given index. -/
  causeFallDamage : ℕ → Float → M Unit := fun _ _ => pure ()

/-- `Entity.getOnPos(offset)` for an entity at `pos` whose supporting block
(`mainSupportingBlockPos`) is `support`: the block below the entity that is `offset` under its
feet, or its supporting block. -/
def onPos (l : Level) (pos : Vec3) (support : Option Pos) (offset : Float) : Pos :=
  match support with
  | some p =>
    if !(offset > Phys.eps5f) then p
    else
      let below := l.blockAt p
      if (!(offset ≤ 0.5) || !below.isFence) && !below.isWall && !below.isFenceGate then
        { p with y := Phys.floor (pos.y - offset) }
      else p
  | none => ⟨Phys.floor pos.x, Phys.floor (pos.y - offset), Phys.floor pos.z⟩

/-- `Entity.getOnPos(offset)`. -/
def getOnPos (l : Level) (e : Entity) (offset : Float) : Pos :=
  onPos l e.base.pos e.phys.mainSupportingBlockPos offset

/-- `Entity.getOnPosLegacy`. -/
def getOnPosLegacy (l : Level) (e : Entity) : Pos := getOnPos l e (Phys.f 0x3e4ccccd)

/-- `Entity.checkSupportingBlock(onGround, movement)`. -/
def checkSupportingBlock (l : Level) (dims : Dimensions) (e : Entity) (onGround : Bool)
    (movement : Option Vec3) : Entity :=
  if onGround then
    let box := dims.box e.base.pos
    let testArea := AABB.of box.minX (box.minY - Phys.eps6) box.minZ box.maxX box.minY box.maxZ
    let found := l.findSupportingBlock e.base.pos testArea
    if found.isSome || e.phys.onGroundNoBlocks then
      e.modifyPhys fun p =>
        { p with mainSupportingBlockPos := found, onGroundNoBlocks := found.isNone }
    else
      match movement with
      | some m =>
        let found := l.findSupportingBlock e.base.pos (testArea.move ⟨-m.x, 0.0, -m.z⟩)
        e.modifyPhys fun p =>
          { p with mainSupportingBlockPos := found, onGroundNoBlocks := found.isNone }
      | none => e.modifyPhys fun p => { p with onGroundNoBlocks := true }
  else
    e.modifyPhys fun p => { p with onGroundNoBlocks := false, mainSupportingBlockPos := none }

/-- `Entity.getBlockSpeedFactor`. -/
def getBlockSpeedFactor (l : Level) (k : Kind) (e : Entity) : Float :=
  let state := l.blockAt e.base.pos.blockPos
  let here := state.speedFactor
  if !state.is .water && !state.is .bubble_column then
    if here == 1.0 then (l.blockAt (getOnPos l e k.movementOffset)).speedFactor else here
  else here

/-- The blocks in the tag `minecraft:fall_damage_resetting`. -/
def isFallDamageResetting (b : Block) : Bool :=
  b.is .ladder || b.is .vine || b.is .scaffolding || b.is .weeping_vines ||
    b.is .weeping_vines_plant || b.is .twisting_vines || b.is .twisting_vines_plant ||
    b.is .cave_vines || b.is .cave_vines_plant || b.is .sweet_berry_bush || b.is .cobweb

/-- Whether the ray that `Entity.move` casts for a fast fall (`ClipContext.Block
.FALLDAMAGE_RESETTING` with water) could hit something: a block of the tag or a fluid lies in
the box spanned by the two ends of the movement. The ray itself is not modelled. -/
def fallResetPossible (l : Level) (pos movement : Vec3) : Bool :=
  let target := pos.add movement
  let box := AABB.of pos.x pos.y pos.z target.x target.y target.z
  (PlacedShape.range (Phys.floor box.minX) (Phys.floor box.maxX + 1)).any fun x =>
    (PlacedShape.range (Phys.floor box.minY) (Phys.floor box.maxY + 1)).any fun y =>
      (PlacedShape.range (Phys.floor box.minZ) (Phys.floor box.maxZ + 1)).any fun z =>
        let b := l.blockAt ⟨x, y, z⟩
        b.hasFluid || isFallDamageResetting b

/-- The blocks that override `Block.fallOn` with more than a call of `causeFallDamage`. -/
def fallOnUnmodelled (b : Block) : Bool :=
  b.is .farmland || b.is .turtle_egg || b.is .powder_snow || b.is .pointed_dripstone

/-- The fall distance that `Block.fallOn` passes to `Entity.causeFallDamage`. Slime, hay and
honey blocks pass it unchanged; the others reduce it by `getFallDistanceReduction`. -/
def fallOnDistance (b : Block) (fallDistance : Float) : Float :=
  if b.is .slime_block || b.is .hay_block || b.is .honey_block then fallDistance
  else
    let one : Float32 := 1
    fallDistance * (one - Float32.ofBits b.fallDistanceReductionBits).toFloat

/-- `Entity.getBlockBounciness` for an entity that is not a `LivingEntity`. -/
def blockBounciness (b : Block) : Float :=
  (Float32.ofBits b.bounceRestitutionBits * Float32.ofBits 0x3f4ccccd).toFloat

/-- `Entity.restituteMovementAfterCollisions` for an entity without bounciness of its own: the
velocity after a collision. The flag tells that the entity bounced. -/
def restitute (k : Kind) (effectState : Block) (e : Entity) (xCollision zCollision : Bool)
    (movement : Vec3) : Vec3 × Bool :=
  let restitution : Float := 0.0
  let current := e.base.motion
  let after := if xCollision then current.set .x ((-current.x) * restitution) else current
  let after := if zCollision then after.set .z ((-current.z) * restitution) else after
  let bounced := restitution > 0 && (xCollision || zCollision)
  if e.phys.verticalCollision then
    let restitution :=
      if e.phys.verticalCollisionBelow then
        if !(-current.y ≤ k.gravity) && !effectState.is .honey_block then
          Phys.max restitution (blockBounciness effectState)
        else 0.0
      else restitution
    let (gravityCompensation, effectiveDrag, bounced) :=
      if restitution > 0 then
        let portionWithMovement := movement.y / current.y
        (portionWithMovement * k.gravity, 1.0 + portionWithMovement * (k.airDrag - 1.0), true)
      else (0.0, 1.0, bounced)
    (after.set .y ((gravityCompensation - current.y) * effectiveDrag * restitution), bounced)
  else (after, bounced)

end Entity

namespace Level

/-- The entity with the given index, if it is alive. -/
def getEntity (i : ℕ) : M (Option Entity) := return (← get).entity? i

/-- Replaces the entity that has the index of `e`. -/
def setEntity (e : Entity) : M Unit := modifyEntity e.index fun _ => e

/-- The entity section a point lies in (`SectionPos.of(BlockPos.containing(p))`). -/
def sectionOf (p : Vec3) : ℤ × ℤ × ℤ :=
  (Phys.floor p.x / 16, Phys.floor p.y / 16, Phys.floor p.z / 16)

/-- `Entity.setPos(pos)`: the entity moves to `pos`. When that takes it to another entity
section it is added at the end of that section (`EntitySection.add`); `actor` tells what moves
the entity, as in `Entities.Physics.sectionEntry`. -/
def setPos (e : Entity) (pos : Vec3) (gameTime actor : ℕ) : Entity :=
  let moved : Entity := { e with base := { e.base with pos := pos } }
  if sectionOf e.base.pos == sectionOf pos then moved
  else moved.modifyPhys fun p => { p with sectionEntry := (gameTime, actor) }

/-- `Entity.checkFallDamage(ya, onGround, onState, pos)` followed by the bounce and the block
speed factor: the end of `Entity.move`, from the point where the entity has its new position
and its collision flags. -/
def finishMove (k : Entity.Kind) (i : ℕ) (delta movement : Vec3) (xCollision zCollision : Bool) :
    M Unit := do
  let some e ← getEntity i | return
  let l ← get
  let effectPos := Entity.getOnPosLegacy l e
  let effectState := l.blockAt effectPos
  -- `checkFallDamage`
  let fall := e.phys.fallDistance
  let fall := if movement.y < 0 then fall - Phys.toFloat32 movement.y else fall
  setEntity (e.modifyPhys fun p => { p with fallDistance := fall })
  if e.base.onGround then
    if fall > 0 then
      if Entity.fallOnUnmodelled effectState then setOverflow
      k.causeFallDamage i (Entity.fallOnDistance effectState fall)
      gameEvent "minecraft:hit_ground" e.base.pos.blockPos
    modifyEntity i fun e => e.modifyPhys fun p => { p with fallDistance := 0 }
  let some e ← getEntity i | return
  let movedVertically := delta.y.abs > 0
  if (movedVertically && e.phys.verticalCollision) || e.phys.horizontalCollision then
    let (motion, bounced) := Entity.restitute k effectState e xCollision zCollision movement
    if bounced then gameEvent "minecraft:bounce" e.base.pos.blockPos
    modifyEntity i fun e => { e with base := { e.base with motion := motion } }
  let some e ← getEntity i | return
  let factor := Entity.getBlockSpeedFactor (← get) k e
  setEntity { e with base := { e.base with motion := e.base.motion.mul factor 1.0 factor } }

/-- `Entity.move(MoverType.SELF, delta)` for the entity with index `i`. -/
def moveEntity (k : Entity.Kind) (i : ℕ) (delta : Vec3) : M Unit := do
  let some e ← getEntity i | return
  let l ← get
  if e.phys.noPhysics then
    let e := setPos e (e.base.pos.add delta) l.gameTime (i + 1)
    setEntity (e.modifyPhys fun p => { p with
      horizontalCollision := false, verticalCollision := false, verticalCollisionBelow := false })
  else
    let stuck := e.phys.stuckSpeedMultiplier
    let (delta, e) :=
      if stuck.lengthSqr > Phys.eps7 then
        (delta.mul stuck.x stuck.y stuck.z,
          { e.modifyPhys fun p => { p with stuckSpeedMultiplier := .zero } with
            base := { e.base with motion := .zero } })
      else (delta, e)
    let (movement, unmodelled) := Phys.collide l (k.dims.box e.base.pos) delta
    if unmodelled then setOverflow
    let movementLength := movement.lengthSqr
    let moves := movementLength > Phys.eps7 || delta.lengthSqr - movementLength < Phys.eps7
    if moves && e.phys.fallDistance != 0 && movementLength ≥ 1.0 &&
        Entity.fallResetPossible l e.base.pos movement then
      setOverflow
    -- `addMovementThisTick(new Movement(pos, newPosition, delta))`
    let e :=
      if moves then
        let target := e.base.pos.add movement
        (setPos e target l.gameTime (i + 1)).modifyPhys fun p =>
          { p with movementThisTick := p.movementThisTick ++ [⟨e.base.pos, target, some delta⟩] }
      else e
    let xCollision := !Phys.equal delta.x movement.x
    let zCollision := !Phys.equal delta.z movement.z
    let horizontalCollision := xCollision || zCollision
    let verticalCollision := delta.y != movement.y
    let verticalCollisionBelow := verticalCollision && delta.y < 0
    let e := e.modifyPhys fun p => { p with
      horizontalCollision := horizontalCollision
      verticalCollision := verticalCollision
      verticalCollisionBelow := verticalCollisionBelow }
    -- `setOnGroundWithMovement(verticalCollisionBelow, horizontalCollision, movement)`
    let e := { e with base := { e.base with onGround := verticalCollisionBelow } }
    setEntity (Entity.checkSupportingBlock l k.dims e verticalCollisionBelow (some movement))
    finishMove k i delta movement xCollision zCollision

/-- `Entity.applyGravity` for the entity with index `i`. -/
def applyGravity (k : Entity.Kind) (i : ℕ) : M Unit :=
  modifyEntity i fun e =>
    if e.phys.noGravity || k.gravity == 0 then e
    else { e with base := { e.base with motion := e.base.motion.add ⟨0.0, -k.gravity, 0.0⟩ } }

/-- `Entity.applyEffectsFromBlocksForLastMovements` for the entity with index `i`: the block the
entity stands on is told (`stepOn`), and so are the blocks it met (`entityInside`) during the
movements for which the effects of blocks were last applied (`Entity.Touch`). -/
def applyEffectsFromBlocksForLastMovements (k : Entity.Kind) (i : ℕ) : M Unit := do
  let some e ← getEntity i | return
  if e.phys.noPhysics then return
  let l ← get
  let effectPos := if e.base.onGround then some (Entity.getOnPosLegacy l e) else none
  Entity.Touch.applyEffectsFromBlocks k.dims i effectPos e.phys.finalMovementsThisTick

/-- `Entity.applyEffectsFromBlocks()` for the entity with index `i`: the effects of blocks are
applied for the movements the entity made since the last time. `old` is where the entity was
when its tick began (`Entity.oldPosition`). -/
def applyEffectsFromBlocks (k : Entity.Kind) (i : ℕ) (old : Vec3) : M Unit := do
  let some e ← getEntity i | return
  let final := Entity.Touch.finalMovements e.phys.movementThisTick old e.base.pos
  setEntity (e.modifyPhys fun p =>
    { p with movementThisTick := [], finalMovementsThisTick := final })
  applyEffectsFromBlocksForLastMovements k i

/-- The entity with index `i` touches a fluid, which the model does not handle: records it. -/
def checkNoFluid (k : Entity.Kind) (i : ℕ) : M Unit := do
  let some e ← getEntity i | return
  if (← get).touchesFluid (k.dims.box e.base.pos) then setOverflow

end Level

end Redstone
