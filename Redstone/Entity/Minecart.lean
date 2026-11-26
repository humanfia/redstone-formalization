module

public import Redstone.Mechanics.Tick
public import Redstone.Entity.Minecart.Tables

/-!
# Minecarts

Java classes: `AbstractMinecart`, `MinecartBehavior`, `OldMinecartBehavior`, `Minecart`,
`MinecartChest`, `MinecartHopper`, `MinecartTNT`, `MinecartFurnace`, `MinecartCommandBlock`,
`MinecartSpawner`, with the parts of `Entity` they use (`move`, `collide`, the supporting block,
the effects of blocks).

The server runs without the `minecart_improvements` feature flag, so every minecart has an
`OldMinecartBehavior`; `NewMinecartBehavior` is not formalized.

A minecart is moved once per game tick. On a rail it is snapped to the rail and moved along it
(`moveAlongTrack`): slopes accelerate it downhill, a powered rail that is on accelerates it, one
that is off brakes it, and an activator rail acts on its load. Off the rails it falls and slides
like any entity (`comeOffTrack`). All arithmetic is that of the game: `double` is `Float`,
`float` is `Float32`, and every expression is evaluated in the game's order, so positions and
velocities agree with the server bit for bit.

What is left out, and how. The model sets `Level.overflow`, which says that the level is no
longer a faithful image of the game, when it meets one of these:

* another entity within four blocks (minecarts push and block each other and pick up mobs, and
  a hopper minecart collects items);
* a fluid in or next to the minecart's box;
* a TNT minecart that explodes;
* a command block minecart with a command on an active activator rail;
* a hopper minecart that is enabled under a block with a block entity or a composter;
* a movement of a block or more per tick while falling (the game then traces a ray to reset
  the fall distance);
* landing with speed on a bouncy block (slime, beds, shelf mushrooms).

Left out silently: the hurt animation that an activator rail starts in a plain minecart, the
world border, portals, fire and freezing, blocks that slow an entity inside them (cobweb, sweet
berries, powder snow), and the collision shapes that depend on the entity (scaffolding, powder
snow) or on a block entity (shulker boxes, moving pistons). A shape of several boxes is treated
box by box, which differs from the game only for an entity that already overlaps the shape.

The helpers of the first sections (Java arithmetic, boxes, collision with block shapes, the
supporting block) are not particular to minecarts. They are private copies, to be shared with
the other entities once the common entity physics exists.
-/

@[expose] public section

namespace Redstone.Entity.Minecart

/-! ### Java arithmetic -/

/-- `Math.min` on `double`: `-0.0` is smaller than `0.0`, and a `NaN` argument gives `NaN`. -/
def jmin (a b : Float) : Float :=
  if a.isNaN then a
  else if a == 0 && b == 0 && b.toBits == 0x8000000000000000 then b
  else if a ≤ b then a else b

/-- `Math.max` on `double`. -/
def jmax (a b : Float) : Float :=
  if a.isNaN then a
  else if a == 0 && b == 0 && a.toBits == 0x8000000000000000 then b
  else if a ≥ b then a else b

/-- `Mth.clamp(value, min, max)` on `double`. -/
def clamp (v lo hi : Float) : Float := if v < lo then lo else jmin v hi

/-- `Mth.floor(double)`. -/
def floor (v : Float) : ℤ := v.floor.toInt64.toInt

/-- `Mth.equal(a, b)`: the two values differ by less than `1.0E-5F`. -/
def mthEqual (a b : Float) : Bool := (b - a).abs < (1.0E-5 : Float32).toFloat

/-- An integer as a `double`. -/
def ofInt (n : ℤ) : Float := Float.ofInt n

/-- `Math.PI`. -/
def pi : Float := Float.ofBits 0x400921FB54442D18

/-- `Math.PI / 2`. -/
def halfPi : Float := Float.ofBits 0x3FF921FB54442D18

/-- `Mth.fastInvSqrt(double)`. The argument is never negative here, so the arithmetic shift of
the game is a logical one. -/
def fastInvSqrt (x : Float) : Float :=
  let xhalf := 0.5 * x
  let i : UInt64 := (6910469410427058090 : UInt64) - (x.toBits >>> 1)
  let x := Float.ofBits i
  x * (1.5 - xhalf * x * x)

/-- `Mth.atan2(y, x)`: the game's table-based arc tangent. -/
def atan2 (y x : Float) : Float :=
  let d2 := x * x + y * y
  if d2.isNaN then d2
  else
    let negY := y < 0
    let y := if negY then -y else y
    let negX := x < 0
    let x := if negX then -x else x
    let steep := y > x
    let (x, y) := if steep then (y, x) else (x, y)
    let rinv := fastInvSqrt d2
    let x := x * rinv
    let y := y * rinv
    let fracBias := Float.ofBits 4805340802404319232
    let yp := fracBias + y
    let index := (yp.toBits.toNat % 2 ^ 32)
    let phi := Float.ofBits (Tables.asinBits.getD index 0)
    let cPhi := Float.ofBits (Tables.cosBits.getD index 0)
    let sPhi := yp - fracBias
    let sd := y * cPhi - x * sPhi
    let d := (6.0 + sd * sd) * sd * 0.16666666666666666
    let theta := phi + d
    let theta := if steep then halfPi - theta else theta
    let theta := if negX then pi - theta else theta
    if negY then -theta else theta

/-- `x % 360.0F` on `float`: the remainder has the sign of `x` and is exact. -/
def fmod360 (x : Float32) : Float32 :=
  let v := x.toFloat
  if v.isNaN || v.isInf then Float32.ofBits 0x7fc00000
  else
    let bits := v.toBits.toNat
    let e := (bits / 2 ^ 52) % 2048
    let m := bits % 2 ^ 52
    let mant := if e == 0 then m else m + 2 ^ 52
    let exp : ℤ := if e == 0 then -1074 else Int.ofNat e - 1075
    let r :=
      if exp ≥ 0 then (Float.ofNat ((mant * 2 ^ exp.toNat) % 360))
      else (Float.ofNat (mant % (360 * 2 ^ (-exp).toNat))).scaleB exp
    (if bits ≥ 2 ^ 63 then -r else r).toFloat32

/-- `Mth.wrapDegrees(float)`: the angle brought into `[-180, 180)`. -/
def wrapDegrees (angle : Float32) : Float32 :=
  let n := fmod360 angle
  let n := if n ≥ 180 then n - 360 else n
  if n < -180 then n + 360 else n

/-! ### Vectors -/

/-- `Vec3.add(x, y, z)`. -/
def vadd (v : Vec3) (x y z : Float) : Vec3 := ⟨v.x + x, v.y + y, v.z + z⟩

/-- `Vec3.multiply(x, y, z)`. -/
def vmul (v : Vec3) (x y z : Float) : Vec3 := ⟨v.x * x, v.y * y, v.z * z⟩

/-- `Vec3.scale(s)`. -/
def vscale (v : Vec3) (s : Float) : Vec3 := vmul v s s s

/-- `Vec3.horizontalDistanceSqr()`. -/
def hdistSqr (v : Vec3) : Float := v.x * v.x + v.z * v.z

/-- `Vec3.horizontalDistance()`. -/
def hdist (v : Vec3) : Float := (hdistSqr v).sqrt

/-- `Vec3.lengthSqr()`. -/
def lengthSqr (v : Vec3) : Float := v.x * v.x + v.y * v.y + v.z * v.z

/-- `Vec3.length()`. -/
def length (v : Vec3) : Float := (lengthSqr v).sqrt

/-- `Vec3.normalize()`. -/
def normalize (v : Vec3) : Vec3 :=
  let dist := length v
  if dist < (1.0E-5 : Float32).toFloat then ⟨0, 0, 0⟩ else ⟨v.x / dist, v.y / dist, v.z / dist⟩

/-- `BlockPos.containing(x, y, z)`. -/
def blockPosOf (v : Vec3) : Pos := ⟨floor v.x, floor v.y, floor v.z⟩

/-! ### Boxes and shapes -/

/-- An axis-aligned box (`AABB`). -/
structure AABB where
  minX : Float
  minY : Float
  minZ : Float
  maxX : Float
  maxY : Float
  maxZ : Float
  deriving Repr, Inhabited

/-- The three axes (`Direction.Axis`). -/
inductive Axis3
  | x
  | y
  | z
  deriving DecidableEq, Repr

namespace AABB

/-- `AABB.min(axis)`. -/
def lo (b : AABB) : Axis3 → Float
  | .x => b.minX
  | .y => b.minY
  | .z => b.minZ

/-- `AABB.max(axis)`. -/
def hi (b : AABB) : Axis3 → Float
  | .x => b.maxX
  | .y => b.maxY
  | .z => b.maxZ

/-- `AABB.move(x, y, z)`. -/
def move (b : AABB) (x y z : Float) : AABB :=
  ⟨b.minX + x, b.minY + y, b.minZ + z, b.maxX + x, b.maxY + y, b.maxZ + z⟩

/-- `AABB.inflate(x, y, z)`. -/
def inflate (b : AABB) (x y z : Float) : AABB :=
  ⟨b.minX - x, b.minY - y, b.minZ - z, b.maxX + x, b.maxY + y, b.maxZ + z⟩

/-- `AABB.expandTowards(x, y, z)`. -/
def expandTowards (b : AABB) (x y z : Float) : AABB :=
  { minX := if x < 0 then b.minX + x else b.minX
    maxX := if x < 0 then b.maxX else if x > 0 then b.maxX + x else b.maxX
    minY := if y < 0 then b.minY + y else b.minY
    maxY := if y < 0 then b.maxY else if y > 0 then b.maxY + y else b.maxY
    minZ := if z < 0 then b.minZ + z else b.minZ
    maxZ := if z < 0 then b.maxZ else if z > 0 then b.maxZ + z else b.maxZ }

/-- `AABB.intersects(AABB)`: the interiors meet. -/
def intersects (a b : AABB) : Bool :=
  a.minX < b.maxX && a.maxX > b.minX && a.minY < b.maxY && a.maxY > b.minY
    && a.minZ < b.maxZ && a.maxZ > b.minZ

/-- `AABB.contains(x, y, z)`. -/
def contains (b : AABB) (v : Vec3) : Bool :=
  v.x ≥ b.minX && v.x < b.maxX && v.y ≥ b.minY && v.y < b.maxY && v.z ≥ b.minZ && v.z < b.maxZ

/-- `AABB.getCenter()`. -/
def center (b : AABB) : Vec3 :=
  ⟨b.minX + 0.5 * (b.maxX - b.minX), b.minY + 0.5 * (b.maxY - b.minY),
    b.minZ + 0.5 * (b.maxZ - b.minZ)⟩

end AABB

/-- The server's shape table: the boxes of each shape. -/
def shapeTable : Array (List AABB) :=
  Tables.shapeBits.map fun boxes => boxes.filterMap fun
    | [a, b, c, d, e, f] =>
      some ⟨.ofBits a, .ofBits b, .ofBits c, .ofBits d, .ofBits e, .ofBits f⟩
    | _ => none

/-- The boxes of the shape with the given index, moved to the block at `p` (`VoxelShape.move`). -/
def shapeAt (index : ℕ) (p : Pos) : List AABB :=
  (shapeTable.getD index []).map (·.move (ofInt p.x) (ofInt p.y) (ofInt p.z))

/-- The collision shape of the block at `p`, as boxes in world coordinates. This is the shape
of the block state in an empty world; shapes that depend on the entity or on a block entity are
not modelled. -/
def collisionBoxes (l : Level) (p : Pos) : List AABB := shapeAt (l.blockAt p).attrs.collision p

/-- `BlockState.hasLargeCollisionShape`: the collision shape reaches outside the block. -/
def hasLargeCollisionShape (b : Block) : Bool :=
  (shapeTable.getD b.attrs.collision []).any fun s =>
    s.minX < 0 || s.minY < 0 || s.minZ < 0 || s.maxX > 1 || s.maxY > 1 || s.maxZ > 1

/-- The integers from `lo` to `hi`. -/
def intRange (lo hi : ℤ) : List ℤ := (List.range (hi - lo + 1).toNat).map (lo + ·)

/-- `BlockCollisions`: the blocks whose collision shape meets `box`, with their shapes, in the
order of the game's cursor (x fastest, then y, then z). Positions one block outside the box are
visited as well, for the shapes that reach outside their block; the world border and the
moving pistons are left out. -/
def blockCollisions (l : Level) (box : AABB) : List (Pos × List AABB) :=
  let x0 := floor (box.minX - 1.0E-7) - 1
  let x1 := floor (box.maxX + 1.0E-7) + 1
  let y0 := floor (box.minY - 1.0E-7) - 1
  let y1 := floor (box.maxY + 1.0E-7) + 1
  let z0 := floor (box.minZ - 1.0E-7) - 1
  let z1 := floor (box.maxZ + 1.0E-7) + 1
  (intRange z0 z1).flatMap fun z => (intRange y0 y1).flatMap fun y =>
    (intRange x0 x1).filterMap fun x =>
      let type := (if x == x0 || x == x1 then 1 else 0) + (if y == y0 || y == y1 then 1 else 0)
        + (if z == z0 || z == z1 then 1 else 0)
      let p : Pos := ⟨x, y, z⟩
      let b := l.blockAt p
      if type ≥ 2 || (type == 1 && !hasLargeCollisionShape b) then none
      else
        let boxes := collisionBoxes l p
        if boxes.any (·.intersects box) then some (p, boxes) else none

/-- `VoxelShape.collide(axis, moving, distance)` for a shape given by its boxes: how far `moving`
can travel along `axis` before it meets the shape, at most `distance`. Boxes that `moving`
already overlaps along `axis` do not stop it. -/
def collideShape (axis : Axis3) (moving : AABB) (boxes : List AABB) (distance : Float) : Float :=
  if boxes.isEmpty then distance
  else if distance.abs < 1.0E-7 then 0.0
  else
    let (b, c) : Axis3 × Axis3 :=
      match axis with
      | .x => (.y, .z)
      | .y => (.z, .x)
      | .z => (.x, .y)
    let beside := boxes.filter fun s =>
      s.lo b ≤ moving.hi b - 1.0E-7 && s.hi b > moving.lo b + 1.0E-7
        && s.lo c ≤ moving.hi c - 1.0E-7 && s.hi c > moving.lo c + 1.0E-7
    if distance > 0 then
      let maxA := moving.hi axis
      let ahead := (beside.filter fun s => !(s.lo axis ≤ maxA - 1.0E-7)).map (·.lo axis)
      match ahead with
      | [] => distance
      | f :: fs =>
        let newDistance := fs.foldl (fun m v => if v < m then v else m) f - maxA
        if newDistance ≥ -1.0E-7 then jmin distance newDistance else distance
    else
      let minA := moving.lo axis
      let behind := (beside.filter fun s => s.hi axis ≤ minA + 1.0E-7).map (·.hi axis)
      match behind with
      | [] => distance
      | f :: fs =>
        let newDistance := fs.foldl (fun m v => if v > m then v else m) f - minA
        if newDistance ≤ 1.0E-7 then jmax distance newDistance else distance

/-- `Shapes.collide(axis, moving, shapes, distance)`. -/
def collideShapes (axis : Axis3) (moving : AABB) (shapes : List (List AABB)) (distance : Float) :
    Float :=
  match shapes with
  | [] => distance
  | s :: rest =>
    if distance.abs < 1.0E-7 then 0.0
    else collideShapes axis moving rest (collideShape axis moving s distance)

/-- `Entity.collideBoundingBox` without entities: the part of `movement` that the box `aabb`
can make among the blocks. The vertical axis is resolved first, then the horizontal axis with
the larger movement (`Direction.axisStepOrder`). -/
def collideBoundingBox (l : Level) (aabb : AABB) (movement : Vec3) : Vec3 :=
  let shapes := (blockCollisions l (aabb.expandTowards movement.x movement.y movement.z)).map
    (·.2)
  if shapes.isEmpty then movement
  else
    let order : List Axis3 :=
      if movement.x.abs < movement.z.abs then [.y, .z, .x] else [.y, .x, .z]
    order.foldl (init := (⟨0, 0, 0⟩ : Vec3)) fun resolved axis =>
      let axisMovement :=
        match axis with
        | .x => movement.x
        | .y => movement.y
        | .z => movement.z
      if axisMovement != 0 then
        let collision := collideShapes axis (aabb.move resolved.x resolved.y resolved.z) shapes
          axisMovement
        match axis with
        | .x => { resolved with x := collision }
        | .y => { resolved with y := collision }
        | .z => { resolved with z := collision }
      else resolved

/-- `CollisionGetter.findSupportingBlock(entity, box)`: among the blocks whose collision shape
meets `box`, the one whose centre is nearest to `pos`; of two equally near, the greater in the
order of `Vec3i.compareTo` (y, then z, then x). -/
def findSupportingBlock (l : Level) (pos : Vec3) (box : AABB) : Option Pos :=
  let dist (p : Pos) : Float :=
    let dx := ofInt p.x + 0.5 - pos.x
    let dy := ofInt p.y + 0.5 - pos.y
    let dz := ofInt p.z + 0.5 - pos.z
    dx * dx + dy * dy + dz * dz
  let less (a b : Pos) : Bool :=
    a.y < b.y || (a.y == b.y && (a.z < b.z || (a.z == b.z && a.x < b.x)))
  ((blockCollisions l box).foldl (init := (none : Option (Pos × Float))) fun best (p, _) =>
    let d := dist p
    match best with
    | none => if d < Float.ofBits 0x7FEFFFFFFFFFFFFF then some (p, d) else none
    | some (q, e) => if d < e || (d == e && less q p) then some (p, d) else some (q, e)).map (·.1)

/-! ### Rails -/

/-- The shape of a rail (`RailShape`). -/
abbrev Shape := RailShape

/-- Widens the shape of a rail that cannot curve. -/
def Shape.ofStraight :
    RailShapeNorthSouthEastWestAscendingEastAscendingWestAscendingNorthAscendingSouth → Shape
  | .north_south => .north_south
  | .east_west => .east_west
  | .ascending_east => .ascending_east
  | .ascending_west => .ascending_west
  | .ascending_north => .ascending_north
  | .ascending_south => .ascending_south

/-- The shape of a rail block (`state.getValue(getShapeProperty())`), if the block is a rail
(`BaseRailBlock.isRail`). -/
def railShape? : Block → Option Shape
  | .rail s => some s.shape
  | .poweredRail _ s => some (.ofStraight s.shape)
  | .detectorRail s => some (.ofStraight s.shape)
  | _ => none

/-- `AbstractMinecart.exits(shape)`: the two ends of a rail, as offsets from its block. The end
of a slope that lies one block lower has `y = -1`. -/
def exits : Shape → (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)
  | .north_south => ((0, 0, -1), (0, 0, 1))
  | .east_west => ((-1, 0, 0), (1, 0, 0))
  | .ascending_east => ((-1, -1, 0), (1, 0, 0))
  | .ascending_west => ((-1, 0, 0), (1, -1, 0))
  | .ascending_north => ((0, 0, -1), (0, -1, 1))
  | .ascending_south => ((0, -1, -1), (0, 0, 1))
  | .south_east => ((0, 0, 1), (1, 0, 0))
  | .south_west => ((0, 0, 1), (-1, 0, 0))
  | .north_west => ((0, 0, -1), (-1, 0, 0))
  | .north_east => ((0, 0, -1), (1, 0, 0))

/-- `OldMinecartBehavior.getPos(x, y, z)`: the point of the rail under `(x, y, z)` that the
position projects to, or `none` when there is no rail there. Only its height is used. -/
def getPos (l : Level) (x y z : Float) : Option Vec3 :=
  let xt := floor x
  let yt := floor y
  let zt := floor z
  let yt := if (l.blockAt ⟨xt, yt - 1, zt⟩).isRail then yt - 1 else yt
  match railShape? (l.blockAt ⟨xt, yt, zt⟩) with
  | none => none
  | some shape =>
    let ((e0x, e0y, e0z), (e1x, e1y, e1z)) := exits shape
    let x0 := ofInt xt + 0.5 + ofInt e0x * 0.5
    let y0 := ofInt yt + 0.0625 + ofInt e0y * 0.5
    let z0 := ofInt zt + 0.5 + ofInt e0z * 0.5
    let x1 := ofInt xt + 0.5 + ofInt e1x * 0.5
    let y1 := ofInt yt + 0.0625 + ofInt e1y * 0.5
    let z1 := ofInt zt + 0.5 + ofInt e1z * 0.5
    let xD := x1 - x0
    let yD := (y1 - y0) * 2.0
    let zD := z1 - z0
    let progress :=
      if xD == 0.0 then z - ofInt zt
      else if zD == 0.0 then x - ofInt xt
      else
        let xx := x - x0
        let zz := z - z0
        (xx * xD + zz * zD) * 2.0
    let x := x0 + xD * progress
    let y := y0 + yD * progress
    let z := z0 + zD * progress
    let y := if yD < 0.0 then y + 1.0 else if yD > 0.0 then y + 0.5 else y
    some ⟨x, y, z⟩

/-! ### The minecart being ticked -/

/-- The state of the minecart while it is ticked. -/
structure Cart where
  /-- The index of the entity. -/
  index : ℕ
  /-- The kind of minecart. -/
  kind : MinecartKind
  /-- `Entity.position()`. -/
  pos : Vec3
  /-- `Entity.getDeltaMovement()`. -/
  motion : Vec3
  /-- `Entity.onGround()`. -/
  onGround : Bool
  /-- The rest of the state. -/
  d : Entities.Minecart
  /-- The entity is still in the level. -/
  alive : Bool

/-- The monad of a minecart's tick: the minecart over the level. -/
abbrev CartM := StateT Cart M

/-- The level, as the minecart sees it. -/
def level : CartM Level := getThe Level

/-- `Entity.getBoundingBox()`, which always is `EntityDimensions.makeBoundingBox(position)`: a
minecart is `0.98F` wide and `0.7F` high. -/
def boundingBox (pos : Vec3) : AABB :=
  let w := ((0.98 : Float32) / 2.0).toFloat
  let h := (0.7 : Float32).toFloat
  ⟨pos.x - w, pos.y, pos.z - w, pos.x + w, pos.y + h, pos.z + w⟩

/-- Writes the minecart back into the level. -/
def store : CartM Unit := do
  let c ← getThe Cart
  if c.alive then
    Level.modifyEntity c.index fun e =>
      { e with base := ⟨c.pos, c.motion, c.onGround⟩, data := .minecart c.kind c.d }

/-- Reads the minecart from the level; it may have been changed or removed meanwhile. -/
def reload : CartM Unit := do
  let c ← getThe Cart
  match (← level).entity? c.index with
  | some ⟨_, base, .minecart kind d⟩ =>
    set { c with kind, pos := base.pos, motion := base.motion, onGround := base.onGround, d }
  | _ => set { c with alive := false }

/-- Runs a reaction of the level, such as a block's `entityInside`, with the minecart in its
place in the level. -/
def withLevel (act : M Unit) : CartM Unit := do
  if (← getThe Cart).alive then
    store
    StateT.lift act
    reload

/-- Marks the level as no longer faithful: the minecart met something that is not modelled. -/
def unmodelled : CartM Unit := StateT.lift Level.setOverflow

/-- `Entity.setDeltaMovement`. -/
def setMotion (v : Vec3) : CartM Unit := modifyThe Cart fun c => { c with motion := v }

/-- `Entity.setPos`. -/
def setPos (v : Vec3) : CartM Unit := modifyThe Cart fun c => { c with pos := v }

/-- Changes the kind-specific data. -/
def modifyData (f : Entities.Minecart → Entities.Minecart) : CartM Unit :=
  modifyThe Cart fun c => { c with d := f c.d }

/-! ### The supporting block -/

/-- A fence, by its name (`BlockTags.FENCES`). -/
def isFence (b : Block) : Bool := b.id.name.endsWith "_fence"

/-- A wall, by its name (`BlockTags.WALLS`). -/
def isWall (b : Block) : Bool := b.id.name.endsWith "_wall"

/-- A fence gate, by its name (`FenceGateBlock`). -/
def isFenceGate (b : Block) : Bool := b.id.name.endsWith "_fence_gate"

/-- `Entity.getOnPos(offset)`: the block the entity stands on, or the one `offset` below its
feet. -/
def getOnPos (l : Level) (c : Cart) (offset : Float32) : Pos :=
  match c.d.supportingPos with
  | some p =>
    if !(offset > 1.0E-5) then p
    else
      let below := l.blockAt p
      if (!(offset.toFloat ≤ 0.5) || !isFence below) && !isWall below && !isFenceGate below then
        ⟨p.x, floor (c.pos.y - offset.toFloat), p.z⟩
      else p
  | none => ⟨floor c.pos.x, floor (c.pos.y - offset.toFloat), floor c.pos.z⟩

/-- `Entity.getOnPosLegacy()`. -/
def getOnPosLegacy (l : Level) (c : Cart) : Pos := getOnPos l c 0.2

/-- `Entity.checkSupportingBlock(onGround, movement)`. -/
def checkSupportingBlock (onGround : Bool) (movement : Option Vec3) : CartM Unit := do
  let c ← getThe Cart
  let l ← level
  if onGround then
    let bb := boundingBox c.pos
    let testArea : AABB := ⟨bb.minX, bb.minY - 1.0E-6, bb.minZ, bb.maxX, bb.minY, bb.maxZ⟩
    let found := findSupportingBlock l c.pos testArea
    if found.isSome || c.d.onGroundNoBlocks then
      modifyData fun d => { d with supportingPos := found, onGroundNoBlocks := found.isNone }
    else
      match movement with
      | some m =>
        let found := findSupportingBlock l c.pos (testArea.move (-m.x) 0.0 (-m.z))
        modifyData fun d => { d with supportingPos := found, onGroundNoBlocks := found.isNone }
      | none => modifyData fun d => { d with onGroundNoBlocks := found.isNone }
  else
    modifyData fun d => { d with onGroundNoBlocks := false, supportingPos := none }

/-! ### The effects of blocks -/

/-- `Block.getSpeedFactor()`. -/
def speedFactor (b : Block) : Float32 :=
  if b.id == .soul_sand || b.id == .honey_block then 0.4 else 1.0

/-- `Block.getBounceRestitution()` is not zero. -/
def isBouncy (b : Block) : Bool :=
  b.id == .slime_block || b.id == .shelf_mushroom || b.id.name.endsWith "_bed"

/-- `Entity.isStateClimbable`, for the blocks an entity can stand on. -/
def isClimbable (b : Block) : Bool :=
  b.id == .ladder || b.id == .scaffolding || b.id == .powder_snow

/-- `AbstractMinecart.getBlockSpeedFactor()`: rails never slow a minecart; otherwise the block
the minecart is in decides, or the block below it. -/
def blockSpeedFactor (l : Level) (c : Cart) : Float32 :=
  let here := l.blockAt (blockPosOf c.pos)
  if here.isRail then 1.0
  else
    let f := speedFactor here
    if f.toFloat == 1.0 then speedFactor (l.blockAt (getOnPos l c 0.500001)) else f

/-- The blocks whose `getEntityInsideCollisionShape` is not the full block and not modelled. -/
def insideShapeUnmodelled (b : Block) : Bool :=
  b.id == .water_cauldron || b.id == .powder_snow_cauldron || b.id == .lava_cauldron
    || b.id == .end_portal

/-- The test of `Entity.checkInsideBlocks` for a minecart that does not move during the test:
the minecart at `pos` is inside the block at `p`. Every block counts with its full cube, except
tripwire, which counts with its outline (`AABB.collidedAlongVector`). -/
def isInsideBlock (l : Level) (pos : Vec3) (p : Pos) : Bool :=
  let b := l.blockAt p
  if b.id == .tripwire then
    let bb := boundingBox pos
    let c := bb.center
    (shapeAt b.attrs.outline p).any fun part =>
      (part.inflate ((bb.maxX - bb.minX) * 0.5 - 1.0E-7) ((bb.maxY - bb.minY) * 0.5 - 1.0E-7)
        ((bb.maxZ - bb.minZ) * 0.5 - 1.0E-7)).contains c
  else !insideShapeUnmodelled b

/-- `AbstractMinecart.applyEffectsFromBlocks()` with the old behaviour, which is
`Entity.applyEffectsFromBlocks(position, position)`: the block under a minecart on the ground
is stepped on (`Block.stepOn`), and every block the minecart's box reaches is told that the
minecart is inside it (`BlockBehaviour.entityInside`), x fastest, then y, then z. -/
def applyEffectsFromBlocks : CartM Unit := do
  let c ← getThe Cart
  if !c.alive then return
  if c.onGround then
    let p := getOnPosLegacy (← level) c
    withLevel do (← Level.behaviour (← Level.getBlock p)).stepOn p c.index
  let c ← getThe Cart
  let v := (1.0E-5 : Float32).toFloat
  let box := (boundingBox c.pos).inflate (-v) (-v) (-v)
  let lo := blockPosOf ⟨box.minX, box.minY, box.minZ⟩
  let hi := blockPosOf ⟨box.maxX, box.maxY, box.maxZ⟩
  for z in intRange lo.z hi.z do
    for y in intRange lo.y hi.y do
      for x in intRange lo.x hi.x do
        let p : Pos := ⟨x, y, z⟩
        let l ← level
        let state := l.blockAt p
        if (← getThe Cart).alive && !state.isAir && isInsideBlock l c.pos p then
          withLevel do (← Level.behaviour state).entityInside p c.index

/-! ### Moving -/

/-- `MinecartTNT.explode`. Explosions are not modelled. -/
def explode : CartM Unit := unmodelled

/-- `Entity.checkFallDamage(ya, onGround, onState, pos)`: the fall distance grows while the
minecart falls and is reset when it lands. Landing announces `hit_ground`; a TNT minecart that
fell three blocks or more explodes (`MinecartTNT.causeFallDamage`); farmland draws from the
level's random generator before it finds that a minecart does not trample it. -/
def checkFallDamage (ya : Float) (onState : Block) : CartM Unit := do
  if ya < 0.0 then
    modifyData fun d => { d with fallDistance := d.fallDistance - ya.toFloat32.toFloat }
  let c ← getThe Cart
  if c.onGround then
    if c.d.fallDistance > 0.0 then
      if onState.id == .farmland then
        StateT.lift <| modify fun l => { l with random := l.random.nextFloat24.2 }
      if c.kind == .tnt then
        let special := isBouncy onState || onState.id == .hay_block || onState.id == .honey_block
          || onState.id == .powder_snow || onState.id == .pointed_dripstone
        if special || c.d.fallDistance ≥ 3.0 then explode
      withLevel (Level.gameEvent "minecraft:hit_ground" (blockPosOf c.pos))
    modifyData fun d => { d with fallDistance := 0.0 }

/-- `Entity.restituteMovementAfterCollisions`: the velocity is cancelled along the axes on which
the minecart hit something. A minecart has no bounciness of its own, so it only bounces off
bouncy blocks, which is not modelled. -/
def restituteMovementAfterCollisions (effectState : Block) (xCollision zCollision
    verticalCollision verticalCollisionBelow : Bool) : CartM Unit := do
  let c ← getThe Cart
  let restitution : Float := 0.0
  let current := c.motion
  let after := if xCollision then { current with x := -current.x * restitution } else current
  let after := if zCollision then { after with z := -current.z * restitution } else after
  if verticalCollision then
    if verticalCollisionBelow && !(-current.y ≤ 0.04) && effectState.id != .honey_block
        && isBouncy effectState then
      unmodelled
    setMotion { after with y := (0.0 - current.y) * 1.0 * restitution }
  else setMotion after

/-- `AbstractMinecart.getCurrentBlockPosOrRailBelow()`. -/
def currentBlockPosOrRailBelow (l : Level) (pos : Vec3) : Pos :=
  let p := blockPosOf pos
  if (l.blockAt ⟨p.x, p.y - 1, p.z⟩).isRail then ⟨p.x, p.y - 1, p.z⟩ else p

/-- `Entity.applyMovementEmissionAndPlaySound` for an entity that emits events only: the
distance covered is added up, and each time it passes the next whole number while the minecart
is on the ground or on rails, a `step` event is announced. -/
def applyMovementEmission (movement : Vec3) (effectPos : Pos) (effectState : Block)
    (onRails : Bool) : CartM Unit := do
  let c ← getThe Cart
  let l ← level
  let movedDistance := (length movement * (0.6 : Float32).toFloat).toFloat32
  let horizontalMovedDistance := (hdist movement * (0.6 : Float32).toFloat).toFloat32
  let supportingPos := getOnPos l c 1.0E-5
  let supportingState := l.blockAt supportingPos
  let moveDist := c.d.moveDist +
    (if isClimbable supportingState then movedDistance else horizontalMovedDistance)
  modifyData fun d => { d with moveDist }
  if moveDist > c.d.nextStep && !supportingState.isAir then
    -- Entity.vibrationAndSoundEffectsFromBlock
    let mayStep (b : Block) : Bool := !b.isAir && (c.onGround || isClimbable b || onRails)
    let onlyEffect := supportingPos == effectPos
    let mut produced := false
    if mayStep effectState then
      produced := true
      if onlyEffect then withLevel (Level.gameEvent "minecraft:step" (blockPosOf c.pos))
    if !onlyEffect && mayStep supportingState then
      produced := true
      withLevel (Level.gameEvent "minecraft:step" (blockPosOf c.pos))
    if produced then
      modifyData fun d =>
        { d with nextStep := (Float.ofInt (d.moveDist.toFloat.toInt64.toInt + 1)).toFloat32 }

/-- `AbstractMinecart.move(MoverType.SELF, delta)` with the old behaviour: `Entity.move`
followed by the effects of the blocks. `onRails` is `AbstractMinecart.isOnRails()`. -/
def move (delta : Vec3) (onRails : Bool) : CartM Unit := do
  let c ← getThe Cart
  let l ← level
  -- Entity.collide
  let movement :=
    if lengthSqr delta == 0.0 then delta else collideBoundingBox l (boundingBox c.pos) delta
  let movementLength := lengthSqr movement
  if movementLength > 1.0E-7 || lengthSqr delta - movementLength < 1.0E-7 then
    if c.d.fallDistance != 0.0 && movementLength ≥ 1.0 then unmodelled
    setPos (vadd c.pos movement.x movement.y movement.z)
  let xCollision := !mthEqual delta.x movement.x
  let zCollision := !mthEqual delta.z movement.z
  let horizontalCollision := xCollision || zCollision
  let movedVertically := delta.y.abs > 0.0
  let verticalCollision := delta.y != movement.y
  let verticalCollisionBelow := verticalCollision && delta.y < 0.0
  -- Entity.setOnGroundWithMovement
  modifyThe Cart fun c =>
    { c with onGround := verticalCollisionBelow, d := { c.d with horizontalCollision } }
  checkSupportingBlock verticalCollisionBelow (some movement)
  let c ← getThe Cart
  let effectPos := getOnPosLegacy l c
  let effectState := l.blockAt effectPos
  checkFallDamage movement.y effectState
  if (movedVertically && verticalCollision) || horizontalCollision then
    restituteMovementAfterCollisions effectState xCollision zCollision verticalCollision
      verticalCollisionBelow
  applyMovementEmission movement effectPos effectState onRails
  let c ← getThe Cart
  let f := (blockSpeedFactor (← level) c).toFloat
  setMotion (vmul c.motion f 1.0 f)
  applyEffectsFromBlocks

/-- `AbstractMinecart.getMaxSpeed`: `0.4` blocks per tick, half of it for a furnace minecart. -/
def maxSpeed (kind : MinecartKind) : Float := if kind == .furnace then 0.4 * 0.5 else 0.4

/-- `AbstractMinecart.comeOffTrack`: the movement of a minecart that is not on a rail. -/
def comeOffTrack : CartM Unit := do
  let c ← getThe Cart
  let max := maxSpeed c.kind
  let m := c.motion
  setMotion ⟨clamp m.x (-max) max, m.y, clamp m.z (-max) max⟩
  if c.onGround then setMotion (vscale (← getThe Cart).motion 0.5)
  move (← getThe Cart).motion false
  let c ← getThe Cart
  if !c.onGround then setMotion (vscale c.motion (0.95 : Float32).toFloat)

/-! ### The load -/

/-- `Container.getMaxStackSize(itemStack)`: the stack size of the item, at most 99. -/
def maxStackSize (item : String) : ℕ :=
  if Tables.maxStack1.contains item then 1 else if Tables.maxStack16.contains item then 16
  else 64

/-- `AbstractContainerMenu.getRedstoneSignalFromContainer` for the stacks of a minecart with
`size` slots. -/
def containerSignal (items : List (ℕ × String × ℕ)) (size : ℕ) : ℤ :=
  let filled := items.filter (fun (slot, _, count) => slot < size && count > 0)
  let sorted := filled.mergeSort (fun a b => a.1 ≤ b.1)
  let total : Float32 := sorted.foldl (init := 0) fun t (_, item, count) =>
    t + (Float.ofNat count).toFloat32 / (Float.ofNat (maxStackSize item)).toFloat32
  let total := total / (Float.ofNat size).toFloat32
  floor (total * 14).toFloat + (if total > 0 then 1 else 0)

/-- The number of slots of a minecart with a container (`getContainerSize`). -/
def containerSize : MinecartKind → Option ℕ
  | .chest => some 27
  | .hopper => some 5
  | _ => none

/-- `applyNaturalSlowdown(movement)`: the friction of the rail. A plain minecart keeps `0.96`
of its speed; a minecart with a container keeps more the emptier it is
(`AbstractMinecartContainer`); a furnace minecart is driven by its push (`MinecartFurnace`).
The vertical velocity is cleared. -/
def applyNaturalSlowdown (movement : Vec3) : CartM Vec3 := do
  let c ← getThe Cart
  match containerSize c.kind with
  | some size =>
    let keep : Float32 := 0.98
    let keep :=
      if c.d.hasLootTable then keep
      else
        let emptiness := 15 - containerSignal c.d.items size
        keep + (Float.ofInt emptiness).toFloat32 * 0.001
    return vmul movement keep.toFloat 0.0 keep.toFloat
  | none =>
    let movement ←
      if c.kind == .furnace then do
        let push : Vec3 := ⟨c.d.pushX, c.d.pushY, c.d.pushZ⟩
        if lengthSqr push > 1.0E-7 then
          -- MinecartFurnace.calculateNewPushAlong
          let push :=
            if hdistSqr push > 1.0E-4 && hdistSqr movement > 0.001 then
              let projected :=
                if lengthSqr movement == 0.0 then movement
                else
                  let dot := push.x * movement.x + push.y * movement.y + push.z * movement.z
                  vscale (vscale movement dot) (1.0 / lengthSqr movement)
              vscale (normalize projected) (length push)
            else push
          modifyData fun d => { d with pushX := push.x, pushY := push.y, pushZ := push.z }
          pure (vadd (vmul movement 0.8 0.0 0.8) push.x push.y push.z)
        else pure (vmul movement 0.98 0.0 0.98)
      else pure movement
    return vmul movement 0.96 0.0 0.96

/-- `activateMinecart(level, x, y, z, state)`: what an activator rail does to the minecart
standing on it. An active rail primes a TNT minecart and disables a hopper minecart, an inactive
one enables it again. In a plain minecart an active rail starts the hurt animation, which is not
kept; in a command block minecart it runs the command, which is not modelled. -/
def activateMinecart (powered : Bool) : CartM Unit := do
  let c ← getThe Cart
  match c.kind with
  | .tnt => if powered && c.d.fuse < 0 then modifyData fun d => { d with fuse := 80 }
  | .hopper => modifyData fun d => { d with enabled := !powered }
  | .commandBlock => if powered && c.d.command != "" then unmodelled
  | _ => pure ()

/-! ### Moving along rails -/

/-- `OldMinecartBehavior.moveAlongTrack`: the movement of a minecart on the rail at `pos`,
whose shape is `shape`. -/
def moveAlongTrack (pos : Pos) (state : Block) (shape : Shape) : CartM Unit := do
  let l ← level
  modifyData fun d => { d with fallDistance := 0.0 }
  let c ← getThe Cart
  let x := c.pos.x
  let z := c.pos.z
  let oldPos := getPos l x c.pos.y z
  let y := ofInt pos.y
  let powerTrack :=
    match state with
    | .poweredRail .powered_rail s => s.powered
    | _ => false
  let haltTrack :=
    match state with
    | .poweredRail .powered_rail s => !s.powered
    | _ => false
  let slideSpeed : Float := 0.0078125
  let movement := c.motion
  let (movement, y) :=
    match shape with
    | .ascending_east => (vadd movement (-slideSpeed) 0.0 0.0, y + 1.0)
    | .ascending_west => (vadd movement slideSpeed 0.0 0.0, y + 1.0)
    | .ascending_north => (vadd movement 0.0 0.0 slideSpeed, y + 1.0)
    | .ascending_south => (vadd movement 0.0 0.0 (-slideSpeed), y + 1.0)
    | _ => (movement, y)
  let ((e0x, e0y, e0z), (e1x, e1y, e1z)) := exits shape
  let xD := ofInt (e1x - e0x)
  let zD := ofInt (e1z - e0z)
  let length := (xD * xD + zD * zD).sqrt
  let flip := movement.x * xD + movement.z * zD
  let (xD, zD) := if flip < 0.0 then (-xD, -zD) else (xD, zD)
  let pow := jmin 2.0 (hdist movement)
  let movement : Vec3 := ⟨pow * xD / length, movement.y, pow * zD / length⟩
  let movement :=
    if haltTrack then
      if hdist movement < 0.03 then ⟨0.0, 0.0, 0.0⟩ else vmul movement 0.5 0.0 0.5
    else movement
  setMotion movement
  let x0 := ofInt pos.x + 0.5 + ofInt e0x * 0.5
  let z0 := ofInt pos.z + 0.5 + ofInt e0z * 0.5
  let x1 := ofInt pos.x + 0.5 + ofInt e1x * 0.5
  let z1 := ofInt pos.z + 0.5 + ofInt e1z * 0.5
  let xD := x1 - x0
  let zD := z1 - z0
  let progress :=
    if xD == 0.0 then z - ofInt pos.z
    else if zD == 0.0 then x - ofInt pos.x
    else
      let xx := x - x0
      let zz := z - z0
      (xx * xD + zz * zD) * 2.0
  let x := x0 + xD * progress
  let z := z0 + zD * progress
  setPos ⟨x, y, z⟩
  let max := maxSpeed c.kind
  move ⟨clamp (1.0 * movement.x) (-max) max, 0.0, clamp (1.0 * movement.z) (-max) max⟩ true
  let c ← getThe Cart
  let fx := floor c.pos.x - pos.x
  let fz := floor c.pos.z - pos.z
  if e0y != 0 && fx == e0x && fz == e0z then
    setPos ⟨c.pos.x, c.pos.y + ofInt e0y, c.pos.z⟩
  else if e1y != 0 && fx == e1x && fz == e1z then
    setPos ⟨c.pos.x, c.pos.y + ofInt e1y, c.pos.z⟩
  setMotion (← applyNaturalSlowdown (← getThe Cart).motion)
  let c ← getThe Cart
  match getPos (← level) c.pos.x c.pos.y c.pos.z, oldPos with
  | some newPos, some oldPos =>
    let speed := (oldPos.y - newPos.y) * 0.05
    let otherPow := hdist c.motion
    if otherPow > 0.0 then
      setMotion (vmul c.motion ((otherPow + speed) / otherPow) 1.0 ((otherPow + speed) / otherPow))
    setPos ⟨c.pos.x, newPos.y, c.pos.z⟩
  | _, _ => pure ()
  let c ← getThe Cart
  let xn := floor c.pos.x
  let zn := floor c.pos.z
  if xn != pos.x || zn != pos.z then
    let otherPow := hdist c.motion
    setMotion ⟨otherPow * ofInt (xn - pos.x), c.motion.y, otherPow * ofInt (zn - pos.z)⟩
  if powerTrack then
    let c ← getThe Cart
    let v := c.motion
    let speedLength := hdist v
    if speedLength > 0.01 then
      setMotion (vadd v (v.x / speedLength * 0.06) 0.0 (v.z / speedLength * 0.06))
    else
      let l ← level
      let conductor (d : Direction) : Bool := (l.blockAt (pos.step d)).isConductor
      match shape with
      | .east_west =>
        let dx := if conductor .west then 0.02 else if conductor .east then -0.02 else v.x
        setMotion ⟨dx, v.y, v.z⟩
      | .north_south =>
        let dz := if conductor .north then 0.02 else if conductor .south then -0.02 else v.z
        setMotion ⟨v.x, v.y, dz⟩
      | _ => pure ()

/-! ### The tick -/

/-- The model's check for what it leaves out around the minecart: another entity within four
blocks, or a fluid in or next to the minecart's box. -/
def checkSurroundings : CartM Unit := do
  let c ← getThe Cart
  let l ← level
  let near (e : Entity) : Bool :=
    e.index != c.index && (e.base.pos.x - c.pos.x).abs < 4.0 && (e.base.pos.y - c.pos.y).abs < 4.0
      && (e.base.pos.z - c.pos.z).abs < 4.0
  if l.entities.any near then unmodelled
  let bb := boundingBox c.pos
  let lo := blockPosOf ⟨bb.minX, bb.minY, bb.minZ⟩
  let hi := blockPosOf ⟨bb.maxX, bb.maxY, bb.maxZ⟩
  let wet := (intRange (lo.x - 1) (hi.x + 1)).any fun x => (intRange (lo.y - 1) (hi.y + 1)).any
    fun y => (intRange (lo.z - 1) (hi.z + 1)).any fun z => (l.blockAt ⟨x, y, z⟩).attrs.fluid != ""
  if wet then unmodelled

/-- `OldMinecartBehavior.tick` on the server. `old` and `yRotO` are the position and the yaw
before the tick (`Entity.xo`, `zo`, `yRotO`). -/
def behaviorTick (old : Vec3) (yRotO : Float32) : CartM Unit := do
  -- Entity.applyGravity
  setMotion (vadd (← getThe Cart).motion 0.0 (-0.04) 0.0)
  let c ← getThe Cart
  let l ← level
  let pos := currentBlockPosOrRailBelow l c.pos
  let state := l.blockAt pos
  match railShape? state with
  | some shape =>
    moveAlongTrack pos state shape
    match state with
    | .poweredRail .activator_rail s => activateMinecart s.powered
    | _ => pure ()
  | none => comeOffTrack
  applyEffectsFromBlocks
  modifyData fun d => { d with xRot := 0.0 }
  let c ← getThe Cart
  let xDiff := old.x - c.pos.x
  let zDiff := old.z - c.pos.z
  if xDiff * xDiff + zDiff * zDiff > 0.001 then
    let yRot := (atan2 zDiff xDiff * 180.0 / pi).toFloat32
    modifyData fun d => { d with yRot := if d.flipped then yRot + 180.0 else yRot }
  let c ← getThe Cart
  let rotDiff := (wrapDegrees (c.d.yRot - yRotO)).toFloat
  if rotDiff < -170.0 || rotDiff ≥ 170.0 then
    modifyData fun d => { d with yRot := d.yRot + 180.0, flipped := !d.flipped }
  modifyData fun d => { d with xRot := fmod360 d.xRot, yRot := fmod360 d.yRot }

/-- What the subclasses add to `tick()` after `AbstractMinecart.tick()`: the fuse of a TNT
minecart burns down and the minecart explodes when it runs out or when the minecart runs into
something (`MinecartTNT`); a furnace minecart burns its fuel and loses its push when the fuel
is gone (`MinecartFurnace`); a hopper minecart that is enabled looks for items (`MinecartHopper`),
which is modelled only when there is nothing to find. -/
def kindTick : CartM Unit := do
  let c ← getThe Cart
  match c.kind with
  | .tnt =>
    if c.d.fuse > 0 then modifyData fun d => { d with fuse := d.fuse - 1 }
    else if c.d.fuse == 0 then explode
    if c.d.horizontalCollision && hdistSqr c.motion ≥ (0.01 : Float32).toFloat then explode
  | .furnace =>
    if c.d.fuel > 0 then modifyData fun d => { d with fuel := d.fuel - 1 }
    if (← getThe Cart).d.fuel ≤ 0 then
      modifyData fun d => { d with pushX := 0.0, pushY := 0.0, pushZ := 0.0 }
  | .hopper =>
    if c.d.enabled then
      let above := (← level).blockAt (blockPosOf ⟨c.pos.x, c.pos.y + 0.5 + 1.0, c.pos.z⟩)
      if above.hasBlockEntity || above.id == .composter then unmodelled
  | _ => pure ()

/-- `tick()` of a minecart: `Entity.commonTick`, `AbstractMinecart.tick` and the additions of
the subclasses. A minecart that fell 64 blocks below the world is removed
(`Entity.checkBelowWorld`). -/
def cartTick : CartM Unit := do
  let c ← getThe Cart
  let old := c.pos
  let yRotO := c.d.yRot
  if c.pos.y < -128.0 then
    StateT.lift (Level.removeEntity c.index)
    modifyThe Cart fun c => { c with alive := false }
    return
  checkSurroundings
  behaviorTick old yRotO
  checkSurroundings
  kindTick
  store

/-- `tick()`: what the minecart with the given index does in a game tick. -/
def tick (index : ℕ) : M Unit := do
  match (← get).entity? index with
  | some ⟨_, base, .minecart kind d⟩ =>
    discard <| cartTick.run ⟨index, kind, base.pos, base.motion, base.onGround, d, true⟩
  | _ => pure ()

/-- The behaviour of the entity. -/
def behaviour : EntityBehaviour := ⟨tick⟩

end Redstone.Entity.Minecart
