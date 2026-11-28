module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.Attrs
public import Redstone.Block.FaceShape

/-!
# Block entity `minecraft:piston`

The data that the model keeps of the block entity `PistonMovingBlockEntity`: a block that a
piston is moving, or the head or base of the piston itself while it moves.

## Progress and what is saved

The game keeps two progress values: `progress`, and `progressO`, the progress before the last
tick. Only `progressO` is saved (under the name `progress`), so the saved data does not
determine `progress`. `ofNbt?` reads the saved data of a block entity that **has been ticked
since `progressO` was set**, that is, `progress = min (progressO + 1/2) 1`. This is the state of
every moving block at the end of a game tick, which is when traces are taken: a moving block is
created by a block event and ticked in the same game tick. It is not what the game does when it
loads a chunk (`loadAdditional` sets `progress = progressO`); loading is not modelled, and the
harness cannot place a moving block with data (`MovingPistonBlock.newBlockEntity` is null).

Progress is a rational number. The game uses 32-bit floats, but the values a piston produces
are 0, 1/2 and 1, on which float arithmetic is exact.

`lastTicked` is not kept here either, for the same reason: `Level.tickedBlockEntities` stands
for it. The client-only `deathTicks` is left out.

## The shape of a moving block

The collision shape of a `moving_piston` comes from its block entity (`getCollisionShape`): the
shape of the moved block, displaced by what is left of its way, and for the base of a
retracting piston the extended base with the head that moves back into it. This shape is also
the shape that decides what the block supports (`getBlockSupportShape`). `collisionFaceShape`
gives it in exact arithmetic and `supportMasksOfShape` reads the faces off it; `supportMasks`
is what `Level.supportAttrs` uses: the same answer, given directly for a piston's own head and
base and for a moved full cube, so that the common cases cost nothing to evaluate. The checks
at the end of the file compare the two for every direction and every progress.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:piston` block entity (`PistonMovingBlockEntity`). The defaults are
the field initialisers of the Java class, with `direction` as `loadAdditional` defaults it. -/
structure Piston where
  /-- `movedState`: the block being moved; for a source piston, the head (extending) or the
  base (retracting). -/
  movedState : Block := Block.default .air
  /-- `direction`: the facing of the piston that moves the block. -/
  direction : Direction := .down
  /-- `extending`: the piston is extending. -/
  extending : Bool := false
  /-- `isSourcePiston`: this is the piston's own head or base. -/
  isSourcePiston : Bool := false
  /-- `progress`: how far the block has moved, from 0 to 1. -/
  progress : ℚ := 0
  /-- `progressO`: `progress` before the last tick. This is the value that is saved. -/
  progressO : ℚ := 0
  deriving DecidableEq, Repr

namespace Piston

instance : Inhabited Piston := ⟨{}⟩

/-- `PistonMovingBlockEntity.getMovementDirection()`, which is also `getPushDirection()`: the
direction in which the block moves. -/
def movementDirection (d : Piston) : Direction :=
  if d.extending then d.direction else d.direction.opposite

/-- `PistonMovingBlockEntity.getCollisionShape(level, pos)` while no piston is moving an entity
(`NOCLIP` is not set), relative to the position of the block entity, in exact arithmetic. The
grid of the shape is made by the faces of its boxes; the game rebuilds the grid from the merged
boxes (`VoxelShape.optimize`), which gives the same faces. -/
def collisionFaceShape (d : Piston) : FaceShape :=
  let boxesOf (b : Block) : List RatBox := (FaceShape.ofIndex b.attrs.collision).boxes
  let pistonHeadShape : List RatBox :=
    match d.movedState with
    | .pistonBase id s =>
      if !d.extending && d.isSourcePiston then
        boxesOf (.pistonBase id { s with extended := true })
      else []
    | _ => []
  let blockState : Block :=
    if d.isSourcePiston then
      .pistonHead ⟨d.direction, d.extending != decide (1 - d.progress < 1 / 4), .normal⟩
    else d.movedState
  let extendedProgress : ℚ := if d.extending then d.progress - 1 else 1 - d.progress
  let move (b : RatBox) : RatBox :=
    match d.direction with
    | .down => { b with minY := b.minY - extendedProgress, maxY := b.maxY - extendedProgress }
    | .up => { b with minY := b.minY + extendedProgress, maxY := b.maxY + extendedProgress }
    | .north => { b with minZ := b.minZ - extendedProgress, maxZ := b.maxZ - extendedProgress }
    | .south => { b with minZ := b.minZ + extendedProgress, maxZ := b.maxZ + extendedProgress }
    | .west => { b with minX := b.minX - extendedProgress, maxX := b.maxX - extendedProgress }
    | .east => { b with minX := b.minX + extendedProgress, maxX := b.maxX + extendedProgress }
  FaceShape.ofBoxes (pistonHeadShape ++ (boxesOf blockState).map move)

/-- The faces of a block with the support shape `s` that are sturdy, as the masks
`Attrs.sturdyFull`, `Attrs.sturdyCenter` and `Attrs.sturdyRigid` (`SupportType.isSupporting`):
the face shape is the full square, or covers `CENTER_SUPPORT_SHAPE` (the column
`Block.column(2, 0, 10)`), or covers `RIGID_SUPPORT_SHAPE` (the cube without the column
`Block.column(12, 0, 16)`). -/
def supportMasksOfShape (s : FaceShape) : ℕ × ℕ × ℕ :=
  let center := FaceShape.ofBoxes [RatBox.ofPixels 7 0 7 9 10 9]
  let rigid := FaceShape.ofBoxes [RatBox.ofPixels 0 0 0 2 16 16, RatBox.ofPixels 14 0 0 16 16 16,
    RatBox.ofPixels 0 0 0 16 16 2, RatBox.ofPixels 0 0 14 16 16 16]
  let mask (test : FaceShape → Bool) : ℕ :=
    Direction.values.foldl
      (fun m dir => if test (s.faceShape dir) then m ||| (1 <<< dir.bit) else m) 0
  (mask FaceShape.isFullBlock, mask (FaceShape.subset center), mask (FaceShape.subset rigid))

/-- The mask of a single face, or no face. -/
def faceMask (cond : Bool) (dir : Direction) : ℕ := if cond then 1 <<< dir.bit else 0

/-- The faces of the `moving_piston` with this block entity that are sturdy
(`BlockState.isFaceSturdy`, which reads the collision shape of the block entity), as the masks
`Attrs.sturdyFull`, `Attrs.sturdyCenter` and `Attrs.sturdyRigid`. It is
`supportMasksOfShape d.collisionFaceShape`, written out for the cases that are common:

* the base of a retracting piston: on its way, it supports what the extended base supports,
  and the arm of the head that moves in supports the centre of the front face of a vertical
  piston; once the head is in (`progress` is 1) the shape is the full cube;
* the head of an extending piston: at the start it is outside its block; half way, its arm
  supports the centre of the back face of a vertical piston; arrived, it is the head;
* a moved block that is a full cube: at the start it is outside its block, half way it covers
  the face it comes from, and arrived it is the cube.

Any other moved block goes through the general computation. -/
def supportMasks (d : Piston) : ℕ × ℕ × ℕ :=
  let general (_ : Unit) := supportMasksOfShape d.collisionFaceShape
  let vertical := d.direction = .up || d.direction = .down
  if d.isSourcePiston then
    match d.movedState with
    | .pistonBase id s =>
      if d.extending || s.facing ≠ d.direction then general ()
      else if d.progress = 1 then (63, 63, 63)
      else if d.progress = 0 || d.progress = 1 / 2 then
        let a := (Block.pistonBase id { s with extended := true }).attrs
        (a.sturdyFull, a.sturdyCenter ||| faceMask vertical d.direction, a.sturdyRigid)
      else general ()
    | .pistonHead h =>
      if !d.extending || h.facing ≠ d.direction then general ()
      else if d.progress = 1 then
        let a := (Block.pistonHead ⟨d.direction, false, .normal⟩).attrs
        (a.sturdyFull, a.sturdyCenter, a.sturdyRigid)
      else if d.progress = 1 / 2 then (0, faceMask vertical d.direction.opposite, 0)
      else if d.progress = 0 then (0, 0, 0)
      else general ()
    | _ => general ()
  else if d.movedState.attrs.collision = 1 then
    if d.progress = 1 then (63, 63, 63)
    else if d.progress = 1 / 2 then
      let m := faceMask true d.movementDirection.opposite
      (m, m, m)
    else if d.progress = 0 then (0, 0, 0)
    else general ()
  else general ()

/-- `Direction.from3DDataValue(data)`. -/
def from3DDataValue (data : ℤ) : Direction :=
  match (data.tmod 6).natAbs with
  | 0 => .down
  | 1 => .up
  | 2 => .north
  | 3 => .south
  | 4 => .west
  | _ => .east

/-- `Direction.get3DDataValue()`. -/
def get3DDataValue (d : Direction) : ℤ := d.bit

/-- The value of a finite 32-bit float given by its IEEE bits. Infinities and NaNs are read as
if their exponent were an ordinary one. -/
def ofFloatBits (bits : ℕ) : ℚ :=
  let sign : ℚ := if bits.testBit 31 then -1 else 1
  let exp := (bits >>> 23) &&& 0xff
  let mant := bits &&& 0x7fffff
  if exp = 0 then sign * mant / 2 ^ 149
  else sign * (mant + 2 ^ 23) * 2 ^ exp / 2 ^ 150

/-- Reads a block state as `BlockState.CODEC` of 26.3 writes it: the block's name alone for the
block's default state, and otherwise a compound with `id` and `properties`. A property that is
not given has the value of the default state. (`BlockId.ofName?` is defined downstream of this
file.) -/
def blockOfNbt? (t : Nbt) : Option Block :=
  let blockOf (name : String) : Option BlockId := BlockId.all.find? (·.name == name)
  match t with
  | .string name => Block.default <$> blockOf name
  | _ => do
    let id ← ((t.get? "id").bind Nbt.toString?).bind blockOf
    let default := (Block.default id).toProps
    let props := t.get? "properties"
    Block.ofProps? id fun k =>
      ((props.bind (·.get? k)).bind Nbt.toString?).orElse fun _ =>
        (default.find? (·.1 == k)).map (·.2)

/-- Reads the data from the block entity's saved NBT (`loadAdditional`), as the data of a block
entity that was ticked after `progressO` was set; see the module docstring. -/
def ofNbt? (t : Nbt) : Option Piston :=
  let progressO : ℚ :=
    match t.get? "progress" with
    | some (.float bits) => ofFloatBits bits
    | _ => 0
  some
    { movedState := ((t.get? "blockState").bind blockOfNbt?).getD (Block.default .air)
      direction := from3DDataValue (t.intD "facing" 0)
      extending := t.boolD "extending" false
      isSourcePiston := t.boolD "source" false
      progress := min (progressO + 1 / 2) 1
      progressO := progressO }

/-! ### `supportMasks` is the general computation -/

/-- The block entities of a piston's own head and base and of a moved full cube, for every
direction and every progress a piston produces. -/
def supportMaskCases : List Piston :=
  Direction.values.flatMap fun direction =>
    [(0 : ℚ), 1 / 2, 1].flatMap fun progress =>
      [Blocks.PistonBase.Id.piston, .sticky_piston].flatMap fun id =>
        let type : PistonType :=
          match id with
          | .sticky_piston => .sticky
          | .piston => .normal
        [{ movedState := .pistonBase id ⟨false, direction⟩, direction, extending := false
           isSourcePiston := true, progress },
         { movedState := .pistonHead ⟨direction, false, type⟩, direction, extending := true
           isSourcePiston := true, progress },
         { movedState := Block.default .stone, direction, extending := true, progress },
         { movedState := Block.default .stone, direction, extending := false, progress }]

/-- On a piston's own head and base and on a moved full cube, `supportMasks` is the general
computation on the collision shape of the block entity. -/
theorem supportMasks_eq_general :
    (supportMaskCases.all fun d => d.supportMasks == supportMasksOfShape d.collisionFaceShape) =
      true := by
  decide +kernel

end Piston

end Redstone.BlockEntities
