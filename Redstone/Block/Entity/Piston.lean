module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

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

end Piston

end Redstone.BlockEntities
