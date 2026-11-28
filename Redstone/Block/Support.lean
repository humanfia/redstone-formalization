module

public import Redstone.Basic.Direction

/-!
# Support for the generated block inventory

The types the generated files under `Redstone.Block.Generated` are written in terms of:
integer ranges for integer properties, the piston push reactions, and the record of
attributes the server reports for each block state.
-/

@[expose] public section

namespace Redstone

/-- An integer property whose values run from `lo` to `hi`, where `lo` is not zero. Properties
that start at zero use `Fin` instead. -/
structure IntRange (lo hi : ℕ) where
  /-- The value, as written in the block state. -/
  val : ℕ
  lo_le : lo ≤ val
  le_hi : val ≤ hi
  deriving DecidableEq, Repr

namespace IntRange

/-- The value `n`, if it lies in the range. -/
def ofNat? (lo hi n : ℕ) : Option (IntRange lo hi) :=
  if h : lo ≤ n ∧ n ≤ hi then some ⟨n, h.1, h.2⟩ else none

/-- Reads a value written in decimal. -/
def parse? (lo hi : ℕ) (s : String) : Option (IntRange lo hi) := s.toNat? >>= ofNat? lo hi

end IntRange

/-- Reads `true` or `false`. -/
def parseBool? : String → Option Bool
  | "true" => some true
  | "false" => some false
  | _ => none

/-- Reads a number below `n` written in decimal. -/
def parseFin? (n : ℕ) (s : String) : Option (Fin n) :=
  s.toNat? >>= fun k => if h : k < n then some ⟨k, h⟩ else none

/-- How a block reacts to being pushed by a piston (`PushReaction`). -/
inductive PushReaction
  /-- Can be pushed and pulled. -/
  | push_pull
  /-- Can be pushed but not pulled. -/
  | push
  /-- Is broken when a piston pushes it. -/
  | popped
  /-- Cannot be moved. -/
  | immoveable
  /-- Used by entities that pistons do not move. -/
  | ignore_entity
  deriving DecidableEq, Repr

/-- Bit of a direction in the face masks of `Attrs`: down, up, north, south, west, east. -/
def Direction.bit : Direction → ℕ
  | .down => 0
  | .up => 1
  | .north => 2
  | .south => 3
  | .west => 4
  | .east => 5

/-- The attributes of a block state that do not depend on its surroundings, as reported by the
server for the state placed in an empty world. -/
structure Attrs where
  /-- `BlockState.isAir`. -/
  air : Bool
  /-- `BlockState.isRedstoneConductor`: the block passes on the power it receives. -/
  conductor : Bool
  /-- `BlockState.isSolid`. -/
  solid : Bool
  /-- `BlockState.isSolidRender`. -/
  solidRender : Bool
  /-- `BlockState.canBeReplaced`. -/
  replaceable : Bool
  /-- `BlockState.isSignalSource`. -/
  signalSource : Bool
  /-- `BlockState.hasAnalogOutputSignal`: comparators can read the block. -/
  analog : Bool
  /-- `BlockState.isRandomlyTicking`. -/
  randomlyTicks : Bool
  /-- `BlockState.hasBlockEntity`. -/
  hasBlockEntity : Bool
  /-- `BlockState.getPistonPushReaction`. -/
  push : PushReaction
  /-- The bits of the `float` `BlockState.getDestroySpeed`; `-1.0` means unbreakable. -/
  destroySpeedBits : ℕ
  /-- `BlockState.getLightEmission`. -/
  light : ℕ
  /-- Faces that are sturdy with `SupportType.FULL`, as a mask of `Direction.bit`. -/
  sturdyFull : ℕ
  /-- Faces that are sturdy with `SupportType.CENTER`. -/
  sturdyCenter : ℕ
  /-- Faces that are sturdy with `SupportType.RIGID`. -/
  sturdyRigid : ℕ
  /-- The block state of the fluid the block holds (`getFluidState().createLegacyBlock()`),
  written as a string; empty when there is no fluid. -/
  fluid : String
  /-- Index of the collision shape in the dump's shape table. -/
  collision : ℕ
  /-- Index of the outline shape. -/
  outline : ℕ
  /-- Index of the support shape. -/
  supportShape : ℕ
  /-- `BlockState.getLightDampening`: how much light loses on entering the block, from 0 to 15. -/
  lightDampening : ℕ
  /-- Index of the shape with which the block occludes light at its faces
  (`LightEngine.getOcclusionShape`): `BlockState.getOcclusionShape` for a state that occludes
  and uses its shape for light occlusion (`canOcclude`, `useShapeForLightOcclusion`), the empty
  shape for every other state. -/
  lightOcclusion : ℕ
  deriving DecidableEq, Repr

namespace Attrs

/-- `BlockState.isFaceSturdy(level, pos, d)`: the face `d` can support a block attached to it. -/
def isFaceSturdy (a : Attrs) (d : Direction) : Bool := a.sturdyFull.testBit d.bit

/-- `isFaceSturdy` with `SupportType.CENTER`. -/
def isFaceSturdyCenter (a : Attrs) (d : Direction) : Bool := a.sturdyCenter.testBit d.bit

/-- `isFaceSturdy` with `SupportType.RIGID`. -/
def isFaceSturdyRigid (a : Attrs) (d : Direction) : Bool := a.sturdyRigid.testBit d.bit

/-- The block cannot be broken (destroy speed `-1.0`), which also stops pistons. -/
def unbreakable (a : Attrs) : Bool := a.destroySpeedBits == 0xbf800000

end Attrs

end Redstone
