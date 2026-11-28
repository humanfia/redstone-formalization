module

public import Redstone.Basic.Float32
public import Redstone.Block.Entity.Inventory

/-!
# Block entity `minecraft:shulker_box`

The data that the model keeps of the block entity `ShulkerBoxBlockEntity`: the 27 slots and the
lid (`openCount`, `animationStatus`, `progress`), which the game does not save.

The game keeps `progress` as a `float` and moves it by `0.1F` a tick. The model keeps the value
of that `float` as a rational number and rounds every sum to a `float` (`F32.roundFloat`), so
the tick in which the lid arrives is the game's, also when the lid turns around half way.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- `ShulkerBoxBlockEntity.AnimationStatus`. -/
inductive ShulkerBoxAnimationStatus
  | closed
  | opening
  | opened
  | closing
  deriving DecidableEq, Repr, Inhabited

/-- The data of a `minecraft:shulker_box` block entity. -/
structure ShulkerBox where
  /-- `itemStacks`: the 27 slots. -/
  items : Inventory := Inventory.empty 27
  /-- `openCount`: how many players the box believes have it open. Not saved. -/
  openCount : ℤ := 0
  /-- `animationStatus`: what the lid is doing. Not saved. -/
  animationStatus : ShulkerBoxAnimationStatus := .closed
  /-- `progress`: how far the lid is open, from 0 to 1, as the value of the game's `float`. Not
  saved. -/
  progress : ℚ := 0
  /-- `progressOld`: the progress before the last tick of the block entity. Not saved. -/
  progressOld : ℚ := 0
  /-- The player of the `use` actions has the menu of this box open, so closing that menu will
  call `stopOpen` on it. Not saved. -/
  viewed : Bool := false
  deriving DecidableEq, Repr

namespace ShulkerBox

/-- The data of a freshly created shulker box. -/
instance : Inhabited ShulkerBox := ⟨{}⟩

/-- `isClosed()`. -/
def isClosed (d : ShulkerBox) : Bool := d.animationStatus = .closed

/-- The `float` `0.1F`. -/
def lidStep : ℚ := F32.roundFloat (1 / 10)

/-- `getProgress(1.0F)`, that is `Mth.lerp(1.0F, progressOld, progress)`: the `float`
`progressOld + 1.0F * (progress - progressOld)`. -/
def getProgress (d : ShulkerBox) : ℚ :=
  F32.roundFloat (d.progressOld + F32.roundFloat (d.progress - d.progressOld))

/-- The shape of the box (`ShulkerBoxBlock.getShape`, the shape of `getBoundingBox(state)`) is
the full block. The box reaches `0.5F * getProgress(1.0F)` beyond the block on the side of the
lid, and `Shapes.create` takes a box for the full block when its corners are within `1.0E-7` of
those of the block. So a lid that has stopped a few `float` rounding errors short of closed
still has the shape of a closed one. -/
def isFullBlock (d : ShulkerBox) : Bool := d.getProgress / 2 < 1 / 10000000

/-- Reads the data from the block entity's saved NBT (`loadFromTag`). Fields the model does not
keep are ignored. -/
def ofNbt? (t : Nbt) : Option ShulkerBox := do
  if !t.plainContainer then none
  return { items := Inventory.ofNbt 27 t }

end ShulkerBox

end Redstone.BlockEntities
