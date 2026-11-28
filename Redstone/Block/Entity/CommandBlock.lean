module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:command_block`

The data that the model keeps of the block entity `CommandBlockEntity`, which the impulse, the
chain and the repeating command block share, together with its `BaseCommandBlock`.

Not kept: `CustomName` and `LastOutput`. Neither is read by the game logic, and `LastOutput`
contains the wall-clock time of the execution.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:command_block` block entity. -/
structure CommandBlock where
  /-- `BaseCommandBlock.command`. -/
  command : String
  /-- `BaseCommandBlock.successCount`: what a comparator reads. -/
  successCount : ℤ
  /-- `BaseCommandBlock.trackOutput`. It only decides whether the output is kept. -/
  trackOutput : Bool
  /-- `BaseCommandBlock.updateLastExecution`. -/
  updateLastExecution : Bool
  /-- `BaseCommandBlock.lastExecution`: the game time of the last execution, or `-1`. -/
  lastExecution : ℤ
  /-- `CommandBlockEntity.powered`: the block saw a signal at its last neighbour update. -/
  powered : Bool
  /-- `CommandBlockEntity.conditionMet`. -/
  conditionMet : Bool
  /-- `CommandBlockEntity.auto`: "always active". -/
  auto : Bool
  deriving DecidableEq, Repr

/-- The data of a `CommandBlockEntity` as its constructor leaves it. `CommandBlock.newBlockEntity`
then sets `auto` for a chain command block. -/
instance : Inhabited CommandBlock :=
  ⟨{ command := "", successCount := 0, trackOutput := true, updateLastExecution := true,
     lastExecution := -1, powered := false, conditionMet := false, auto := false }⟩

namespace CommandBlock

/-- Reads the data from the block entity's saved NBT, as `BaseCommandBlock.load` and
`CommandBlockEntity.loadAdditional` do. Fields the model does not keep are ignored. -/
def ofNbt? (t : Nbt) : Option CommandBlock :=
  let updateLastExecution := t.boolD "UpdateLastExecution" true
  some
    { command := ((t.get? "Command").bind Nbt.toString?).getD ""
      successCount := t.intD "SuccessCount" 0
      trackOutput := t.boolD "TrackOutput" true
      updateLastExecution
      lastExecution := if updateLastExecution then t.intD "LastExecution" (-1) else -1
      powered := t.boolD "powered" false
      conditionMet := t.boolD "conditionMet" false
      auto := t.boolD "auto" false }

end CommandBlock

end Redstone.BlockEntities
