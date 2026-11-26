module

public import Redstone.Mechanics.Tick

/-!
# Command blocks, structure blocks and test blocks

Java classes: `CommandBlock`, `CommandBlockEntity`, `BaseCommandBlock`, `StructureBlock`,
`TestBlock`, `TestBlockEntity`.

## Command blocks

The impulse (`command_block`), the repeating and the chain command block are one class; the
block decides the mode (`CommandBlockEntity.getMode`). The block entity remembers whether the
block was powered at its last neighbour update. An impulse or repeating block that becomes
powered, and is not "always active" (`auto`), schedules a tick one game tick later. On that
tick it executes its command if its condition was met, then runs the chain of chain command
blocks it points at, within the same tick. A repeating block schedules the next tick as long as
it is powered or always active. A comparator reads `successCount`.

### The command is an oracle

What a command does is outside the model. `performCommand` takes an `Oracle`: a reaction that
runs the command text at the position of the block and returns how often it succeeded. The
bookkeeping around it (`lastExecution`, `successCount`, the special command `Searge`) is
modelled exactly. `behaviour` uses `Oracle.default`, which knows the commands whose effect on
the world is nil:

* a text whose first word is not the name of a command fails: it succeeds zero times and
  changes nothing;
* `say <message>`, with a message that contains no `@`, succeeds once and changes nothing, and
  `say` without a message fails;
* any other command is unknown to the model. It is treated as failing, and `Level.overflow` is
  set to record that the level no longer follows the game. For such a command `behaviourWith`
  has to be given an oracle that describes it.

The game rule `command_blocks_work` is taken to be true, its default.

### What is left out

* `setPlacedBy` (a player places the block from an item), `CommandBlockEntity.onModeSwitch`
  and `setAutomatic` after creation (the editing screen): no action of the model reaches them.
* `LastOutput` and `CustomName`.
* The reaction keeps no reference to the block entity as the game does: if an oracle removes
  the block that executes it, the bookkeeping that follows is skipped.

## Test blocks

A test block in the mode `log`, `fail` or `accept` remembers whether it is powered, and is
triggered on the rising edge; being triggered only sets a flag for the game test framework and
writes to the log, so nothing but `powered` changes. A test block in the mode `start` ignores
power and is itself a signal source while its block entity is `powered`, which the game test
framework sets (`TestBlockEntity.trigger`) and a scheduled tick resets.

## Structure blocks

A structure block remembers whether it is powered and is triggered on the rising edge. The
trigger saves a structure to memory (`save`), places it (`load`), forgets it (`corner`) or does
nothing (`data`). Only placing changes the world, and only when a structure of that name
exists. Structure templates are not modelled: the trigger does nothing here. This is exact as
long as no template exists under the name of a `load` block. Templates exist in the namespace
`minecraft` (the game's own) and under the names that a `save` block was triggered with, so
`Level.overflow` is set when a `save` block with a name, or a `load` block with a name in the
namespace `minecraft`, is triggered.

## Block entities that do not exist yet

The game's `Level.getBlockEntity` creates a missing block entity on the spot. This is
observable: when a block replaces a powered lever, the lever's `affectNeighborsAfterRemoval`
sends the new block a neighbour update before `LevelChunk.setBlockState` has created its block
entity. `Level.getBlockEntity` of the model does not create anything, so this file has its own
`getBlockEntityImmediate`.
-/

@[expose] public section

namespace Redstone.Component.CommandBlock

/-! ### The command oracle -/

/-- What `Commands.performPrefixedCommand` does for a command block: the reaction to the command
text `command` run by the block at the given position. It returns the number of successes the
command reports to its source (`successCount` is increased by it). -/
abbrev Oracle := Pos → String → M ℕ

namespace Oracle

/-- `Commands.trimOptionalPrefix`: one leading `/` is dropped. -/
def trimOptionalPrefix (command : List Char) : List Char :=
  match command with
  | '/' :: rest => rest
  | cs => cs

/-- The names of the commands of the dedicated server of 26.3: the literals below the root of
its command tree (the server's `commands.json` report). -/
def rootLiterals : List String :=
  ["advancement", "attribute", "ban", "ban-ip", "banlist", "bossbar", "clear", "clone",
   "compute", "damage", "data", "datapack", "debug", "defaultgamemode", "deop", "dialog",
   "difficulty", "effect", "enchant", "execute", "experience", "fetchprofile", "fill",
   "fillbiome", "forceload", "function", "gamemode", "gamerule", "give", "help", "item", "jfr",
   "kick", "kill", "list", "locate", "loot", "me", "msg", "op", "pardon", "pardon-ip",
   "particle", "perf", "place", "playsound", "posteffect", "publish", "random", "recipe",
   "reload", "return", "ride", "rotate", "save-all", "save-off", "save-on", "say", "schedule",
   "scoreboard", "seed", "setblock", "setidletimeout", "setworldspawn", "spawnpoint", "spectate",
   "spreadplayers", "stop", "stopsound", "stopwatch", "summon", "swing", "tag", "team",
   "teammsg", "teleport", "tell", "tellraw", "test", "tick", "time", "title", "tm", "tp",
   "transfer", "trigger", "unpublish", "version", "w", "waypoint", "weather", "whitelist",
   "worldborder", "xp"]

/-- The oracle of the commands without effect on the world.

* A text whose first word is not a root literal does not parse (`dispatcherUnknownCommand`): no
  success, no effect.
* `say <message>` succeeds once (`SayCommand`) and only sends a chat message. A message with
  an `@` may contain an entity selector and is not covered. `say` without a message does not
  parse.
* Any other command is unknown to the model: it is treated as failing and `Level.overflow` is
  set. -/
def default : Oracle := fun _ command => do
  let text := trimOptionalPrefix command.toList
  let word := text.takeWhile (· ≠ ' ')
  if !rootLiterals.contains (String.ofList word) then return 0
  match text with
  | ['s', 'a', 'y'] | ['s', 'a', 'y', ' '] => return 0
  | 's' :: 'a' :: 'y' :: ' ' :: message =>
    if !message.contains '@' then return 1
    Level.setOverflow
    return 0
  | _ =>
    Level.setOverflow
    return 0

end Oracle

/-! ### Block entities -/

/-- `Level.getBlockEntity(pos)`, which is `LevelChunk.getBlockEntity(pos, IMMEDIATE)`: the block
entity at `p`. If there is none although the block at `p` has one, it is created on the spot.
This happens while a block is being placed: the reactions of the block it replaces
(`affectNeighborsAfterRemoval`) run before `LevelChunk.setBlockState` creates the block entity
of the new block, and they can send it a neighbour update. -/
def getBlockEntityImmediate (p : Pos) : M (Option BlockEntity) := do
  if let some be ← Level.getBlockEntity p then return some be
  let state ← Level.getBlock p
  if !state.hasBlockEntity then return none
  let b ← Level.behaviour state
  let some be := b.newBlockEntity | return none
  Level.setBlockEntity p be
  if b.ticksBlockEntity then Level.addBlockEntityTicker p
  return some be

/-! ### `CommandBlockEntity` and `BaseCommandBlock` -/

/-- `level.getBlockEntity(pos) instanceof CommandBlockEntity`: the data of the command block
entity at `p`. -/
def getData (p : Pos) : M (Option BlockEntities.CommandBlock) := do
  match ← getBlockEntityImmediate p with
  | some (.commandBlock d) => return some d
  | _ => return none

/-- Changes the data of the command block entity at `p`, if there is one. -/
def modifyData (p : Pos) (f : BlockEntities.CommandBlock → BlockEntities.CommandBlock) :
    M Unit := do
  if let some d ← getData p then
    if f d ≠ d then Level.setBlockEntity p (.commandBlock (f d))

/-- `BaseCommandBlock.setSuccessCount`. -/
def setSuccessCount (p : Pos) (n : ℤ) : M Unit := modifyData p ({ · with successCount := n })

/-- `CommandBlockEntity.isConditional`: the block at `p` is a command block whose state is
conditional. -/
def isConditional (p : Pos) : M Bool := do
  match ← Level.getBlock p with
  | .command _ s => return s.conditional
  | _ => return false

/-- `CommandBlockEntity.markConditionMet`: recomputes `conditionMet` and returns it. An
unconditional block always meets its condition. A conditional block meets it when the block
behind it is a command block whose last execution succeeded. -/
def markConditionMet (p : Pos) : M Bool := do
  let met ← match ← Level.getBlock p with
    | .command _ s =>
      if s.conditional then
        let q := p.step s.facing.opposite
        match ← Level.getBlock q with
        | .command _ _ =>
          match ← getData q with
          | some d => pure (decide (d.successCount > 0))
          | none => pure false
        | _ => pure false
      else pure true
    | _ => pure true
  modifyData p ({ · with conditionMet := met })
  return met

/-- `"Searge".equalsIgnoreCase(command)`. Java compares the upper-case forms of the characters;
besides the ASCII letters, the long s (`ſ`) has the upper-case form `S`. -/
def isSearge (command : String) : Bool :=
  command.toList.map (fun c => if c = 'ſ' then 'S' else c.toUpper) == "SEARGE".toList

/-- `BaseCommandBlock.performCommand`: executes the command of the block entity at `p`. Returns
false, and does nothing, if the block already executed in this game tick. -/
def performCommand (oracle : Oracle) (p : Pos) : M Bool := do
  let some d ← getData p | return false
  let now : ℤ := (← get).gameTime
  if now = d.lastExecution then return false
  if isSearge d.command then
    setSuccessCount p 1
    return true
  setSuccessCount p 0
  if d.command ≠ "" then
    let successes ← oracle p d.command
    modifyData p fun d => { d with successCount := d.successCount + successes }
  modifyData p fun d => { d with lastExecution := if d.updateLastExecution then now else -1 }
  return true

/-! ### `CommandBlock` -/

/-- `CommandBlockEntity.getMode() == Mode.SEQUENCE`: the block is a chain command block. This is
also the constructor argument `automatic` of `CommandBlock`. -/
def isSequence : Blocks.Command.Id → Bool
  | .chain_command_block => true
  | _ => false

/-- `MAX_COMMAND_SEQUENCE_LENGTH`: the default value of the game rule
`max_command_sequence_length`. -/
def maxCommandSequenceLength : ℕ := 65536

/-- `executeChain`: runs the chain command blocks that follow the block at `p` in direction
`dir`, each one pointing at the next, for at most `fuel` blocks. A chain block that is neither
powered nor always active is passed over. The chain ends at a block that is not a chain command
block, or at one that already executed in this game tick. -/
def executeChain (oracle : Oracle) : ℕ → Pos → Direction → M Unit
  | 0, _, _ => pure ()
  | fuel + 1, p, dir => do
    let q := p.step dir
    match ← Level.getBlock q with
    | .command .chain_command_block s =>
      let some d ← getData q | return
      if d.powered || d.auto then
        if ← markConditionMet q then
          if !(← performCommand oracle q) then return
          Level.updateNeighbourForOutputSignal q .chain_command_block
        else if ← isConditional q then setSuccessCount q 0
      executeChain oracle fuel q s.facing
    | _ => pure ()

/-- `execute`: executes the command of the block at `p`, if it has one, and then the chain it
points at. -/
def execute (oracle : Oracle) (s : Blocks.Command) (p : Pos) (commandSet : Bool) : M Unit := do
  if commandSet then discard <| performCommand oracle p
  else setSuccessCount p 0
  executeChain oracle maxCommandSequenceLength p s.facing

/-- `setPoweredAndUpdate`: records whether the block is powered. On the rising edge an impulse
or repeating block that is not always active schedules its tick. -/
def setPoweredAndUpdate (id : Blocks.Command.Id) (p : Pos) (isPowered : Bool) : M Unit := do
  let some d ← getData p | return
  if isPowered != d.powered then
    modifyData p ({ · with powered := isPowered })
    if isPowered then
      if d.auto || isSequence id then return
      discard <| markConditionMet p
      Level.scheduleTick p id.toBlockId 1

/-- `tick`: the scheduled tick of a command block. -/
def tick (oracle : Oracle) (id : Blocks.Command.Id) (s : Blocks.Command) (p : Pos) : M Unit := do
  let some d ← getData p | return
  let commandSet := d.command ≠ ""
  let wasConditionMet := d.conditionMet
  let executeOrReset : M Unit := do
    if wasConditionMet then execute oracle s p commandSet
    else if ← isConditional p then setSuccessCount p 0
  match id with
  | .repeating_command_block =>
    discard <| markConditionMet p
    executeOrReset
    if let some d ← getData p then
      if d.powered || d.auto then Level.scheduleTick p id.toBlockId 1
  | .command_block => executeOrReset
  | .chain_command_block => pure ()
  Level.updateNeighbourForOutputSignal p id.toBlockId

/-- The behaviour of a command block whose commands are run by `oracle`. -/
def command (oracle : Oracle) (id : Blocks.Command.Id) (s : Blocks.Command) : Behaviour :=
  let self : Block := .command id s
  { Behaviour.inert self with
    newBlockEntity := some (.commandBlock { (default : BlockEntities.CommandBlock) with
      auto := isSequence id })
    neighborChanged := fun p _ _ => do
      if (← getData p).isSome then setPoweredAndUpdate id p (← Level.hasNeighborSignal p)
    tick := tick oracle id s
    -- A block entity that does not exist yet would be created with a success count of 0.
    analogSignal := fun l p _ =>
      match l.blockEntities p with
      | some (.commandBlock d) => d.successCount.toNat
      | _ => 0
    -- The player is taken to be an operator in creative mode; the screen it opens is not
    -- modelled.
    useWithoutItem := fun p _ => return (← getData p).isSome }

/-! ### `TestBlock` -/

/-- `getServerTestBlockEntity`: the data of the test block entity at `p`. -/
def getTestData (p : Pos) : M (Option BlockEntities.TestBlock) := do
  match ← getBlockEntityImmediate p with
  | some (.testBlock d) => return some d
  | _ => return none

/-- `TestBlock.ownSignal`: a test block whose state has the mode `start` gives 15 while its
block entity is powered. A block entity that does not exist yet would be created unpowered. -/
def testOwnSignal (s : Blocks.Test) (l : Level) (p : Pos) : ℕ :=
  match s.mode, l.blockEntities p with
  | .start, some (.testBlock d) => if d.powered then 15 else 0
  | _, _ => 0

/-- The behaviour of a test block. -/
def test (s : Blocks.Test) : Behaviour :=
  let self : Block := .test s
  { Behaviour.inert self with
    newBlockEntity := some (.testBlock { mode := s.mode, message := "", powered := false })
    ownSignal := testOwnSignal s
    signal := fun l p _ => testOwnSignal s l p
    neighborChanged := fun p _ _ => do
      let some d ← getTestData p | return
      if d.mode ≠ .start then
        let shouldTrigger ← Level.hasNeighborSignal p
        -- On the rising edge the block is triggered. Outside the mode `start`, `trigger` only
        -- writes to the log and sets `triggered`, which is not kept.
        if shouldTrigger != d.powered then
          Level.setBlockEntity p (.testBlock { d with powered := shouldTrigger })
    -- `TestBlockEntity.reset`.
    tick := fun p => do
      let some d ← getTestData p | return
      if d.mode = .start then
        Level.setBlockEntity p (.testBlock { d with powered := false })
        Level.updateNeighborsAt p .test_block
    useWithoutItem := fun p _ => return (← getTestData p).isSome }

/-! ### `StructureBlock` -/

/-- `StructureBlock.trigger`: saves, places or forgets the structure template named by the block
entity. Templates are not modelled, so nothing happens; `Level.overflow` is set when this may be
wrong, that is when a template is saved under a name, or when one is placed whose name is in
the game's own namespace. -/
def structureTrigger (d : BlockEntities.StructureBlock) : M Unit := do
  let unmodelled := match d.mode with
    | .save => true
    | .load => "minecraft:".isPrefixOf d.name
    | .corner | .data => false
  if d.name ≠ "" && unmodelled then Level.setOverflow

/-- The behaviour of a structure block. -/
def «structure» (s : Blocks.Structure) : Behaviour :=
  let self : Block := .«structure» s
  { Behaviour.inert self with
    newBlockEntity := some (.structureBlock { name := "", mode := s.mode, powered := false })
    neighborChanged := fun p _ _ => do
      let some (.structureBlock d) ← getBlockEntityImmediate p | return
      let shouldTrigger ← Level.hasNeighborSignal p
      if shouldTrigger != d.powered then
        Level.setBlockEntity p (.structureBlock { d with powered := shouldTrigger })
        if shouldTrigger then structureTrigger d
    useWithoutItem := fun p _ => do
      let some (.structureBlock _) ← getBlockEntityImmediate p | return false
      return true }

/-! ### The component -/

/-- The behaviour of the blocks of this component, with the commands run by `oracle`. -/
def behaviourWith (oracle : Oracle) (self : Block) : Behaviour :=
  match self with
  | .command id s => command oracle id s
  | .test s => test s
  | .«structure» s => «structure» s
  | _ => .inert self

/-- The behaviour of the blocks of this component. Commands are run by `Oracle.default`. -/
def behaviour (self : Block) : Behaviour := behaviourWith Oracle.default self

end Redstone.Component.CommandBlock
