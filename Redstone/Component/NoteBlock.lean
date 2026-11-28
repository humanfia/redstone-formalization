module

public import Redstone.Mechanics.Tick
public import Redstone.Component.NoteBlockInstrument

/-!
# Note block

Java class: `NoteBlock` (with `NoteBlockInstrument`).

A note block plays when the signal it receives appears, and when a player uses it, which also
raises its note by one. Playing queues a block event and announces `note_block_play`; the
sound itself is made when the block event runs. The instrument follows the blocks above and
below: a mob head above wins, otherwise the block below decides.

Not modelled:

* `attack` (a player hitting the block plays it); the model has no such action.
* The sound and the particle of `triggerEvent`. Its draw from the level's random generator is
  modelled.
* The custom sound of a player head (`SkullBlockEntity.getNoteBlockSound`): the model keeps no
  data of skull block entities, so a player head above a note block is taken to have none, in
  which case `triggerEvent` does nothing.
* `useItemOn` with a mob head on the top face: the game then goes on to use the item itself,
  which places the head. Here nothing happens (pending scenario `lamp-misc/note-head-item`).

The instrument a note block takes from every block of the game, above and below it, is checked
by the scenarios `lamp-misc/note-grid-*`. Five of them, `note-grid-other-*`, wait in
`tests/pending` for reasons that are not the note block's: some of the blocks they place do
something by themselves that their own units have yet to model (the tickers of signs, spawners,
beacons, end gateways, vaults, campfires and conduits, fire that goes out, the scheduled ticks
of suspicious sand and gravel, frogspawn, sniffer eggs and coral, scaffolding that falls, and
the random draws of a rail that breaks). `note-grid-rest-*` are the same grids without those blocks
(`tests/palettes/note_grid_rest_gen.py`), and agree with the server.
-/

@[expose] public section

namespace Redstone.Component.NoteBlock

/-- `NoteBlockInstrument.worksAboveNoteBlock`: the instrument of a mob head. -/
def worksAboveNoteBlock : NoteBlockInstrument → Bool
  | .zombie | .skeleton | .creeper | .dragon | .wither_skeleton | .piglin | .custom_head => true
  | _ => false

/-- `NoteBlockInstrument.hasCustomSound`. -/
def hasCustomSound (i : NoteBlockInstrument) : Bool := i = .custom_head

/-- The item tag `minecraft:noteblock_top_instruments`. -/
def topInstrumentItems : List String :=
  ["minecraft:zombie_head", "minecraft:skeleton_skull", "minecraft:creeper_head",
    "minecraft:dragon_head", "minecraft:wither_skeleton_skull", "minecraft:piglin_head",
    "minecraft:player_head"]

/-- `setInstrument(level, position, state)`: the state with the instrument given by the block
above, if that is a mob head, and otherwise by the block below; a mob head below counts as
`harp`. -/
def setInstrument (l : Level) (p : Pos) (s : Blocks.Note) : Blocks.Note :=
  let above := (l.blockAt (p.step .up)).instrument
  if worksAboveNoteBlock above then { s with instrument := above }
  else
    let below := (l.blockAt (p.step .down)).instrument
    { s with instrument := if worksAboveNoteBlock below then .harp else below }

/-- `playNote(source, state, level, pos)`: queues the block event that makes the sound, unless
the block above is not air and the instrument is not a mob head. -/
def playNote (s : Blocks.Note) (p : Pos) : M Unit := do
  if worksAboveNoteBlock s.instrument || (← Level.getBlock (p.step .up)).isAir then
    Level.blockEvent p .note_block 0 0
    Level.gameEvent "minecraft:note_block_play" p

/-- `state.cycle(NOTE)`: the next note, from 24 back to 0. -/
def cycleNote (s : Blocks.Note) : Blocks.Note := { s with note := s.note + 1 }

/-- `useWithoutItem`: raises the note by one and plays. -/
def use (s : Blocks.Note) (p : Pos) : M Unit := do
  let s := cycleNote s
  discard <| Level.setBlock p (.note s)
  playNote s p

/-- `level.getRandom().nextLong()`, the value being dropped: two draws of 32 bits. -/
def drawLong : M Unit :=
  modify fun l => { l with random := ((l.random.next 32).2.next 32).2 }

/-- `triggerEvent`: makes the sound. What remains of it here is the seed of the sound, drawn
from the level's random generator, and the result. With the instrument of a player head the
game looks for the head's custom sound (`getCustomSoundId`) and stops when there is none; the
model keeps no data of skull block entities and takes it that there is none. -/
def triggerEvent (s : Blocks.Note) : M Bool := do
  if hasCustomSound s.instrument then return false
  drawLong
  return true

/-- The behaviour of a note block. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .note s =>
    { Behaviour.inert self with
      updateShape := fun p d _ _ => do
        if d.axis = .y then return .note (setInstrument (← get) p s) else return self
      neighborChanged := fun p _ _ => do
        let signal ← Level.hasNeighborSignal p
        if signal != s.powered then
          if signal then playNote s p
          discard <| Level.setBlock p (.note { s with powered := signal })
      -- `useItemOn` with a mob head on the top face answers `InteractionResult.PASS`: neither
      -- the block nor the empty hand reacts. Otherwise `super.useItemOn` asks for the
      -- empty-hand interaction.
      tryEmptyHand := fun face item => !(topInstrumentItems.contains item && face = .up)
      useWithoutItem := fun p _ => do
        use s p
        return true
      triggerEvent := fun _ _ _ => triggerEvent s }
  | _ => .inert self

end Redstone.Component.NoteBlock
