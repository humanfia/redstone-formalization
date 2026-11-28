import Redstone.Proof.Circuit

/-!
# The note block: one note per rising edge

A note block on a stone block, with a lever on the floor next to it:

```
y = 2:      (air)         x = 0: lever, on stone
y = 1:   L  N             x = 1: note block, on stone
y = 0:   S  S
```

`NoteBlock.neighborChanged` compares the signal with the property `powered`. When they differ
it stores the signal, and if the signal has just appeared it plays: it queues a block event,
which runs later in the same game tick and makes the sound.

What a theorem can observe of a note being played is

* the block event `(note block, 0, 0)` in the queue right after the input, before the game
  tick runs, and
* one `nextLong()` drawn from the level's random generator when the block event runs
  (`NoteBlock.triggerEvent`: the seed of the sound). Nothing else in this level draws from
  the generator, so the number of notes played is the number of draws (`played`).

The run:

| before game tick | input | `powered` | note played |
|---|---|---|---|
| 1 | lever on | true | yes (1) |
| 3 | lever off | false | no |
| 5 | lever on | true | yes (2) |
| 7 | lever off | false | no |
| 8 | the stone below is replaced by a gold block | false | no; the instrument becomes `bell` |
| 10 | the note block is used | false | yes (3); the note goes from 0 to 1 |
| 12 | a stone block is put on top | false | no |
| 13 | lever on | true | no: a note block with a block on top is mute |

So the block plays exactly once per rising edge of its signal, never on the falling edge and
never while the signal stays; the instrument is that of the block below (`basedrum` on stone,
`bell` on gold); and with a block on top the rising edge still sets `powered` but plays
nothing.

The level is loaded raw; `circuit_quiescent` shows that it is at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.RailMisc.NoteBlock

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The position of the note block. -/
def note : Pos := ⟨1, 1, 0⟩

/-- The cell below the note block, which decides the instrument. -/
def below : Pos := ⟨1, 0, 0⟩

/-- The cell above the note block, which has to be air for it to play. -/
def above : Pos := ⟨1, 2, 0⟩

/-- The lever, on or off. -/
def leverState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- A note block. -/
def noteState (instrument : NoteBlockInstrument) (n : Fin 25) (powered : Bool) : Block :=
  .note ⟨instrument, n, powered⟩

/-- The lever and the note block, on stone. -/
def circuit : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (below, .plain .stone), (lever, leverState false),
    (note, noteState .basedrum 0 false)]

/-- The inputs of the table in the module documentation; fourteen game ticks. -/
def schedule : Schedule :=
  .first [.use lever .up] 2 ++ .first [.use lever .up] 2 ++ .first [.use lever .up] 2 ++
    .first [.use lever .up] 1 ++ .first [.set below (.plain .gold_block)] 2 ++
    .first [.use note .north] 2 ++ .first [.set above (.plain .stone)] 1 ++
    .first [.use lever .up] 2

checkpoints state := schedule from circuit

/-- The level's random generator after `n` notes have been played: `n` times `nextLong()`, two
draws of 32 bits each, from the generator the level starts with. -/
def played (n : ℕ) : JavaRandom := (fun r => ((r.next 32).2.next 32).2)^[n] circuit.random

/-- The block event a note block queues when it plays. -/
def noteEvent : BlockEvent := ⟨note, .note_block, 0, 0⟩

/-- The level as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **The rising edge plays.** Using the lever queues exactly one block event of the note
block, before the game tick runs; after the game tick the note block is `powered`, the event
has run, and one note has been played. During the next game tick nothing more is played. -/
theorem rising_edge_plays :
    (rules.input (.use lever .up) circuit).blockEvents = [noteEvent] ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt [lever, note] =
        [leverState true, noteState .basedrum 0 true] ∧
      (rules.runSchedule (schedule.take 1) circuit).blockEvents = [] ∧
      (rules.runSchedule (schedule.take 1) circuit).random = played 1 ∧
      (rules.runSchedule (schedule.take 2) circuit).random = played 1 ∧
      (rules.runSchedule (schedule.take 2) circuit).overflow = false := by
  rw [state_run_1, state_run_2]
  circuit_decide

assert_standard_axioms rising_edge_plays

/-- **While the signal stays, nothing is played**, for ever: with the lever on the level is at
rest. -/
theorem held_signal_is_silent (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).blockAt note =
        noteState .basedrum 0 true ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).random = played 1 ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).overflow = false := by
  rw [state_run_1, rules.steps_of_quiescent (by circuit_decide)]
  refine ⟨?_, ?_, ?_⟩
  · rw [Level.blockAt_advance]
    circuit_decide
  · change state_1.random = played 1
    circuit_decide
  · rw [Level.overflow_advance]
    circuit_decide

assert_standard_axioms held_signal_is_silent

/-- **The falling edge does not play.** Switching the lever off (before game tick 3) queues no
block event; the note block is no longer `powered`, and still only one note has been played. -/
theorem falling_edge_is_silent :
    (rules.input (.use lever .up) (rules.runSchedule (schedule.take 2) circuit)).blockEvents =
        [] ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt [lever, note] =
        [leverState false, noteState .basedrum 0 false] ∧
      (rules.runSchedule (schedule.take 4) circuit).random = played 1 ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_2, state_run_3, state_run_4]
  circuit_decide

assert_standard_axioms falling_edge_is_silent

/-- **Once per rising edge.** The second time the lever is switched on (before game tick 5)
one block event is queued again and a second note is played; switching it off (before game
tick 7) plays nothing. -/
theorem second_rising_edge_plays :
    (rules.input (.use lever .up) (rules.runSchedule (schedule.take 4) circuit)).blockEvents =
        [noteEvent] ∧
      (rules.runSchedule (schedule.take 5) circuit).blockAt note = noteState .basedrum 0 true ∧
      (rules.runSchedule (schedule.take 6) circuit).random = played 2 ∧
      (rules.runSchedule (schedule.take 7) circuit).blockAt note = noteState .basedrum 0 false ∧
      (rules.runSchedule (schedule.take 7) circuit).random = played 2 ∧
      (rules.runSchedule (schedule.take 7) circuit).overflow = false := by
  rw [state_run_4, state_run_5, state_run_6, state_run_7]
  circuit_decide

assert_standard_axioms second_rising_edge_plays

/-- **The instrument is that of the block below.** On stone the note block is a `basedrum`.
When the stone is replaced by a gold block (before game tick 8) it becomes a `bell` in the
same game tick, without playing. -/
theorem instrument_from_below :
    circuit.blockAt note = noteState .basedrum 0 false ∧
      (rules.runSchedule (schedule.take 8) circuit).blocksAt [below, note] =
        [.plain .gold_block, noteState .bell 0 false] ∧
      (rules.runSchedule (schedule.take 9) circuit).random = played 2 ∧
      (rules.runSchedule (schedule.take 9) circuit).overflow = false := by
  rw [state_run_8, state_run_9]
  circuit_decide

assert_standard_axioms instrument_from_below

/-- **Using the note block raises the note and plays.** Used before game tick 10, the note
block goes from note 0 to note 1, queues one block event, and a third note is played. -/
theorem use_tunes_and_plays :
    (rules.input (.use note .north) (rules.runSchedule (schedule.take 9) circuit)).blockEvents =
        [noteEvent] ∧
      (rules.runSchedule (schedule.take 10) circuit).blockAt note = noteState .bell 1 false ∧
      (rules.runSchedule (schedule.take 11) circuit).random = played 3 ∧
      (rules.runSchedule (schedule.take 11) circuit).overflow = false := by
  rw [state_run_9, state_run_10, state_run_11]
  circuit_decide

assert_standard_axioms use_tunes_and_plays

/-- **A note block with a block on top is mute.** With a stone block above it (put there
before game tick 12), the rising edge (lever on before game tick 13) still makes the note
block `powered`, but queues no block event and plays nothing; and so it stays for ever. -/
theorem covered_is_mute (n : ℕ) :
    (rules.input (.use lever .up) (rules.runSchedule (schedule.take 12) circuit)).blockEvents =
        [] ∧
      (rules.runSchedule (schedule.take 13) circuit).blocksAt [lever, note, above] =
        [leverState true, noteState .bell 1 true, .plain .stone] ∧
      (rules.runSchedule schedule circuit).random = played 3 ∧
      (rules.steps n (rules.runSchedule schedule circuit)).blockAt note =
        noteState .bell 1 true ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run_12, state_run_13, state_run, rules.blockAt_steps_of_quiescent (by circuit_decide),
    rules.overflow_steps_of_quiescent (by circuit_decide)]
  circuit_decide

assert_standard_axioms covered_is_mute

end Redstone.Theorems.RailMisc.NoteBlock
