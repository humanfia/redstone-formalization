import Redstone.Proof.Circuit

/-!
# The observer doorbell: an observer watching a door, and a note block

Side view (east is to the right, up is up):

```
y = 2:   d                d, D the two halves of an oak door
y = 1:   D  O> N          O observer, its face towards the lower half; N note block
y = 0:   S                S stone
```

The observer at `(1, 1, 0)` looks at the lower half of the door and has a note block behind
it. Opening or closing the door changes the state of both halves, so the observer gives a
pulse, and the note block, which plays on a rising edge, rings once: a doorbell without any
wiring in the door frame.

What is proved, in game ticks from the use of the door:

* `bell_on_opening`: a player opens the door (on its lower half). Both halves are open after
  game tick 1. The observer is on after game ticks 2 and 3, and the note block is `powered`
  for exactly those two game ticks.
* `bell_on_closing`: the same from the level with the door open, the player closing it (on
  its upper half).
* `rings_once`: the note block plays exactly once per pulse. Playing is a block event that
  draws one `nextLong` from the level's random generator (`NoteBlock.triggerEvent`); the
  theorem says that the generator after the game tick in which the note block becomes powered
  is the generator before it advanced by exactly one `nextLong`, that it does not move in the
  following game ticks, and that no block event is left queued.
* `muffled_bell`: the same circuit with a stone block on top of the note block. The note block
  is powered and unpowered as before, but does not play: the generator does not move in the
  game tick in which it becomes powered. (`NoteBlock.playNote`: a block above silences a note
  block.)
* `rests_after_ringing`: five game ticks after the door was opened the level is at rest, and
  nothing rings again, for ever.

The three levels are loaded raw and are at rest (`levels_quiescent`).

**How this file is proved, and why.** The other files of this directory use the command
`checkpoints`, which writes the level after every game tick as a literal. It cannot be used
for a level with a door: the literal is what `Repr` prints, parsed back as a term
(`Redstone.Proof.parseRepr`), and the door's property `open` is printed as the field name
`open`, which is a keyword and does not parse. Here every statement is therefore evaluated by
the kernel from the level as built, up to five game ticks in one evaluation. That is more
than `Redstone/Proof/README.md` recommends, and it is why the runs are short and the opening
and the closing start from two levels instead of being one run. The circuit is small: the
file was measured at 1.4 GB of peak memory, like the files that use checkpoints, so it is not
a heavy file.

Not yet proved, for that reason: the closing as a continuation of the opening in one run (the
level after the opening being at rest and having the blocks of `opened` is proved:
`rests_after_ringing`), and a run longer than five game ticks.

Not stated: the sound itself. The model keeps the draw of the sound's seed and the game event
`note_block_play`, not the sound (`Redstone/Component/NoteBlock.lean`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Observer.Doorbell

/-- The lower half of the door. -/
def lower : Pos := ⟨0, 1, 0⟩

/-- The upper half of the door. -/
def upper : Pos := ⟨0, 2, 0⟩

/-- The position of the observer. -/
def observer : Pos := ⟨1, 1, 0⟩

/-- The position of the note block. -/
def bell : Pos := ⟨2, 1, 0⟩

/-- The half `half` of the oak door, open or closed. -/
def door (half : DoubleBlockHalf) (isOpen : Bool) : Block :=
  .door .oak_door ⟨.north, half, .left, isOpen, false⟩

/-- The doorbell with the door open or closed: an oak door on a stone block, an observer
looking at its lower half, and a note block behind the observer. -/
def doorbell (isOpen : Bool) : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (lower, door .lower isOpen), (upper, door .upper isOpen),
    (observer, .observer ⟨.west, false⟩), (bell, .note ⟨.harp, 0, false⟩)]

/-- The doorbell with the door closed. -/
def circuit : Level := doorbell false

/-- The doorbell with the door open. -/
def opened : Level := doorbell true

/-- The doorbell, door closed, with a stone block on top of the note block. -/
def muffled : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (lower, door .lower false), (upper, door .upper false),
    (observer, .observer ⟨.west, false⟩), (bell, .note ⟨.harp, 0, false⟩),
    (⟨2, 2, 0⟩, .plain .stone)]

/-- A player uses the lower half of the door before game tick 1; five game ticks. -/
def useLower : Schedule := .first [.use lower .up] 5

/-- A player uses the upper half of the door before game tick 1; five game ticks. -/
def useUpper : Schedule := .first [.use upper .up] 5

/-- The three levels as built are at rest. -/
theorem levels_quiescent : circuit.Quiescent ∧ opened.Quiescent ∧ muffled.Quiescent := by
  circuit_decide

assert_standard_axioms levels_quiescent

/-- The blocks of the door, the observer and the note block. -/
def reading (l : Level) : List Block := l.blocksAt [lower, upper, observer, bell]

/-- **Opening the door rings the bell.** After game tick 1 both halves of the door are open
and the observer and the note block are still off; after game ticks 2 and 3 the observer is on
and the note block powered; after game tick 4 both are off again. -/
theorem bell_on_opening :
    reading circuit =
        [door .lower false, door .upper false, .observer ⟨.west, false⟩,
          .note ⟨.harp, 0, false⟩] ∧
      reading (rules.runSchedule (useLower.take 1) circuit) =
        [door .lower true, door .upper true, .observer ⟨.west, false⟩,
          .note ⟨.harp, 0, false⟩] ∧
      reading (rules.runSchedule (useLower.take 2) circuit) =
        [door .lower true, door .upper true, .observer ⟨.west, true⟩, .note ⟨.harp, 0, true⟩] ∧
      reading (rules.runSchedule (useLower.take 3) circuit) =
        [door .lower true, door .upper true, .observer ⟨.west, true⟩, .note ⟨.harp, 0, true⟩] ∧
      reading (rules.runSchedule (useLower.take 4) circuit) =
        [door .lower true, door .upper true, .observer ⟨.west, false⟩,
          .note ⟨.harp, 0, false⟩] ∧
      (rules.runSchedule (useLower.take 4) circuit).overflow = false := by
  circuit_decide

assert_standard_axioms bell_on_opening

/-- **Closing the door rings the bell too.** From the level with the door open, a player uses
the upper half: after game tick 1 both halves are closed; the observer is on and the note
block powered after game ticks 2 and 3, and both are off after game tick 4. -/
theorem bell_on_closing :
    reading (rules.runSchedule (useUpper.take 1) opened) =
        [door .lower false, door .upper false, .observer ⟨.west, false⟩,
          .note ⟨.harp, 0, false⟩] ∧
      reading (rules.runSchedule (useUpper.take 2) opened) =
        [door .lower false, door .upper false, .observer ⟨.west, true⟩,
          .note ⟨.harp, 0, true⟩] ∧
      reading (rules.runSchedule (useUpper.take 3) opened) =
        [door .lower false, door .upper false, .observer ⟨.west, true⟩,
          .note ⟨.harp, 0, true⟩] ∧
      reading (rules.runSchedule (useUpper.take 4) opened) =
        [door .lower false, door .upper false, .observer ⟨.west, false⟩,
          .note ⟨.harp, 0, false⟩] ∧
      (rules.runSchedule (useUpper.take 4) opened).overflow = false := by
  circuit_decide

assert_standard_axioms bell_on_closing

/-- `RandomSource.nextLong()`, the value being dropped: the generator after two draws of 32
bits. This is what one playing of a note block does to the level's random generator. -/
def afterNextLong (r : JavaRandom) : JavaRandom := ((r.next 32).2.next 32).2

/-- **The bell rings exactly once.** In the game tick in which the note block becomes powered
(game tick 2) the level's random generator advances by exactly one `nextLong`, the draw of the
one block event of the note block; in the game ticks after it the generator does not move. No
block event is left queued. The same when the door is closed. -/
theorem rings_once :
    (rules.runSchedule (useLower.take 2) circuit).random =
        afterNextLong (rules.runSchedule (useLower.take 1) circuit).random ∧
      (rules.runSchedule (useLower.take 4) circuit).random =
        (rules.runSchedule (useLower.take 2) circuit).random ∧
      (rules.runSchedule (useLower.take 2) circuit).blockEvents = [] ∧
      (rules.runSchedule (useUpper.take 2) opened).random =
        afterNextLong (rules.runSchedule (useUpper.take 1) opened).random ∧
      (rules.runSchedule (useUpper.take 4) opened).random =
        (rules.runSchedule (useUpper.take 2) opened).random ∧
      (rules.runSchedule (useUpper.take 2) opened).blockEvents = [] ∧
      (rules.runSchedule (useLower.take 4) circuit).overflow = false ∧
      (rules.runSchedule (useUpper.take 4) opened).overflow = false := by
  circuit_decide

assert_standard_axioms rings_once

/-- **A block on top silences the bell.** With a stone block above the note block the pulse is
the same, the note block is powered after game ticks 2 and 3 and unpowered after game tick 4,
but it does not play: the random generator is after game tick 4 what it was after game
tick 1. -/
theorem muffled_bell :
    reading (rules.runSchedule (useLower.take 1) muffled) =
        [door .lower true, door .upper true, .observer ⟨.west, false⟩,
          .note ⟨.harp, 0, false⟩] ∧
      reading (rules.runSchedule (useLower.take 2) muffled) =
        [door .lower true, door .upper true, .observer ⟨.west, true⟩, .note ⟨.harp, 0, true⟩] ∧
      reading (rules.runSchedule (useLower.take 3) muffled) =
        [door .lower true, door .upper true, .observer ⟨.west, true⟩, .note ⟨.harp, 0, true⟩] ∧
      reading (rules.runSchedule (useLower.take 4) muffled) =
        [door .lower true, door .upper true, .observer ⟨.west, false⟩,
          .note ⟨.harp, 0, false⟩] ∧
      (rules.runSchedule (useLower.take 2) muffled).random =
        (rules.runSchedule (useLower.take 1) muffled).random ∧
      (rules.runSchedule (useLower.take 4) muffled).random =
        (rules.runSchedule (useLower.take 1) muffled).random ∧
      (rules.runSchedule (useLower.take 4) muffled).overflow = false := by
  circuit_decide

assert_standard_axioms muffled_bell

/-- The level five game ticks after the door was opened is at rest. -/
theorem quiescent_after_opening : (rules.runSchedule useLower circuit).Quiescent := by
  circuit_decide

assert_standard_axioms quiescent_after_opening

/-- **Nothing rings until the door is used again.** Five game ticks after the door was opened
the blocks are those of the doorbell with the door open, and the level is at rest: the door
stays open, the observer off and the note block unpowered, for ever. -/
theorem rests_after_ringing (n : ℕ) :
    (rules.runSchedule useLower circuit).world = opened.world ∧
      reading (rules.steps n (rules.runSchedule useLower circuit)) =
        [door .lower true, door .upper true, .observer ⟨.west, false⟩,
          .note ⟨.harp, 0, false⟩] ∧
      (rules.steps n (rules.runSchedule useLower circuit)).overflow = false := by
  have hreading : ∀ l : Level, reading (l.advance n) = reading l := fun _ => rfl
  rw [rules.steps_of_quiescent quiescent_after_opening, hreading, Level.overflow_advance]
  circuit_decide

assert_standard_axioms rests_after_ringing

end Redstone.Theorems.Observer.Doorbell
