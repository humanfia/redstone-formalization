import Redstone.Proof.Circuit

/-!
# The bell: one ring per rising edge

A bell standing on a stone block, with a lever on the floor next to it:

```
y = 1:   L  B        x = 0: lever, on stone
y = 0:   S  S        x = 1: bell (attachment `floor`, facing north), on stone
```

`BellBlock.neighborChanged` compares the signal with the property `powered`; when they differ
it stores the signal, and if the signal has just appeared it rings the bell
(`attemptToRing`), which queues the block event `(bell, 1, direction)`. The event runs later
in the same game tick; what it does there (the swing of the bell, the sound, the glow of
raiders) is not kept by the model, so the ring is observed as the block event in the queue
right after the input, before the game tick runs.

| before game tick | input | `powered` | block event queued |
|---|---|---|---|
| 1 | lever on | true | one ring |
| 3 | lever off | false | none |
| 5 | lever on | true | one ring |
| 7 | the bell is used on its north face | true | one ring |

So the bell rings once per rising edge of its signal, not on the falling edge and not while
the signal stays, and a player can still ring it while it is powered.

The level is loaded raw. It is not quiescent in the sense of `Level.Quiescent`, because the
bell has a ticking block entity (`BellBlockEntity.serverTick`); the statements are about the
eight game ticks of the schedule, and `idle_is_silent` shows that the level as built does
nothing in a game tick.
-/

set_option Elab.async false

namespace Redstone.Theorems.RailMisc.Bell

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The position of the bell. -/
def bell : Pos := ⟨1, 1, 0⟩

/-- The lever, on or off. -/
def leverState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- The bell on the floor, facing north. -/
def bellState (powered : Bool) : Block := .bell ⟨.floor, .north, powered⟩

/-- The lever and the bell, on stone. -/
def circuit : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (⟨1, 0, 0⟩, .plain .stone), (lever, leverState false),
    (bell, bellState false)]

/-- The lever is used before game ticks 1, 3 and 5, the bell itself before game tick 7; eight
game ticks in all. -/
def schedule : Schedule :=
  .first [.use lever .up] 2 ++ .first [.use lever .up] 2 ++ .first [.use lever .up] 2 ++
    .first [.use bell .north] 2

checkpoints state := schedule from circuit

/-- The block event of a ring in the direction the bell faces (north, data value 2), which is
also the direction of a hit on its north face. -/
def ring : BlockEvent := ⟨bell, .bell, 1, 2⟩

/-- **Nothing happens by itself.** A game tick without input leaves the blocks of the level as
built as they are, and queues nothing. -/
theorem idle_is_silent :
    (rules.step circuit).world = circuit.world ∧ (rules.step circuit).blockEvents = [] ∧
      (rules.step circuit).pending = [] ∧ (rules.step circuit).overflow = false := by
  circuit_decide

assert_standard_axioms idle_is_silent

/-- **The rising edge rings once.** Using the lever queues exactly one ring before the game
tick runs; after the game tick the bell is `powered` and the queue is empty. The next game
tick, with the signal still there, queues nothing. -/
theorem rising_edge_rings :
    (rules.input (.use lever .up) circuit).blockEvents = [ring] ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt [lever, bell] =
        [leverState true, bellState true] ∧
      (rules.runSchedule (schedule.take 1) circuit).blockEvents = [] ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt [lever, bell] =
        [leverState true, bellState true] ∧
      (rules.runSchedule (schedule.take 2) circuit).blockEvents = [] ∧
      (rules.runSchedule (schedule.take 2) circuit).overflow = false := by
  rw [state_run_1, state_run_2]
  circuit_decide

assert_standard_axioms rising_edge_rings

/-- **The falling edge does not ring.** Switching the lever off (before game tick 3) queues no
block event; the bell is no longer `powered`. -/
theorem falling_edge_is_silent :
    (rules.input (.use lever .up) (rules.runSchedule (schedule.take 2) circuit)).blockEvents =
        [] ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt [lever, bell] =
        [leverState false, bellState false] ∧
      (rules.runSchedule (schedule.take 4) circuit).blockEvents = [] ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_2, state_run_3, state_run_4]
  circuit_decide

assert_standard_axioms falling_edge_is_silent

/-- **Once per rising edge.** The second time the lever is switched on (before game tick 5),
one ring is queued again. -/
theorem second_rising_edge_rings :
    (rules.input (.use lever .up) (rules.runSchedule (schedule.take 4) circuit)).blockEvents =
        [ring] ∧
      (rules.runSchedule (schedule.take 5) circuit).blocksAt [lever, bell] =
        [leverState true, bellState true] ∧
      (rules.runSchedule (schedule.take 6) circuit).blockEvents = [] ∧
      (rules.runSchedule (schedule.take 6) circuit).overflow = false := by
  rw [state_run_4, state_run_5, state_run_6]
  circuit_decide

assert_standard_axioms second_rising_edge_rings

/-- **A powered bell can still be rung by hand.** Used on its north face before game tick 7,
while the lever is on, the bell queues one ring; its state does not change. -/
theorem use_rings_while_powered :
    (rules.input (.use bell .north) (rules.runSchedule (schedule.take 6) circuit)).blockEvents =
        [ring] ∧
      (rules.runSchedule schedule circuit).blocksAt [lever, bell] =
        [leverState true, bellState true] ∧
      (rules.runSchedule schedule circuit).blockEvents = [] ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_6, state_run]
  circuit_decide

assert_standard_axioms use_rings_while_powered

end Redstone.Theorems.RailMisc.Bell
