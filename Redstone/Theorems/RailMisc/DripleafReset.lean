import Redstone.Proof.Circuit

/-!
# A redstone signal resets the tilt of a big dripleaf

A big dripleaf on clay, fully tilted, with a lever on the floor next to it:

```
y = 1:   L  F        x = 0: lever, on stone
y = 0:   S  C        x = 1: big dripleaf (tilt `full`), on clay
```

A big dripleaf tilts under an entity that stands on it or when a projectile hits it, and
comes back by itself after a while. A redstone signal brings it back at once and keeps it
level: `BigDripleafBlock.neighborChanged` resets the tilt whenever the leaf has a signal.

* Lever on: the tilt is `none` in the same game tick. The reset of a tilted leaf plays a
  sound, which draws one `nextFloat()` from the level's random generator.
* The leaf stays level while the lever is on and after it is switched off.
* Lever on again, with the leaf already level: nothing changes and nothing is drawn.

The level is loaded raw, with the leaf tilted as a projectile leaves it but without the
scheduled tick that would bring it back after 100 game ticks: it is the leaf a `/setblock`
gives, and it is at rest (`circuit_quiescent`). How a leaf gets tilted, and its way back by
scheduled ticks, start from an entity and are out of reach of these proofs (`Overview`).
-/

set_option Elab.async false

namespace Redstone.Theorems.RailMisc.DripleafReset

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The position of the leaf. -/
def leaf : Pos := ⟨1, 1, 0⟩

/-- The lever, on or off. -/
def leverState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- The big dripleaf with the given tilt. -/
def leafState (tilt : Tilt) : Block := .bigDripleaf ⟨.north, tilt, false⟩

/-- The lever and the fully tilted leaf. -/
def circuit : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (⟨1, 0, 0⟩, .plain .clay), (lever, leverState false),
    (leaf, leafState .full)]

/-- The lever is switched on before game tick 1, off before game tick 3 and on again before
game tick 5; six game ticks in all. -/
def schedule : Schedule :=
  .first [.use lever .up] 2 ++ .first [.use lever .up] 2 ++ .first [.use lever .up] 2

checkpoints state := schedule from circuit

/-- The level's random generator after the sound of one reset: one `nextFloat()`. -/
def afterOneSound : JavaRandom := circuit.random.nextFloat24.2

/-- The tilted leaf without a signal is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- Without a signal the leaf loaded here stays tilted for ever (it has no scheduled tick). -/
theorem tilted_stays (n : ℕ) :
    (rules.steps n circuit).blockAt leaf = leafState .full ∧
      (rules.steps n circuit).overflow = false := by
  rw [rules.blockAt_steps_of_quiescent circuit_quiescent,
    rules.overflow_steps_of_quiescent circuit_quiescent]
  circuit_decide

assert_standard_axioms tilted_stays

/-- **The signal resets the tilt at once.** In the game tick in which the lever is switched
on, the leaf is level, and one sound has been played. -/
theorem signal_resets :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt [lever, leaf] =
        [leverState true, leafState .none] ∧
      (rules.runSchedule (schedule.take 1) circuit).random = afterOneSound ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms signal_resets

/-- **The leaf stays level** while the lever is on, for ever. -/
theorem level_while_on (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).blockAt leaf =
        leafState .none ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).overflow = false := by
  rw [state_run_1, rules.blockAt_steps_of_quiescent (by circuit_decide),
    rules.overflow_steps_of_quiescent (by circuit_decide)]
  circuit_decide

assert_standard_axioms level_while_on

/-- **Switching the lever off, and on again, changes nothing more.** After the lever is
switched off (before game tick 3) the leaf is still level; when it is switched on again
(before game tick 5) the leaf is level and no further sound is played. After the schedule the
level is at rest and the leaf stays level for ever. -/
theorem level_afterwards (n : ℕ) :
    (rules.runSchedule (schedule.take 3) circuit).blocksAt [lever, leaf] =
        [leverState false, leafState .none] ∧
      (rules.runSchedule (schedule.take 5) circuit).blocksAt [lever, leaf] =
        [leverState true, leafState .none] ∧
      (rules.runSchedule schedule circuit).random = afterOneSound ∧
      (rules.steps n (rules.runSchedule schedule circuit)).blockAt leaf = leafState .none ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run_3, state_run_5, state_run, rules.blockAt_steps_of_quiescent (by circuit_decide),
    rules.overflow_steps_of_quiescent (by circuit_decide)]
  circuit_decide

assert_standard_axioms level_afterwards

end Redstone.Theorems.RailMisc.DripleafReset
