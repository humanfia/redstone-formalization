import Redstone.Proof.Circuit

/-!
# Redstone lamp and copper bulb on one lever

A lever on a stone block with a redstone lamp to its east and a (waxed) copper bulb to its
west; a comparator reads the bulb.

```
y = 1:   C  B  L  M        x = -2: comparator (on stone), reads the bulb to its east
y = 0:   S     S           x = -1: copper bulb    x = 0: lever (on stone)    x = 1: lamp
```

Both blocks see the same signal, and they do different things with it:

* The **lamp** follows the signal: lit in the game tick in which the signal appears, dark four
  game ticks (two redstone ticks) after it is gone (`RedstoneLampBlock`).
* The **bulb** counts rising edges: it switches its light in the game tick in which the signal
  appears and does nothing when the signal goes (`CopperBulbBlock.checkAndFlip`); `powered`
  follows the signal. Two pulses bring it back to where it was: it is a T flip-flop in one
  block.
* The **comparator** reads 15 from a lit bulb and 0 from a dark one, two game ticks after the
  bulb switched.

| before game tick | lever | lamp | bulb `lit` | bulb `powered` | comparator |
|---|---|---|---|---|---|
| 1 | on | lit at 1 | true at 1 | true | 15 at 2 |
| 3 | off | dark at 6 | true | false | 15 |
| 9 | on | lit at 9 | false at 9 | true | 0 at 10 |
| 11 | off | dark at 14 | false | false | 0 |

The level is loaded raw with everything off; `circuit_quiescent` shows that this is a state of
rest. Only the waxed bulb is used: the unwaxed ones behave alike until they oxidise, which is
a random tick.
-/

set_option Elab.async false

namespace Redstone.Theorems.RailMisc.LampAndBulb

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The position of the lamp. -/
def lamp : Pos := ⟨1, 1, 0⟩

/-- The position of the copper bulb. -/
def bulb : Pos := ⟨-1, 1, 0⟩

/-- The position of the comparator that reads the bulb. -/
def comparator : Pos := ⟨-2, 1, 0⟩

/-- The lever, on or off. -/
def leverState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- The lamp, lit or dark. -/
def lampState (lit : Bool) : Block := .redstoneLamp ⟨lit⟩

/-- The waxed copper bulb with the given `lit` and `powered`. -/
def bulbState (lit powered : Bool) : Block := .copperBulb .waxed_copper_bulb ⟨lit, powered⟩

/-- The comparator, facing the bulb, in compare mode. -/
def comparatorState (powered : Bool) : Block := .comparator ⟨.east, .compare, powered⟩

/-- The lever with the lamp and the bulb, and the comparator behind the bulb. -/
def circuit : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (⟨-2, 0, 0⟩, .plain .stone), (lever, leverState false),
    (lamp, lampState false), (bulb, bulbState false false),
    (comparator, comparatorState false)]

/-- Two pulses of the lever, each two game ticks long, six game ticks apart: the lever is used
before game ticks 1, 3, 9 and 11; sixteen game ticks in all. -/
def schedule : Schedule :=
  .first [.use lever .up] 2 ++ .first [.use lever .up] 6 ++ .first [.use lever .up] 2 ++
    .first [.use lever .up] 6

checkpoints state := schedule from circuit

/-- The observed blocks: lever, lamp, bulb, comparator. -/
def cells : List Pos := [lever, lamp, bulb, comparator]

/-- With everything off the level is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **First rising edge: both light at once.** In the game tick in which the lever is switched
on, the lamp is lit and the bulb is lit and `powered`. The comparator follows two game ticks
after the bulb: off after game tick 1, on and reading 15 after game tick 2. -/
theorem first_rising_edge :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt cells =
        [leverState true, lampState true, bulbState true true, comparatorState false] ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt cells =
        [leverState true, lampState true, bulbState true true, comparatorState true] ∧
      (rules.runSchedule (schedule.take 2) circuit).blockEntities comparator =
        some (.comparator ⟨15⟩) ∧
      (rules.runSchedule (schedule.take 2) circuit).overflow = false := by
  rw [state_run_1, state_run_2]
  circuit_decide

assert_standard_axioms first_rising_edge

/-- **First falling edge: the lamp goes dark after four game ticks, the bulb stays lit.** The
lever is switched off before game tick 3. The bulb only clears `powered`, at once. The lamp is
still lit after game ticks 3, 4 and 5 and dark after game tick 6. The comparator keeps reading
15. -/
theorem first_falling_edge :
    (rules.runSchedule (schedule.take 3) circuit).blocksAt cells =
        [leverState false, lampState true, bulbState true false, comparatorState true] ∧
      (rules.runSchedule (schedule.take 4) circuit).blockAt lamp = lampState true ∧
      (rules.runSchedule (schedule.take 5) circuit).blockAt lamp = lampState true ∧
      (rules.runSchedule (schedule.take 6) circuit).blocksAt cells =
        [leverState false, lampState false, bulbState true false, comparatorState true] ∧
      (rules.runSchedule (schedule.take 6) circuit).blockEntities comparator =
        some (.comparator ⟨15⟩) ∧
      (rules.runSchedule (schedule.take 6) circuit).overflow = false := by
  rw [state_run_3, state_run_4, state_run_5, state_run_6]
  circuit_decide

assert_standard_axioms first_falling_edge

/-- **After one pulse the bulb remembers it**, for ever: the lever is off, the lamp is dark,
the bulb is lit and the comparator reads 15. The level is at rest after game tick 8. -/
theorem one_pulse_is_remembered (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 8) circuit)).blocksAt cells =
        [leverState false, lampState false, bulbState true false, comparatorState true] ∧
      (rules.steps n (rules.runSchedule (schedule.take 8) circuit)).overflow = false := by
  rw [state_run_8, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms one_pulse_is_remembered

/-- **Second rising edge: the lamp lights, the bulb goes dark.** The lever is switched on
before game tick 9; in that game tick the lamp is lit and the bulb is dark and `powered`. The
comparator is off and reads 0 after game tick 10. -/
theorem second_rising_edge :
    (rules.runSchedule (schedule.take 9) circuit).blocksAt cells =
        [leverState true, lampState true, bulbState false true, comparatorState true] ∧
      (rules.runSchedule (schedule.take 10) circuit).blocksAt cells =
        [leverState true, lampState true, bulbState false true, comparatorState false] ∧
      (rules.runSchedule (schedule.take 10) circuit).blockEntities comparator =
        some (.comparator ⟨0⟩) ∧
      (rules.runSchedule (schedule.take 10) circuit).overflow = false := by
  rw [state_run_9, state_run_10]
  circuit_decide

assert_standard_axioms second_rising_edge

/-- **Second falling edge, and back to the start.** The lever is switched off before game tick
11; the lamp is lit after game tick 13 and dark after game tick 14. After the whole schedule
the blocks are those the level started with, the level is at rest, and it stays so for
ever: two pulses bring the bulb back. -/
theorem two_pulses_restore (n : ℕ) :
    (rules.runSchedule (schedule.take 11) circuit).blocksAt cells =
        [leverState false, lampState true, bulbState false false, comparatorState false] ∧
      (rules.runSchedule (schedule.take 13) circuit).blockAt lamp = lampState true ∧
      (rules.runSchedule (schedule.take 14) circuit).blockAt lamp = lampState false ∧
      (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.steps n (rules.runSchedule schedule circuit)).blocksAt cells =
        [leverState false, lampState false, bulbState false false, comparatorState false] ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run_11, state_run_13, state_run_14, state_run,
    rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms two_pulses_restore

end Redstone.Theorems.RailMisc.LampAndBulb
