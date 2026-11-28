import Redstone.Theorems.Pulse.Trace

/-!
# The locked-repeater falling-edge detector

The repeater-locking design. The output repeater `O` reads the input through a delaying
repeater `D`, and a third repeater `K`, which reads the input directly, points into the side
of `O` and locks it. While the input is on, `K` holds `O` locked in the off state. When the
input goes off, `K` releases `O` while the delayed input is still on (or was on when `O`
looked): `O` schedules its tick, switches on two game ticks later, finds its input gone and
switches off again after its own delay. That is one pulse of one redstone tick on the falling
edge, and nothing on the rising edge.

```
          x = -1   x = 0        y = 1, seen from above, x to the right, on a stone floor
z = 0:      d        O          L: lever (the input)      d: redstone dust
z = 1:      D        K          D: repeater, input south, output north (the delay)
z = 2:      d        L          K: repeater, delay 1, input south, output north into the side of O
                                O: repeater, delay 1, input west, output east (the output)
```

The clock is explained in `Redstone/Theorems/Pulse/Trace.lean`. What is proved, for the delays
1 and 2 of `D`:

* **nothing on the rising edge** (`rising_one`, `rising_two`): the lever is switched on at time
  0; `O` is locked from time 2 on and never switches on; the level is at rest with the lever
  on.
* **one pulse of two game ticks on the falling edge** (`falling_one`, `falling_two`): the lever
  is switched off at time 6; `O` is on from time 10 to time 12, four game ticks after the
  edge, and the level is then at rest with the blocks it started with.
* **the input may be short** (`short_input`): with an input pulse of two game ticks (on at time
  0, off at time 2) the output pulse is the same, from time 6 to time 8.

With the delay 1 this works although `D` and `K` go off in the same game tick: `K` ticks first
(a repeater that points into the side of another diode ticks with the highest priority), so
`O` is released while the dust behind `D` still has power.

A design that *shortens* a pulse with a locked repeater (a pulse limiter) is not proved here:
a lock freezes the state of a repeater, so a repeater that is on when it is locked stays on.
The pulse limiters of this directory are `ComparatorLimiter.lean` and `Monostable.lean`.

The levels are loaded raw and are at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Pulse.FallingEdgeLock

/-- The position of the lever: the input. -/
def lever : Pos := ⟨0, 1, 2⟩

/-- The position of the repeater that delays the input. -/
def delayer : Pos := ⟨-1, 1, 1⟩

/-- The position of the repeater that locks the output repeater. -/
def lock : Pos := ⟨0, 1, 1⟩

/-- The position of the output repeater. -/
def out : Pos := ⟨0, 1, 0⟩

/-- The 2×3 stone floor. -/
def floor : List (Pos × Block) :=
  (List.range 2).flatMap fun x =>
    (List.range 3).map fun z => (⟨(x : ℤ) - 1, 0, z⟩, Block.plain .stone)

/-- The detector with the given delay of the delaying repeater, everything off. -/
def circuit (delay : IntRange 1 4) : Level :=
  .ofCells (floor ++ [
    (lever, .lever ⟨.floor, .north, false⟩),
    (⟨-1, 1, 2⟩,
      blk% "minecraft:redstone_wire[east=side,north=side,power=0,south=none,west=none]"),
    (delayer, .repeater { delay, facing := .south, locked := false, powered := false }),
    (⟨-1, 1, 0⟩,
      blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=side,west=none]"),
    (lock, blk% "minecraft:repeater[delay=1,facing=south,locked=false,powered=false]"),
    (out, blk% "minecraft:repeater[delay=1,facing=west,locked=false,powered=false]")])

/-- The detector with a delaying repeater of delay 1. -/
def circuit1 : Level := circuit ⟨1, by decide, by decide⟩

/-- The detector with a delaying repeater of delay 2. -/
def circuit2 : Level := circuit ⟨2, by decide, by decide⟩

/-- The lever is switched on before game tick 1 and off before game tick 7; 16 game ticks. -/
def schedule : Schedule := .first [.use lever .up] 6 ++ .first [.use lever .up] 10

/-- The lever is switched on before game tick 1 and off before game tick 3; 12 game ticks. -/
def shortSchedule : Schedule := .first [.use lever .up] 2 ++ .first [.use lever .up] 10

checkpoints one := schedule from circuit1
checkpoints two := schedule from circuit2
checkpoints short := shortSchedule from circuit1

/-- What is observed: is the lever on, is the delaying repeater on, is the locking repeater
on, is the output repeater locked, is the output repeater on. -/
def observe (l : Level) : Bool × Bool × Bool × Bool × Bool :=
  (leverOn l lever, repeaterOn l delayer, repeaterOn l lock, repeaterLocked l out,
    repeaterOn l out)

/-- Everything is off. -/
def off : Bool × Bool × Bool × Bool × Bool := (false, false, false, false, false)

/-- The lever is on and nothing has followed yet: the first game tick. -/
def started : Bool × Bool × Bool × Bool × Bool := (true, false, false, false, false)

/-- The lever and the locking repeater are on, the delaying repeater not yet: the output
repeater is locked, off. -/
def locking : Bool × Bool × Bool × Bool × Bool := (true, false, true, true, false)

/-- The lever and both repeaters are on, the output repeater is locked, off: the state in
which the detector waits while the input is on. -/
def armed : Bool × Bool × Bool × Bool × Bool := (true, true, true, true, false)

/-- The lever is off and the repeaters have not followed yet. -/
def releasing : Bool × Bool × Bool × Bool × Bool := (false, true, true, true, false)

/-- The lock is released and the delaying repeater is still on (delay 2). -/
def released : Bool × Bool × Bool × Bool × Bool := (false, true, false, false, false)

/-- The output repeater is on, alone: the pulse. -/
def pulse : Bool × Bool × Bool × Bool × Bool := (false, false, false, false, true)

/-- Before the lever is used, both circuits are at rest, with everything off. -/
theorem circuit_quiescent :
    circuit1.Quiescent ∧ circuit2.Quiescent ∧ observe circuit1 = off ∧ observe circuit2 = off := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Delay 1, the rising edge: no pulse.** The output repeater is locked in game tick 2 and
stays off; after game tick 6 the level is at rest with the lever on. -/
theorem rising_one :
    after observe schedule circuit1 [1, 2, 3, 4, 5, 6] = [started] ++ List.replicate 5 armed ∧
      (rules.runSchedule (schedule.take 6) circuit1).Quiescent ∧
      (rules.runSchedule (schedule.take 6) circuit1).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs one 1 6
  circuit_decide

assert_standard_axioms rising_one

/-- **Delay 2, the rising edge: no pulse.** The output repeater is locked in game tick 2, two
game ticks before the delayed input reaches it, and stays off. -/
theorem rising_two :
    after observe schedule circuit2 [1, 2, 3, 4, 5, 6] =
        [started] ++ List.replicate 2 locking ++ List.replicate 3 armed ∧
      (rules.runSchedule (schedule.take 6) circuit2).Quiescent ∧
      (rules.runSchedule (schedule.take 6) circuit2).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs two 1 6
  circuit_decide

assert_standard_axioms rising_two

/-- **The input may stay on for ever**: with the delay 1, the output repeater stays off, and
locked, for as long as the lever is on. -/
theorem armed_for_ever (n : ℕ) :
    observe (rules.steps n (rules.runSchedule (schedule.take 6) circuit1)) = armed ∧
      (rules.steps n (rules.runSchedule (schedule.take 6) circuit1)).overflow = false := by
  rw [one_run_6, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, leverOn, repeaterOn, repeaterLocked, Level.blockAt_advance,
    Level.overflow_advance]
  circuit_decide

assert_standard_axioms armed_for_ever

/-- **Delay 1, the falling edge: one pulse of two game ticks.** The lever is switched off
before game tick 7. In game tick 8 the lock is released and the delaying repeater goes off; the
output repeater is on after the game ticks 10 and 11, and off from game tick 12 on. The level
is then at rest with the blocks it started with. -/
theorem falling_one :
    after observe schedule circuit1 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16] =
        [releasing] ++ List.replicate 2 off ++ List.replicate 2 pulse ++ List.replicate 5 off ∧
      (rules.runSchedule schedule circuit1).world = circuit1.world ∧
      (rules.runSchedule schedule circuit1).Quiescent ∧
      (rules.runSchedule schedule circuit1).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs one 7 16
  rw [one_run]
  circuit_decide

assert_standard_axioms falling_one

/-- **Delay 2, the falling edge: one pulse of two game ticks**, after the game ticks 10 and
11: the lock is released in game tick 8, while the delaying repeater is still on. -/
theorem falling_two :
    after observe schedule circuit2 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16] =
        [releasing] ++ List.replicate 2 released ++ List.replicate 2 pulse ++
          List.replicate 5 off ∧
      (rules.runSchedule schedule circuit2).world = circuit2.world ∧
      (rules.runSchedule schedule circuit2).Quiescent ∧
      (rules.runSchedule schedule circuit2).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs two 7 16
  rw [two_run]
  circuit_decide

assert_standard_axioms falling_two

/-- **An input pulse of two game ticks** (delay 1): the lever is on after the game ticks 1 and
2. The output repeater is locked in game tick 2 and gives its pulse after the game ticks 6 and
7, four game ticks after the falling edge. -/
theorem short_input :
    after observe shortSchedule circuit1 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] =
        [started, armed, releasing] ++ List.replicate 2 off ++ List.replicate 2 pulse ++
          List.replicate 5 off ∧
      (rules.runSchedule shortSchedule circuit1).world = circuit1.world ∧
      (rules.runSchedule shortSchedule circuit1).Quiescent ∧
      (rules.runSchedule shortSchedule circuit1).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs short 1 12
  rw [short_run]
  circuit_decide

assert_standard_axioms short_input

end Redstone.Theorems.Pulse.FallingEdgeLock
