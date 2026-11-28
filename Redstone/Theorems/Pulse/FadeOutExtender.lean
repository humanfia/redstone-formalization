import Redstone.Theorems.Pulse.Trace

/-!
# The comparator fade-out pulse extender

Two comparators side by side, pointing in opposite directions, joined at both ends by two
pieces of redstone dust: a loop in which a signal goes round and loses strength. Each
comparator passes on the strength it reads, and each pair of dust loses one, so a signal loses
two with every lap of four game ticks. While the input is on the loop is held at full
strength; when the input goes off the signal fades out, and the output stays on until it has
faded to nothing.

```
          x = -1   x = 0   x = 1   x = 2     y = 1, seen from above, x to the right, stone floor
z = 0:      L        a       C1      b       L: lever (the input)
z = 1:               d       C2      c       C1: comparator, back west (a), output east (b)
                                             C2: comparator, back east (c), output west (d)
                                             a, b, c, d: redstone dust; b is the output
```

The clock is explained in `Redstone/Theorems/Pulse/Trace.lean`. What is proved:

* **charging** (`charge`): the lever is switched on at time 0; the output dust `b` has power 15
  from time 2 on, and after game tick 6 the loop is at rest with the powers 15, 15, 14, 14 at
  `a`, `b`, `c`, `d`.
* **the fade-out, lap by lap** (`fade_out`): the lever is switched off at time 6. The powers of
  the four pieces of dust after each of the following 34 game ticks are stated: `a` drops to 13
  at once, and then every two game ticks one comparator passes the lower strength on, so that
  `b` reads 13, 11, 9, 7, 5, 3, 1 for four game ticks each and is dark from game tick 36 on.
* **the exact length for this loop** (`output_trace`): the output dust has power after the game
  ticks 2 to 35 and not after game tick 36. The input ended at time 6: the output outlasts it
  by exactly 30 game ticks, fifteen redstone ticks.
* in the end the level is at rest with the blocks it started with (`back_to_rest`).

A loop with more dust loses more strength per lap and fades faster; only this loop of four
pieces is proved. The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Pulse.FadeOutExtender

/-- The position of the lever: the input. -/
def lever : Pos := ⟨-1, 1, 0⟩

/-- The dust `a`: next to the lever, read by the first comparator. -/
def a : Pos := ⟨0, 1, 0⟩

/-- The dust `b`: at the output of the first comparator. This is the output of the circuit. -/
def b : Pos := ⟨2, 1, 0⟩

/-- The dust `c`: read by the second comparator. -/
def c : Pos := ⟨2, 1, 1⟩

/-- The dust `d`: at the output of the second comparator. -/
def d : Pos := ⟨0, 1, 1⟩

/-- The 4×2 stone floor. -/
def floor : List (Pos × Block) :=
  (List.range 4).flatMap fun x =>
    (List.range 2).map fun z => (⟨(x : ℤ) - 1, 0, z⟩, Block.plain .stone)

/-- The loop of two comparators and four pieces of dust, with the lever next to it, everything
off. -/
def circuit : Level :=
  .ofCells (floor ++ [
    (lever, .lever ⟨.floor, .north, false⟩),
    (a, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=side,west=side]"),
    (⟨1, 1, 0⟩, .comparator ⟨.west, .compare, false⟩),
    (b, blk% "minecraft:redstone_wire[east=none,north=none,power=0,south=side,west=side]"),
    (c, blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=none,west=side]"),
    (⟨1, 1, 1⟩, .comparator ⟨.east, .compare, false⟩),
    (d, blk% "minecraft:redstone_wire[east=side,north=side,power=0,south=none,west=none]")])

/-- The lever is switched on before game tick 1 and off before game tick 7; 40 game ticks. -/
def schedule : Schedule := .first [.use lever .up] 6 ++ .first [.use lever .up] 34

checkpoints state := schedule from circuit

/-- What is observed: is the lever on, and the powers of the dust at `a`, `b`, `c`, `d`. -/
def observe (l : Level) : Bool × ℕ × ℕ × ℕ × ℕ :=
  (leverOn l lever, l.dustPower a, l.dustPower b, l.dustPower c, l.dustPower d)

/-- Has the output dust power? -/
def outputOn (l : Level) : Bool := decide (0 < l.dustPower b)

/-- One lap of four game ticks in which the output `b` has power `s`: for two game ticks the
second comparator still gives `s + 1`, then it has followed and `a` reads `s - 2`. -/
def lap (s : ℕ) : List (Bool × ℕ × ℕ × ℕ × ℕ) :=
  [(false, s, s, s - 1, s + 1), (false, s, s, s - 1, s + 1),
    (false, s - 2, s, s - 1, s - 1), (false, s - 2, s, s - 1, s - 1)]

/-- The circuit as built is at rest, with everything off. -/
theorem circuit_quiescent : circuit.Quiescent ∧ observe circuit = (false, 0, 0, 0, 0) := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Charging.** The lever is switched on before game tick 1. The first comparator switches
on in game tick 2 and the output has power 15 from then on; after game tick 6 the loop is at
rest at full strength. -/
theorem charge :
    after observe schedule circuit [1, 2, 3, 4, 5, 6] =
        [(true, 15, 0, 0, 14)] ++ List.replicate 5 (true, 15, 15, 14, 14) ∧
      (rules.runSchedule (schedule.take 6) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 6) circuit).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs state 1 6
  circuit_decide

assert_standard_axioms charge

/-- **While the input is on the loop keeps its strength**, for ever. -/
theorem charged_for_ever (n : ℕ) :
    observe (rules.steps n (rules.runSchedule (schedule.take 6) circuit)) =
        (true, 15, 15, 14, 14) ∧
      (rules.steps n (rules.runSchedule (schedule.take 6) circuit)).overflow = false := by
  rw [state_run_6, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, leverOn, Level.blockAt_advance, Level.dustPower_advance,
    Level.overflow_advance]
  circuit_decide

assert_standard_axioms charged_for_ever

/-- **The fade-out.** The lever is switched off before game tick 7. After game tick 7 the dust
`a` has dropped to 13 and the rest of the loop has not followed yet; then come seven laps of
four game ticks in which the output has the powers 13, 11, 9, 7, 5, 3, 1; after game tick 36
all four pieces of dust are dark. -/
theorem fade_out :
    after observe schedule circuit (List.range' 7 34) =
        [(false, 13, 15, 14, 14)] ++ [13, 11, 9, 7, 5, 3, 1].flatMap lap ++
          List.replicate 5 (false, 0, 0, 0, 0) ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [show List.range' 7 34 = [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
    24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40] from by decide]
  simp only [after, List.map_cons, List.map_nil]
  rw_runs state 7 40
  rw [state_run]
  circuit_decide

assert_standard_axioms fade_out

/-- **The output outlasts the input by 30 game ticks.** The lever is on after the game ticks 1
to 6. The output dust has power after each of the game ticks 2 to 35, and none after the game
ticks 36 to 40. -/
theorem output_trace :
    after outputOn schedule circuit (List.range' 1 40) =
      [false] ++ List.replicate 34 true ++ List.replicate 5 false := by
  rw [show List.range' 1 40 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
    19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40]
    from by decide]
  simp only [after, List.map_cons, List.map_nil]
  rw_runs state 1 40
  circuit_decide

assert_standard_axioms output_trace

/-- After the fade-out the blocks are those the circuit started with, and the level is at
rest: the output stays dark for ever. -/
theorem back_to_rest (n : ℕ) :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      observe (rules.steps n (rules.runSchedule schedule circuit)) = (false, 0, 0, 0, 0) ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, leverOn, Level.blockAt_advance, Level.dustPower_advance,
    Level.overflow_advance]
  circuit_decide

assert_standard_axioms back_to_rest

end Redstone.Theorems.Pulse.FadeOutExtender
