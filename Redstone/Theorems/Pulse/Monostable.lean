import Redstone.Theorems.Pulse.Trace

/-!
# The torch-and-repeater monostable (rising-edge detector)

The classic rising-edge detector: the output torch is lit while the input is on *and* the
delayed input is not yet on. The input goes two ways to the block `B` that carries the output
torch: inverted by a torch under `B`, and delayed by a repeater that points into `B`. `B` is
powered, and the output torch dark, unless the input is on (the inverting torch is out) and
the repeater has not switched on yet.

```
y = 2 (seen from above, x to the right)        y = 1
          x = 0   x = 1   x = 2                          x = 0   x = 1
z = -2:     d       d                          z = -2:     s       s
z = -1:     d       R                          z = -1:     s       s
z =  0:     L       B       T                  z =  0:     A       I

L: lever, on the stone block A (the input)     s, A: stone
d: redstone dust, from the lever to the repeater
R: repeater, input north, output south into the stone block B
I: the inverting torch, on the east side of A, under B
T: the output torch, on the east side of B
```

The lever is switched on at time 0 (the clock is explained in
`Redstone/Theorems/Pulse/Trace.lean`) and stays on. What is proved, for each delay of the
repeater:

* **delay 3 and 4: one pulse of `2 * delay - 2` game ticks** (`pulse_three`, `pulse_four`):
  the output torch is lit from time 4 to time `2 * delay + 2`, that is 4 or 6 game ticks, and
  then dark while the lever stays on; the level is at rest with the lever on.
  In all four cases the output torch is still in its place, dark, at the end.
* **delay 1 and 2: no pulse** (`pulse_one`, `pulse_two`). The inverting torch goes out in game
  tick 2. With the delay 1 the repeater switches on in the same game tick, so the output torch
  is dark throughout. With the delay 2 the repeater switches on in game tick 4, the game tick
  in which the output torch would light up, and the output torch is still dark after it. (The
  order of the ticks inside a game tick, to which this is due, is not itself part of the
  statements: they are about the levels after each game tick.)
* **nothing on the falling edge** (`release_one` to `release_four`): when the lever is switched
  off, the inverting torch lights up two game ticks later and the repeater goes off after its
  delay; `B` is powered throughout and the output torch stays dark. The level is then at rest
  with the blocks it started with.

The levels are loaded raw, in the state the model settles in when the circuit is built block
by block (the inverting torch lit, the output torch dark), and are at rest
(`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Pulse.Monostable

/-- The position of the lever: the input. -/
def lever : Pos := ⟨0, 2, 0⟩

/-- The position of the repeater that delays the input. -/
def repeater : Pos := ⟨1, 2, -1⟩

/-- The position of the torch that inverts the input. -/
def inverter : Pos := ⟨1, 1, 0⟩

/-- The position of the output torch. -/
def out : Pos := ⟨2, 2, 0⟩

/-- The monostable with the given delay of the repeater, at rest with the lever off. -/
def circuit (delay : IntRange 1 4) : Level :=
  .ofCells [
    (⟨0, 1, 0⟩, .plain .stone), (⟨0, 1, -1⟩, .plain .stone), (⟨0, 1, -2⟩, .plain .stone),
    (⟨1, 1, -2⟩, .plain .stone), (⟨1, 1, -1⟩, .plain .stone), (⟨1, 2, 0⟩, .plain .stone),
    (lever, .lever ⟨.floor, .north, false⟩),
    (⟨0, 2, -1⟩, blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=side,west=none]"),
    (⟨0, 2, -2⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=side,west=none]"),
    (⟨1, 2, -2⟩, blk% "minecraft:redstone_wire[east=none,north=none,power=0,south=side,west=side]"),
    (repeater, .repeater { delay, facing := .north, locked := false, powered := false }),
    (inverter, .redstoneWallTorch ⟨.east, true⟩),
    (out, .redstoneWallTorch ⟨.east, false⟩)]

/-- The monostable with a repeater of delay 1. -/
def circuit1 : Level := circuit ⟨1, by decide, by decide⟩

/-- The monostable with a repeater of delay 2. -/
def circuit2 : Level := circuit ⟨2, by decide, by decide⟩

/-- The monostable with a repeater of delay 3. -/
def circuit3 : Level := circuit ⟨3, by decide, by decide⟩

/-- The monostable with a repeater of delay 4. -/
def circuit4 : Level := circuit ⟨4, by decide, by decide⟩

/-- The lever is switched on before game tick 1 and off before game tick 7; 12 game ticks. -/
def schedule1 : Schedule := .first [.use lever .up] 6 ++ .first [.use lever .up] 6

/-- The lever is switched on before game tick 1 and off before game tick 9; 16 game ticks. -/
def schedule2 : Schedule := .first [.use lever .up] 8 ++ .first [.use lever .up] 8

/-- The lever is switched on before game tick 1 and off before game tick 11; 20 game ticks. -/
def schedule3 : Schedule := .first [.use lever .up] 10 ++ .first [.use lever .up] 10

/-- The lever is switched on before game tick 1 and off before game tick 13; 24 game ticks. -/
def schedule4 : Schedule := .first [.use lever .up] 12 ++ .first [.use lever .up] 12

checkpoints one := schedule1 from circuit1
checkpoints two := schedule2 from circuit2
checkpoints three := schedule3 from circuit3
checkpoints four := schedule4 from circuit4

/-- What is observed: is the lever on, is the repeater powered, is the inverting torch lit, is
the output torch lit. -/
def observe (l : Level) : Bool × Bool × Bool × Bool :=
  (leverOn l lever, repeaterOn l repeater, torchLit l inverter, torchLit l out)

/-- At rest with the lever off: only the inverting torch is lit. -/
def rest : Bool × Bool × Bool × Bool := (false, false, true, false)

/-- The lever is on and nothing has followed yet: the first game tick. -/
def started : Bool × Bool × Bool × Bool := (true, false, true, false)

/-- The lever is on and the inverting torch is out; the output torch has not followed yet. -/
def inverted : Bool × Bool × Bool × Bool := (true, false, false, false)

/-- The output torch is lit: the pulse. -/
def pulse : Bool × Bool × Bool × Bool := (true, false, false, true)

/-- The repeater is on and the output torch is still lit: the two game ticks the output torch
takes to follow the repeater. -/
def pulseEnding : Bool × Bool × Bool × Bool := (true, true, false, true)

/-- The lever and the repeater are on, both torches are out: the state in which the circuit
waits while the input stays on. -/
def waiting : Bool × Bool × Bool × Bool := (true, true, false, false)

/-- The lever is off, the repeater still on, the inverting torch still out. -/
def releasing : Bool × Bool × Bool × Bool := (false, true, false, false)

/-- The lever is off, the repeater still on, the inverting torch lit again. -/
def relit : Bool × Bool × Bool × Bool := (false, true, true, false)

/-- Before the lever is used, each of the four circuits is at rest, with the inverting torch
lit and the output torch dark. -/
theorem circuit_quiescent :
    (circuit1.Quiescent ∧ circuit2.Quiescent ∧ circuit3.Quiescent ∧ circuit4.Quiescent) ∧
      observe circuit1 = rest ∧ observe circuit2 = rest ∧ observe circuit3 = rest ∧
      observe circuit4 = rest := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Delay 1: no pulse.** The inverting torch goes out and the repeater switches on in the
same game tick 2; the output torch stays dark. -/
theorem pulse_one :
    after observe schedule1 circuit1 [1, 2, 3, 4, 5, 6] = [started] ++ List.replicate 5 waiting ∧
      (rules.runSchedule (schedule1.take 6) circuit1).blockAt out =
        .redstoneWallTorch ⟨.east, false⟩ ∧
      (rules.runSchedule (schedule1.take 6) circuit1).Quiescent ∧
      (rules.runSchedule (schedule1.take 6) circuit1).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs one 1 6
  circuit_decide

assert_standard_axioms pulse_one

/-- **Delay 2: no pulse.** The inverting torch goes out in game tick 2; the repeater switches
on in game tick 4, and the output torch is dark after every game tick. -/
theorem pulse_two :
    after observe schedule2 circuit2 [1, 2, 3, 4, 5, 6, 7, 8] =
        [started] ++ List.replicate 2 inverted ++ List.replicate 5 waiting ∧
      (rules.runSchedule (schedule2.take 8) circuit2).blockAt out =
        .redstoneWallTorch ⟨.east, false⟩ ∧
      (rules.runSchedule (schedule2.take 8) circuit2).Quiescent ∧
      (rules.runSchedule (schedule2.take 8) circuit2).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs two 1 8
  circuit_decide

assert_standard_axioms pulse_two

/-- **Delay 3: one pulse of four game ticks.** The output torch is lit after the game ticks 4
to 7 and dark from game tick 8 on, while the lever stays on. After game tick 10 the level is at
rest with the lever on. -/
theorem pulse_three :
    after observe schedule3 circuit3 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] =
        [started] ++ List.replicate 2 inverted ++ List.replicate 2 pulse ++
          List.replicate 2 pulseEnding ++ List.replicate 3 waiting ∧
      (rules.runSchedule (schedule3.take 10) circuit3).blockAt out =
        .redstoneWallTorch ⟨.east, false⟩ ∧
      (rules.runSchedule (schedule3.take 10) circuit3).Quiescent ∧
      (rules.runSchedule (schedule3.take 10) circuit3).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs three 1 10
  circuit_decide

assert_standard_axioms pulse_three

/-- **Delay 4: one pulse of six game ticks.** The output torch is lit after the game ticks 4 to
9 and dark from game tick 10 on, while the lever stays on. After game tick 12 the level is at
rest with the lever on. -/
theorem pulse_four :
    after observe schedule4 circuit4 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] =
        [started] ++ List.replicate 2 inverted ++ List.replicate 4 pulse ++
          List.replicate 2 pulseEnding ++ List.replicate 3 waiting ∧
      (rules.runSchedule (schedule4.take 12) circuit4).blockAt out =
        .redstoneWallTorch ⟨.east, false⟩ ∧
      (rules.runSchedule (schedule4.take 12) circuit4).Quiescent ∧
      (rules.runSchedule (schedule4.take 12) circuit4).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs four 1 12
  circuit_decide

assert_standard_axioms pulse_four

/-- **The input may stay on for ever.** With the delay 4, once the pulse is over the output
torch stays dark for as long as the lever is on. -/
theorem waiting_for_ever (n : ℕ) :
    observe (rules.steps n (rules.runSchedule (schedule4.take 12) circuit4)) = waiting ∧
      (rules.steps n (rules.runSchedule (schedule4.take 12) circuit4)).overflow = false := by
  rw [four_run_12, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, leverOn, repeaterOn, torchLit, Level.blockAt_advance,
    Level.overflow_advance]
  circuit_decide

assert_standard_axioms waiting_for_ever

/-- **Delay 1, the falling edge.** The lever is switched off before game tick 7. In game tick 8
the repeater goes off and the inverting torch lights up; the output torch stays dark, and the
level is at rest with the blocks it started with. -/
theorem release_one :
    after observe schedule1 circuit1 [7, 8, 9, 10, 11, 12] = [releasing] ++ List.replicate 5 rest ∧
      (rules.runSchedule schedule1 circuit1).world = circuit1.world ∧
      (rules.runSchedule schedule1 circuit1).Quiescent ∧
      (rules.runSchedule schedule1 circuit1).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs one 7 12
  rw [one_run]
  circuit_decide

assert_standard_axioms release_one

/-- **Delay 2, the falling edge**: the output torch stays dark. -/
theorem release_two :
    after observe schedule2 circuit2 [9, 10, 11, 12, 13, 14, 15, 16] =
        [releasing] ++ List.replicate 2 relit ++ List.replicate 5 rest ∧
      (rules.runSchedule schedule2 circuit2).world = circuit2.world ∧
      (rules.runSchedule schedule2 circuit2).Quiescent ∧
      (rules.runSchedule schedule2 circuit2).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs two 9 16
  rw [two_run]
  circuit_decide

assert_standard_axioms release_two

/-- **Delay 3, the falling edge**: the output torch stays dark. -/
theorem release_three :
    after observe schedule3 circuit3 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20] =
        [releasing] ++ List.replicate 4 relit ++ List.replicate 5 rest ∧
      (rules.runSchedule schedule3 circuit3).world = circuit3.world ∧
      (rules.runSchedule schedule3 circuit3).Quiescent ∧
      (rules.runSchedule schedule3 circuit3).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs three 11 20
  rw [three_run]
  circuit_decide

assert_standard_axioms release_three

/-- **Delay 4, the falling edge**: the output torch stays dark. -/
theorem release_four :
    after observe schedule4 circuit4 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] =
        [releasing] ++ List.replicate 6 relit ++ List.replicate 5 rest ∧
      (rules.runSchedule schedule4 circuit4).world = circuit4.world ∧
      (rules.runSchedule schedule4 circuit4).Quiescent ∧
      (rules.runSchedule schedule4 circuit4).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs four 13 24
  rw [four_run]
  circuit_decide

assert_standard_axioms release_four

end Redstone.Theorems.Pulse.Monostable
