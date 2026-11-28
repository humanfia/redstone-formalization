import Redstone.Theorems.Memory.Observe

/-!
# A JK flip-flop from repeater latches and two subtracting comparators

The D flip-flop of `DFlipFlop.lean` (master and slave repeater, locked by the clock and by the
inverted clock) with its data input computed from `J`, `K` and `Q`:

`D = (J and not Q) or (Q and not K)`.

Each of the two terms is one comparator in subtraction mode, whose output is its rear input
minus its side input: `J - Q` and `Q - K`, with all signals 0 or 15. Both comparators point
into the one piece of dust in front of the master, which takes the stronger of the two.

```
z = -2:  .  .  .  C  T  .      C: stone block with the clock lever on top, T: torch on its east side
z = -1:  .  .  .  v  v  .      v: the two lock repeaters, pointing south
z =  0:  J  a  d  M  S  X      J: lever, a: comparator J - Q pointing east, d: dust,
                               M: master, S: slave (pointing east), X: stone (powered by Q)
z =  1:  .  ^  b  <  K  v      ^: repeater pointing north into the side of a,
                               b: comparator Q - K pointing north, <: repeater pointing west
                               into the side of b, K: lever, v: repeater pointing south, from
                               X into Z
z =  2:  .  e  W  <  <  Z      Z: stone, <: two repeaters pointing west, W: stone (powered by
                               Q, the rear input of b), e: dust next to W, read by the repeater
                               x from -2 to 3; y = 1, seen from above
```

So with `Q = 0` the master sees `J`, and with `Q = 1` it sees `not K`: `J = K = 0` holds,
`J = 1, K = 0` sets, `J = 0, K = 1` resets and `J = K = 1` toggles, on the rising edge of the
clock. The feedback of `Q` to the dust takes up to 14 game ticks; the master is locked during
that time, so each edge acts once.

This is not the classic design made of torches only (see `Redstone/Theorems/Memory/Index.lean`
for what is not proved).

What is proved (`Q` is the `powered` property of the slave):

* **The full table**: for every `(J, K, Q)`, from a level at rest with the clock low, the
  clock lever is switched on, and `Q` after the edge is as the table of the JK flip-flop says
  (`hold_zero`, `reset_zero`, `set_zero`, `hold_one`, `set_one`, `reset_one`,
  `toggle_zero`, `toggle_one`). When `Q` changes, the slave switches in the fifth game tick
  after the lever (the lever is used before game tick `k`, the slave switches in game tick
  `k + 5`).
* **After the edge `Q` holds** for the rest of the clock pulse and after it: `Q` is the same
  17 game ticks after each edge, with the clock still high, and after the falling edge
  (`holds_after_edge`); and for ever in a level at rest with the clock high after a toggle
  (`toggled_holds`).
* After the whole schedule the blocks and block entities are those the circuit started with
  (`back_to_start`).

The level is loaded raw, with all three levers off and `Q = 0`; it is at rest
(`circuit_quiescent`), and it is the state the circuit itself returns to.
-/

set_option Elab.async false

namespace Redstone.Theorems.Memory.JKFlipFlop

/-- The lever `J`. -/
def leverJ : Pos := ⟨-2, 1, 0⟩

/-- The lever `K`. -/
def leverK : Pos := ⟨2, 1, 1⟩

/-- The clock lever, on top of the clock block. -/
def clockLever : Pos := ⟨1, 2, -2⟩

/-- The master repeater. -/
def master : Pos := ⟨1, 1, 0⟩

/-- The slave repeater: its `powered` property is `Q`. -/
def slave : Pos := ⟨2, 1, 0⟩

/-- The comparator that computes `J - Q`. -/
def comparatorJ : Pos := ⟨-1, 1, 0⟩

/-- The comparator that computes `Q - K`. -/
def comparatorK : Pos := ⟨0, 1, 1⟩

/-- The dust in front of the master: the data input `D`. -/
def dust : Pos := ⟨0, 1, 0⟩

/-- The stone floor under the circuit. -/
def floor : List (Pos × Block) :=
  (List.range 6).flatMap fun x =>
    (List.range 5).map fun z => (⟨(x : ℤ) - 2, 0, (z : ℤ) - 2⟩, Block.plain .stone)

/-- The flip-flop with the three levers off and `Q = 0`. -/
def circuit : Level :=
  .ofCells (floor ++ [
    (master, blk% "minecraft:repeater[delay=1,facing=west,locked=false,powered=false]"),
    (slave, blk% "minecraft:repeater[delay=1,facing=west,locked=true,powered=false]"),
    (⟨3, 1, 0⟩, .plain .stone),
    (⟨1, 1, -2⟩, .plain .stone),
    (clockLever, .lever ⟨.floor, .north, false⟩),
    (⟨2, 1, -2⟩, .redstoneWallTorch ⟨.east, true⟩),
    (⟨1, 1, -1⟩, blk% "minecraft:repeater[delay=1,facing=north,locked=false,powered=false]"),
    (⟨2, 1, -1⟩, blk% "minecraft:repeater[delay=1,facing=north,locked=false,powered=true]"),
    (⟨3, 1, 1⟩, blk% "minecraft:repeater[delay=1,facing=north,locked=false,powered=false]"),
    (⟨3, 1, 2⟩, .plain .stone),
    (⟨2, 1, 2⟩, blk% "minecraft:repeater[delay=1,facing=east,locked=false,powered=false]"),
    (⟨1, 1, 2⟩, blk% "minecraft:repeater[delay=1,facing=east,locked=false,powered=false]"),
    (⟨0, 1, 2⟩, .plain .stone),
    (⟨-1, 1, 2⟩,
      blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=side,west=none]"),
    (⟨-1, 1, 1⟩, blk% "minecraft:repeater[delay=1,facing=south,locked=false,powered=false]"),
    (leverJ, .lever ⟨.floor, .north, false⟩),
    (comparatorJ, blk% "minecraft:comparator[facing=west,mode=subtract,powered=false]"),
    (comparatorK, blk% "minecraft:comparator[facing=south,mode=subtract,powered=false]"),
    (⟨1, 1, 1⟩, blk% "minecraft:repeater[delay=1,facing=east,locked=false,powered=false]"),
    (leverK, .lever ⟨.floor, .north, false⟩),
    (dust, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=side,west=side]")])

/-- One clock pulse, 34 game ticks: the levers in `pre` are used, eight game ticks pass, the
clock lever is switched on for 18 game ticks and off for eight. -/
def pulse (pre : List Input) : Schedule :=
  .first pre 8 ++ .first [.use clockLever .up] 18 ++ .first [.use clockLever .up] 8

/-- Eight clock pulses, one for each `(J, K, Q)`, and a last change of the levers that puts
them back. The rising edges come before game ticks 9, 43, 77, 111, 145, 179, 213 and 247,
with `(J, K)` = (0,0), (0,1), (1,0), (0,0), (1,0), (0,1), (1,1), (1,1). -/
def schedule : Schedule :=
  pulse [] ++ pulse [.use leverK .up] ++ pulse [.use leverK .up, .use leverJ .up] ++
    pulse [.use leverJ .up] ++ pulse [.use leverJ .up] ++
    pulse [.use leverJ .up, .use leverK .up] ++ pulse [.use leverJ .up] ++ pulse [] ++
    .first [.use leverJ .up, .use leverK .up] 8

checkpoints state := schedule from circuit

/-- The inputs and the state: `J`, `K`, the clock lever, and `Q` (the `powered` property of
the slave). -/
def flipFlop (l : Level) : Option Bool × Option Bool × Option Bool × Option Bool :=
  (leverAt? l leverJ, leverAt? l leverK, leverAt? l clockLever, (repeaterAt? l slave).map (·.1))

/-- The circuit as built is at rest, with the levers off and `Q = 0`. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧ flipFlop circuit = (some false, some false, some false, some false) := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **`J = 0`, `K = 0`, `Q = 0`: hold.** The level is at rest; the clock lever is switched on
before game tick 9; `Q` is 0 after game tick 14 and at the end of the clock pulse. -/
theorem hold_zero :
    flipFlop (rules.runSchedule (schedule.take 8) circuit) =
        (some false, some false, some false, some false) ∧
      (rules.runSchedule (schedule.take 8) circuit).Quiescent ∧
      flipFlop (rules.runSchedule (schedule.take 14) circuit) =
        (some false, some false, some true, some false) ∧
      flipFlop (rules.runSchedule (schedule.take 26) circuit) =
        (some false, some false, some true, some false) ∧
      (rules.runSchedule (schedule.take 26) circuit).overflow = false := by
  rw [state_run_8, state_run_14, state_run_26]
  circuit_decide

assert_standard_axioms hold_zero

/-- **`J = 0`, `K = 1`, `Q = 0`: reset, `Q` stays 0.** The clock lever is switched on before
game tick 43. -/
theorem reset_zero :
    flipFlop (rules.runSchedule (schedule.take 42) circuit) =
        (some false, some true, some false, some false) ∧
      (rules.runSchedule (schedule.take 42) circuit).Quiescent ∧
      flipFlop (rules.runSchedule (schedule.take 48) circuit) =
        (some false, some true, some true, some false) ∧
      flipFlop (rules.runSchedule (schedule.take 60) circuit) =
        (some false, some true, some true, some false) ∧
      (rules.runSchedule (schedule.take 60) circuit).overflow = false := by
  rw [state_run_42, state_run_48, state_run_60]
  circuit_decide

assert_standard_axioms reset_zero

/-- **`J = 1`, `K = 0`, `Q = 0`: set, `Q` becomes 1.** The comparator `J - Q` gives 15 and the
master is on before the edge. The clock lever is switched on before game tick 77; the slave
is off after game tick 81 and on after game tick 82. -/
theorem set_zero :
    flipFlop (rules.runSchedule (schedule.take 76) circuit) =
        (some true, some false, some false, some false) ∧
      (rules.runSchedule (schedule.take 76) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 76) circuit).dustPower dust = 15 ∧
      repeaterAt? (rules.runSchedule (schedule.take 76) circuit) master = some (true, false) ∧
      flipFlop (rules.runSchedule (schedule.take 81) circuit) =
        (some true, some false, some true, some false) ∧
      flipFlop (rules.runSchedule (schedule.take 82) circuit) =
        (some true, some false, some true, some true) ∧
      (rules.runSchedule (schedule.take 82) circuit).overflow = false := by
  rw [state_run_76, state_run_81, state_run_82]
  circuit_decide

assert_standard_axioms set_zero

/-- **`J = 0`, `K = 0`, `Q = 1`: hold.** The comparator `Q - K` keeps the master on. The clock
lever is switched on before game tick 111; `Q` stays 1. -/
theorem hold_one :
    flipFlop (rules.runSchedule (schedule.take 110) circuit) =
        (some false, some false, some false, some true) ∧
      (rules.runSchedule (schedule.take 110) circuit).Quiescent ∧
      flipFlop (rules.runSchedule (schedule.take 116) circuit) =
        (some false, some false, some true, some true) ∧
      flipFlop (rules.runSchedule (schedule.take 128) circuit) =
        (some false, some false, some true, some true) ∧
      (rules.runSchedule (schedule.take 128) circuit).overflow = false := by
  rw [state_run_110, state_run_116, state_run_128]
  circuit_decide

assert_standard_axioms hold_one

/-- **`J = 1`, `K = 0`, `Q = 1`: set, `Q` stays 1.** The clock lever is switched on before
game tick 145. -/
theorem set_one :
    flipFlop (rules.runSchedule (schedule.take 144) circuit) =
        (some true, some false, some false, some true) ∧
      (rules.runSchedule (schedule.take 144) circuit).Quiescent ∧
      flipFlop (rules.runSchedule (schedule.take 150) circuit) =
        (some true, some false, some true, some true) ∧
      flipFlop (rules.runSchedule (schedule.take 162) circuit) =
        (some true, some false, some true, some true) ∧
      (rules.runSchedule (schedule.take 162) circuit).overflow = false := by
  rw [state_run_144, state_run_150, state_run_162]
  circuit_decide

assert_standard_axioms set_one

/-- **`J = 0`, `K = 1`, `Q = 1`: reset, `Q` becomes 0.** With `K` on, the comparator `Q - K`
gives 0 and the master is off before the edge. The clock lever is switched on before game
tick 179; the slave is on after game tick 183 and off after game tick 184. -/
theorem reset_one :
    flipFlop (rules.runSchedule (schedule.take 178) circuit) =
        (some false, some true, some false, some true) ∧
      (rules.runSchedule (schedule.take 178) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 178) circuit).dustPower dust = 0 ∧
      repeaterAt? (rules.runSchedule (schedule.take 178) circuit) master = some (false, false) ∧
      flipFlop (rules.runSchedule (schedule.take 183) circuit) =
        (some false, some true, some true, some true) ∧
      flipFlop (rules.runSchedule (schedule.take 184) circuit) =
        (some false, some true, some true, some false) ∧
      (rules.runSchedule (schedule.take 184) circuit).overflow = false := by
  rw [state_run_178, state_run_183, state_run_184]
  circuit_decide

assert_standard_axioms reset_one

/-- **`J = 1`, `K = 1`, `Q = 0`: toggle, `Q` becomes 1.** The clock lever is switched on
before game tick 213; the slave is off after game tick 217 and on after game tick 218. -/
theorem toggle_zero :
    flipFlop (rules.runSchedule (schedule.take 212) circuit) =
        (some true, some true, some false, some false) ∧
      (rules.runSchedule (schedule.take 212) circuit).Quiescent ∧
      flipFlop (rules.runSchedule (schedule.take 217) circuit) =
        (some true, some true, some true, some false) ∧
      flipFlop (rules.runSchedule (schedule.take 218) circuit) =
        (some true, some true, some true, some true) ∧
      (rules.runSchedule (schedule.take 218) circuit).overflow = false := by
  rw [state_run_212, state_run_217, state_run_218]
  circuit_decide

assert_standard_axioms toggle_zero

/-- **`J = 1`, `K = 1`, `Q = 1`: toggle, `Q` becomes 0.** The clock lever is switched on
before game tick 247; the slave is on after game tick 251 and off after game tick 252. -/
theorem toggle_one :
    flipFlop (rules.runSchedule (schedule.take 246) circuit) =
        (some true, some true, some false, some true) ∧
      (rules.runSchedule (schedule.take 246) circuit).Quiescent ∧
      flipFlop (rules.runSchedule (schedule.take 251) circuit) =
        (some true, some true, some true, some true) ∧
      flipFlop (rules.runSchedule (schedule.take 252) circuit) =
        (some true, some true, some true, some false) ∧
      (rules.runSchedule (schedule.take 252) circuit).overflow = false := by
  rw [state_run_246, state_run_251, state_run_252]
  circuit_decide

assert_standard_axioms toggle_one

/-- **One edge acts once.** `Q` 17 game ticks after each rising edge, with the clock still
high and the feedback long back at the master, and `Q` at the end of the pulse, after the
falling edge: the same value both times, for the eight pulses. In particular the two toggles
toggle once. -/
theorem holds_after_edge :
    ([26, 60, 94, 128, 162, 196, 230, 264].map fun k =>
        (repeaterAt? (rules.runSchedule (schedule.take k) circuit) slave).map (·.1)) =
        [some false, some false, some true, some true, some true, some false, some true,
          some false] ∧
      ([34, 68, 102, 136, 170, 204, 238, 272].map fun k =>
        (repeaterAt? (rules.runSchedule (schedule.take k) circuit) slave).map (·.1)) =
        [some false, some false, some true, some true, some true, some false, some true,
          some false] ∧
      (rules.runSchedule (schedule.take 272) circuit).overflow = false := by
  simp only [List.map_cons, List.map_nil]
  rw [state_run_26, state_run_60, state_run_94, state_run_128, state_run_162, state_run_196,
    state_run_230, state_run_264, state_run_34, state_run_68, state_run_102, state_run_136,
    state_run_170, state_run_204, state_run_238, state_run_272]
  circuit_decide

assert_standard_axioms holds_after_edge

/-- **After a toggle, `Q` holds for ever while the clock stays high.** 17 game ticks after the
toggling edges (game ticks 213 and 247) the level is at rest, with `J = K = 1` and the clock
high: `Q` stays 1, respectively 0, for ever. The flip-flop does not oscillate. -/
theorem toggled_holds (n : ℕ) :
    flipFlop (rules.steps n (rules.runSchedule (schedule.take 230) circuit)) =
        (some true, some true, some true, some true) ∧
      flipFlop (rules.steps n (rules.runSchedule (schedule.take 264) circuit)) =
        (some true, some true, some true, some false) ∧
      (rules.steps n (rules.runSchedule (schedule.take 230) circuit)).overflow = false ∧
      (rules.steps n (rules.runSchedule (schedule.take 264) circuit)).overflow = false := by
  rw [state_run_230, state_run_264, rules.steps_of_quiescent (l := state_230) (by circuit_decide),
    rules.steps_of_quiescent (l := state_264) (by circuit_decide)]
  simp only [flipFlop, leverAt?, repeaterAt?, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms toggled_holds

/-- After the whole schedule the blocks and the block entities are those the circuit started
with, and the level is at rest. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).blockEntities = circuit.blockEntities ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Memory.JKFlipFlop
