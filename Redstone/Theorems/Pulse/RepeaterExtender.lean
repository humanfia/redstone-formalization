import Redstone.Theorems.Pulse.Trace

/-!
# The repeater pulse extender

The output is the input OR the input delayed by a chain of repeaters: the output comes on with
the input and stays on until the delayed copy has gone off, so a pulse comes out longer by the
delay of the chain.

```
          x = 0   x = 1   x = 2        y = 1, seen from above, x to the right, on a stone floor
z = 0:      L       R1      B          L: lever (the input)
z = 1:      o       R2      d          R1: repeater, input west, output east into the stone B
                                       d: redstone dust, powered by B
                                       R2: repeater, input east (the dust d), output west
                                       o: redstone dust, the output: next to the lever, and at
                                          the output of R2
```

The clock is explained in `Redstone/Theorems/Pulse/Trace.lean`. What is proved:

* **delays 1 and 1, an input of 4 game ticks gives an output of 8** (`extend_one`): the lever
  is on from time 0 to time 4, the output dust has power 15 from time 0 to time 8.
* **delays 2 and 2, an input of 8 game ticks gives an output of 16** (`extend_two`).
  In both cases the output is longer than the input by the delay of the chain, 4 or 8 game
  ticks.
* **the input must not be shorter than the chain is long** (`gap_two`): with the delays 2 and
  2 and an input of 4 game ticks the output is not one pulse. It is on from time 0 to time 4,
  off from time 4 to time 8, and on again from time 8 to time 12: the delayed copy arrives
  after the input has gone.

Every run ends at rest, with the blocks it started with. The levels are loaded raw and are at
rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Pulse.RepeaterExtender

/-- The position of the lever: the input. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The position of the first repeater of the chain. -/
def first : Pos := ⟨1, 1, 0⟩

/-- The position of the second repeater of the chain. -/
def second : Pos := ⟨1, 1, 1⟩

/-- The position of the output dust. -/
def out : Pos := ⟨0, 1, 1⟩

/-- The 3×2 stone floor. -/
def floor : List (Pos × Block) :=
  (List.range 3).flatMap fun x => (List.range 2).map fun z => (⟨x, 0, z⟩, Block.plain .stone)

/-- The extender with the given delay of both repeaters, everything off. -/
def circuit (delay : IntRange 1 4) : Level :=
  .ofCells (floor ++ [
    (lever, .lever ⟨.floor, .north, false⟩),
    (first, .repeater { delay, facing := .west, locked := false, powered := false }),
    (⟨2, 1, 0⟩, .plain .stone),
    (⟨2, 1, 1⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]"),
    (second, .repeater { delay, facing := .east, locked := false, powered := false }),
    (out, blk% "minecraft:redstone_wire[east=side,north=side,power=0,south=none,west=none]")])

/-- The extender with two repeaters of delay 1: the chain is 4 game ticks long. -/
def circuit1 : Level := circuit ⟨1, by decide, by decide⟩

/-- The extender with two repeaters of delay 2: the chain is 8 game ticks long. -/
def circuit2 : Level := circuit ⟨2, by decide, by decide⟩

/-- The lever is switched on before game tick 1 and off before game tick 5; 12 game ticks. -/
def schedule1 : Schedule := .first [.use lever .up] 4 ++ .first [.use lever .up] 8

/-- The lever is switched on before game tick 1 and off before game tick 9; 20 game ticks. -/
def schedule2 : Schedule := .first [.use lever .up] 8 ++ .first [.use lever .up] 12

/-- The lever is switched on before game tick 1 and off before game tick 5; 16 game ticks. -/
def gapSchedule : Schedule := .first [.use lever .up] 4 ++ .first [.use lever .up] 12

checkpoints one := schedule1 from circuit1
checkpoints two := schedule2 from circuit2
checkpoints gap := gapSchedule from circuit2

/-- What is observed: is the lever on, is the first repeater on, is the second repeater on,
and the power of the output dust. -/
def observe (l : Level) : Bool × Bool × Bool × ℕ :=
  (leverOn l lever, repeaterOn l first, repeaterOn l second, l.dustPower out)

/-- Everything is off. -/
def off : Bool × Bool × Bool × ℕ := (false, false, false, 0)

/-- Before the lever is used, both circuits are at rest, with everything off. -/
theorem circuit_quiescent :
    circuit1.Quiescent ∧ circuit2.Quiescent ∧ observe circuit1 = off ∧ observe circuit2 = off := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Delays 1 and 1: four game ticks in, eight game ticks out.** The lever is on after the
game ticks 1 to 4. The output dust has power 15 after the game ticks 1 to 7 and is dark from
game tick 8 on: first the lever holds it, then the second repeater, which is on after the game
ticks 4 to 7. -/
theorem extend_one :
    after observe schedule1 circuit1 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] =
        [(true, false, false, 15), (true, true, false, 15), (true, true, false, 15),
          (true, true, true, 15), (false, true, true, 15), (false, false, true, 15),
          (false, false, true, 15)] ++ List.replicate 5 off ∧
      (rules.runSchedule schedule1 circuit1).world = circuit1.world ∧
      (rules.runSchedule schedule1 circuit1).Quiescent ∧
      (rules.runSchedule schedule1 circuit1).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs one 1 12
  rw [one_run]
  circuit_decide

assert_standard_axioms extend_one

/-- **Delays 2 and 2: eight game ticks in, sixteen game ticks out.** The lever is on after the
game ticks 1 to 8. The output dust has power 15 after the game ticks 1 to 15 and is dark from
game tick 16 on; the second repeater is on after the game ticks 8 to 15. -/
theorem extend_two :
    after observe schedule2 circuit2 (List.range' 1 20) =
        List.replicate 3 (true, false, false, 15) ++ List.replicate 4 (true, true, false, 15) ++
          [(true, true, true, 15)] ++ List.replicate 3 (false, true, true, 15) ++
          List.replicate 4 (false, false, true, 15) ++ List.replicate 5 off ∧
      (rules.runSchedule schedule2 circuit2).world = circuit2.world ∧
      (rules.runSchedule schedule2 circuit2).Quiescent ∧
      (rules.runSchedule schedule2 circuit2).overflow = false := by
  rw [show List.range' 1 20 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
    19, 20] from by decide]
  simp only [after, List.map_cons, List.map_nil]
  rw_runs two 1 20
  rw [two_run]
  circuit_decide

assert_standard_axioms extend_two

/-- **An input shorter than the chain leaves a gap.** Delays 2 and 2, and the lever on after
the game ticks 1 to 4 only. The output dust has power 15 after the game ticks 1 to 4, is dark
after the game ticks 5 to 7, and has power 15 again after the game ticks 8 to 11. -/
theorem gap_two :
    after observe gapSchedule circuit2 (List.range' 1 16) =
        List.replicate 3 (true, false, false, 15) ++ [(true, true, false, 15)] ++
          List.replicate 3 (false, true, false, 0) ++ List.replicate 4 (false, false, true, 15) ++
          List.replicate 5 off ∧
      (rules.runSchedule gapSchedule circuit2).world = circuit2.world ∧
      (rules.runSchedule gapSchedule circuit2).Quiescent ∧
      (rules.runSchedule gapSchedule circuit2).overflow = false := by
  rw [show List.range' 1 16 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
    from by decide]
  simp only [after, List.map_cons, List.map_nil]
  rw_runs gap 1 16
  rw [gap_run]
  circuit_decide

assert_standard_axioms gap_two

end Redstone.Theorems.Pulse.RepeaterExtender
