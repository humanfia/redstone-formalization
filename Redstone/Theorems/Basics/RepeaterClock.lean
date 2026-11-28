import Redstone.Proof.Circuit

/-!
# The four-repeater clock

A ring of four repeaters (delay 1) with redstone dust at the corners, on a 3×3 stone floor.
A block of redstone next to one corner, there for one game tick, starts a pulse that goes
round the ring: each repeater is on for two game ticks, one after the other, and the ring is
back where it was after 8 game ticks.

What is proved:

* the state of the four repeaters after each of 18 game ticks (`pulse_goes_round`): the two
  game ticks of the start, and two periods;
* a **cycle certificate** (`cycle`): 8 game ticks take the level after game tick 10 to
  itself, moved on in time by 8 game ticks, with 16 more ticks scheduled. This is an equation
  between whole levels: blocks, scheduled ticks with their delays and their order, counters,
  random number generator. The certificate starts at game tick 10 and not at game tick 2,
  because the first round is not yet the steady state: the level after game tick 2 has the
  blocks and the scheduled ticks of the level after game tick 10, but `Level.lightWorld`, the
  blocks as the light engine last saw them, still has the block of redstone that started the
  pulse.

Not proved: that the clock runs for ever. The certificate says that the level repeats once;
that it then repeats again follows only if a game tick commutes with the time shift on these
levels (`Rules.periodic_of_shiftInvariant`), which is not proved for the repeater or the dust.

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Basics.RepeaterClock

/-- The cell next to the first corner, where the block of redstone is put. -/
def start : Pos := ⟨-1, 1, 0⟩

/-- The positions of the four repeaters, in the order in which the pulse reaches them. -/
def repeaters : List Pos := [⟨1, 1, 0⟩, ⟨2, 1, 1⟩, ⟨1, 1, 2⟩, ⟨0, 1, 1⟩]

/-- The 3×3 stone floor. -/
def floor : List (Pos × Block) :=
  (List.range 3).flatMap fun x => (List.range 3).map fun z => (⟨x, 0, z⟩, Block.plain .stone)

/-- Four repeaters in a ring, each reading the dust at the corner before it, all off. -/
def circuit : Level :=
  .ofCells (floor ++ [
    (⟨0, 1, 0⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=side,west=none]"),
    (⟨1, 1, 0⟩, blk% "minecraft:repeater[delay=1,facing=west,locked=false,powered=false]"),
    (⟨2, 1, 0⟩, blk% "minecraft:redstone_wire[east=none,north=none,power=0,south=side,west=side]"),
    (⟨2, 1, 1⟩, blk% "minecraft:repeater[delay=1,facing=north,locked=false,powered=false]"),
    (⟨2, 1, 2⟩, blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=none,west=side]"),
    (⟨1, 1, 2⟩, blk% "minecraft:repeater[delay=1,facing=east,locked=false,powered=false]"),
    (⟨0, 1, 2⟩, blk% "minecraft:redstone_wire[east=side,north=side,power=0,south=none,west=none]"),
    (⟨0, 1, 1⟩, blk% "minecraft:repeater[delay=1,facing=south,locked=false,powered=false]")])

/-- A block of redstone is put next to the first corner before game tick 1 and removed before
game tick 2; then 16 game ticks without input. -/
def schedule : Schedule :=
  [[.set start (.plain .redstone_block)], [.set start .AIR]] ++ Schedule.idle 16

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- Which of the four repeaters are on, in the order of the ring. -/
def lit (l : Level) : List Bool :=
  repeaters.map fun p =>
    match l.blockAt p with
    | .repeater s => s.powered
    | _ => false

/-- **The pulse goes round the ring.** After game tick 1 no repeater is on yet; after game tick
2 the first repeater is on; every two
game ticks the pulse is at the next repeater; after game tick 10 it is back at the first, and
after game tick 18 again. The model reaches no bound. -/
theorem pulse_goes_round :
    lit (rules.runSchedule (schedule.take 1) circuit) = [false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 2) circuit) = [true, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 3) circuit) = [true, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 4) circuit) = [false, true, false, false] ∧
      lit (rules.runSchedule (schedule.take 5) circuit) = [false, true, false, false] ∧
      lit (rules.runSchedule (schedule.take 6) circuit) = [false, false, true, false] ∧
      lit (rules.runSchedule (schedule.take 7) circuit) = [false, false, true, false] ∧
      lit (rules.runSchedule (schedule.take 8) circuit) = [false, false, false, true] ∧
      lit (rules.runSchedule (schedule.take 9) circuit) = [false, false, false, true] ∧
      lit (rules.runSchedule (schedule.take 10) circuit) = [true, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 11) circuit) = [true, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 12) circuit) = [false, true, false, false] ∧
      lit (rules.runSchedule (schedule.take 13) circuit) = [false, true, false, false] ∧
      lit (rules.runSchedule (schedule.take 14) circuit) = [false, false, true, false] ∧
      lit (rules.runSchedule (schedule.take 15) circuit) = [false, false, true, false] ∧
      lit (rules.runSchedule (schedule.take 16) circuit) = [false, false, false, true] ∧
      lit (rules.runSchedule (schedule.take 17) circuit) = [false, false, false, true] ∧
      lit (rules.runSchedule (schedule.take 18) circuit) = [true, false, false, false] ∧
      (rules.runSchedule (schedule.take 18) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13, state_run_14,
    state_run_15, state_run_16, state_run_17, state_run_18]
  circuit_decide

assert_standard_axioms pulse_goes_round

/-- **The cycle certificate.** Eight game ticks take the level after game tick 10 to itself,
moved on in time by 8 game ticks, with 16 more ticks scheduled: every block, every scheduled
tick (due 8 game ticks later, 16 further in the scheduling order), every counter and the
random number generator. -/
theorem cycle : rules.Cycle (rules.runSchedule (schedule.take 10) circuit) 8 16 := by
  rw [state_run_10]
  exact (Rules.steps_of_runs (k := 10) (m := 8) state_run_10 state_run_18
    (by circuit_decide)).trans (Level.eq_of_beqBlocks (by circuit_decide))

assert_standard_axioms cycle

end Redstone.Theorems.Basics.RepeaterClock
