import Redstone.Proof.Circuit

/-!
# The five-torch ring clock

Five inverters in a ring: each is a stone block with a redstone torch on its side, and the
torch powers redstone dust that runs into the next block. A ring with an odd number of
inverters has no state of rest, so it oscillates. The layer `y = 1` on a 7×4 stone floor, seen
from above (east is right, south is down); `B` is a block, `T` a torch, `d` dust:

```
        x=0  1  2  3  4  5  6
  z=0    B   T  d  B  T  d  B
  z=1    d                  T
  z=2    T                  d
  z=3    B   d  d  d  d  T  B
```

The signal goes round clockwise. The level is loaded without the fifth torch (the one at
`⟨0, 1, 2⟩`), which is a state of rest (`circuit_quiescent`): the torches are lit, out, lit,
out. Placing the fifth torch starts the clock.

**The period is 20 game ticks (10 redstone ticks)**: a torch follows its input after 2 game
ticks, a change has to go round the ring of five twice to bring it back to where it was, and
dust adds no delay. Every torch is lit for 10 game ticks and out for 10, and each one switches
2 game ticks after the one before it.

What is proved:

* which torches are lit after each of the first 41 game ticks (`signal_goes_round`): two
  periods, and one game tick more to see the second one close;
* the cycle certificate (`cycle`): 20 game ticks take the level after game tick 60 to itself,
  moved on in time by 20 game ticks, with 18 more ticks scheduled. The certificate starts
  at game tick 60 because the level keeps the game times of the torches' recent switch-offs
  for 60 game ticks (the burn-out list, `Level.recentTorchToggles`), and only then has that
  list reached its steady length. No torch burns out: each is switched off once in 20 game
  ticks.

The certificate says that the level repeats once. That it repeats for ever follows only if
a game tick commutes with the time shift on these levels (`Rules.periodic_of_shiftInvariant`).
`Redstone/Lemmas/ShiftInvariant.lean` proves that for levels without redstone dust; for dust
it is not proved.
-/

set_option Elab.async false

namespace Redstone.Theorems.Clock.TorchRing5

/-- The 7×4 stone floor. -/
def floor : List (Pos × Block) :=
  (List.range 7).flatMap fun x => (List.range 4).map fun z => (⟨x, 0, z⟩, Block.plain .stone)

/-- The positions of the five torches, in the order of the ring. The last one is missing in
the level as loaded and is placed to start the clock. -/
def torches : List Pos := [⟨1, 1, 0⟩, ⟨4, 1, 0⟩, ⟨6, 1, 1⟩, ⟨5, 1, 3⟩, ⟨0, 1, 2⟩]

/-- The position of the fifth torch, on the north side of the fifth block. -/
def last : Pos := ⟨0, 1, 2⟩

/-- The ring without its fifth torch, at rest: the first and the third torch are lit, the
second and the fourth are out. -/
def circuit : Level :=
  .ofCells (floor ++ [
    (⟨0, 1, 0⟩, .plain .stone), (⟨3, 1, 0⟩, .plain .stone), (⟨6, 1, 0⟩, .plain .stone),
    (⟨6, 1, 3⟩, .plain .stone), (⟨0, 1, 3⟩, .plain .stone),
    (⟨1, 1, 0⟩, .redstoneWallTorch ⟨.east, true⟩),
    (⟨2, 1, 0⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=15,south=none,west=side]"),
    (⟨4, 1, 0⟩, .redstoneWallTorch ⟨.east, false⟩),
    (⟨5, 1, 0⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]"),
    (⟨6, 1, 1⟩, .redstoneWallTorch ⟨.south, true⟩),
    (⟨6, 1, 2⟩, blk% "minecraft:redstone_wire[east=none,north=side,power=15,south=side,west=none]"),
    (⟨5, 1, 3⟩, .redstoneWallTorch ⟨.west, false⟩),
    (⟨4, 1, 3⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]"),
    (⟨3, 1, 3⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]"),
    (⟨2, 1, 3⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]"),
    (⟨1, 1, 3⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]"),
    (⟨0, 1, 1⟩, blk% "minecraft:redstone_wire[east=none,north=none,power=0,south=none,west=none]")])

/-- The fifth torch is placed, lit, before game tick 1; 80 game ticks in all. -/
def schedule : Schedule :=
  [[.set last (.redstoneWallTorch ⟨.north, true⟩)]] ++ Schedule.idle 79

/-- Which of the torches are lit, in the order of the ring. -/
def lit (l : Level) : List Bool :=
  torches.map fun p =>
    match l.blockAt p with
    | .redstoneWallTorch s => s.lit
    | _ => false

checkpoints state := schedule from circuit

/-- The ring without its fifth torch is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

set_option synthInstance.maxSize 4096 in
/-- **Two periods of the clock.** After game tick 1 the five torches are lit, out, lit, out,
lit: the first and the fifth are both lit, which cannot last. Every two game ticks the next
torch in the ring switches: the first goes out after game tick 2, the second comes on after
game tick 4, and so on; after game tick 21 the torches are as after game tick 1, and after
game tick 41 again. The model reaches no bound in 80 game ticks. -/
theorem signal_goes_round :
    lit (rules.runSchedule (schedule.take 1) circuit) = [true, false, true, false, true] ∧
      lit (rules.runSchedule (schedule.take 2) circuit) = [false, false, true, false, true] ∧
      lit (rules.runSchedule (schedule.take 3) circuit) = [false, false, true, false, true] ∧
      lit (rules.runSchedule (schedule.take 4) circuit) = [false, true, true, false, true] ∧
      lit (rules.runSchedule (schedule.take 5) circuit) = [false, true, true, false, true] ∧
      lit (rules.runSchedule (schedule.take 6) circuit) = [false, true, false, false, true] ∧
      lit (rules.runSchedule (schedule.take 7) circuit) = [false, true, false, false, true] ∧
      lit (rules.runSchedule (schedule.take 8) circuit) = [false, true, false, true, true] ∧
      lit (rules.runSchedule (schedule.take 9) circuit) = [false, true, false, true, true] ∧
      lit (rules.runSchedule (schedule.take 10) circuit) = [false, true, false, true, false] ∧
      lit (rules.runSchedule (schedule.take 11) circuit) = [false, true, false, true, false] ∧
      lit (rules.runSchedule (schedule.take 12) circuit) = [true, true, false, true, false] ∧
      lit (rules.runSchedule (schedule.take 13) circuit) = [true, true, false, true, false] ∧
      lit (rules.runSchedule (schedule.take 14) circuit) = [true, false, false, true, false] ∧
      lit (rules.runSchedule (schedule.take 15) circuit) = [true, false, false, true, false] ∧
      lit (rules.runSchedule (schedule.take 16) circuit) = [true, false, true, true, false] ∧
      lit (rules.runSchedule (schedule.take 17) circuit) = [true, false, true, true, false] ∧
      lit (rules.runSchedule (schedule.take 18) circuit) = [true, false, true, false, false] ∧
      lit (rules.runSchedule (schedule.take 19) circuit) = [true, false, true, false, false] ∧
      lit (rules.runSchedule (schedule.take 20) circuit) = [true, false, true, false, true] ∧
      lit (rules.runSchedule (schedule.take 21) circuit) = [true, false, true, false, true] ∧
      lit (rules.runSchedule (schedule.take 22) circuit) = [false, false, true, false, true] ∧
      lit (rules.runSchedule (schedule.take 23) circuit) = [false, false, true, false, true] ∧
      lit (rules.runSchedule (schedule.take 24) circuit) = [false, true, true, false, true] ∧
      lit (rules.runSchedule (schedule.take 25) circuit) = [false, true, true, false, true] ∧
      lit (rules.runSchedule (schedule.take 26) circuit) = [false, true, false, false, true] ∧
      lit (rules.runSchedule (schedule.take 27) circuit) = [false, true, false, false, true] ∧
      lit (rules.runSchedule (schedule.take 28) circuit) = [false, true, false, true, true] ∧
      lit (rules.runSchedule (schedule.take 29) circuit) = [false, true, false, true, true] ∧
      lit (rules.runSchedule (schedule.take 30) circuit) = [false, true, false, true, false] ∧
      lit (rules.runSchedule (schedule.take 31) circuit) = [false, true, false, true, false] ∧
      lit (rules.runSchedule (schedule.take 32) circuit) = [true, true, false, true, false] ∧
      lit (rules.runSchedule (schedule.take 33) circuit) = [true, true, false, true, false] ∧
      lit (rules.runSchedule (schedule.take 34) circuit) = [true, false, false, true, false] ∧
      lit (rules.runSchedule (schedule.take 35) circuit) = [true, false, false, true, false] ∧
      lit (rules.runSchedule (schedule.take 36) circuit) = [true, false, true, true, false] ∧
      lit (rules.runSchedule (schedule.take 37) circuit) = [true, false, true, true, false] ∧
      lit (rules.runSchedule (schedule.take 38) circuit) = [true, false, true, false, false] ∧
      lit (rules.runSchedule (schedule.take 39) circuit) = [true, false, true, false, false] ∧
      lit (rules.runSchedule (schedule.take 40) circuit) = [true, false, true, false, true] ∧
      lit (rules.runSchedule (schedule.take 41) circuit) = [true, false, true, false, true] ∧
      (rules.runSchedule (schedule.take 80) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13,
    state_run_14, state_run_15, state_run_16, state_run_17, state_run_18, state_run_19,
    state_run_20, state_run_21, state_run_22, state_run_23, state_run_24, state_run_25,
    state_run_26, state_run_27, state_run_28, state_run_29, state_run_30, state_run_31,
    state_run_32, state_run_33, state_run_34, state_run_35, state_run_36, state_run_37,
    state_run_38, state_run_39, state_run_40, state_run_41, state_run_80]
  circuit_decide

assert_standard_axioms signal_goes_round

/-- **The cycle certificate.** Twenty game ticks take the level after game tick 60 to itself,
moved on in time by 20 game ticks, with 18 more ticks scheduled: every block, the scheduled
tick, every counter, and the list of recent torch toggles (fifteen entries, each 20 game ticks
later). -/
theorem cycle : rules.Cycle (rules.runSchedule (schedule.take 60) circuit) 20 18 := by
  rw [state_run_60]
  exact (Rules.steps_of_runs (k := 60) (m := 20) state_run_60 state_run_80
    (by circuit_decide)).trans (Level.eq_of_beqBlocks (by circuit_decide))

assert_standard_axioms cycle

end Redstone.Theorems.Clock.TorchRing5
