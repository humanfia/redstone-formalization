import Redstone.Proof.Circuit

/-!
# The three-torch ring clock

Three inverters in a ring: the smallest torch clock that does not burn out. Each inverter is
a stone block with a redstone torch on its side, and the torch powers redstone dust that runs
into the next block. The layer `y = 1` on a 4×4 stone floor, seen from above (east is right,
south is down); `B` is a block, `T` a torch, `d` dust:

```
        x=0  1  2  3
  z=0    B   T  d  B
  z=1    d         T
  z=2    d         d
  z=3    d   d  T  B
```

The signal goes round clockwise. The level is loaded without the third torch (the one at
`⟨2, 1, 3⟩`), which is a state of rest (`circuit_quiescent`): the first torch is lit, the
second is out. Placing the third torch starts the clock.

**The period is 12 game ticks (6 redstone ticks)**: a torch follows its input after 2 game
ticks and a change has to go round the ring of three twice. Every torch is lit for 6 game
ticks and out for 6.

What is proved:

* which torches are lit after each of the first 25 game ticks (`signal_goes_round`): two
  periods, and one game tick more;
* the cycle certificate (`cycle`): 12 game ticks take the level after game tick 60 to itself,
  moved on in time by 12 game ticks, with 22 more ticks scheduled. As for the five-torch
  ring, the certificate waits until the burn-out list has its steady length. Each torch is
  switched off once in 12 game ticks, five times in any 60: fewer than the eight that burn a
  torch out (`Redstone.Theorems.Clock.RapidClock` is the clock that does burn out).

The certificate says that the level repeats once. That it repeats for ever follows only if
a game tick commutes with the time shift on these levels (`Rules.periodic_of_shiftInvariant`).
`Redstone/Lemmas/ShiftInvariant.lean` proves that for levels without redstone dust; for dust
it is not proved.
-/

set_option Elab.async false

namespace Redstone.Theorems.Clock.TorchRing3

/-- The 4×4 stone floor. -/
def floor : List (Pos × Block) :=
  (List.range 4).flatMap fun x => (List.range 4).map fun z => (⟨x, 0, z⟩, Block.plain .stone)

/-- The positions of the three torches, in the order of the ring. The last one is missing in
the level as loaded and is placed to start the clock. -/
def torches : List Pos := [⟨1, 1, 0⟩, ⟨3, 1, 1⟩, ⟨2, 1, 3⟩]

/-- The position of the third torch, on the west side of the third block. -/
def last : Pos := ⟨2, 1, 3⟩

/-- The ring without its third torch, at rest: the first torch is lit, the second is out. -/
def circuit : Level :=
  .ofCells (floor ++ [
    (⟨0, 1, 0⟩, .plain .stone), (⟨3, 1, 0⟩, .plain .stone), (⟨3, 1, 3⟩, .plain .stone),
    (⟨1, 1, 0⟩, .redstoneWallTorch ⟨.east, true⟩),
    (⟨2, 1, 0⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=15,south=none,west=side]"),
    (⟨3, 1, 1⟩, .redstoneWallTorch ⟨.south, false⟩),
    (⟨3, 1, 2⟩, blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=side,west=none]"),
    (⟨1, 1, 3⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]"),
    (⟨0, 1, 3⟩, blk% "minecraft:redstone_wire[east=side,north=side,power=0,south=none,west=none]"),
    (⟨0, 1, 2⟩, blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=side,west=none]"),
    (⟨0, 1, 1⟩, blk% "minecraft:redstone_wire[east=none,north=none,power=0,south=none,west=none]")])

/-- The third torch is placed, lit, before game tick 1; 72 game ticks in all. -/
def schedule : Schedule :=
  [[.set last (.redstoneWallTorch ⟨.west, true⟩)]] ++ Schedule.idle 71

/-- Which of the torches are lit, in the order of the ring. -/
def lit (l : Level) : List Bool :=
  torches.map fun p =>
    match l.blockAt p with
    | .redstoneWallTorch s => s.lit
    | _ => false

checkpoints state := schedule from circuit

/-- The ring without its third torch is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

set_option synthInstance.maxSize 4096 in
/-- **Two periods of the clock.** After game tick 1 the three torches are lit, out, lit.
Every two game ticks the next torch in the ring switches; after game tick 13 the torches are
as after game tick 1, and after game tick 25 again. The model reaches no bound in 72 game
ticks. -/
theorem signal_goes_round :
    lit (rules.runSchedule (schedule.take 1) circuit) = [true, false, true] ∧
      lit (rules.runSchedule (schedule.take 2) circuit) = [false, false, true] ∧
      lit (rules.runSchedule (schedule.take 3) circuit) = [false, false, true] ∧
      lit (rules.runSchedule (schedule.take 4) circuit) = [false, true, true] ∧
      lit (rules.runSchedule (schedule.take 5) circuit) = [false, true, true] ∧
      lit (rules.runSchedule (schedule.take 6) circuit) = [false, true, false] ∧
      lit (rules.runSchedule (schedule.take 7) circuit) = [false, true, false] ∧
      lit (rules.runSchedule (schedule.take 8) circuit) = [true, true, false] ∧
      lit (rules.runSchedule (schedule.take 9) circuit) = [true, true, false] ∧
      lit (rules.runSchedule (schedule.take 10) circuit) = [true, false, false] ∧
      lit (rules.runSchedule (schedule.take 11) circuit) = [true, false, false] ∧
      lit (rules.runSchedule (schedule.take 12) circuit) = [true, false, true] ∧
      lit (rules.runSchedule (schedule.take 13) circuit) = [true, false, true] ∧
      lit (rules.runSchedule (schedule.take 14) circuit) = [false, false, true] ∧
      lit (rules.runSchedule (schedule.take 15) circuit) = [false, false, true] ∧
      lit (rules.runSchedule (schedule.take 16) circuit) = [false, true, true] ∧
      lit (rules.runSchedule (schedule.take 17) circuit) = [false, true, true] ∧
      lit (rules.runSchedule (schedule.take 18) circuit) = [false, true, false] ∧
      lit (rules.runSchedule (schedule.take 19) circuit) = [false, true, false] ∧
      lit (rules.runSchedule (schedule.take 20) circuit) = [true, true, false] ∧
      lit (rules.runSchedule (schedule.take 21) circuit) = [true, true, false] ∧
      lit (rules.runSchedule (schedule.take 22) circuit) = [true, false, false] ∧
      lit (rules.runSchedule (schedule.take 23) circuit) = [true, false, false] ∧
      lit (rules.runSchedule (schedule.take 24) circuit) = [true, false, true] ∧
      lit (rules.runSchedule (schedule.take 25) circuit) = [true, false, true] ∧
      (rules.runSchedule (schedule.take 72) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13,
    state_run_14, state_run_15, state_run_16, state_run_17, state_run_18, state_run_19,
    state_run_20, state_run_21, state_run_22, state_run_23, state_run_24, state_run_25,
    state_run_72]
  circuit_decide

assert_standard_axioms signal_goes_round

/-- **The cycle certificate.** Twelve game ticks take the level after game tick 60 to itself,
moved on in time by 12 game ticks, with 22 more ticks scheduled: every block, the scheduled
tick, every counter, and the list of recent torch toggles (fifteen entries, each 12 game ticks
later). -/
theorem cycle : rules.Cycle (rules.runSchedule (schedule.take 60) circuit) 12 22 := by
  rw [state_run_60]
  exact (Rules.steps_of_runs (k := 60) (m := 12) state_run_60 state_run_72
    (by circuit_decide)).trans (Level.eq_of_beqBlocks (by circuit_decide))

assert_standard_axioms cycle

end Redstone.Theorems.Clock.TorchRing3
