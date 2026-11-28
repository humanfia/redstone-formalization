import Redstone.Proof.Circuit

/-!
# The two-repeater loop clock

The clock most often built by hand: two repeaters side by side that point in opposite
directions, joined at both ends by two pieces of redstone dust, on a 3×2 stone floor. The
layer `y = 1`, seen from above (east is right, south is down); an arrow is a repeater and
shows which way the signal goes through it, `d` is dust:

```
        x=0  1  2
  z=0    d   >  d
  z=1    d   <  d
```

A block of redstone next to the first dust starts the clock; it is taken away as soon as the
first repeater has come on. From then on the two repeaters take turns. **The period is the
sum of the two delays**: with both repeaters at delay 1 it is 4 game ticks (2 redstone
ticks), with both at delay 4 it is 16 game ticks (8 redstone ticks). Once the clock runs,
exactly one of the two repeaters is on at any time, and the dust at its output has the powers
15 and 14.

What is proved:

* delays 1 and 1 (`circuit`): the two repeaters and the four pieces of dust after each of 15
  game ticks (`alternates`), which is the start and three periods; and the cycle certificate
  (`cycle`): 4 game ticks take the level after game tick 7 to itself, moved on in time by 4
  game ticks, with 13 more ticks scheduled;
* delays 4 and 4 (`slow`): the same after each of 42 game ticks (`slow_alternates`), which is
  the start and two periods; and the cycle certificate (`slow_cycle`): 16 game ticks take the
  level after game tick 24 to itself, with 13 more ticks scheduled.

The certificate says that the level repeats once. That it repeats for ever follows only if
a game tick commutes with the time shift on these levels (`Rules.periodic_of_shiftInvariant`).
`Redstone/Lemmas/ShiftInvariant.lean` proves that for levels without redstone dust; for dust
it is not proved.

## What is not yet proved

**The start by a pulse of one game tick** (the block of redstone removed before game tick 2,
while the first repeater is still off and waits for its tick). The compiled model runs it and
gives the same clock, but the kernel does not get through that game tick: more than 64 GB.
The two pieces of dust at the input lose their source and go down from 15 and 14 to zero in
thirteen steps, each of which tells the repeater; the repeater, off with its input still on,
calls `Level.scheduleTick` every time. What was measured: the same two pieces of dust alone
take 3 seconds, and so do they next to a repeater that is on; next to a repeater that is off
and waits for its tick, 16 GB are not enough. The likely reason is that `Level.scheduleTick`
uses the level twice (to count and to look for a waiting tick), so that every call doubles
what the kernel has to evaluate of the level before it. One piece of dust goes to zero in one
step, which is why the ring of `Redstone.Theorems.Basics.RepeaterClock` can be started that
way. Here the block stays until the repeater is on (game tick 3 for delay 1, game tick 9 for
delay 4); a repeater that is on does not ask for a tick while its input is still above
zero.

Both levels are loaded raw and are at rest (`circuit_quiescent`, `slow_quiescent`). The
four-repeater ring with dust at the corners is `Redstone.Theorems.Basics.RepeaterClock`; the
ring without dust is `Redstone.Theorems.Clock.RepeaterRing`.
-/

set_option Elab.async false

namespace Redstone.Theorems.Clock.RepeaterLoop

/-- The 3×2 stone floor. -/
def floor : List (Pos × Block) :=
  (List.range 3).flatMap fun x => (List.range 2).map fun z => (⟨x, 0, z⟩, Block.plain .stone)

/-- The cell next to the first dust, where a block of redstone is put to start the clock. -/
def start : Pos := ⟨-1, 1, 0⟩

/-- The two repeaters: the first points east, the second points back west. -/
def repeaters : List Pos := [⟨1, 1, 0⟩, ⟨1, 1, 1⟩]

/-- The four pieces of dust, in the order of the loop: the input of the first repeater, its
output, the input of the second repeater, its output. -/
def wires : List Pos := [⟨0, 1, 0⟩, ⟨2, 1, 0⟩, ⟨2, 1, 1⟩, ⟨0, 1, 1⟩]

/-- The loop made of the two given repeaters, with two pieces of dust at each end. -/
def loop (r₁ r₂ : Block) : Level :=
  .ofCells (floor ++ [
    (⟨0, 1, 0⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=side,west=none]"),
    (⟨2, 1, 0⟩, blk% "minecraft:redstone_wire[east=none,north=none,power=0,south=side,west=side]"),
    (⟨2, 1, 1⟩, blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=none,west=side]"),
    (⟨0, 1, 1⟩, blk% "minecraft:redstone_wire[east=side,north=side,power=0,south=none,west=none]"),
    (⟨1, 1, 0⟩, r₁), (⟨1, 1, 1⟩, r₂)])

/-- The loop with both repeaters at delay 1 (two game ticks), all off. -/
def circuit : Level :=
  loop (blk% "minecraft:repeater[delay=1,facing=west,locked=false,powered=false]")
    (blk% "minecraft:repeater[delay=1,facing=east,locked=false,powered=false]")

/-- The loop with both repeaters at delay 4 (eight game ticks), all off. -/
def slow : Level :=
  loop (blk% "minecraft:repeater[delay=4,facing=west,locked=false,powered=false]")
    (blk% "minecraft:repeater[delay=4,facing=east,locked=false,powered=false]")

/-- A block of redstone is put at `start` before game tick 1 and removed before game tick 3,
when the first repeater has come on; then 12 game ticks without input. -/
def schedule : Schedule :=
  [[.set start (.plain .redstone_block)], [], [.set start .AIR]] ++ Schedule.idle 12

/-- A block of redstone is put at `start` before game tick 1 and removed before game tick 9,
when the first repeater has come on; then 33 game ticks without input. -/
def slowSchedule : Schedule :=
  [[.set start (.plain .redstone_block)]] ++ Schedule.idle 7 ++ [[.set start .AIR]] ++
    Schedule.idle 33

/-- Which of the two repeaters are on, and the power of the four pieces of dust. -/
def look (l : Level) : List Bool × List ℕ :=
  (repeaters.map fun p =>
      match l.blockAt p with
      | .repeater s => s.powered
      | _ => false,
    wires.map l.dustPower)

checkpoints state := schedule from circuit

checkpoints sstate := slowSchedule from slow

/-- The loop with delays 1 and 1 as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- The loop with delays 4 and 4 as built is at rest. -/
theorem slow_quiescent : slow.Quiescent := by circuit_decide

assert_standard_axioms slow_quiescent

/-- **The two repeaters take turns, delays 1 and 1.** The block of redstone powers the first
dust during game ticks 1 and 2. After game tick 2 the first repeater is on and the dust at its
output has the powers 15 and 14; after game tick 4 the second repeater is on instead; and so
on, every two game ticks, for three periods of four game ticks. The model reaches no
bound. -/
theorem alternates :
    look (rules.runSchedule (schedule.take 1) circuit) = ([false, false], [15, 0, 0, 14]) ∧
      look (rules.runSchedule (schedule.take 2) circuit) = ([true, false], [15, 15, 14, 14]) ∧
      look (rules.runSchedule (schedule.take 3) circuit) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (schedule.take 4) circuit) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (schedule.take 5) circuit) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (schedule.take 6) circuit) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (schedule.take 7) circuit) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (schedule.take 8) circuit) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (schedule.take 9) circuit) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (schedule.take 10) circuit) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (schedule.take 11) circuit) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (schedule.take 12) circuit) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (schedule.take 13) circuit) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (schedule.take 14) circuit) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (schedule.take 15) circuit) = ([true, false], [0, 15, 14, 0]) ∧
      (rules.runSchedule (schedule.take 15) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13,
    state_run_14, state_run_15]
  circuit_decide

assert_standard_axioms alternates

/-- **The cycle certificate, delays 1 and 1.** Four game ticks take the level after game tick
7 to itself, moved on in time by 4 game ticks, with 13 more ticks scheduled. -/
theorem cycle : rules.Cycle (rules.runSchedule (schedule.take 7) circuit) 4 13 := by
  rw [state_run_7]
  exact (Rules.steps_of_runs (k := 7) (m := 4) state_run_7 state_run_11
    (by circuit_decide)).trans (Level.eq_of_beqBlocks (by circuit_decide))

assert_standard_axioms cycle

set_option synthInstance.maxSize 4096 in
/-- **The two repeaters take turns, delays 4 and 4.** The first repeater comes on after game
tick 8 and is on for eight game ticks; then the second is on for eight game ticks; and so on,
for two periods of sixteen game ticks. The model reaches no bound. -/
theorem slow_alternates :
    look (rules.runSchedule (slowSchedule.take 1) slow) = ([false, false], [15, 0, 0, 14]) ∧
      look (rules.runSchedule (slowSchedule.take 2) slow) = ([false, false], [15, 0, 0, 14]) ∧
      look (rules.runSchedule (slowSchedule.take 3) slow) = ([false, false], [15, 0, 0, 14]) ∧
      look (rules.runSchedule (slowSchedule.take 4) slow) = ([false, false], [15, 0, 0, 14]) ∧
      look (rules.runSchedule (slowSchedule.take 5) slow) = ([false, false], [15, 0, 0, 14]) ∧
      look (rules.runSchedule (slowSchedule.take 6) slow) = ([false, false], [15, 0, 0, 14]) ∧
      look (rules.runSchedule (slowSchedule.take 7) slow) = ([false, false], [15, 0, 0, 14]) ∧
      look (rules.runSchedule (slowSchedule.take 8) slow) = ([true, false], [15, 15, 14, 14]) ∧
      look (rules.runSchedule (slowSchedule.take 9) slow) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (slowSchedule.take 10) slow) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (slowSchedule.take 11) slow) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (slowSchedule.take 12) slow) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (slowSchedule.take 13) slow) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (slowSchedule.take 14) slow) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (slowSchedule.take 15) slow) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (slowSchedule.take 16) slow) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (slowSchedule.take 17) slow) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (slowSchedule.take 18) slow) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (slowSchedule.take 19) slow) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (slowSchedule.take 20) slow) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (slowSchedule.take 21) slow) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (slowSchedule.take 22) slow) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (slowSchedule.take 23) slow) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (slowSchedule.take 24) slow) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (slowSchedule.take 25) slow) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (slowSchedule.take 26) slow) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (slowSchedule.take 27) slow) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (slowSchedule.take 28) slow) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (slowSchedule.take 29) slow) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (slowSchedule.take 30) slow) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (slowSchedule.take 31) slow) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (slowSchedule.take 32) slow) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (slowSchedule.take 33) slow) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (slowSchedule.take 34) slow) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (slowSchedule.take 35) slow) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (slowSchedule.take 36) slow) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (slowSchedule.take 37) slow) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (slowSchedule.take 38) slow) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (slowSchedule.take 39) slow) = ([false, true], [14, 0, 0, 15]) ∧
      look (rules.runSchedule (slowSchedule.take 40) slow) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (slowSchedule.take 41) slow) = ([true, false], [0, 15, 14, 0]) ∧
      look (rules.runSchedule (slowSchedule.take 42) slow) = ([true, false], [0, 15, 14, 0]) ∧
      (rules.runSchedule (slowSchedule.take 42) slow).overflow = false := by
  rw [sstate_run_1, sstate_run_2, sstate_run_3, sstate_run_4, sstate_run_5, sstate_run_6,
    sstate_run_7, sstate_run_8, sstate_run_9, sstate_run_10, sstate_run_11, sstate_run_12,
    sstate_run_13, sstate_run_14, sstate_run_15, sstate_run_16, sstate_run_17, sstate_run_18,
    sstate_run_19, sstate_run_20, sstate_run_21, sstate_run_22, sstate_run_23, sstate_run_24,
    sstate_run_25, sstate_run_26, sstate_run_27, sstate_run_28, sstate_run_29, sstate_run_30,
    sstate_run_31, sstate_run_32, sstate_run_33, sstate_run_34, sstate_run_35, sstate_run_36,
    sstate_run_37, sstate_run_38, sstate_run_39, sstate_run_40, sstate_run_41, sstate_run_42]
  circuit_decide

assert_standard_axioms slow_alternates

/-- **The cycle certificate, delays 4 and 4.** Sixteen game ticks take the level after game
tick 24 to itself, moved on in time by 16 game ticks, with 13 more ticks scheduled. -/
theorem slow_cycle : rules.Cycle (rules.runSchedule (slowSchedule.take 24) slow) 16 13 := by
  rw [sstate_run_24]
  exact (Rules.steps_of_runs (k := 24) (m := 16) sstate_run_24 sstate_run_40
    (by circuit_decide)).trans (Level.eq_of_beqBlocks (by circuit_decide))

assert_standard_axioms slow_cycle

end Redstone.Theorems.Clock.RepeaterLoop
