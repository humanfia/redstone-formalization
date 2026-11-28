import Redstone.Proof.Circuit
import Redstone.Lemmas.ShiftInvariant

/-!
# The repeater ring without dust

Four repeaters in a ring, with a stone block at each corner, on a 3×3 stone floor. Each
repeater points into a corner block and powers it; the next repeater reads that block. No
redstone dust is needed. The layer `y = 1`, seen from above (east is right, south is down);
an arrow is a repeater and shows which way the signal goes through it, `S` is stone:

```
        x=0  1  2
  z=0    S   >  S
  z=1    ^      v
  z=2    S   <  S
```

The corner `⟨0, 1, 0⟩` is a block of redstone for one game tick. That starts a pulse which
goes round the ring for good. **The period is the sum of the four delays**: a repeater at
delay `d` takes `2 * d` game ticks (`d` redstone ticks), so the ring with delays 1, 1, 1, 1
has a period of 8 game ticks (4 redstone ticks), the ring with delays 1, 2, 3, 4 a period of
20 game ticks (10 redstone ticks), and the ring with delays 4, 4, 4, 4 a period of 32 game
ticks (16 redstone ticks).

What is proved, for the delays 1, 1, 1, 1 (`circuit`):

* the state of the four repeaters after each of 18 game ticks (`pulse_goes_round`): the two
  game ticks of the start and two periods. Each repeater is on for two game ticks, one after
  the other;
* the cycle certificate (`cycle`): 8 game ticks take the level after game tick 10 to itself,
  moved on in time by 8 game ticks, with 8 more ticks scheduled.

For the delays 1, 2, 3, 4 (`mixed`):

* the first lap (`mixed_first_lap`, game ticks 1 to 21): the pulse starts two game ticks long
  and every slower repeater stretches it to its own delay, so it comes out of the last
  repeater eight game ticks long;
* two periods of the steady state (`mixed_period`, game ticks 22 to 62): each repeater is on
  for 8 game ticks out of 20, and two neighbours overlap;
* the cycle certificate (`mixed_cycle`): 20 game ticks take the level after game tick 22 to
  itself, moved on by 20 game ticks, with 8 more ticks scheduled.

For the delays 4, 4, 4, 4 (`slow`):

* the state of the four repeaters after each of 74 game ticks (`slow_pulse_goes_round`): the
  start and two periods. One game tick of input is enough: the first repeater comes on after
  game tick 8 and stays on for 8 game ticks, and so does each of the others in turn;
* the cycle certificate (`slow_cycle`): 32 game ticks take the level after game tick 10 to
  itself, moved on by 32 game ticks, with 8 more ticks scheduled.

**The three rings run for ever** (`runs_for_ever`, `mixed_runs_for_ever`,
`slow_runs_for_ever`): for every number `n` of game ticks after the first checkpoint of the
certificate, the repeaters are as they are `n` modulo the period game ticks after it, which
the bounded theorems list, and the model reaches no bound. This is periodicity in the full
sense. It follows from the certificate because a game tick commutes with the time shift on
levels made of air, stone, blocks of redstone, repeaters and torches
(`ShiftInvariant.step_shift` in `Redstone/Lemmas/ShiftInvariant.lean`), and these rings have
no other block.

All three levels are loaded raw and are at rest (`circuit_quiescent`, `mixed_quiescent`,
`slow_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Clock.RepeaterRing

/-- The 3×3 stone floor. -/
def floor : List (Pos × Block) :=
  (List.range 3).flatMap fun x => (List.range 3).map fun z => (⟨x, 0, z⟩, Block.plain .stone)

/-- The corner whose stone block is a block of redstone for one game tick, to start the pulse. -/
def start : Pos := ⟨0, 1, 0⟩

/-- The positions of the four repeaters, in the order in which the pulse reaches them. -/
def repeaters : List Pos := [⟨1, 1, 0⟩, ⟨2, 1, 1⟩, ⟨1, 1, 2⟩, ⟨0, 1, 1⟩]

/-- The ring made of the four given repeaters, in the order of `repeaters`, with a stone block
at each corner. -/
def ring (r₁ r₂ r₃ r₄ : Block) : Level :=
  .ofCells (floor ++ [
    (⟨0, 1, 0⟩, .plain .stone), (⟨2, 1, 0⟩, .plain .stone), (⟨2, 1, 2⟩, .plain .stone),
    (⟨0, 1, 2⟩, .plain .stone),
    (⟨1, 1, 0⟩, r₁), (⟨2, 1, 1⟩, r₂), (⟨1, 1, 2⟩, r₃), (⟨0, 1, 1⟩, r₄)])

/-- The ring with every repeater at delay 1 (two game ticks), all off. -/
def circuit : Level :=
  ring (blk% "minecraft:repeater[delay=1,facing=west,locked=false,powered=false]")
    (blk% "minecraft:repeater[delay=1,facing=north,locked=false,powered=false]")
    (blk% "minecraft:repeater[delay=1,facing=east,locked=false,powered=false]")
    (blk% "minecraft:repeater[delay=1,facing=south,locked=false,powered=false]")

/-- The ring with the repeaters at delays 1, 2, 3 and 4 (2, 4, 6 and 8 game ticks), all off. -/
def mixed : Level :=
  ring (blk% "minecraft:repeater[delay=1,facing=west,locked=false,powered=false]")
    (blk% "minecraft:repeater[delay=2,facing=north,locked=false,powered=false]")
    (blk% "minecraft:repeater[delay=3,facing=east,locked=false,powered=false]")
    (blk% "minecraft:repeater[delay=4,facing=south,locked=false,powered=false]")

/-- The ring with every repeater at delay 4 (eight game ticks), all off. -/
def slow : Level :=
  ring (blk% "minecraft:repeater[delay=4,facing=west,locked=false,powered=false]")
    (blk% "minecraft:repeater[delay=4,facing=north,locked=false,powered=false]")
    (blk% "minecraft:repeater[delay=4,facing=east,locked=false,powered=false]")
    (blk% "minecraft:repeater[delay=4,facing=south,locked=false,powered=false]")

/-- The corner `start` is a block of redstone during game tick 1 and stone again from game
tick 2 on; then 16 game ticks without input. -/
def schedule : Schedule :=
  [[.set start (.plain .redstone_block)], [.set start (.plain .stone)]] ++ Schedule.idle 16

/-- The same start, and then 60 game ticks without input. -/
def mixedSchedule : Schedule :=
  [[.set start (.plain .redstone_block)], [.set start (.plain .stone)]] ++ Schedule.idle 60

/-- The same start, and then 72 game ticks without input. -/
def slowSchedule : Schedule :=
  [[.set start (.plain .redstone_block)], [.set start (.plain .stone)]] ++ Schedule.idle 72

/-- Which of the four repeaters are on, in the order of the ring. -/
def lit (l : Level) : List Bool :=
  repeaters.map fun p =>
    match l.blockAt p with
    | .repeater s => s.powered
    | _ => false

checkpoints state := schedule from circuit

checkpoints mstate := mixedSchedule from mixed

checkpoints sstate := slowSchedule from slow

/-- The ring with delays 1, 1, 1, 1 as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- The ring with delays 1, 2, 3, 4 as built is at rest. -/
theorem mixed_quiescent : mixed.Quiescent := by circuit_decide

assert_standard_axioms mixed_quiescent

/-- The ring with delays 4, 4, 4, 4 as built is at rest. -/
theorem slow_quiescent : slow.Quiescent := by circuit_decide

assert_standard_axioms slow_quiescent

/-- `lit` only looks at the blocks. -/
theorem lit_congr {l l' : Level} (h : ∀ p, l.blockAt p = l'.blockAt p) : lit l = lit l' := by
  unfold lit
  simp only [h]

/-- **The pulse goes round the ring, delays 1, 1, 1, 1.** After game tick 1 no repeater is on
yet; after game tick 2 the first one is on; every two game ticks the pulse is at the next
repeater; after game tick 10 it is back at the first, and after game tick 18 again. The model
reaches no bound. -/
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
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13,
    state_run_14, state_run_15, state_run_16, state_run_17, state_run_18]
  circuit_decide

assert_standard_axioms pulse_goes_round

/-- **The cycle certificate.** Eight game ticks take the level after game tick 10 to itself,
moved on in time by 8 game ticks, with 8 more ticks scheduled: every block, every scheduled
tick, every counter. -/
theorem cycle : rules.Cycle (rules.runSchedule (schedule.take 10) circuit) 8 8 := by
  rw [state_run_10]
  exact (Rules.steps_of_runs (k := 10) (m := 8) state_run_10 state_run_18
    (by circuit_decide)).trans (Level.eq_of_beqBlocks (by circuit_decide))

assert_standard_axioms cycle

set_option synthInstance.maxSize 4096 in
/-- **The first lap, delays 1, 2, 3, 4.** The first repeater is on for two game ticks (2 and
3), the second for four (6 to 9), the third for six (12 to 17): a repeater whose input goes
away before its delay has passed stays on for the length of its delay. The fourth comes on
after game tick 20. -/
theorem mixed_first_lap :
    lit (rules.runSchedule (mixedSchedule.take 1) mixed) = [false, false, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 2) mixed) = [true, false, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 3) mixed) = [true, false, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 4) mixed) = [false, false, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 5) mixed) = [false, false, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 6) mixed) = [false, true, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 7) mixed) = [false, true, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 8) mixed) = [false, true, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 9) mixed) = [false, true, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 10) mixed) = [false, false, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 11) mixed) = [false, false, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 12) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 13) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 14) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 15) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 16) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 17) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 18) mixed) = [false, false, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 19) mixed) = [false, false, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 20) mixed) = [false, false, false, true] ∧
      lit (rules.runSchedule (mixedSchedule.take 21) mixed) = [false, false, false, true] ∧
      (rules.runSchedule (mixedSchedule.take 21) mixed).overflow = false := by
  rw [mstate_run_1, mstate_run_2, mstate_run_3, mstate_run_4, mstate_run_5, mstate_run_6,
    mstate_run_7, mstate_run_8, mstate_run_9, mstate_run_10, mstate_run_11, mstate_run_12,
    mstate_run_13, mstate_run_14, mstate_run_15, mstate_run_16, mstate_run_17, mstate_run_18,
    mstate_run_19, mstate_run_20, mstate_run_21]
  circuit_decide

assert_standard_axioms mixed_first_lap

set_option synthInstance.maxSize 4096 in
/-- **Two periods of the steady state, delays 1, 2, 3, 4.** From game tick 22 on the ring
repeats every 20 game ticks: the first repeater is on during game ticks 22 to 29, the second
during 26 to 33, the third during 32 to 39 and the fourth during 40 to 47; and the same 20
game ticks later. The model reaches no bound. -/
theorem mixed_period :
    lit (rules.runSchedule (mixedSchedule.take 22) mixed) = [true, false, false, true] ∧
      lit (rules.runSchedule (mixedSchedule.take 23) mixed) = [true, false, false, true] ∧
      lit (rules.runSchedule (mixedSchedule.take 24) mixed) = [true, false, false, true] ∧
      lit (rules.runSchedule (mixedSchedule.take 25) mixed) = [true, false, false, true] ∧
      lit (rules.runSchedule (mixedSchedule.take 26) mixed) = [true, true, false, true] ∧
      lit (rules.runSchedule (mixedSchedule.take 27) mixed) = [true, true, false, true] ∧
      lit (rules.runSchedule (mixedSchedule.take 28) mixed) = [true, true, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 29) mixed) = [true, true, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 30) mixed) = [false, true, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 31) mixed) = [false, true, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 32) mixed) = [false, true, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 33) mixed) = [false, true, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 34) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 35) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 36) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 37) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 38) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 39) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 40) mixed) = [false, false, false, true] ∧
      lit (rules.runSchedule (mixedSchedule.take 41) mixed) = [false, false, false, true] ∧
      lit (rules.runSchedule (mixedSchedule.take 42) mixed) = [true, false, false, true] ∧
      lit (rules.runSchedule (mixedSchedule.take 43) mixed) = [true, false, false, true] ∧
      lit (rules.runSchedule (mixedSchedule.take 44) mixed) = [true, false, false, true] ∧
      lit (rules.runSchedule (mixedSchedule.take 45) mixed) = [true, false, false, true] ∧
      lit (rules.runSchedule (mixedSchedule.take 46) mixed) = [true, true, false, true] ∧
      lit (rules.runSchedule (mixedSchedule.take 47) mixed) = [true, true, false, true] ∧
      lit (rules.runSchedule (mixedSchedule.take 48) mixed) = [true, true, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 49) mixed) = [true, true, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 50) mixed) = [false, true, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 51) mixed) = [false, true, false, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 52) mixed) = [false, true, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 53) mixed) = [false, true, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 54) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 55) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 56) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 57) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 58) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 59) mixed) = [false, false, true, false] ∧
      lit (rules.runSchedule (mixedSchedule.take 60) mixed) = [false, false, false, true] ∧
      lit (rules.runSchedule (mixedSchedule.take 61) mixed) = [false, false, false, true] ∧
      lit (rules.runSchedule (mixedSchedule.take 62) mixed) = [true, false, false, true] ∧
      (rules.runSchedule (mixedSchedule.take 62) mixed).overflow = false := by
  rw [mstate_run_22, mstate_run_23, mstate_run_24, mstate_run_25, mstate_run_26, mstate_run_27,
    mstate_run_28, mstate_run_29, mstate_run_30, mstate_run_31, mstate_run_32, mstate_run_33,
    mstate_run_34, mstate_run_35, mstate_run_36, mstate_run_37, mstate_run_38, mstate_run_39,
    mstate_run_40, mstate_run_41, mstate_run_42, mstate_run_43, mstate_run_44, mstate_run_45,
    mstate_run_46, mstate_run_47, mstate_run_48, mstate_run_49, mstate_run_50, mstate_run_51,
    mstate_run_52, mstate_run_53, mstate_run_54, mstate_run_55, mstate_run_56, mstate_run_57,
    mstate_run_58, mstate_run_59, mstate_run_60, mstate_run_61, mstate_run_62]
  circuit_decide

assert_standard_axioms mixed_period

/-- **The cycle certificate for the delays 1, 2, 3, 4.** Twenty game ticks take the level
after game tick 22 to itself, moved on in time by 20 game ticks, with 8 more ticks
scheduled. -/
theorem mixed_cycle : rules.Cycle (rules.runSchedule (mixedSchedule.take 22) mixed) 20 8 := by
  rw [mstate_run_22]
  exact (Rules.steps_of_runs (k := 22) (m := 20) mstate_run_22 mstate_run_42
    (by circuit_decide)).trans (Level.eq_of_beqBlocks (by circuit_decide))

assert_standard_axioms mixed_cycle

set_option synthInstance.maxSize 4096 in
/-- **The pulse goes round the ring, delays 4, 4, 4, 4.** The first repeater comes on after
game tick 8, eight game ticks after its input, and stays on for eight game ticks although the
input lasted one; then the second is on for eight game ticks, and so on. After game tick 42
the ring is as after game tick 10, and after game tick 74 again. The model reaches no
bound. -/
theorem slow_pulse_goes_round :
    lit (rules.runSchedule (slowSchedule.take 1) slow) = [false, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 2) slow) = [false, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 3) slow) = [false, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 4) slow) = [false, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 5) slow) = [false, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 6) slow) = [false, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 7) slow) = [false, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 8) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 9) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 10) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 11) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 12) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 13) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 14) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 15) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 16) slow) = [false, true, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 17) slow) = [false, true, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 18) slow) = [false, true, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 19) slow) = [false, true, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 20) slow) = [false, true, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 21) slow) = [false, true, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 22) slow) = [false, true, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 23) slow) = [false, true, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 24) slow) = [false, false, true, false] ∧
      lit (rules.runSchedule (slowSchedule.take 25) slow) = [false, false, true, false] ∧
      lit (rules.runSchedule (slowSchedule.take 26) slow) = [false, false, true, false] ∧
      lit (rules.runSchedule (slowSchedule.take 27) slow) = [false, false, true, false] ∧
      lit (rules.runSchedule (slowSchedule.take 28) slow) = [false, false, true, false] ∧
      lit (rules.runSchedule (slowSchedule.take 29) slow) = [false, false, true, false] ∧
      lit (rules.runSchedule (slowSchedule.take 30) slow) = [false, false, true, false] ∧
      lit (rules.runSchedule (slowSchedule.take 31) slow) = [false, false, true, false] ∧
      lit (rules.runSchedule (slowSchedule.take 32) slow) = [false, false, false, true] ∧
      lit (rules.runSchedule (slowSchedule.take 33) slow) = [false, false, false, true] ∧
      lit (rules.runSchedule (slowSchedule.take 34) slow) = [false, false, false, true] ∧
      lit (rules.runSchedule (slowSchedule.take 35) slow) = [false, false, false, true] ∧
      lit (rules.runSchedule (slowSchedule.take 36) slow) = [false, false, false, true] ∧
      lit (rules.runSchedule (slowSchedule.take 37) slow) = [false, false, false, true] ∧
      lit (rules.runSchedule (slowSchedule.take 38) slow) = [false, false, false, true] ∧
      lit (rules.runSchedule (slowSchedule.take 39) slow) = [false, false, false, true] ∧
      lit (rules.runSchedule (slowSchedule.take 40) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 41) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 42) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 43) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 44) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 45) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 46) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 47) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 48) slow) = [false, true, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 49) slow) = [false, true, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 50) slow) = [false, true, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 51) slow) = [false, true, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 52) slow) = [false, true, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 53) slow) = [false, true, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 54) slow) = [false, true, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 55) slow) = [false, true, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 56) slow) = [false, false, true, false] ∧
      lit (rules.runSchedule (slowSchedule.take 57) slow) = [false, false, true, false] ∧
      lit (rules.runSchedule (slowSchedule.take 58) slow) = [false, false, true, false] ∧
      lit (rules.runSchedule (slowSchedule.take 59) slow) = [false, false, true, false] ∧
      lit (rules.runSchedule (slowSchedule.take 60) slow) = [false, false, true, false] ∧
      lit (rules.runSchedule (slowSchedule.take 61) slow) = [false, false, true, false] ∧
      lit (rules.runSchedule (slowSchedule.take 62) slow) = [false, false, true, false] ∧
      lit (rules.runSchedule (slowSchedule.take 63) slow) = [false, false, true, false] ∧
      lit (rules.runSchedule (slowSchedule.take 64) slow) = [false, false, false, true] ∧
      lit (rules.runSchedule (slowSchedule.take 65) slow) = [false, false, false, true] ∧
      lit (rules.runSchedule (slowSchedule.take 66) slow) = [false, false, false, true] ∧
      lit (rules.runSchedule (slowSchedule.take 67) slow) = [false, false, false, true] ∧
      lit (rules.runSchedule (slowSchedule.take 68) slow) = [false, false, false, true] ∧
      lit (rules.runSchedule (slowSchedule.take 69) slow) = [false, false, false, true] ∧
      lit (rules.runSchedule (slowSchedule.take 70) slow) = [false, false, false, true] ∧
      lit (rules.runSchedule (slowSchedule.take 71) slow) = [false, false, false, true] ∧
      lit (rules.runSchedule (slowSchedule.take 72) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 73) slow) = [true, false, false, false] ∧
      lit (rules.runSchedule (slowSchedule.take 74) slow) = [true, false, false, false] ∧
      (rules.runSchedule (slowSchedule.take 74) slow).overflow = false := by
  rw [sstate_run_1, sstate_run_2, sstate_run_3, sstate_run_4, sstate_run_5, sstate_run_6,
    sstate_run_7, sstate_run_8, sstate_run_9, sstate_run_10, sstate_run_11, sstate_run_12,
    sstate_run_13, sstate_run_14, sstate_run_15, sstate_run_16, sstate_run_17, sstate_run_18,
    sstate_run_19, sstate_run_20, sstate_run_21, sstate_run_22, sstate_run_23, sstate_run_24,
    sstate_run_25, sstate_run_26, sstate_run_27, sstate_run_28, sstate_run_29, sstate_run_30,
    sstate_run_31, sstate_run_32, sstate_run_33, sstate_run_34, sstate_run_35, sstate_run_36,
    sstate_run_37, sstate_run_38, sstate_run_39, sstate_run_40, sstate_run_41, sstate_run_42,
    sstate_run_43, sstate_run_44, sstate_run_45, sstate_run_46, sstate_run_47, sstate_run_48,
    sstate_run_49, sstate_run_50, sstate_run_51, sstate_run_52, sstate_run_53, sstate_run_54,
    sstate_run_55, sstate_run_56, sstate_run_57, sstate_run_58, sstate_run_59, sstate_run_60,
    sstate_run_61, sstate_run_62, sstate_run_63, sstate_run_64, sstate_run_65, sstate_run_66,
    sstate_run_67, sstate_run_68, sstate_run_69, sstate_run_70, sstate_run_71, sstate_run_72,
    sstate_run_73, sstate_run_74]
  circuit_decide

assert_standard_axioms slow_pulse_goes_round

/-- **The cycle certificate for the delays 4, 4, 4, 4.** Thirty-two game ticks take the level
after game tick 10 to itself, moved on in time by 32 game ticks, with 8 more ticks
scheduled. -/
theorem slow_cycle : rules.Cycle (rules.runSchedule (slowSchedule.take 10) slow) 32 8 := by
  rw [sstate_run_10]
  exact (Rules.steps_of_runs (k := 10) (m := 32) sstate_run_10 sstate_run_42
    (by circuit_decide)).trans (Level.eq_of_beqBlocks (by circuit_decide))

assert_standard_axioms slow_cycle

/-- **The ring with delays 1, 1, 1, 1 runs for ever.** For every `n`, the repeaters `n` game
ticks after game tick 10 are as they are `n % 8` game ticks after game tick 10 (see
`pulse_goes_round`), and the model reaches no bound. -/
theorem runs_for_ever (n : ℕ) :
    lit (rules.steps n (rules.runSchedule (schedule.take 10) circuit)) =
        lit (rules.runSchedule (schedule.take (10 + n % 8)) circuit) ∧
      (rules.steps n (rules.runSchedule (schedule.take 10) circuit)).overflow = false := by
  have hl : ShiftInvariant.Calm (rules.runSchedule (schedule.take 10) circuit) := by
    rw [state_run_10]
    exact ShiftInvariant.Calm.of_calm (by circuit_decide)
  rw [lit_congr (ShiftInvariant.blockAt_steps_cycle cycle hl (by decide) n),
    ShiftInvariant.overflow_steps_cycle cycle hl (by decide) n]
  have hn : n % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize n % 8 = i at hn ⊢
  rw [state_run_10]
  interval_cases i
  · rw [show rules.steps 0 state_10 = state_10 from rfl]
    exact ⟨congrArg lit state_run_10.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 1) state_run_10 state_run_11
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_11.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 2) state_run_10 state_run_12
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_12.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 3) state_run_10 state_run_13
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_13.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 4) state_run_10 state_run_14
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_14.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 5) state_run_10 state_run_15
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_15.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 6) state_run_10 state_run_16
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_16.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 7) state_run_10 state_run_17
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_17.symm, by circuit_decide⟩

assert_standard_axioms runs_for_ever

/-- **The ring with delays 1, 2, 3, 4 runs for ever.** For every `n`, the repeaters `n` game
ticks after game tick 22 are as they are `n % 20` game ticks after game tick 22 (see
`mixed_period`), and the model reaches no bound. -/
theorem mixed_runs_for_ever (n : ℕ) :
    lit (rules.steps n (rules.runSchedule (mixedSchedule.take 22) mixed)) =
        lit (rules.runSchedule (mixedSchedule.take (22 + n % 20)) mixed) ∧
      (rules.steps n (rules.runSchedule (mixedSchedule.take 22) mixed)).overflow = false := by
  have hl : ShiftInvariant.Calm (rules.runSchedule (mixedSchedule.take 22) mixed) := by
    rw [mstate_run_22]
    exact ShiftInvariant.Calm.of_calm (by circuit_decide)
  rw [lit_congr (ShiftInvariant.blockAt_steps_cycle mixed_cycle hl (by decide) n),
    ShiftInvariant.overflow_steps_cycle mixed_cycle hl (by decide) n]
  have hn : n % 20 < 20 := Nat.mod_lt _ (by decide)
  generalize n % 20 = i at hn ⊢
  rw [mstate_run_22]
  interval_cases i
  · rw [show rules.steps 0 mstate_22 = mstate_22 from rfl]
    exact ⟨congrArg lit mstate_run_22.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 1) mstate_run_22 mstate_run_23
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_23.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 2) mstate_run_22 mstate_run_24
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_24.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 3) mstate_run_22 mstate_run_25
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_25.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 4) mstate_run_22 mstate_run_26
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_26.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 5) mstate_run_22 mstate_run_27
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_27.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 6) mstate_run_22 mstate_run_28
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_28.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 7) mstate_run_22 mstate_run_29
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_29.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 8) mstate_run_22 mstate_run_30
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_30.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 9) mstate_run_22 mstate_run_31
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_31.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 10) mstate_run_22 mstate_run_32
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_32.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 11) mstate_run_22 mstate_run_33
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_33.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 12) mstate_run_22 mstate_run_34
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_34.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 13) mstate_run_22 mstate_run_35
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_35.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 14) mstate_run_22 mstate_run_36
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_36.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 15) mstate_run_22 mstate_run_37
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_37.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 16) mstate_run_22 mstate_run_38
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_38.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 17) mstate_run_22 mstate_run_39
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_39.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 18) mstate_run_22 mstate_run_40
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_40.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 22) (m := 19) mstate_run_22 mstate_run_41
      (by circuit_decide)]
    exact ⟨congrArg lit mstate_run_41.symm, by circuit_decide⟩

assert_standard_axioms mixed_runs_for_ever

/-- **The ring with delays 4, 4, 4, 4 runs for ever.** For every `n`, the repeaters `n` game
ticks after game tick 10 are as they are `n % 32` game ticks after game tick 10 (see
`slow_pulse_goes_round`), and the model reaches no bound. -/
theorem slow_runs_for_ever (n : ℕ) :
    lit (rules.steps n (rules.runSchedule (slowSchedule.take 10) slow)) =
        lit (rules.runSchedule (slowSchedule.take (10 + n % 32)) slow) ∧
      (rules.steps n (rules.runSchedule (slowSchedule.take 10) slow)).overflow = false := by
  have hl : ShiftInvariant.Calm (rules.runSchedule (slowSchedule.take 10) slow) := by
    rw [sstate_run_10]
    exact ShiftInvariant.Calm.of_calm (by circuit_decide)
  rw [lit_congr (ShiftInvariant.blockAt_steps_cycle slow_cycle hl (by decide) n),
    ShiftInvariant.overflow_steps_cycle slow_cycle hl (by decide) n]
  have hn : n % 32 < 32 := Nat.mod_lt _ (by decide)
  generalize n % 32 = i at hn ⊢
  rw [sstate_run_10]
  interval_cases i
  · rw [show rules.steps 0 sstate_10 = sstate_10 from rfl]
    exact ⟨congrArg lit sstate_run_10.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 1) sstate_run_10 sstate_run_11
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_11.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 2) sstate_run_10 sstate_run_12
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_12.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 3) sstate_run_10 sstate_run_13
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_13.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 4) sstate_run_10 sstate_run_14
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_14.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 5) sstate_run_10 sstate_run_15
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_15.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 6) sstate_run_10 sstate_run_16
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_16.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 7) sstate_run_10 sstate_run_17
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_17.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 8) sstate_run_10 sstate_run_18
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_18.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 9) sstate_run_10 sstate_run_19
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_19.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 10) sstate_run_10 sstate_run_20
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_20.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 11) sstate_run_10 sstate_run_21
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_21.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 12) sstate_run_10 sstate_run_22
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_22.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 13) sstate_run_10 sstate_run_23
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_23.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 14) sstate_run_10 sstate_run_24
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_24.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 15) sstate_run_10 sstate_run_25
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_25.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 16) sstate_run_10 sstate_run_26
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_26.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 17) sstate_run_10 sstate_run_27
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_27.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 18) sstate_run_10 sstate_run_28
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_28.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 19) sstate_run_10 sstate_run_29
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_29.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 20) sstate_run_10 sstate_run_30
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_30.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 21) sstate_run_10 sstate_run_31
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_31.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 22) sstate_run_10 sstate_run_32
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_32.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 23) sstate_run_10 sstate_run_33
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_33.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 24) sstate_run_10 sstate_run_34
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_34.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 25) sstate_run_10 sstate_run_35
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_35.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 26) sstate_run_10 sstate_run_36
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_36.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 27) sstate_run_10 sstate_run_37
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_37.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 28) sstate_run_10 sstate_run_38
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_38.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 29) sstate_run_10 sstate_run_39
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_39.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 30) sstate_run_10 sstate_run_40
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_40.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 10) (m := 31) sstate_run_10 sstate_run_41
      (by circuit_decide)]
    exact ⟨congrArg lit sstate_run_41.symm, by circuit_decide⟩

assert_standard_axioms slow_runs_for_ever

end Redstone.Theorems.Clock.RepeaterRing
