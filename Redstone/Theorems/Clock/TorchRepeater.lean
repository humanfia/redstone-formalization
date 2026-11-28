import Redstone.Proof.Circuit
import Redstone.Lemmas.ShiftInvariant

/-!
# The torch and repeater clock

A redstone torch on the side of a block, and a line of repeaters that carries the torch's
signal round and back into that block. The torch inverts and the repeaters delay, so the loop
oscillates slowly enough for the torch not to burn out. This layout needs no redstone dust:
the first repeater reads the torch, each of the others reads the repeater or the powered
block before it, and the last one points into the block of the torch. The layer `y = 1` on a
4×3 stone floor, seen from above (east is right, south is down); `B` is the block of the
torch, `T` the torch, `S` stone, an arrow a repeater with the direction of its signal:

```
        x=0  1  2  3
  z=0    B   T  >  S
  z=1    ^         v
  z=2    S   <  <  S
```

The level is loaded without the torch, all repeaters off, which is a state of rest
(`circuit_quiescent`). Placing the torch starts the clock.

**The period is 24 game ticks (12 redstone ticks)**, twice the delay round the loop: 2 game
ticks for the torch and 2 for each of the five repeaters at delay 1. In general the period is
`2 * (2 + (2 * d₁ + ... + 2 * dₙ))` game ticks for repeaters at delays `d₁, ..., dₙ`. The torch
is lit for 12 game ticks and out for 12, and each repeater follows the one before it 2 game
ticks later.

What is proved:

* the torch and the five repeaters after each of the first 49 game ticks
  (`signal_goes_round`): two periods, and one game tick more;
* the cycle certificate (`cycle`): 24 game ticks take the level after game tick 60 to itself,
  moved on in time by 24 game ticks, with 12 more ticks scheduled. The certificate starts
  at game tick 60, when the burn-out list of the torch has its steady length;
* the torch and the repeaters after each of the game ticks 60 to 84 (`steady_period`), the
  period of the certificate.

**The clock runs for ever** (`runs_for_ever`): for every number `n` of game ticks after game
tick 60, the torch and the repeaters are as they are `n % 24` game ticks after game tick 60,
and the model reaches no bound. It follows from the certificate because a game tick commutes
with the time shift on levels made of air, stone, blocks of redstone, repeaters and torches
(`ShiftInvariant.step_shift` in `Redstone/Lemmas/ShiftInvariant.lean`). In particular the
torch never burns out.
-/

set_option Elab.async false

namespace Redstone.Theorems.Clock.TorchRepeater

/-- The 4×3 stone floor. -/
def floor : List (Pos × Block) :=
  (List.range 4).flatMap fun x => (List.range 3).map fun z => (⟨x, 0, z⟩, Block.plain .stone)

/-- The position of the torch: on the east side of its block. It is missing in the level as
loaded and is placed to start the clock. -/
def torch : Pos := ⟨1, 1, 0⟩

/-- The positions of the five repeaters, from the one that reads the torch to the one that
points into the block of the torch. -/
def repeaters : List Pos := [⟨2, 1, 0⟩, ⟨3, 1, 1⟩, ⟨2, 1, 2⟩, ⟨1, 1, 2⟩, ⟨0, 1, 1⟩]

/-- The loop without its torch, at rest: five repeaters at delay 1, all off, the block of the
torch at `⟨0, 1, 0⟩` and a stone block at each of the other three corners. -/
def circuit : Level :=
  .ofCells (floor ++ [
    (⟨0, 1, 0⟩, .plain .stone), (⟨3, 1, 0⟩, .plain .stone), (⟨3, 1, 2⟩, .plain .stone),
    (⟨0, 1, 2⟩, .plain .stone),
    (⟨2, 1, 0⟩, blk% "minecraft:repeater[delay=1,facing=west,locked=false,powered=false]"),
    (⟨3, 1, 1⟩, blk% "minecraft:repeater[delay=1,facing=north,locked=false,powered=false]"),
    (⟨2, 1, 2⟩, blk% "minecraft:repeater[delay=1,facing=east,locked=false,powered=false]"),
    (⟨1, 1, 2⟩, blk% "minecraft:repeater[delay=1,facing=east,locked=false,powered=false]"),
    (⟨0, 1, 1⟩, blk% "minecraft:repeater[delay=1,facing=south,locked=false,powered=false]")])

/-- The torch is placed, lit, before game tick 1; 84 game ticks in all. -/
def schedule : Schedule :=
  [[.set torch (.redstoneWallTorch ⟨.east, true⟩)]] ++ Schedule.idle 83

/-- Whether the torch is lit, and which of the five repeaters are on. -/
def lit (l : Level) : List Bool :=
  (match l.blockAt torch with
    | .redstoneWallTorch s => s.lit
    | _ => false) ::
  repeaters.map fun p =>
    match l.blockAt p with
    | .repeater s => s.powered
    | _ => false

checkpoints state := schedule from circuit

/-- The loop without its torch is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- `lit` only looks at the blocks. -/
theorem lit_congr {l l' : Level} (h : ∀ p, l.blockAt p = l'.blockAt p) : lit l = lit l' := by
  unfold lit
  simp only [h]

set_option synthInstance.maxSize 4096 in
/-- **Two periods of the clock.** The torch is lit from game tick 1. The repeaters come on
one after the other, after game ticks 2, 4, 6, 8 and 10; the last one powers the block of the
torch, which goes out after game tick 12; the repeaters go off one after the other, after game
ticks 14 to 22; the torch is lit again after game tick 24. After game tick 25 the loop is as
after game tick 1, and after game tick 49 again. The model reaches no bound in 84 game
ticks. -/
theorem signal_goes_round :
    lit (rules.runSchedule (schedule.take 1) circuit) =
        [true, false, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 2) circuit) =
        [true, true, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 3) circuit) =
        [true, true, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 4) circuit) = [true, true, true, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 5) circuit) = [true, true, true, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 6) circuit) = [true, true, true, true, false, false] ∧
      lit (rules.runSchedule (schedule.take 7) circuit) = [true, true, true, true, false, false] ∧
      lit (rules.runSchedule (schedule.take 8) circuit) = [true, true, true, true, true, false] ∧
      lit (rules.runSchedule (schedule.take 9) circuit) = [true, true, true, true, true, false] ∧
      lit (rules.runSchedule (schedule.take 10) circuit) = [true, true, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 11) circuit) = [true, true, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 12) circuit) = [false, true, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 13) circuit) = [false, true, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 14) circuit) = [false, false, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 15) circuit) = [false, false, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 16) circuit) =
        [false, false, false, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 17) circuit) =
        [false, false, false, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 18) circuit) =
        [false, false, false, false, true, true] ∧
      lit (rules.runSchedule (schedule.take 19) circuit) =
        [false, false, false, false, true, true] ∧
      lit (rules.runSchedule (schedule.take 20) circuit) =
        [false, false, false, false, false, true] ∧
      lit (rules.runSchedule (schedule.take 21) circuit) =
        [false, false, false, false, false, true] ∧
      lit (rules.runSchedule (schedule.take 22) circuit) =
        [false, false, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 23) circuit) =
        [false, false, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 24) circuit) =
        [true, false, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 25) circuit) =
        [true, false, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 26) circuit) =
        [true, true, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 27) circuit) =
        [true, true, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 28) circuit) =
        [true, true, true, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 29) circuit) =
        [true, true, true, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 30) circuit) = [true, true, true, true, false, false] ∧
      lit (rules.runSchedule (schedule.take 31) circuit) = [true, true, true, true, false, false] ∧
      lit (rules.runSchedule (schedule.take 32) circuit) = [true, true, true, true, true, false] ∧
      lit (rules.runSchedule (schedule.take 33) circuit) = [true, true, true, true, true, false] ∧
      lit (rules.runSchedule (schedule.take 34) circuit) = [true, true, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 35) circuit) = [true, true, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 36) circuit) = [false, true, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 37) circuit) = [false, true, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 38) circuit) = [false, false, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 39) circuit) = [false, false, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 40) circuit) =
        [false, false, false, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 41) circuit) =
        [false, false, false, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 42) circuit) =
        [false, false, false, false, true, true] ∧
      lit (rules.runSchedule (schedule.take 43) circuit) =
        [false, false, false, false, true, true] ∧
      lit (rules.runSchedule (schedule.take 44) circuit) =
        [false, false, false, false, false, true] ∧
      lit (rules.runSchedule (schedule.take 45) circuit) =
        [false, false, false, false, false, true] ∧
      lit (rules.runSchedule (schedule.take 46) circuit) =
        [false, false, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 47) circuit) =
        [false, false, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 48) circuit) =
        [true, false, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 49) circuit) =
        [true, false, false, false, false, false] ∧
      (rules.runSchedule (schedule.take 84) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13,
    state_run_14, state_run_15, state_run_16, state_run_17, state_run_18, state_run_19,
    state_run_20, state_run_21, state_run_22, state_run_23, state_run_24, state_run_25,
    state_run_26, state_run_27, state_run_28, state_run_29, state_run_30, state_run_31,
    state_run_32, state_run_33, state_run_34, state_run_35, state_run_36, state_run_37,
    state_run_38, state_run_39, state_run_40, state_run_41, state_run_42, state_run_43,
    state_run_44, state_run_45, state_run_46, state_run_47, state_run_48, state_run_49,
    state_run_84]
  circuit_decide

assert_standard_axioms signal_goes_round

/-- **The cycle certificate.** Twenty-four game ticks take the level after game tick 60 to
itself, moved on in time by 24 game ticks, with 12 more ticks scheduled: every block, the
scheduled tick, every counter, and the list of recent torch toggles. -/
theorem cycle : rules.Cycle (rules.runSchedule (schedule.take 60) circuit) 24 12 := by
  rw [state_run_60]
  exact (Rules.steps_of_runs (k := 60) (m := 24) state_run_60 state_run_84
    (by circuit_decide)).trans (Level.eq_of_beqBlocks (by circuit_decide))

assert_standard_axioms cycle

set_option synthInstance.maxSize 4096 in
/-- **The period the certificate is about**: the torch and the repeaters after each of the
game ticks 60 to 84. The torch is out from game tick 60 and lit again after game tick 72;
after game tick 84 the loop is as after game tick 60. -/
theorem steady_period :
    lit (rules.runSchedule (schedule.take 60) circuit) = [false, true, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 61) circuit) = [false, true, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 62) circuit) = [false, false, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 63) circuit) = [false, false, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 64) circuit) =
        [false, false, false, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 65) circuit) =
        [false, false, false, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 66) circuit) =
        [false, false, false, false, true, true] ∧
      lit (rules.runSchedule (schedule.take 67) circuit) =
        [false, false, false, false, true, true] ∧
      lit (rules.runSchedule (schedule.take 68) circuit) =
        [false, false, false, false, false, true] ∧
      lit (rules.runSchedule (schedule.take 69) circuit) =
        [false, false, false, false, false, true] ∧
      lit (rules.runSchedule (schedule.take 70) circuit) =
        [false, false, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 71) circuit) =
        [false, false, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 72) circuit) =
        [true, false, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 73) circuit) =
        [true, false, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 74) circuit) =
        [true, true, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 75) circuit) =
        [true, true, false, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 76) circuit) =
        [true, true, true, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 77) circuit) =
        [true, true, true, false, false, false] ∧
      lit (rules.runSchedule (schedule.take 78) circuit) = [true, true, true, true, false, false] ∧
      lit (rules.runSchedule (schedule.take 79) circuit) = [true, true, true, true, false, false] ∧
      lit (rules.runSchedule (schedule.take 80) circuit) = [true, true, true, true, true, false] ∧
      lit (rules.runSchedule (schedule.take 81) circuit) = [true, true, true, true, true, false] ∧
      lit (rules.runSchedule (schedule.take 82) circuit) = [true, true, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 83) circuit) = [true, true, true, true, true, true] ∧
      lit (rules.runSchedule (schedule.take 84) circuit) =
        [false, true, true, true, true, true] := by
  rw [state_run_60, state_run_61, state_run_62, state_run_63, state_run_64, state_run_65,
    state_run_66, state_run_67, state_run_68, state_run_69, state_run_70, state_run_71,
    state_run_72, state_run_73, state_run_74, state_run_75, state_run_76, state_run_77,
    state_run_78, state_run_79, state_run_80, state_run_81, state_run_82, state_run_83,
    state_run_84]
  circuit_decide

assert_standard_axioms steady_period

/-- **The clock runs for ever.** For every `n`, the torch and the repeaters `n` game ticks
after game tick 60 are as they are `n % 24` game ticks after game tick 60, which is game tick
`60 + n % 24` of the schedule (`steady_period` lists these); and the model reaches no
bound. -/
theorem runs_for_ever (n : ℕ) :
    lit (rules.steps n (rules.runSchedule (schedule.take 60) circuit)) =
        lit (rules.runSchedule (schedule.take (60 + n % 24)) circuit) ∧
      (rules.steps n (rules.runSchedule (schedule.take 60) circuit)).overflow = false := by
  have hl : ShiftInvariant.Calm (rules.runSchedule (schedule.take 60) circuit) := by
    rw [state_run_60]
    exact ShiftInvariant.Calm.of_calm (by circuit_decide)
  rw [lit_congr (ShiftInvariant.blockAt_steps_cycle cycle hl (by decide) n),
    ShiftInvariant.overflow_steps_cycle cycle hl (by decide) n]
  have hn : n % 24 < 24 := Nat.mod_lt _ (by decide)
  generalize n % 24 = i at hn ⊢
  rw [state_run_60]
  interval_cases i
  · rw [show rules.steps 0 state_60 = state_60 from rfl]
    exact ⟨congrArg lit state_run_60.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 1) state_run_60 state_run_61
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_61.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 2) state_run_60 state_run_62
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_62.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 3) state_run_60 state_run_63
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_63.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 4) state_run_60 state_run_64
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_64.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 5) state_run_60 state_run_65
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_65.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 6) state_run_60 state_run_66
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_66.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 7) state_run_60 state_run_67
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_67.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 8) state_run_60 state_run_68
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_68.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 9) state_run_60 state_run_69
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_69.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 10) state_run_60 state_run_70
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_70.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 11) state_run_60 state_run_71
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_71.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 12) state_run_60 state_run_72
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_72.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 13) state_run_60 state_run_73
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_73.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 14) state_run_60 state_run_74
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_74.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 15) state_run_60 state_run_75
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_75.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 16) state_run_60 state_run_76
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_76.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 17) state_run_60 state_run_77
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_77.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 18) state_run_60 state_run_78
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_78.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 19) state_run_60 state_run_79
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_79.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 20) state_run_60 state_run_80
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_80.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 21) state_run_60 state_run_81
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_81.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 22) state_run_60 state_run_82
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_82.symm, by circuit_decide⟩
  · rw [Rules.steps_of_runs (k := 60) (m := 23) state_run_60 state_run_83
      (by circuit_decide)]
    exact ⟨congrArg lit state_run_83.symm, by circuit_decide⟩

assert_standard_axioms runs_for_ever

end Redstone.Theorems.Clock.TorchRepeater
