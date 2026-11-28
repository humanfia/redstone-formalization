import Redstone.Proof.Circuit

/-!
# The rapid torch clock, and how it burns out

One redstone torch that switches itself off: the torch hangs on the east side of a stone
block, a second stone block sits above the torch, and one piece of redstone dust lies on the
first block, next to the second. Side view (east is right, up is up); `B` is a block, `T`
the torch, `d` the dust:

```
  y=2    d  B
  y=1    B  T
        x=0 1
```

A lit torch gives strong power to the block above it; that block powers the dust; the dust
powers the block under it, which is the block the torch hangs on; so the torch goes out two
game ticks later, the dust goes off, and the torch lights up again after two more. The torch
flashes with a period of 4 game ticks (2 redstone ticks), and that is too fast for it.

`RedstoneTorchBlock` keeps a list of the game times at which torches were switched off
(`RECENT_TOGGLES`, here `Level.recentTorchToggles`). An entry leaves the list, from the
front, once it is more than 60 game ticks old. A torch that is switched off while the list
holds eight entries for its position, the new one included, is *burnt out*: it does not light
up again while eight entries remain.

What is proved, with the torch placed before game tick 1:

* **eight flashes** (`eight_pulses`): the torch is lit after game ticks 1, 4-5, 8-9, ...,
  28-29 and out after game ticks 2-3, 6-7, ..., 30-31, and the dust follows it with power 15
  or 0;
* **the list** (`toggles_recorded`): after game tick 32 the burn-out list holds exactly the
  game times 2, 6, 10, 14, 18, 22, 26, 30 of the eight switch-offs;
* **burnt out for good** (`burnt_out`): after the eighth switch-off the torch stays out, for
  ever, as long as nothing touches the circuit. The level after game tick 32 is at rest.

  A torch that burns out asks for a tick 160 game ticks later (`RESTART_DELAY`). In this
  circuit the model drops that request: by the time it is made, the torch has already
  scheduled its ordinary tick two game ticks ahead (its own switch-off turned the dust off,
  and the neighbour update came back to it), and `Level.scheduleTick`, like the game's
  `LevelChunkTicks.schedule`, keeps one scheduled tick per position and block. The ordinary
  tick runs in game tick 32, finds eight entries, and leaves the torch out. Nothing is
  scheduled after that;
* **a neighbour update that comes too early** (`poke_too_early`): a stone block put next to
  the torch before game tick 61 makes the torch schedule a tick, which runs in game tick 62.
  The oldest entry is from game tick 2, exactly 60 game ticks old and not more, so it stays,
  the list still has eight entries and the torch stays out, again for ever;
* **a neighbour update one game tick later** (`poke_relights`): put before game tick 62, the
  same block makes the torch tick in game tick 63. Now the oldest entry is 61 game ticks old
  and is dropped, seven remain, and the torch lights up. From then on an old entry expires
  just as each new one is added, four game ticks apart, so the torch flashes eight more times
  (lit after game ticks 63-64, 67-68, ..., 91-92) until the list holds eight entries from the
  new run alone, the game times 65, 69, ..., 93. Then it is burnt out again, and at rest.

So the threshold of `RECENT_TOGGLE_TIMER` is exact: more than 60 game ticks, not 60. The
generic statements behind this (the count, the window, the tick of a torch on an arbitrary
level) are in `Redstone/Lemmas/TorchBurnout.lean`.

The level is loaded raw, without the torch, and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Clock.RapidClock

/-- The position of the torch: on the east side of the lower block. -/
def torch : Pos := ⟨1, 1, 0⟩

/-- The position of the dust: on top of the lower block, next to the upper block. -/
def wire : Pos := ⟨0, 2, 0⟩

/-- The cell east of the torch. Putting a block there gives the torch a neighbour update. -/
def poke : Pos := ⟨2, 1, 0⟩

/-- The two blocks and the dust, without the torch: the block the torch will hang on, the
block above the torch, and the dust on the first block. -/
def circuit : Level :=
  .ofCells [(⟨0, 1, 0⟩, .plain .stone), (⟨1, 2, 0⟩, .plain .stone),
    (wire, blk% "minecraft:redstone_wire[east=none,north=none,power=0,south=none,west=none]")]

/-- The torch is placed, lit, before game tick 1; 32 game ticks in all. -/
def schedule : Schedule :=
  [[.set torch (.redstoneWallTorch ⟨.east, true⟩)]] ++ Schedule.idle 31

/-- The level after the 32 game ticks of `schedule`, when the torch has burnt out. -/
def burnt : Level := rules.runSchedule schedule circuit

/-- After the burn-out: nothing until game tick 60, a stone block is put at `poke` before game
tick 61, and three more game ticks (to game tick 64). -/
def early : Schedule := Schedule.idle 28 ++ [[.set poke (.plain .stone)]] ++ Schedule.idle 3

/-- After the burn-out: nothing until game tick 61, a stone block is put at `poke` before game
tick 62, and 34 more game ticks (to game tick 96). -/
def late : Schedule := Schedule.idle 29 ++ [[.set poke (.plain .stone)]] ++ Schedule.idle 34

/-- Whether the torch is lit, and the power of the dust. -/
def look (l : Level) : Bool × ℕ :=
  (match l.blockAt torch with
    | .redstoneWallTorch s => s.lit
    | _ => false,
    l.dustPower wire)

checkpoints state := schedule from circuit

checkpoints estate := early from state_32

checkpoints lstate := late from state_32

/-- The two blocks and the dust, without the torch, are at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- What `look` sees does not depend on the clocks of the level. -/
theorem look_advance (l : Level) (n : ℕ) : look (l.advance n) = look l := rfl

/-- The level after the burn-out is the checkpoint after game tick 32. -/
theorem burnt_eq : burnt = state_32 := by rw [burnt, state_run]

set_option synthInstance.maxSize 4096 in
/-- **Eight flashes.** The torch is placed before game tick 1. It is lit after game tick 1,
out after game ticks 2 and 3, lit after game ticks 4 and 5, and so on with a period of four
game ticks; the dust has power 15 while the torch is lit and 0 while it is out. The eighth
switch-off is in game tick 30, and after that the torch stays out. The model reaches no
bound. -/
theorem eight_pulses :
    look (rules.runSchedule (schedule.take 1) circuit) = (true, 15) ∧
      look (rules.runSchedule (schedule.take 2) circuit) = (false, 0) ∧
      look (rules.runSchedule (schedule.take 3) circuit) = (false, 0) ∧
      look (rules.runSchedule (schedule.take 4) circuit) = (true, 15) ∧
      look (rules.runSchedule (schedule.take 5) circuit) = (true, 15) ∧
      look (rules.runSchedule (schedule.take 6) circuit) = (false, 0) ∧
      look (rules.runSchedule (schedule.take 7) circuit) = (false, 0) ∧
      look (rules.runSchedule (schedule.take 8) circuit) = (true, 15) ∧
      look (rules.runSchedule (schedule.take 9) circuit) = (true, 15) ∧
      look (rules.runSchedule (schedule.take 10) circuit) = (false, 0) ∧
      look (rules.runSchedule (schedule.take 11) circuit) = (false, 0) ∧
      look (rules.runSchedule (schedule.take 12) circuit) = (true, 15) ∧
      look (rules.runSchedule (schedule.take 13) circuit) = (true, 15) ∧
      look (rules.runSchedule (schedule.take 14) circuit) = (false, 0) ∧
      look (rules.runSchedule (schedule.take 15) circuit) = (false, 0) ∧
      look (rules.runSchedule (schedule.take 16) circuit) = (true, 15) ∧
      look (rules.runSchedule (schedule.take 17) circuit) = (true, 15) ∧
      look (rules.runSchedule (schedule.take 18) circuit) = (false, 0) ∧
      look (rules.runSchedule (schedule.take 19) circuit) = (false, 0) ∧
      look (rules.runSchedule (schedule.take 20) circuit) = (true, 15) ∧
      look (rules.runSchedule (schedule.take 21) circuit) = (true, 15) ∧
      look (rules.runSchedule (schedule.take 22) circuit) = (false, 0) ∧
      look (rules.runSchedule (schedule.take 23) circuit) = (false, 0) ∧
      look (rules.runSchedule (schedule.take 24) circuit) = (true, 15) ∧
      look (rules.runSchedule (schedule.take 25) circuit) = (true, 15) ∧
      look (rules.runSchedule (schedule.take 26) circuit) = (false, 0) ∧
      look (rules.runSchedule (schedule.take 27) circuit) = (false, 0) ∧
      look (rules.runSchedule (schedule.take 28) circuit) = (true, 15) ∧
      look (rules.runSchedule (schedule.take 29) circuit) = (true, 15) ∧
      look (rules.runSchedule (schedule.take 30) circuit) = (false, 0) ∧
      look (rules.runSchedule (schedule.take 31) circuit) = (false, 0) ∧
      look (rules.runSchedule schedule circuit) = (false, 0) ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13,
    state_run_14, state_run_15, state_run_16, state_run_17, state_run_18, state_run_19,
    state_run_20, state_run_21, state_run_22, state_run_23, state_run_24, state_run_25,
    state_run_26, state_run_27, state_run_28, state_run_29, state_run_30, state_run_31, state_run]
  circuit_decide

assert_standard_axioms eight_pulses

/-- **The burn-out list after the eight flashes**: the game times of the eight switch-offs
of the torch, 2, 6, ..., 30, and nothing else. Eight entries is `MAX_RECENT_TOGGLES`. -/
theorem toggles_recorded :
    burnt.recentTorchToggles =
        ([2, 6, 10, 14, 18, 22, 26, 30].map fun t => (torch, t)) := by
  rw [burnt_eq]
  circuit_decide

assert_standard_axioms toggles_recorded

/-- **Burnt out for good.** After the 32 game ticks of the schedule the torch is out and the
dust is off, and they stay so for any number `n` of further game ticks; the model reaches no
bound. The level is at rest: the tick the torch asked for when it burnt out was never
scheduled. -/
theorem burnt_out (n : ℕ) :
    look (rules.steps n burnt) = (false, 0) ∧
      (rules.steps n burnt).overflow = false := by
  rw [burnt_eq, rules.steps_of_quiescent (by circuit_decide), look_advance,
    Level.overflow_advance]
  circuit_decide

assert_standard_axioms burnt_out

/-- **A neighbour update before game tick 61 does not relight the torch.** After the
burn-out nothing happens until game tick 60; then a stone block is put next to the torch. The
torch ticks in game tick 62 and stays out: the list still holds its eight entries, because the
oldest, from game tick 2, is 60 game ticks old and an entry is dropped only when it is older
than that. After game tick 64 the level is at rest, so the torch stays out for any number `n`
of further game ticks. -/
theorem poke_too_early (n : ℕ) :
    look (rules.runSchedule (early.take 29) burnt) = (false, 0) ∧
      look (rules.runSchedule (early.take 30) burnt) = (false, 0) ∧
      look (rules.runSchedule (early.take 31) burnt) = (false, 0) ∧
      look (rules.runSchedule early burnt) = (false, 0) ∧
      (rules.runSchedule early burnt).recentTorchToggles =
        ([2, 6, 10, 14, 18, 22, 26, 30].map fun t => (torch, t)) ∧
      look (rules.steps n (rules.runSchedule early burnt)) = (false, 0) ∧
      (rules.steps n (rules.runSchedule early burnt)).overflow = false := by
  rw [burnt_eq, estate_run_29, estate_run_30, estate_run_31, estate_run,
    rules.steps_of_quiescent (by circuit_decide), look_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms poke_too_early

set_option synthInstance.maxSize 4096 in
/-- **A neighbour update before game tick 62 relights the torch, for eight more flashes.**
After the burn-out nothing happens until game tick 61; then a stone block is put next to the
torch. The torch ticks in game tick 63: the entry from game tick 2 is now 61 game ticks old
and is dropped, seven remain, and the torch lights up. It is lit after game ticks 63-64,
67-68, ..., 91-92 and out in between; the switch-off in game tick 93 is the eighth of the new
run. After that the list holds the game times 65, 69, ..., 93, the level is at rest, and the
torch stays out for any number `n` of further game ticks. The lines below are the game ticks
62 to 96. -/
theorem poke_relights (n : ℕ) :
    look (rules.runSchedule (late.take 30) burnt) = (false, 0) ∧
      look (rules.runSchedule (late.take 31) burnt) = (true, 15) ∧
      look (rules.runSchedule (late.take 32) burnt) = (true, 15) ∧
      look (rules.runSchedule (late.take 33) burnt) = (false, 0) ∧
      look (rules.runSchedule (late.take 34) burnt) = (false, 0) ∧
      look (rules.runSchedule (late.take 35) burnt) = (true, 15) ∧
      look (rules.runSchedule (late.take 36) burnt) = (true, 15) ∧
      look (rules.runSchedule (late.take 37) burnt) = (false, 0) ∧
      look (rules.runSchedule (late.take 38) burnt) = (false, 0) ∧
      look (rules.runSchedule (late.take 39) burnt) = (true, 15) ∧
      look (rules.runSchedule (late.take 40) burnt) = (true, 15) ∧
      look (rules.runSchedule (late.take 41) burnt) = (false, 0) ∧
      look (rules.runSchedule (late.take 42) burnt) = (false, 0) ∧
      look (rules.runSchedule (late.take 43) burnt) = (true, 15) ∧
      look (rules.runSchedule (late.take 44) burnt) = (true, 15) ∧
      look (rules.runSchedule (late.take 45) burnt) = (false, 0) ∧
      look (rules.runSchedule (late.take 46) burnt) = (false, 0) ∧
      look (rules.runSchedule (late.take 47) burnt) = (true, 15) ∧
      look (rules.runSchedule (late.take 48) burnt) = (true, 15) ∧
      look (rules.runSchedule (late.take 49) burnt) = (false, 0) ∧
      look (rules.runSchedule (late.take 50) burnt) = (false, 0) ∧
      look (rules.runSchedule (late.take 51) burnt) = (true, 15) ∧
      look (rules.runSchedule (late.take 52) burnt) = (true, 15) ∧
      look (rules.runSchedule (late.take 53) burnt) = (false, 0) ∧
      look (rules.runSchedule (late.take 54) burnt) = (false, 0) ∧
      look (rules.runSchedule (late.take 55) burnt) = (true, 15) ∧
      look (rules.runSchedule (late.take 56) burnt) = (true, 15) ∧
      look (rules.runSchedule (late.take 57) burnt) = (false, 0) ∧
      look (rules.runSchedule (late.take 58) burnt) = (false, 0) ∧
      look (rules.runSchedule (late.take 59) burnt) = (true, 15) ∧
      look (rules.runSchedule (late.take 60) burnt) = (true, 15) ∧
      look (rules.runSchedule (late.take 61) burnt) = (false, 0) ∧
      look (rules.runSchedule (late.take 62) burnt) = (false, 0) ∧
      look (rules.runSchedule (late.take 63) burnt) = (false, 0) ∧
      look (rules.runSchedule late burnt) = (false, 0) ∧
      (rules.runSchedule late burnt).recentTorchToggles =
        ([65, 69, 73, 77, 81, 85, 89, 93].map fun t => (torch, t)) ∧
      look (rules.steps n (rules.runSchedule late burnt)) = (false, 0) ∧
      (rules.steps n (rules.runSchedule late burnt)).overflow = false := by
  rw [burnt_eq, lstate_run_30, lstate_run_31, lstate_run_32, lstate_run_33, lstate_run_34,
    lstate_run_35, lstate_run_36, lstate_run_37, lstate_run_38, lstate_run_39, lstate_run_40,
    lstate_run_41, lstate_run_42, lstate_run_43, lstate_run_44, lstate_run_45, lstate_run_46,
    lstate_run_47, lstate_run_48, lstate_run_49, lstate_run_50, lstate_run_51, lstate_run_52,
    lstate_run_53, lstate_run_54, lstate_run_55, lstate_run_56, lstate_run_57, lstate_run_58,
    lstate_run_59, lstate_run_60, lstate_run_61, lstate_run_62, lstate_run_63, lstate_run,
    rules.steps_of_quiescent (by circuit_decide), look_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms poke_relights

end Redstone.Theorems.Clock.RapidClock
