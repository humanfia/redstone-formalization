import Redstone.Proof.Build
import Redstone.Proof.Checkpoint

/-!
# Levels at rest, and levels that repeat

Kernel evaluation proves what a circuit does for a given number of game ticks. Two general
facts turn that into statements about all later times.

**Rest.** A level is *quiescent* (`Level.Quiescent`, decidable) when nothing in it is waiting to
happen: no scheduled tick, no block event, no entity, no ticking block entity, no neighbour
update, no random ticks. A game tick of a quiescent level changes the clocks and nothing else,
under any rules (`Rules.step_of_quiescent`), so it stays as it is for ever
(`Rules.steps_of_quiescent`, `Rules.blockAt_steps_of_quiescent`). A theorem such as "the lamp
stays lit" is: the run ends in a checkpoint, the checkpoint is quiescent (by evaluation), and
its lamp is lit.

This is the general theorem only for levels without ticking block entities. A level with a
hopper is never quiescent in this sense, because the hopper is ticked every game tick and
records the game time; for it only a bounded run can be stated.

**Repetition.** A clock never rests. What can be checked is a *cycle certificate*
(`Rules.Cycle`): after one period the level is the level it was, except that the game time,
the due times of the scheduled ticks and the times of the recent torch toggles have moved on
by the period, and the counter that orders scheduled ticks by a constant (`Level.shift`). The
certificate is one comparison of two checkpoints.

A cycle certificate is *not* a proof that the clock runs for ever. That needs the game tick to
commute with the shift on the levels of one period of the cycle, which is false for rules in
general (a daylight detector reads the time of day) and is not proved here for any component.
`Rules.periodic_of_shiftInvariant` is the conditional statement: given that commutation, the
level after `k` periods is the level shifted `k` times, and the blocks repeat for ever.

Left out: `Level.shift` does not move times kept inside block entities (the game time a hopper
was last ticked at), so a cycle certificate cannot hold for a clock made of hoppers.
-/

namespace Redstone

namespace Level

/-- Nothing in the level is waiting to happen. See `Quiescent`. -/
def quiescent (l : Level) : Bool :=
  decide (l.ticks = []) && decide (l.ticksToRun = []) && decide (l.fluidTicks = []) &&
  decide (l.fluidTicksToRun = []) && decide (l.blockEvents = []) && l.entities.isEmpty &&
  decide (l.blockEntityTickers = []) && decide (l.pendingBlockEntityTickers = []) &&
  decide (l.tickedBlockEntities = []) && decide (l.handlingTick = false) &&
  decide (l.tickingBlockEntities = false) && decide (l.randomTickSpeed = 0) &&
  decide (l.updateStack = []) && decide (l.lightWorld = l.world)

/-- The level is at rest between two game ticks: no scheduled block or fluid tick, no block
event, no entity, no ticking block entity, no pending neighbour update, no random ticks, and
the light engine has seen the blocks as they are. -/
def Quiescent (l : Level) : Prop := l.quiescent = true

instance (l : Level) : Decidable l.Quiescent := inferInstanceAs (Decidable (_ = true))

/-- The level with the game time moved on by `n` game ticks, and the overworld clock too if
the game rule `advance_time` is set. -/
def advance (l : Level) (n : ℕ) : Level :=
  { l with
    gameTime := l.gameTime + n
    dayTime := if l.advanceTime then l.dayTime + n else l.dayTime }

@[simp]
theorem advance_zero (l : Level) : l.advance 0 = l := by
  cases l
  simp [advance]

theorem advance_advance (l : Level) (m n : ℕ) : (l.advance m).advance n = l.advance (m + n) := by
  cases l
  simp only [advance, mk.injEq, true_and, Nat.add_assoc]
  split <;> simp [Nat.add_assoc]

@[simp]
theorem blockAt_advance (l : Level) (n : ℕ) : (l.advance n).blockAt = l.blockAt := rfl

@[simp]
theorem blocksAt_advance (l : Level) (n : ℕ) : (l.advance n).blocksAt = l.blocksAt := rfl

@[simp]
theorem dustPower_advance (l : Level) (n : ℕ) : (l.advance n).dustPower = l.dustPower := rfl

@[simp]
theorem itemCount_advance (l : Level) (n : ℕ) : (l.advance n).itemCount = l.itemCount := rfl

@[simp]
theorem world_advance (l : Level) (n : ℕ) : (l.advance n).world = l.world := rfl

@[simp]
theorem blockEntities_advance (l : Level) (n : ℕ) :
    (l.advance n).blockEntities = l.blockEntities := rfl

@[simp]
theorem overflow_advance (l : Level) (n : ℕ) : (l.advance n).overflow = l.overflow := rfl

@[simp]
theorem gameTime_advance (l : Level) (n : ℕ) : (l.advance n).gameTime = l.gameTime + n := rfl

/-- A quiescent level stays quiescent while only its clocks move. -/
theorem Quiescent.advance {l : Level} (h : l.Quiescent) (n : ℕ) : (l.advance n).Quiescent := h

end Level

namespace Rules

variable (r : Rules)

/-- **A game tick of a quiescent level changes the clocks and nothing else**, whatever the
rules: the game time goes up by one, the overworld clock too if `advance_time` is set, and
every other field of the level is what it was. -/
theorem step_of_quiescent {l : Level} (h : l.Quiescent) : r.step l = l.advance 1 := by
  obtain ⟨world, blockEntities, blockEntityTickers, pendingBlockEntityTickers,
    tickingBlockEntities, handlingTick, tickedBlockEntities, ticks, ticksToRun, subTickCount,
    blockEvents, entities, nextEntityIndex, gameTime, random, lootSequences, updateStack,
    updatesAdded, updateCount, overflow, recentTorchToggles, dayTime, advanceTime, weather,
    lightWorld, playerMenu, fluidTicks, fluidTicksToRun, randValue, randomTickSpeed, blockDrops,
    randomTickBox, randomSourceCount, fireSpreadRadiusAroundPlayer, blockEntityTickerStates⟩ := l
  simp only [Level.Quiescent, Level.quiescent, Bool.and_eq_true, decide_eq_true_eq,
    List.isEmpty_iff, and_assoc] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- A quiescent level is quiescent after a game tick. -/
theorem quiescent_step {l : Level} (h : l.Quiescent) : (r.step l).Quiescent := by
  rw [step_of_quiescent r h]
  exact h.advance 1

/-- **A quiescent level stays as it is for ever**: after any number of game ticks only its
clocks have moved. -/
theorem steps_of_quiescent {l : Level} (h : l.Quiescent) (n : ℕ) : r.steps n l = l.advance n := by
  induction n with
  | zero => simp [steps]
  | succ n ih =>
    rw [steps_add, ih, steps, Function.iterate_one, step_of_quiescent r (h.advance n),
      Level.advance_advance]

/-- Any number of game ticks without input leaves a quiescent level as it is, up to its
clocks. -/
theorem runSchedule_idle_of_quiescent {l : Level} (h : l.Quiescent) (n : ℕ) :
    r.runSchedule (.idle n) l = l.advance n := by
  rw [runSchedule_idle, steps_of_quiescent r h]

/-- The blocks of a quiescent level never change. -/
theorem blockAt_steps_of_quiescent {l : Level} (h : l.Quiescent) (n : ℕ) (p : Pos) :
    (r.steps n l).blockAt p = l.blockAt p := by
  rw [steps_of_quiescent r h, Level.blockAt_advance]

/-- The block entities of a quiescent level never change. -/
theorem blockEntities_steps_of_quiescent {l : Level} (h : l.Quiescent) (n : ℕ) :
    (r.steps n l).blockEntities = l.blockEntities := by
  rw [steps_of_quiescent r h, Level.blockEntities_advance]

/-- A quiescent level never reaches a bound of the model. -/
theorem overflow_steps_of_quiescent {l : Level} (h : l.Quiescent) (n : ℕ) :
    (r.steps n l).overflow = l.overflow := by
  rw [steps_of_quiescent r h, Level.overflow_advance]

end Rules

/-! ### Cycles -/

namespace ScheduledTickOf

/-- The tick due `dt` game ticks later, scheduled `dc` scheduled ticks later. -/
def shift {α : Type} (dt dc : ℕ) (t : ScheduledTickOf α) : ScheduledTickOf α :=
  { t with trigger := t.trigger + dt, order := t.order + dc }

theorem shift_shift {α : Type} (dt dc dt' dc' : ℕ) (t : ScheduledTickOf α) :
    (t.shift dt dc).shift dt' dc' = t.shift (dt + dt') (dc + dc') := by
  simp [shift, Nat.add_assoc]

end ScheduledTickOf

namespace Level

/-- The same level `dt` game ticks later, after `dc` more ticks have been scheduled: the game
time, the overworld clock (if `advance_time` is set), the due times of the scheduled block and
fluid ticks and the times of the recent torch toggles are moved on by `dt`; the counter that
orders scheduled ticks, and the order of every scheduled tick, by `dc`. Blocks, block entities
and everything else are the same. -/
def shift (l : Level) (dt dc : ℕ) : Level :=
  { l with
    gameTime := l.gameTime + dt
    dayTime := if l.advanceTime then l.dayTime + dt else l.dayTime
    ticks := l.ticks.map (·.shift dt dc)
    ticksToRun := l.ticksToRun.map (·.shift dt dc)
    fluidTicks := l.fluidTicks.map (·.shift dt dc)
    fluidTicksToRun := l.fluidTicksToRun.map (·.shift dt dc)
    subTickCount := l.subTickCount + dc
    recentTorchToggles := l.recentTorchToggles.map fun e => (e.1, e.2 + dt) }

theorem shift_shift (l : Level) (dt dc dt' dc' : ℕ) :
    (l.shift dt dc).shift dt' dc' = l.shift (dt + dt') (dc + dc') := by
  obtain ⟨world, blockEntities, blockEntityTickers, pendingBlockEntityTickers,
    tickingBlockEntities, handlingTick, tickedBlockEntities, ticks, ticksToRun, subTickCount,
    blockEvents, entities, nextEntityIndex, gameTime, random, lootSequences, updateStack,
    updatesAdded, updateCount, overflow, recentTorchToggles, dayTime, advanceTime, weather,
    lightWorld, playerMenu, fluidTicks, fluidTicksToRun, randValue, randomTickSpeed, blockDrops,
    randomTickBox, randomSourceCount, fireSpreadRadiusAroundPlayer, blockEntityTickerStates⟩ := l
  cases advanceTime <;>
    simp [shift, ScheduledTickOf.shift, Function.comp_def, Nat.add_assoc]

@[simp]
theorem blockAt_shift (l : Level) (dt dc : ℕ) : (l.shift dt dc).blockAt = l.blockAt := rfl

@[simp]
theorem world_shift (l : Level) (dt dc : ℕ) : (l.shift dt dc).world = l.world := rfl

@[simp]
theorem blockEntities_shift (l : Level) (dt dc : ℕ) :
    (l.shift dt dc).blockEntities = l.blockEntities := rfl

@[simp]
theorem overflow_shift (l : Level) (dt dc : ℕ) : (l.shift dt dc).overflow = l.overflow := rfl

end Level

namespace Rules

variable (r : Rules)

/-- A **cycle certificate**: `period` game ticks take the level `l` to itself, shifted in time
by the period, with `dc` more ticks scheduled. For checkpoints this is one comparison:
`Level.eq_of_beqBlocks (by circuit_decide)` on the two literals.

It says that the level repeats once. That it repeats for ever is
`periodic_of_shiftInvariant`, under a hypothesis that is not proved for any component. -/
def Cycle (l : Level) (period dc : ℕ) : Prop := r.steps period l = l.shift period dc

/-- If a game tick commutes with the time shift on the first `m` levels of the run from `l`,
then so do `i` game ticks, for `i` up to `m`. -/
theorem steps_shift_of_shiftInvariant {l : Level} {m dt dc : ℕ}
    (hinv : ∀ i < m, r.step ((r.steps i l).shift dt dc) = (r.step (r.steps i l)).shift dt dc)
    (i : ℕ) (hi : i ≤ m) : r.steps i (l.shift dt dc) = (r.steps i l).shift dt dc := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [steps_add, ih (Nat.le_of_succ_le hi), steps, Function.iterate_one, hinv i hi, steps_add]
    rfl

/-- From a cycle certificate to periodicity for ever, **if** a game tick commutes with the
time shift on the levels of one period of the cycle. Under that hypothesis the level after `k`
periods is the level shifted `k` times. -/
theorem periodic_of_shiftInvariant {l : Level} {period dc : ℕ} (hc : r.Cycle l period dc)
    (hinv : ∀ i < period, ∀ k, r.step ((r.steps i l).shift (k * period) (k * dc)) =
      (r.step (r.steps i l)).shift (k * period) (k * dc)) (k : ℕ) :
    r.steps (k * period) l = l.shift (k * period) (k * dc) := by
  induction k with
  | zero =>
    cases l
    simp [steps, Level.shift, ScheduledTickOf.shift]
  | succ k ih =>
    rw [Nat.succ_mul, steps_add, ih,
      steps_shift_of_shiftInvariant r (fun i hi => hinv i hi k) period (Nat.le_refl _), hc,
      Level.shift_shift, Nat.succ_mul, Nat.add_comm period, Nat.add_comm dc]

/-- Under the hypothesis of `periodic_of_shiftInvariant` the blocks repeat for ever: the block
at a position `i` game ticks into any later period is the block `i` game ticks into the
first. -/
theorem blockAt_periodic {l : Level} {period dc : ℕ} (hc : r.Cycle l period dc)
    (hinv : ∀ i < period, ∀ k, r.step ((r.steps i l).shift (k * period) (k * dc)) =
      (r.step (r.steps i l)).shift (k * period) (k * dc)) (k i : ℕ) (hi : i ≤ period)
    (p : Pos) : (r.steps (k * period + i) l).blockAt p = (r.steps i l).blockAt p := by
  rw [steps_add, periodic_of_shiftInvariant r hc hinv,
    steps_shift_of_shiftInvariant r (fun i hi => hinv i hi k) i hi, Level.blockAt_shift]

end Rules

end Redstone
