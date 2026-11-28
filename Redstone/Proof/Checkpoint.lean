import Redstone.Mechanics.Input

/-!
# Checkpoints: comparing levels, and joining the ticks of a run

A theorem about a run of many game ticks is not proved by one evaluation: the kernel keeps
every intermediate result of a declaration, so time and memory grow with the length of the run
(`docs/proof-feasibility.md`). It is proved tick by tick, between levels that are written out
as terms (*checkpoints*). This file has the two things that make that sound and cheap:

* `Level.beqBlocks`, a Boolean comparison of two levels that the kernel can evaluate, and
  `Level.eq_of_beqBlocks`: when it answers `true` the levels are equal. `Level` itself has no
  decidable equality, because an entity carries `Float` coordinates; the comparison therefore
  asks that neither level has an entity, and compares every other field, the random number
  generator included.
* The lemmas that join per-tick equations into an equation about the run
  (`Rules.runSchedule_take_succ`, `Rules.runSchedule_of_take`). They are applied to the *names*
  of the checkpoints. The kernel checks such a step by comparing the names, so joining `n`
  ticks costs `n` small proof terms and never evaluates a level again. This was measured: see
  `Redstone/Proof/README.md`.

The per-tick equations and the checkpoint literals are produced by the command `checkpoints`
(`Redstone.Proof.Tactic`).

Left out: levels with entities. A tick that moves an entity computes in `Float`, which the
kernel cannot evaluate, and `beqBlocks` rejects such levels.
-/

namespace Redstone

namespace Level

/-- Field by field comparison of two levels without entities: `true` when neither level has an
entity and every other field is the same. This is the comparison of a checkpoint lemma. Every
field is compared, also the random number generator and the counters that no block of the
circuit may ever read, so that nothing is left unevaluated from one tick to the next. -/
def beqBlocks (a b : Level) : Bool :=
  a.entities.isEmpty && b.entities.isEmpty &&
  decide (a.world = b.world) && decide (a.blockEntities = b.blockEntities) &&
  decide (a.blockEntityTickers = b.blockEntityTickers) &&
  decide (a.pendingBlockEntityTickers = b.pendingBlockEntityTickers) &&
  decide (a.tickingBlockEntities = b.tickingBlockEntities) &&
  decide (a.handlingTick = b.handlingTick) &&
  decide (a.tickedBlockEntities = b.tickedBlockEntities) &&
  decide (a.ticks = b.ticks) && decide (a.ticksToRun = b.ticksToRun) &&
  decide (a.subTickCount = b.subTickCount) && decide (a.blockEvents = b.blockEvents) &&
  decide (a.nextEntityIndex = b.nextEntityIndex) && decide (a.gameTime = b.gameTime) &&
  decide (a.random = b.random) && decide (a.lootSequences = b.lootSequences) &&
  decide (a.updateStack = b.updateStack) && decide (a.updatesAdded = b.updatesAdded) &&
  decide (a.updateCount = b.updateCount) && decide (a.overflow = b.overflow) &&
  decide (a.recentTorchToggles = b.recentTorchToggles) && decide (a.dayTime = b.dayTime) &&
  decide (a.advanceTime = b.advanceTime) && decide (a.weather = b.weather) &&
  decide (a.lightWorld = b.lightWorld) && decide (a.playerMenu = b.playerMenu) &&
  decide (a.fluidTicks = b.fluidTicks) && decide (a.fluidTicksToRun = b.fluidTicksToRun) &&
  decide (a.randValue = b.randValue) && decide (a.randomTickSpeed = b.randomTickSpeed) &&
  decide (a.blockDrops = b.blockDrops) && decide (a.randomTickBox = b.randomTickBox) &&
  decide (a.randomSourceCount = b.randomSourceCount) &&
  decide (a.blockEntityTickerStates = b.blockEntityTickerStates)

/-- Soundness of the checkpoint comparison: two levels that `beqBlocks` accepts are equal.

The proof takes both levels apart into their fields. A field that is added to `Level` and not
to `beqBlocks` makes it fail, so the comparison cannot silently skip one. -/
theorem eq_of_beqBlocks {a b : Level} (h : a.beqBlocks b = true) : a = b := by
  cases a
  cases b
  simp only [beqBlocks, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, and_assoc] at h
  obtain ⟨rfl, rfl, h⟩ := h
  simp only [h]

/-- A level without entities is accepted against itself. -/
theorem beqBlocks_self {a : Level} (h : a.entities = []) : a.beqBlocks a = true := by
  simp [beqBlocks, h]

/-- The comparison answers `true` exactly for equal levels without entities. -/
theorem beqBlocks_iff {a b : Level} : a.beqBlocks b = true ↔ a = b ∧ a.entities = [] :=
  ⟨fun h => ⟨eq_of_beqBlocks h, by
      simp only [beqBlocks, Bool.and_eq_true, List.isEmpty_iff, and_assoc] at h
      exact h.1⟩,
    fun ⟨h, he⟩ => h ▸ beqBlocks_self he⟩

end Level

namespace Schedule

/-- The inputs that arrive before game tick `k + 1`; none past the end of the schedule. -/
def inputsAt (s : Schedule) (k : ℕ) : List Input := s.getD k []

/-- No input arrives before the game ticks `k + 1` to `k + m` of the schedule, and the schedule
has that many game ticks. -/
def idleBetween (s : Schedule) (k m : ℕ) : Bool :=
  decide (k + m ≤ s.length) && ((s.take (k + m)).drop k).all List.isEmpty

/-- The schedule `s` followed by the schedule `s'`. -/
def andThen (s s' : Schedule) : Schedule := s ++ s'

end Schedule

namespace Rules

variable (r : Rules)

@[simp]
theorem stepWith_nil (l : Level) : r.stepWith [] l = r.step l := rfl

@[simp]
theorem runSchedule_nil (l : Level) : r.runSchedule [] l = l := rfl

@[simp]
theorem runSchedule_cons (is : List Input) (s : Schedule) (l : Level) :
    r.runSchedule (is :: s) l = r.runSchedule s (r.stepWith is l) := by
  simp only [runSchedule, List.foldl_cons]

theorem runSchedule_append (s s' : Schedule) (l : Level) :
    r.runSchedule (s ++ s') l = r.runSchedule s' (r.runSchedule s l) :=
  List.foldl_append ..

/-- A schedule without inputs is as many game ticks. -/
theorem runSchedule_idle (n : ℕ) (l : Level) : r.runSchedule (.idle n) l = r.steps n l := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    change r.runSchedule ([] :: Schedule.idle n) l = _
    rw [steps, Function.iterate_succ_apply, ← steps, ← ih, runSchedule_cons, stepWith_nil]

theorem steps_add (m n : ℕ) (l : Level) : r.steps (m + n) l = r.steps n (r.steps m l) := by
  rw [steps, steps, steps, Nat.add_comm, Function.iterate_add_apply]

variable {r}

/-- Joining checkpoints: if the first `k` ticks of the schedule take `l` to `l'`, and tick
`k + 1` with its inputs takes `l'` to `l''`, then the first `k + 1` ticks take `l` to `l''`.

Applied to checkpoint names, the kernel checks this without looking into the levels. -/
theorem runSchedule_take_succ {s : Schedule} {k : ℕ} {l l' l'' : Level}
    (hk : r.runSchedule (s.take k) l = l') (hs : r.stepWith (s.inputsAt k) l' = l'')
    (hlt : k < s.length) : r.runSchedule (s.take (k + 1)) l = l'' := by
  rw [List.take_add_one, runSchedule_append, hk, List.getElem?_eq_getElem hlt]
  rw [Schedule.inputsAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt] at hs
  exact hs

/-- The first tick of a schedule, as the start of a chain of `runSchedule_take_succ`. -/
theorem runSchedule_take_one {s : Schedule} {l l' : Level}
    (hs : r.stepWith (s.inputsAt 0) l = l') (hlt : 0 < s.length) :
    r.runSchedule (s.take 1) l = l' :=
  runSchedule_take_succ (k := 0) rfl hs hlt

/-- The end of a chain: all the ticks of the schedule. -/
theorem runSchedule_of_take {s : Schedule} {n : ℕ} {l l' : Level}
    (h : r.runSchedule (s.take n) l = l') (hn : s.length = n) : r.runSchedule s l = l' := by
  rwa [List.take_of_length_le hn.le] at h

/-- From two checkpoints of one run to a statement about game ticks: if no input arrives
between game tick `k` and game tick `k + m` of the schedule, then `m` game ticks take the
level after `k` ticks to the level after `k + m` ticks. This is how a cycle certificate
(`Rules.Cycle`) is read off the checkpoints of a clock. -/
theorem steps_of_runs {s : Schedule} {k m : ℕ} {l l' l'' : Level}
    (hk : r.runSchedule (s.take k) l = l') (hkm : r.runSchedule (s.take (k + m)) l = l'')
    (hidle : s.idleBetween k m = true) : r.steps m l' = l'' := by
  simp only [Schedule.idleBetween, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.isEmpty_iff] at hidle
  obtain ⟨hlen, hall⟩ := hidle
  have h₁ : s.take (k + m) = s.take k ++ (s.take (k + m)).drop k := by
    have h := (List.take_append_drop k (s.take (k + m))).symm
    rwa [List.take_take, Nat.min_eq_left (Nat.le_add_right k m)] at h
  have h₂ : (s.take (k + m)).drop k = Schedule.idle m :=
    List.eq_replicate_iff.2 ⟨by rw [List.length_drop, List.length_take]; omega, hall⟩
  rw [h₁, runSchedule_append, hk, h₂, runSchedule_idle] at hkm
  exact hkm

/-- A run in two parts: the schedule `s` from `l`, then the schedule `s'` from where that
ended. -/
theorem runSchedule_andThen {s s' : Schedule} {l l' l'' : Level}
    (h : r.runSchedule s l = l') (h' : r.runSchedule s' l' = l'') :
    r.runSchedule (s.andThen s') l = l'' := by
  rw [Schedule.andThen, runSchedule_append, h, h']

end Rules

end Redstone
