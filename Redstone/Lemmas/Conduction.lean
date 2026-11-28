module

public import Redstone.Component.Lever
public import Redstone.Component.Button
public import Redstone.Component.Torch
public import Redstone.Component.Repeater
public import Redstone.Component.Observer

/-!
# Lemmas about conduction: strong and weak power

Generic facts about how a position reads the signal around it (`Redstone/Mechanics/Power.lean`,
the game's `SignalGetter`), over an arbitrary level and an arbitrary environment.

* **The two maxima.** `getDirectSignalTo` and `getBestNeighborSignal` are folds over the six
  directions that stop at 15. They are characterized here by what one neighbour gives:
  the result is at least what any neighbour gives, capped at 15 (`le_directSignalTo`,
  `le_bestNeighborSignalAt`), at most a bound on all of them (`directSignalTo_le`,
  `bestNeighborSignalAt_le`), never more than 15 for `getBestNeighborSignal`
  (`bestNeighborSignalAt_le_fifteen`), and zero exactly when every neighbour gives zero
  (`directSignalTo_eq_zero_iff`, `bestNeighborSignalAt_eq_zero_iff`). `hasNeighborSignal` is
  "the best neighbour signal is positive" (`hasNeighborSignalAt_iff`,
  `hasNeighborSignalAt_iff_pos`).
* **Conductors.** A conductor gives each neighbour the larger of its own signal and the direct
  (strong) signal it receives (`signalAt_of_conductor`); a block that is not a conductor gives
  its own signal only (`signalAt_of_not_conductor`). So a conductor that receives a direct
  signal of 15 from one side gives at least 15 to every side
  (`fifteen_le_signalAt_of_strong`), and a conductor without a signal of its own that receives
  no direct signal gives nothing (`signalAt_conductor_eq_zero`).
* **Who gives strong power** (`Redstone.Conduction`): a lever and a button that are on, into
  the block they are attached to and nowhere else; a lit torch, into the block above it and
  nowhere else; a powered repeater and a powered observer, into the block at their output,
  where their strong signal is their whole signal.

Redstone dust also answers `getDirectSignal` with its signal; that a block powered by dust
alone does not power other dust is because dust is silent while dust computes its power
(`RedstoneWireBlock.shouldSignal`). Those lemmas are in `Redstone/Lemmas/Dust.lean`
(`Dust.signalAt_muted_wire`, `Dust.signalAt_muted_of_fed_by_dust`).

Left out: the comparator's strong power (its output is read from its block entity, which is
the business of the lemmas about the comparator), and a statement over a whole circuit ("this
lamp is lit"): which blocks surround a position is a fact about a concrete level, proved by
evaluation in `Redstone/Theorems/Wire`.
-/

@[expose] public section

namespace Redstone

namespace Level

/-! ### The two folds that stop at 15 -/

/-- The step of `getDirectSignalTo`, for a neighbour that gives `g d`. -/
private def directStep (g : Direction → ℕ) (best : ℕ) (d : Direction) : ℕ :=
  if best ≥ 15 then best else max best (g d)

/-- The step of `getBestNeighborSignal`, for a neighbour that gives `g d`. -/
private def bestStep (g : Direction → ℕ) (best : ℕ) (d : Direction) : ℕ :=
  if best ≥ 15 then 15 else if g d ≥ 15 then 15 else max best (g d)

private theorem foldl_directStep_ge (g : Direction → ℕ) (ds : List Direction) (b : ℕ) :
    min 15 b ≤ ds.foldl (directStep g) b ∧
      ∀ d ∈ ds, min 15 (g d) ≤ ds.foldl (directStep g) b := by
  induction ds generalizing b with
  | nil => exact ⟨Nat.min_le_right .., fun _ h => by cases h⟩
  | cons e es ih =>
    have hb : min 15 b ≤ min 15 (directStep g b e) := by
      unfold directStep
      split <;> omega
    have he : min 15 (g e) ≤ min 15 (directStep g b e) := by
      unfold directStep
      split <;> omega
    refine ⟨le_trans hb (ih _).1, fun d hd => ?_⟩
    rcases List.mem_cons.mp hd with rfl | hd
    · exact le_trans he (ih _).1
    · exact (ih _).2 d hd

private theorem foldl_directStep_le (g : Direction → ℕ) (ds : List Direction) (b n : ℕ)
    (hb : b ≤ n) (h : ∀ d ∈ ds, g d ≤ n) : ds.foldl (directStep g) b ≤ n := by
  induction ds generalizing b with
  | nil => exact hb
  | cons e es ih =>
    refine ih _ ?_ fun d hd => h d (List.mem_cons_of_mem _ hd)
    have := h e List.mem_cons_self
    unfold directStep
    split <;> omega

private theorem foldl_bestStep_ge (g : Direction → ℕ) (ds : List Direction) (b : ℕ) :
    min 15 b ≤ ds.foldl (bestStep g) b ∧
      ∀ d ∈ ds, min 15 (g d) ≤ ds.foldl (bestStep g) b := by
  induction ds generalizing b with
  | nil => exact ⟨Nat.min_le_right .., fun _ h => by cases h⟩
  | cons e es ih =>
    have hb : min 15 b ≤ min 15 (bestStep g b e) := by
      unfold bestStep
      split_ifs <;> omega
    have he : min 15 (g e) ≤ min 15 (bestStep g b e) := by
      unfold bestStep
      split_ifs <;> omega
    refine ⟨le_trans hb (ih _).1, fun d hd => ?_⟩
    rcases List.mem_cons.mp hd with rfl | hd
    · exact le_trans he (ih _).1
    · exact (ih _).2 d hd

private theorem foldl_bestStep_le (g : Direction → ℕ) (ds : List Direction) (b n : ℕ)
    (hb : b ≤ n) (h : ∀ d ∈ ds, g d ≤ n) : ds.foldl (bestStep g) b ≤ n := by
  induction ds generalizing b with
  | nil => exact hb
  | cons e es ih =>
    refine ih _ ?_ fun d hd => h d (List.mem_cons_of_mem _ hd)
    have := h e List.mem_cons_self
    unfold bestStep
    split_ifs <;> omega

private theorem foldl_bestStep_le_fifteen (g : Direction → ℕ) (ds : List Direction) (b : ℕ)
    (hb : b ≤ 15) : ds.foldl (bestStep g) b ≤ 15 := by
  induction ds generalizing b with
  | nil => exact hb
  | cons e es ih =>
    refine ih _ ?_
    unfold bestStep
    split_ifs <;> omega

private theorem directSignalTo_eq_foldl (env : Env) (l : Level) (p : Pos) :
    l.directSignalTo env p =
      Direction.values.foldl (directStep fun d => l.directSignalAt env (p.step d) d) 0 := by
  delta directSignalTo directStep
  with_reducible rfl

private theorem bestNeighborSignalAt_eq_foldl (env : Env) (l : Level) (p : Pos) :
    l.bestNeighborSignalAt env p =
      Direction.values.foldl (bestStep fun d => l.signalAt env (p.step d) d) 0 := by
  delta bestNeighborSignalAt bestStep
  with_reducible rfl

private theorem mem_values (d : Direction) : d ∈ Direction.values := by
  cases d <;> simp [Direction.values]

/-! ### `getDirectSignalTo` -/

/-- **The strong power a position receives is at least what any one neighbour gives it**,
capped at 15 (the game stops looking once it has found 15). -/
theorem le_directSignalTo (env : Env) (l : Level) (p : Pos) (d : Direction) :
    min 15 (l.directSignalAt env (p.step d) d) ≤ l.directSignalTo env p := by
  rw [directSignalTo_eq_foldl]
  exact (foldl_directStep_ge (fun d => l.directSignalAt env (p.step d) d) Direction.values 0).2 d
    (mem_values d)

/-- If no neighbour gives more than `n` of strong power, the position receives at most `n`. -/
theorem directSignalTo_le (env : Env) (l : Level) (p : Pos) (n : ℕ)
    (h : ∀ d, l.directSignalAt env (p.step d) d ≤ n) : l.directSignalTo env p ≤ n := by
  rw [directSignalTo_eq_foldl]
  exact foldl_directStep_le _ _ _ _ (Nat.zero_le _) fun d _ => h d

/-- A position receives no strong power exactly when no neighbour gives it any. -/
theorem directSignalTo_eq_zero_iff (env : Env) (l : Level) (p : Pos) :
    l.directSignalTo env p = 0 ↔ ∀ d, l.directSignalAt env (p.step d) d = 0 := by
  constructor
  · intro h d
    have := le_directSignalTo env l p d
    omega
  · intro h
    have := directSignalTo_le env l p 0 fun d => (h d).le
    omega

/-! ### `getBestNeighborSignal` and `hasNeighborSignal` -/

/-- **The best neighbour signal is at least what any one neighbour gives**, capped at 15. -/
theorem le_bestNeighborSignalAt (env : Env) (l : Level) (p : Pos) (d : Direction) :
    min 15 (l.signalAt env (p.step d) d) ≤ l.bestNeighborSignalAt env p := by
  rw [bestNeighborSignalAt_eq_foldl]
  exact (foldl_bestStep_ge (fun d => l.signalAt env (p.step d) d) Direction.values 0).2 d
    (mem_values d)

/-- If no neighbour gives more than `n`, the best neighbour signal is at most `n`. -/
theorem bestNeighborSignalAt_le (env : Env) (l : Level) (p : Pos) (n : ℕ)
    (h : ∀ d, l.signalAt env (p.step d) d ≤ n) : l.bestNeighborSignalAt env p ≤ n := by
  rw [bestNeighborSignalAt_eq_foldl]
  exact foldl_bestStep_le _ _ _ _ (Nat.zero_le _) fun d _ => h d

/-- The best neighbour signal is never more than 15, whatever the neighbours give. -/
theorem bestNeighborSignalAt_le_fifteen (env : Env) (l : Level) (p : Pos) :
    l.bestNeighborSignalAt env p ≤ 15 := by
  rw [bestNeighborSignalAt_eq_foldl]
  exact foldl_bestStep_le_fifteen _ _ _ (by omega)

/-- A neighbour that gives 15 or more makes the best neighbour signal 15. -/
theorem bestNeighborSignalAt_eq_fifteen (env : Env) (l : Level) (p : Pos) (d : Direction)
    (h : 15 ≤ l.signalAt env (p.step d) d) : l.bestNeighborSignalAt env p = 15 := by
  have h₁ := le_bestNeighborSignalAt env l p d
  have h₂ := bestNeighborSignalAt_le_fifteen env l p
  omega

/-- The best neighbour signal is zero exactly when every neighbour gives zero. -/
theorem bestNeighborSignalAt_eq_zero_iff (env : Env) (l : Level) (p : Pos) :
    l.bestNeighborSignalAt env p = 0 ↔ ∀ d, l.signalAt env (p.step d) d = 0 := by
  constructor
  · intro h d
    have := le_bestNeighborSignalAt env l p d
    omega
  · intro h
    have := bestNeighborSignalAt_le env l p 0 fun d => (h d).le
    omega

/-- `hasNeighborSignal`: some neighbour gives a signal. -/
theorem hasNeighborSignalAt_iff (env : Env) (l : Level) (p : Pos) :
    l.hasNeighborSignalAt env p = true ↔ ∃ d, 0 < l.signalAt env (p.step d) d := by
  simp only [hasNeighborSignalAt, List.any_eq_true, decide_eq_true_eq, gt_iff_lt]
  exact ⟨fun ⟨d, _, h⟩ => ⟨d, h⟩, fun ⟨d, h⟩ => ⟨d, mem_values d, h⟩⟩

/-- A position has a neighbour signal exactly when its best neighbour signal is positive. -/
theorem hasNeighborSignalAt_iff_pos (env : Env) (l : Level) (p : Pos) :
    l.hasNeighborSignalAt env p = true ↔ 0 < l.bestNeighborSignalAt env p := by
  rw [hasNeighborSignalAt_iff, Nat.pos_iff_ne_zero, ne_eq, bestNeighborSignalAt_eq_zero_iff]
  constructor
  · rintro ⟨d, hd⟩ h
    have := h d
    omega
  · intro h
    by_contra hne
    exact h fun d => by
      by_contra hd
      exact hne ⟨d, Nat.pos_of_ne_zero hd⟩

/-! ### Conductors -/

/-- **A conductor gives each neighbour the larger of its own signal and the strong power it
receives.** -/
theorem signalAt_of_conductor (env : Env) (l : Level) (p : Pos) (d : Direction)
    (h : (l.blockAt p).isConductor = true) :
    l.signalAt env p d =
      max ((env.block (l.blockAt p)).signal l p d) (l.directSignalTo env p) := by
  simp only [signalAt, h, ite_true]

/-- A block that is not a conductor gives its own signal and nothing else: it passes nothing
on. -/
theorem signalAt_of_not_conductor (env : Env) (l : Level) (p : Pos) (d : Direction)
    (h : (l.blockAt p).isConductor = false) :
    l.signalAt env p d = (env.block (l.blockAt p)).signal l p d := by
  simp only [signalAt, h, Bool.false_eq_true, ite_false]

/-- **A strongly powered conductor powers everything around it.** If the conductor at `p`
receives a direct signal of 15 from its neighbour in direction `e`, it gives at least 15 to
each of its six neighbours. -/
theorem fifteen_le_signalAt_of_strong (env : Env) (l : Level) (p : Pos) (d e : Direction)
    (h : (l.blockAt p).isConductor = true) (he : 15 ≤ l.directSignalAt env (p.step e) e) :
    15 ≤ l.signalAt env p d := by
  rw [signalAt_of_conductor env l p d h]
  have := le_directSignalTo env l p e
  omega

/-- A conductor without a signal of its own that receives no strong power gives nothing. -/
theorem signalAt_conductor_eq_zero (env : Env) (l : Level) (p : Pos) (d : Direction)
    (h : (l.blockAt p).isConductor = true) (hs : (env.block (l.blockAt p)).signal l p d = 0)
    (hd : ∀ e, l.directSignalAt env (p.step e) e = 0) : l.signalAt env p d = 0 := by
  rw [signalAt_of_conductor env l p d h, hs, (directSignalTo_eq_zero_iff env l p).mpr hd]
  rfl

end Level

/-! ### Who gives strong power -/

namespace Conduction

open Component

/-- **A lever gives strong power to the block it is attached to, and to no other.** The
direction `d` points from the block that asks to the lever; the block the lever is attached
to asks with `connectedDirection`. -/
theorem lever_directSignal (s : Blocks.Lever) (l : Level) (p : Pos) (d : Direction) :
    (Lever.behaviour (.lever s)).directSignal l p d =
      if s.powered = true ∧ Lever.connectedDirection s = d then 15 else 0 := by
  change (if (s.powered && decide (Lever.connectedDirection s = d)) = true then 15 else 0) = _
  by_cases h : s.powered = true <;> by_cases h' : Lever.connectedDirection s = d <;>
    simp [h, h']

/-- A lever gives 15 to every neighbour when it is on, and nothing when it is off. -/
theorem lever_signal (s : Blocks.Lever) (l : Level) (p : Pos) (d : Direction) :
    (Lever.behaviour (.lever s)).signal l p d = if s.powered = true then 15 else 0 := rfl

/-- **A button gives strong power to the block it is attached to, and to no other.** -/
theorem button_directSignal (id : Blocks.Button.Id) (s : Blocks.Button) (l : Level) (p : Pos)
    (d : Direction) :
    (Button.button id s).directSignal l p d =
      if s.powered = true ∧ Button.connectedDirection s = d then 15 else 0 := by
  change (if (s.powered && decide (Button.connectedDirection s = d)) = true then 15 else 0) = _
  by_cases h : s.powered = true <;> by_cases h' : Button.connectedDirection s = d <;>
    simp [h, h']

/-- **A lit torch gives strong power to the block above it**, which asks with `down`. -/
theorem torch_directSignal_down (k : Torch.Kind) :
    Torch.directSignal k .down = if k.lit = true then 15 else 0 := by
  cases k with
  | floor s =>
    simp [Torch.directSignal, Torch.signal, Torch.ownSignal, Torch.Kind.attachment,
      Torch.Kind.lit, Direction.opposite]
  | wall s =>
    obtain ⟨f, lit⟩ := s
    cases f <;>
      simp [Torch.directSignal, Torch.signal, Torch.ownSignal, Torch.Kind.attachment,
        Torch.Kind.lit, Direction.opposite, HorizontalDirection.toDirection]

/-- A torch gives no strong power to its sides or downwards. -/
theorem torch_directSignal_of_ne_down (k : Torch.Kind) (d : Direction) (h : d ≠ .down) :
    Torch.directSignal k d = 0 := by
  simp [Torch.directSignal, h]

/-- A torch gives its signal to every neighbour except the block it is attached to. -/
theorem torch_signal (k : Torch.Kind) (d : Direction) :
    Torch.signal k d = if d ≠ k.attachment.opposite ∧ k.lit = true then 15 else 0 := by
  unfold Torch.signal Torch.ownSignal
  by_cases h : d = k.attachment.opposite <;> by_cases h' : k.lit = true <;> simp [h, h']

/-- **All of a repeater's signal is strong**: what it gives to the block at its output it
gives as a direct signal. -/
theorem repeater_directSignal (s : Blocks.Repeater) (l : Level) (p : Pos) (d : Direction) :
    (Repeater.repeater s).directSignal l p d = (Repeater.repeater s).signal l p d := rfl

/-- **All of an observer's signal is strong.** -/
theorem observer_directSignal (s : Blocks.Observer) (l : Level) (p : Pos) (d : Direction) :
    (Observer.observer s).directSignal l p d = (Observer.observer s).signal l p d := rfl

end Conduction

end Redstone
