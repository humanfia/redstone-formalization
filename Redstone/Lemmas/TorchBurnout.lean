module

public import Redstone.Component.Torch

/-!
# Lemmas about the redstone torch and its burn-out

Generic facts about the redstone torch (`RedstoneTorchBlock`, `RedstoneWallTorchBlock`), over
an arbitrary level. The theorems about concrete torch circuits are in `Redstone/Theorems`;
`Redstone/Theorems/Clock/RapidClock.lean` is the circuit in which a torch burns out.

* **Attribute lemmas.** A lit torch gives 15 to every neighbour but the block it is attached
  to, and an unlit torch gives nothing (`signal_torch`, `signal_torch_of_unlit`); its strong
  power goes to the block above it only (`directSignal_torch_down`,
  `directSignal_torch_of_ne_down`). The four constants of the class are 2, 60, 8 and 160
  game ticks or entries (`toggleDelay_eq`, `recentToggleTimer_eq`, `maxRecentToggles_eq`,
  `restartDelay_eq`).
* **The burn-out list.** `toggleCount l p` is the number of entries of the torch at `p` on the
  list `Level.recentTorchToggles`. Asking whether the torch is toggled too often compares
  that number with 8 and changes nothing (`isToggledTooFrequently_peek`); asking with `add`
  first appends the current game time, so it answers yes exactly when seven entries were
  there already (`isToggledTooFrequently_add`, `isToggledTooFrequently_add_iff`): **the eighth
  switch-off burns the torch out**.
* **The window.** The loop at the start of a tick drops entries from the front of the list
  while they are more than 60 game ticks old (`dropOldToggles_eq`). The list is in the order
  in which the toggles happened; when its times do not decrease, what is left is exactly the
  entries at most 60 game ticks old (`dropWhile_old_eq_filter`), and the count of a torch
  after the loop is the number of its switch-offs in the last 60 game ticks
  (`toggleCount_afterDrop`).
* **Single-reaction lemmas**, each under a hypothesis that says what the torch reads at its
  input (`hasNeighborSignal`), and that reading changes nothing:
  * a burnt-out torch stays out: an unlit torch without input whose count is still at least
    8 after the loop does nothing but run the loop (`tick_of_burnt_out`);
  * a torch that has rested relights: with a count below 8 the same tick sets the lit state
    (`tick_relights`);
  * a lit torch with input is switched off, the switch-off is put on the list, and when that
    makes eight entries a tick is asked for 160 game ticks later (`tick_switches_off`);
  * a torch whose state already fits its input only runs the loop (`tick_of_lit_unpowered`,
    `tick_of_unlit_powered`);
  * a neighbour update schedules the tick of a torch that does not fit its input 2 game ticks
    ahead, unless one is waiting (`neighborChanged_schedules`), and does nothing to a torch
    that fits (`neighborChanged_of_fits`).

Left out: a lemma about a whole burn-out ("eight switch-offs within 60 game ticks leave the
torch out until an entry expires") over an arbitrary level. Between two ticks of the torch the
rest of the level runs, and `Level.setBlock` in the middle of `tick` sends neighbour updates
that may come back to the torch; that is proved for a concrete circuit by evaluation
(`Redstone/Theorems/Clock/RapidClock.lean`). In particular nothing here says that the tick
asked for on burn-out is in fact scheduled: `Level.scheduleTick` drops it when the torch
already has a tick waiting, which is what happens in that circuit.
-/

@[expose] public section

namespace Redstone.Component.Torch

/-! ### Attribute lemmas -/

/-- `TOGGLE_DELAY`: a torch follows its input two game ticks later. -/
theorem toggleDelay_eq : toggleDelay = 2 := rfl

/-- `RECENT_TOGGLE_TIMER`: a toggle counts for 60 game ticks. -/
theorem recentToggleTimer_eq : recentToggleTimer = 60 := rfl

/-- `MAX_RECENT_TOGGLES`: eight toggles on the list burn a torch out. -/
theorem maxRecentToggles_eq : maxRecentToggles = 8 := rfl

/-- `RESTART_DELAY`: on burn-out the torch asks for a tick 160 game ticks later. -/
theorem restartDelay_eq : restartDelay = 160 := rfl

/-- A torch gives a signal of 15 to every neighbour except the block it is attached to, when
it is lit (the direction `d` points from the neighbour to the torch). -/
theorem signal_torch (k : Kind) (l : Level) (p : Pos) (d : Direction) :
    (torch k).signal l p d = if d ≠ k.attachment.opposite ∧ k.lit = true then 15 else 0 := by
  change (if d ≠ k.attachment.opposite then (if k.lit then 15 else 0) else 0) = _
  by_cases h : d ≠ k.attachment.opposite <;> by_cases h' : k.lit = true <;> simp [h, h']

/-- An unlit torch gives no signal. -/
theorem signal_torch_of_unlit (k : Kind) (l : Level) (p : Pos) (d : Direction)
    (h : k.lit = false) : (torch k).signal l p d = 0 := by
  simp [signal_torch, h]

/-- A torch gives strong power to no block but the one above it. -/
theorem directSignal_torch_of_ne_down (k : Kind) (l : Level) (p : Pos) (d : Direction)
    (h : d ≠ .down) : (torch k).directSignal l p d = 0 := by
  change (if d = .down then signal k d else 0) = 0
  simp only [h, ↓reduceIte]

/-- A lit torch gives strong power 15 to the block above it (the direction from that block to
the torch is `down`), whether it stands on a block or hangs on a wall. -/
theorem directSignal_torch_down (k : Kind) (l : Level) (p : Pos) :
    (torch k).directSignal l p .down = if k.lit = true then 15 else 0 := by
  cases k with
  | floor s =>
    obtain ⟨lit⟩ := s
    cases lit <;> rfl
  | wall s =>
    obtain ⟨f, lit⟩ := s
    cases f <;> cases lit <;> rfl

/-! ### The burn-out list -/

/-- The number of entries of the torch at `p` on the burn-out list. -/
def toggleCount (l : Level) (p : Pos) : ℕ := (l.recentTorchToggles.filter (·.1 == p)).length

/-- `isToggledTooFrequently(level, pos, false)` compares the number of entries of the torch
with `MAX_RECENT_TOGGLES` and leaves the level as it is. -/
theorem isToggledTooFrequently_peek (p : Pos) (env : Env) (l : Level) :
    isToggledTooFrequently p false env l = (decide (toggleCount l p ≥ maxRecentToggles), l) :=
  rfl

/-- `isToggledTooFrequently(level, pos, true)` appends the current game time for the torch and
then compares: the new entry counts. -/
theorem isToggledTooFrequently_add (p : Pos) (env : Env) (l : Level) :
    isToggledTooFrequently p true env l =
      (decide (toggleCount l p + 1 ≥ maxRecentToggles),
        { l with recentTorchToggles := l.recentTorchToggles ++ [(p, l.gameTime)] }) := by
  have h : ((l.recentTorchToggles ++ [(p, l.gameTime)]).filter (·.1 == p)).length =
      toggleCount l p + 1 := by
    simp [toggleCount, List.filter_append]
  change (decide (((l.recentTorchToggles ++ [(p, l.gameTime)]).filter (·.1 == p)).length ≥
    maxRecentToggles), _) = _
  rw [h]

/-- **The eighth switch-off burns the torch out**: a switch-off is "too frequent" exactly when
the list already holds seven entries of the torch. -/
theorem isToggledTooFrequently_add_iff (p : Pos) (env : Env) (l : Level) :
    (isToggledTooFrequently p true env l).1 = true ↔ 7 ≤ toggleCount l p := by
  rw [isToggledTooFrequently_add]
  simp only [maxRecentToggles, ge_iff_le, decide_eq_true_eq]
  omega

/-! ### The window of 60 game ticks -/

/-- The level after the loop at the start of a torch's tick: the entries at the front of the
burn-out list that are more than 60 game ticks old are gone. -/
def afterDrop (l : Level) : Level :=
  { l with
    recentTorchToggles := l.recentTorchToggles.dropWhile (l.gameTime - ·.2 > recentToggleTimer) }

/-- The loop at the start of `tick` changes nothing but the burn-out list. -/
theorem dropOldToggles_eq (env : Env) (l : Level) : dropOldToggles env l = ((), afterDrop l) :=
  rfl

/-- The loop only looks at the front of the list. When the times on the list do not decrease,
as they do not when every entry was added at the game time of its toggle, what the loop
leaves is exactly the entries that are at most 60 game ticks old. -/
theorem dropWhile_old_eq_filter (now : ℕ) (ts : List (Pos × ℕ))
    (h : ts.Pairwise fun a b => a.2 ≤ b.2) :
    ts.dropWhile (now - ·.2 > recentToggleTimer) =
      ts.filter (fun e => decide (now - e.2 ≤ recentToggleTimer)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨ht, hts⟩ := List.pairwise_cons.1 h
    by_cases hold : now - t.2 > recentToggleTimer
    · have h1 : (decide (now - t.2 > recentToggleTimer)) = true := by simpa using hold
      have h2 : (decide (now - t.2 ≤ recentToggleTimer)) = false := by
        simp only [decide_eq_false_iff_not]
        omega
      rw [List.dropWhile_cons, List.filter_cons]
      simp only [h1, h2, ↓reduceIte, Bool.false_eq_true]
      exact ih hts
    · have h1 : (decide (now - t.2 > recentToggleTimer)) = false := by simpa using hold
      rw [List.dropWhile_cons]
      simp only [h1, Bool.false_eq_true, ↓reduceIte]
      symm
      rw [List.filter_eq_self]
      intro e he
      simp only [decide_eq_true_eq]
      rcases List.mem_cons.1 he with rfl | he
      · omega
      · have := ht e he
        omega

/-- The count of a torch after the loop, when the times on the list do not decrease: the
number of its entries that are at most 60 game ticks old. -/
theorem toggleCount_afterDrop (l : Level) (p : Pos)
    (h : l.recentTorchToggles.Pairwise fun a b => a.2 ≤ b.2) :
    toggleCount (afterDrop l) p =
      (l.recentTorchToggles.filter fun e =>
        decide (l.gameTime - e.2 ≤ recentToggleTimer) && e.1 == p).length := by
  change ((l.recentTorchToggles.dropWhile (l.gameTime - ·.2 > recentToggleTimer)).filter
    (·.1 == p)).length = _
  rw [dropWhile_old_eq_filter _ _ h, List.filter_filter]
  congr 2
  funext e
  rw [Bool.and_comm]

/-! ### Single-reaction lemmas -/

/-- `discard` runs the reaction and forgets its result. -/
theorem discard_apply {α : Type} (x : M α) (env : Env) (l : Level) :
    discard x env l = ((), (x env l).2) := rfl

/-- **A burnt-out torch stays out.** An unlit torch whose input is off would light up; but if
the burn-out list still holds eight entries of the torch after the old ones were dropped, its
tick does nothing except drop the old entries. -/
theorem tick_of_burnt_out (k : Kind) (p : Pos) (env : Env) (l : Level) (hk : k.lit = false)
    (hsig : hasNeighborSignal k p env l = (false, l))
    (hcount : maxRecentToggles ≤ toggleCount (afterDrop l) p) :
    tick k p env l = ((), afterDrop l) := by
  have h2 : isToggledTooFrequently p false env (afterDrop l) = (true, afterDrop l) := by
    rw [isToggledTooFrequently_peek]
    simp [hcount]
  simp only [tick, bind, ReaderT.bind, StateT.bind, hsig, dropOldToggles_eq, hk, h2, pure,
    ReaderT.pure, StateT.pure, Bool.false_eq_true, ite_false, Bool.not_false, Bool.not_true,
    ite_true]

/-- **A torch that has rested relights.** An unlit torch whose input is off, with fewer than
eight entries left after the old ones were dropped, is set to its lit state by its tick. -/
theorem tick_relights (k : Kind) (p : Pos) (env : Env) (l : Level) (hk : k.lit = false)
    (hsig : hasNeighborSignal k p env l = (false, l))
    (hcount : toggleCount (afterDrop l) p < maxRecentToggles) :
    tick k p env l =
      ((), ((Level.setBlock p (k.setLit true).toBlock : M Bool) env (afterDrop l)).2) := by
  have h2 : isToggledTooFrequently p false env (afterDrop l) = (false, afterDrop l) := by
    rw [isToggledTooFrequently_peek]
    simp [Nat.not_le.2 hcount]
  simp only [tick, bind, ReaderT.bind, StateT.bind, hsig, dropOldToggles_eq, hk, h2, pure,
    Bool.false_eq_true, ite_false, Bool.not_false, ite_true, discard_apply]

/-- **A lit torch with input is switched off, and the switch-off is counted.** The tick of a
lit torch whose input is on drops the old entries, sets the unlit state, and puts the
switch-off on the burn-out list with the current game time. If that makes eight entries of
the torch (seven were there), a tick is asked for `RESTART_DELAY` game ticks later, for the
block then at the position. `l₂` is the level after the unlit state was set. -/
theorem tick_switches_off (k : Kind) (p : Pos) (env : Env) (l l₂ : Level) (hk : k.lit = true)
    (hsig : hasNeighborSignal k p env l = (true, l))
    (hset : ((Level.setBlock p (k.setLit false).toBlock : M Bool) env (afterDrop l)).2 = l₂) :
    tick k p env l =
      if 7 ≤ toggleCount l₂ p then
        Level.scheduleTick p (l₂.blockAt p).id restartDelay .normal env
          { l₂ with recentTorchToggles := l₂.recentTorchToggles ++ [(p, l₂.gameTime)] }
      else ((), { l₂ with recentTorchToggles := l₂.recentTorchToggles ++ [(p, l₂.gameTime)] }) := by
  have h2 := isToggledTooFrequently_add p env l₂
  have h3 : decide (toggleCount l₂ p + 1 ≥ maxRecentToggles) = decide (7 ≤ toggleCount l₂ p) := by
    simp only [maxRecentToggles, ge_iff_le, decide_eq_decide]
    omega
  rw [h3] at h2
  subst hset
  by_cases hc : 7 ≤ toggleCount
      ((Level.setBlock p (k.setLit false).toBlock : M Bool) env (afterDrop l)).2 p
  · simp only [hc, decide_true] at h2
    simp only [hc, ↓reduceIte, tick, bind, ReaderT.bind, StateT.bind, hsig, dropOldToggles_eq,
      hk, h2, pure, ReaderT.pure, StateT.pure, discard_apply, Level.getBlock, get, getThe,
      MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get]
    rfl
  · simp only [hc, decide_false] at h2
    simp only [hc, ↓reduceIte, tick, bind, ReaderT.bind, StateT.bind, hsig, dropOldToggles_eq,
      hk, h2, pure, ReaderT.pure, StateT.pure, discard_apply, Bool.false_eq_true]

/-- A lit torch whose input is off is as it should be: its tick only drops the old entries. -/
theorem tick_of_lit_unpowered (k : Kind) (p : Pos) (env : Env) (l : Level) (hk : k.lit = true)
    (hsig : hasNeighborSignal k p env l = (false, l)) : tick k p env l = ((), afterDrop l) := by
  simp only [tick, bind, ReaderT.bind, StateT.bind, hsig, dropOldToggles_eq, hk, pure,
    ReaderT.pure, StateT.pure, Bool.false_eq_true, ite_false, ite_true]

/-- An unlit torch whose input is on is as it should be: its tick only drops the old
entries. -/
theorem tick_of_unlit_powered (k : Kind) (p : Pos) (env : Env) (l : Level) (hk : k.lit = false)
    (hsig : hasNeighborSignal k p env l = (true, l)) : tick k p env l = ((), afterDrop l) := by
  simp only [tick, bind, ReaderT.bind, StateT.bind, hsig, dropOldToggles_eq, hk, pure,
    ReaderT.pure, StateT.pure, Bool.false_eq_true, ite_false, Bool.not_true]

/-- **A torch follows its input two game ticks later.** A neighbour update for a torch that
does not fit its input (lit with the input on, or unlit with the input off), with no tick of
its own collected for the current game tick or waiting, schedules exactly one tick, due
`TOGGLE_DELAY` game ticks from now, and changes nothing else but the counter that orders the
ticks. That tick is what switches the torch (`tick`). -/
theorem neighborChanged_schedules (k : Kind) (p : Pos) (env : Env) (l : Level) (s : Bool)
    (hsig : hasNeighborSignal k p env l = (s, l)) (heq : k.lit = s)
    (hwill : l.willTickThisTick p k.id = false) (hsched : l.hasScheduledTick p k.id = false) :
    neighborChanged k p env l =
      ((), { l with
        subTickCount := l.subTickCount + 1
        ticks := l.ticks ++ [⟨p, k.id, l.gameTime + toggleDelay, .normal, l.subTickCount⟩] }) := by
  have heq' : (k.lit == s) = true := by simp [heq]
  have hsched' : Level.hasScheduledTick { l with subTickCount := l.subTickCount + 1 } p k.id
      = false := hsched
  simp only [neighborChanged, Level.scheduleTick, bind, ReaderT.bind, StateT.bind, hsig, get,
    getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, heq', hwill, hsched', pure,
    Bool.not_false, Bool.and_self, ite_true, Bool.false_eq_true, ite_false]

/-- A neighbour update does nothing to a torch that fits its input (lit with the input off, or
unlit with the input on). -/
theorem neighborChanged_of_fits (k : Kind) (p : Pos) (env : Env) (l : Level) (s : Bool)
    (hsig : hasNeighborSignal k p env l = (s, l)) (hne : k.lit ≠ s) :
    neighborChanged k p env l = ((), l) := by
  have hne' : (k.lit == s) = false := by simpa using hne
  simp only [neighborChanged, bind, ReaderT.bind, StateT.bind, hsig, get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, hne', pure,
    ReaderT.pure, StateT.pure, Bool.false_and, Bool.false_eq_true, ite_false]

end Redstone.Component.Torch
