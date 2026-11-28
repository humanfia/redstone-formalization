module

public import Redstone.Component.Torch

/-!
# Lemmas about the redstone torch

Generic facts about the torch of either kind (standing on a block, or on the side of one), over
an arbitrary level. The theorems about concrete circuits are in `Redstone/Theorems`; the gates
built from torches are in `Redstone/Theorems/Logic`.

* **Attribute lemmas**: the signal of a torch as a table. A lit torch gives 15 in every
  direction but into the block it is attached to (`signal_of_lit`, `signal_attachment`), and
  strong power only to the block above it (`directSignal_down_of_lit`,
  `directSignal_of_ne_down`); a torch that is not lit gives nothing (`signal_of_unlit`).
* **What the torch reads**: its input is the signal of the one block it is attached to, and
  reading it does not change the level (`hasNeighborSignal_eq`).
* **`neighborChanged`**: a torch whose state does not fit its input (lit with a signal, or out
  without one) schedules one tick, due two game ticks later, and changes nothing else but the
  counter that orders the ticks (`neighborChanged_schedules`). When a tick of the torch is
  already waiting, only that counter moves (`neighborChanged_of_scheduled`); when the state fits
  the input, or the tick of the torch is about to run in this game tick, nothing happens
  (`neighborChanged_of_fits`, `neighborChanged_of_willTick`).
* **`tick`**: a torch whose state fits its input only cleans the burn-out list
  (`tick_of_fits`). A lit torch with a signal is put out, and then the burn-out list is asked
  (`tick_of_lit_of_signal`); a torch that is out and has no signal is lit unless it is burnt
  out (`tick_of_unlit_of_no_signal`), where burnt out means that the list holds eight toggles
  of this torch (`isToggledTooFrequently_false`).

Together: the torch inverts the signal of its block, two game ticks late. That statement
itself, "two game ticks after the block is powered the torch is out", is left out for an
arbitrary level: between the scheduling and the tick the rest of the level runs, and the
writing of the new torch (`Level.setBlock`) sends updates to every neighbour, so the statement
needs to know the whole neighbourhood. It is proved for concrete circuits by evaluation
(`Redstone/Theorems/Basics/TorchInverter.lean`, `Redstone/Theorems/Logic`).
-/

@[expose] public section

namespace Redstone.Component.Torch

/-! ### Attribute lemmas -/

namespace Kind

/-- Switching a torch leaves it attached where it was. -/
@[simp]
theorem attachment_setLit (k : Kind) (lit : Bool) : (k.setLit lit).attachment = k.attachment := by
  cases k <;> rfl

/-- A torch that was switched has the state it was given. -/
@[simp]
theorem lit_setLit (k : Kind) (lit : Bool) : (k.setLit lit).lit = lit := by
  cases k <;> rfl

/-- Switching a torch does not change which block it is. -/
@[simp]
theorem id_setLit (k : Kind) (lit : Bool) : (k.setLit lit).id = k.id := by
  cases k <;> rfl

/-- No torch is attached to the block above it. -/
theorem attachment_ne_up (k : Kind) : k.attachment ≠ .up := by
  cases k with
  | floor s => simp [attachment]
  | wall s =>
    cases s with
    | mk facing lit =>
      cases facing <;>
        simp [attachment, HorizontalDirection.toDirection, Direction.opposite]

end Kind

/-- A lit torch gives a signal of 15 to every neighbour but the block it is attached to. Here
`d` points from the neighbour to the torch, as in `getSignal(pos, direction)`. -/
theorem signal_of_lit (k : Kind) (d : Direction) (hlit : k.lit = true)
    (hd : d ≠ k.attachment.opposite) : signal k d = 15 := by
  simp [signal, ownSignal, hlit, hd]

/-- A torch gives no signal to the block it is attached to. -/
theorem signal_attachment (k : Kind) : signal k k.attachment.opposite = 0 := by
  simp [signal]

/-- A torch that is not lit gives no signal. -/
theorem signal_of_unlit (k : Kind) (d : Direction) (hlit : k.lit = false) : signal k d = 0 := by
  simp [signal, ownSignal, hlit]

/-- A lit torch gives strong power to the block above it. -/
theorem directSignal_down_of_lit (k : Kind) (hlit : k.lit = true) : directSignal k .down = 15 := by
  have h : Direction.down ≠ k.attachment.opposite := by
    intro h
    have h' := congrArg Direction.opposite h
    rw [Direction.opposite_opposite] at h'
    exact k.attachment_ne_up h'.symm
  simp [directSignal, signal_of_lit k .down hlit h]

/-- A torch gives strong power to no block but the one above it. -/
theorem directSignal_of_ne_down (k : Kind) (d : Direction) (hd : d ≠ .down) :
    directSignal k d = 0 := by
  simp [directSignal, hd]

/-- A torch that is not lit gives no strong power. -/
theorem directSignal_of_unlit (k : Kind) (d : Direction) (hlit : k.lit = false) :
    directSignal k d = 0 := by
  simp [directSignal, signal_of_unlit k d hlit]

/-! ### What the torch reads -/

/-- **The input of a torch is the block it is attached to.** `hasNeighborSignal` asks for the
signal that block gives towards the torch, and leaves the level as it is. -/
theorem hasNeighborSignal_eq (k : Kind) (p : Pos) (env : Env) (l : Level) :
    hasNeighborSignal k p env l =
      (decide (l.signalAt env (p.step k.attachment) k.attachment > 0), l) := rfl

/-- The burn-out list is asked without adding to it: the torch at `p` counts as burnt out when
the list holds at least eight of its toggles, and the level stays as it is. -/
theorem isToggledTooFrequently_false (p : Pos) (env : Env) (l : Level) :
    isToggledTooFrequently p false env l =
      (decide (((l.recentTorchToggles.filter (·.1 == p)).length) ≥ maxRecentToggles), l) := rfl

/-! ### `neighborChanged` -/

/-- **A torch that does not fit its input schedules its tick, two game ticks ahead.** Let the
torch `k` at `p` be lit while the block it is attached to gives it a signal, or out while it
gives none (`hsig`: the input equals `k.lit`). Let no tick of the torch be collected for the
current game tick or waiting. Then `neighborChanged` adds one scheduled tick at `p`, due two
game ticks from now, with the normal priority, and changes nothing else in the level but the
counter that orders the ticks. -/
theorem neighborChanged_schedules (k : Kind) (p : Pos) (env : Env) (l : Level)
    (hsig : hasNeighborSignal k p env l = (k.lit, l))
    (hwill : l.willTickThisTick p k.id = false) (hsched : l.hasScheduledTick p k.id = false) :
    neighborChanged k p env l =
      ((), { l with
        subTickCount := l.subTickCount + 1
        ticks := l.ticks ++ [⟨p, k.id, l.gameTime + 2, .normal, l.subTickCount⟩] }) := by
  have hsched' : Level.hasScheduledTick { l with subTickCount := l.subTickCount + 1 } p k.id
      = false := hsched
  simp only [neighborChanged, Level.scheduleTick, toggleDelay, bind, ReaderT.bind, StateT.bind,
    hsig, get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, hwill, hsched', pure, beq_self_eq_true,
    Bool.not_false, Bool.and_self, ite_true, Bool.false_eq_true, ite_false]

/-- **At most one tick of a torch waits.** If the torch does not fit its input but a tick of it
is already waiting, `neighborChanged` schedules no second one: only the counter that orders the
ticks moves. -/
theorem neighborChanged_of_scheduled (k : Kind) (p : Pos) (env : Env) (l : Level)
    (hsig : hasNeighborSignal k p env l = (k.lit, l))
    (hwill : l.willTickThisTick p k.id = false) (hsched : l.hasScheduledTick p k.id = true) :
    neighborChanged k p env l = ((), { l with subTickCount := l.subTickCount + 1 }) := by
  have hsched' : Level.hasScheduledTick { l with subTickCount := l.subTickCount + 1 } p k.id
      = true := hsched
  simp only [neighborChanged, Level.scheduleTick, toggleDelay, bind, ReaderT.bind, StateT.bind,
    hsig, get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, hwill, hsched', pure, beq_self_eq_true,
    Bool.not_false, Bool.and_self, ite_true]

/-- **A torch that fits its input does nothing**: when the torch is lit and its block gives no
signal, or it is out and the block gives one, `neighborChanged` leaves the level as it is. -/
theorem neighborChanged_of_fits (k : Kind) (p : Pos) (env : Env) (l : Level)
    (hsig : hasNeighborSignal k p env l = (!k.lit, l)) :
    neighborChanged k p env l = ((), l) := by
  have h : (k.lit == !k.lit) = false := by cases k.lit <;> rfl
  simp only [neighborChanged, bind, ReaderT.bind, StateT.bind, hsig, get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, pure, ReaderT.pure,
    StateT.pure, h, Bool.false_and, Bool.false_eq_true, ite_false]

/-- A torch whose tick is about to run in this game tick schedules nothing: `neighborChanged`
leaves the level as it is, whatever the input. -/
theorem neighborChanged_of_willTick (k : Kind) (p : Pos) (env : Env) (l : Level)
    (hwill : l.willTickThisTick p k.id = true) : neighborChanged k p env l = ((), l) := by
  simp only [neighborChanged, hasNeighborSignal_eq, bind, ReaderT.bind, StateT.bind, get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, pure, ReaderT.pure,
    StateT.pure, hwill, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]

/-! ### `tick` -/

/-- **The tick of a torch that fits its input changes no block.** When the torch is lit and its
block gives no signal, or it is out and the block gives one, `tick` only drops the old entries
of the burn-out list. -/
theorem tick_of_fits (k : Kind) (p : Pos) (env : Env) (l : Level)
    (hsig : hasNeighborSignal k p env l = (!k.lit, l)) :
    tick k p env l = dropOldToggles env l := by
  cases hk : k.lit <;> rw [hk] at hsig <;>
    simp only [tick, bind, ReaderT.bind, StateT.bind, hsig, hk, pure, ReaderT.pure, StateT.pure,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false] <;>
    rfl

/-- **The tick of a lit torch with a signal puts it out.** After the old entries of the
burn-out list are dropped, the torch at `p` is replaced by the same torch, not lit; this toggle
is added to the burn-out list, and if the list then holds eight toggles of the torch, a tick is
scheduled 160 game ticks ahead. -/
theorem tick_of_lit_of_signal (k : Kind) (p : Pos) (env : Env) (l : Level) (hlit : k.lit = true)
    (hsig : hasNeighborSignal k p env l = (true, l)) :
    tick k p env l =
      (do
        discard <| Level.setBlock p (k.setLit false).toBlock
        if ← isToggledTooFrequently p true then
          Level.scheduleTick p (← Level.getBlock p).id restartDelay : M Unit) env
        (dropOldToggles env l).2 := by
  simp only [tick, bind, ReaderT.bind, StateT.bind, hsig, hlit, ite_true]
  rfl

/-- **The tick of a torch that is out and has no signal lights it, unless it is burnt out.**
After the old entries of the burn-out list are dropped, the list is asked (without adding to
it); if it holds fewer than eight toggles of the torch, the torch at `p` is replaced by the same
torch, lit. -/
theorem tick_of_unlit_of_no_signal (k : Kind) (p : Pos) (env : Env) (l : Level)
    (hlit : k.lit = false) (hsig : hasNeighborSignal k p env l = (false, l)) :
    tick k p env l =
      (do
        if !(← isToggledTooFrequently p false) then
          discard <| Level.setBlock p (k.setLit true).toBlock : M Unit) env
        (dropOldToggles env l).2 := by
  simp only [tick, bind, ReaderT.bind, StateT.bind, hsig, hlit, Bool.false_eq_true, ite_false,
    Bool.not_false, ite_true]
  rfl

end Redstone.Component.Torch
