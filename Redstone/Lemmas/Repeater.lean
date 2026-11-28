module

public import Redstone.Component.Repeater

/-!
# Lemmas about the repeater

Generic facts about one component, as opposed to the theorems about concrete circuits in
`Redstone/Theorems`. This file is the model for the lemma files of the other components. It
has the two kinds of lemma that can be proved for an arbitrary level:

* **Attribute lemmas**: facts about the block state alone, with no level and no monad. The
  repeater's delay is twice its `delay` property, so 2, 4, 6 or 8 game ticks
  (`getDelay_eq`, `getDelay_mem`); a repeater gives 15 to the block at its output when it is
  powered and nothing anywhere else (`signal_repeater`).
* **Single-reaction lemmas**: what one reaction of the block does to an arbitrary level, under
  hypotheses about what the reaction reads. `checkTickOnNeighbor_schedules` says that a
  repeater that is not locked and disagrees with its input schedules exactly one tick, due
  `2 * delay` game ticks later, and changes nothing else; `checkTickOnNeighbor_of_agrees`
  that a repeater that agrees with its input does nothing.

Left out: a lemma about the whole delay ("the output follows the input `2 * delay` game ticks
later") over an arbitrary level. Between the scheduling and the tick the rest of the level
runs, so such a lemma needs to know that nothing else interferes; that is proved for concrete
circuits by evaluation (`Redstone/Theorems/Basics/RepeaterDelay.lean`).
-/

@[expose] public section

namespace Redstone.Component

namespace Repeater

/-! ### Attribute lemmas -/

/-- The delay of a repeater, in game ticks, is twice its `delay` property. -/
theorem getDelay_eq (s : Blocks.Repeater) : getDelay s = 2 * s.delay.val := Nat.mul_comm ..

/-- The delay of a repeater is 2, 4, 6 or 8 game ticks. -/
theorem getDelay_mem (s : Blocks.Repeater) : getDelay s ∈ [2, 4, 6, 8] := by
  have h₁ := s.delay.lo_le
  have h₂ := s.delay.le_hi
  simp only [getDelay, List.mem_cons, List.mem_nil_iff, or_false]
  omega

/-- Using a repeater moves it to the next delay: one more game-tick pair, and from 8 game
ticks back to 2. -/
theorem getDelay_cycleDelay (s : Blocks.Repeater) :
    getDelay (cycleDelay s) = if getDelay s = 8 then 2 else getDelay s + 2 := by
  have h₁ := s.delay.lo_le
  have h₂ := s.delay.le_hi
  split
  · next h =>
    simp only [getDelay, cycleDelay] at h ⊢
    omega
  · next h =>
    simp only [getDelay, cycleDelay] at h ⊢
    omega

/-- The delay the repeater schedules its ticks with is `2 * delay`. -/
@[simp]
theorem delay_diode (s : Blocks.Repeater) : (diode s).delay = 2 * s.delay.val := getDelay_eq s

/-- A repeater gives a signal only to the block at its output (the direction `d` points from
that block back to the repeater, which is the repeater's `facing`): 15 when it is powered. -/
theorem signal_repeater (s : Blocks.Repeater) (l : Level) (p : Pos) (d : Direction) :
    (repeater s).signal l p d = if s.facing.toDirection = d ∧ s.powered = true then 15 else 0 := by
  change (if s.facing.toDirection = d then (if s.powered then 15 else 0) else 0) = _
  by_cases h : s.facing.toDirection = d <;> by_cases h' : s.powered = true <;> simp [h, h']

/-- A repeater that is not powered gives no signal. -/
theorem signal_repeater_of_unpowered (s : Blocks.Repeater) (l : Level) (p : Pos) (d : Direction)
    (h : s.powered = false) : (repeater s).signal l p d = 0 := by
  simp [signal_repeater, h]

end Repeater

/-! ### Single-reaction lemmas -/

namespace Diode

/-- The priority with which `checkTickOnNeighbor` schedules the tick of the diode `d` at `p`. -/
def tickPriority (d : Diode) (l : Level) (p : Pos) : TickPriority :=
  if shouldPrioritize d.facing l p then .extremelyHigh else if d.powered then .veryHigh else .high

/-- **A diode that disagrees with its input schedules its tick.** Let the diode `d` at `p` be
unlocked, let its input say `on` while its `powered` property says the opposite, and let no
tick of the diode be collected for the current game tick or waiting. Then
`checkTickOnNeighbor` adds one scheduled tick at `p`, due `d.delay` game ticks from now, and
changes nothing else in the level but the counter that orders the ticks.

The hypotheses on `isLocked` and `shouldTurnOn` say what they answer in this level, and that
they only read it. -/
theorem checkTickOnNeighbor_schedules (d : Diode) (p : Pos) (env : Env) (l : Level) (on : Bool)
    (hlock : d.isLocked p env l = (false, l)) (hon : d.shouldTurnOn p env l = (on, l))
    (hne : d.powered ≠ on) (hwill : l.willTickThisTick p d.id = false)
    (hsched : l.hasScheduledTick p d.id = false) :
    d.checkTickOnNeighbor p env l =
      ((), { l with
        subTickCount := l.subTickCount + 1
        ticks := l.ticks ++
          [⟨p, d.id, l.gameTime + d.delay, d.tickPriority l p, l.subTickCount⟩] }) := by
  have hne' : (d.powered != on) = true := by simpa using hne
  have hsched' : Level.hasScheduledTick { l with subTickCount := l.subTickCount + 1 } p d.id
      = false := hsched
  simp only [checkTickOnNeighbor, Level.scheduleTick, tickPriority, bind, ReaderT.bind,
    StateT.bind, hlock, hon, get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift,
    StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    hne', hwill, hsched', pure, Bool.not_false, Bool.and_self,
    ite_true, Bool.false_eq_true, ite_false]

/-- **A diode that agrees with its input does nothing**: `checkTickOnNeighbor` leaves the level
as it is. -/
theorem checkTickOnNeighbor_of_agrees (d : Diode) (p : Pos) (env : Env) (l : Level)
    (hlock : d.isLocked p env l = (false, l)) (hon : d.shouldTurnOn p env l = (d.powered, l)) :
    d.checkTickOnNeighbor p env l = ((), l) := by
  simp only [checkTickOnNeighbor, bind, ReaderT.bind, StateT.bind, hlock, hon, get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, pure,
    ReaderT.pure, StateT.pure, bne_self_eq_false, Bool.false_and, Bool.not_false,
    Bool.false_eq_true, ite_true, ite_false]

end Diode

namespace Repeater

/-- **The repeater's delay is `2 * delay` game ticks.** A repeater at `p` that is not locked
and whose `powered` property disagrees with its input (`on`), with no tick of its own pending,
reacts to a neighbour update by scheduling exactly one tick, due `2 * delay` game ticks after
the current game time; nothing else in the level changes but the counter that orders the
ticks. That tick is what switches the repeater (`Diode.tick`). -/
theorem checkTickOnNeighbor_schedules (s : Blocks.Repeater) (p : Pos) (env : Env) (l : Level)
    (on : Bool) (hlock : isLocked s p env l = (false, l))
    (hon : (diode s).shouldTurnOn p env l = (on, l)) (hne : s.powered ≠ on)
    (hwill : l.willTickThisTick p .repeater = false)
    (hsched : l.hasScheduledTick p .repeater = false) :
    (diode s).checkTickOnNeighbor p env l =
      ((), { l with
        subTickCount := l.subTickCount + 1
        ticks := l.ticks ++ [⟨p, .repeater, l.gameTime + 2 * s.delay.val,
          (diode s).tickPriority l p, l.subTickCount⟩] }) := by
  rw [← delay_diode]
  exact Diode.checkTickOnNeighbor_schedules (diode s) p env l on hlock hon hne hwill hsched

end Repeater

end Redstone.Component
