module

public import Redstone.Lemmas.Repeater

/-!
# Lemmas about the pulses of a repeater

What the scheduled tick of a diode (`Diode.tick`, the tick of a repeater or a comparator's
superclass) does, case by case, on an arbitrary level. `Redstone/Lemmas/Repeater.lean` has the
other half, the scheduling of that tick (`Diode.checkTickOnNeighbor_schedules`); the pulses of
concrete circuits are in `Redstone/Theorems/Pulse`.

The hypotheses say what `isLocked` and `shouldTurnOn` answer in the level, and that they only
read it, as in `Redstone/Lemmas/Repeater.lean`.

* `Diode.tick_of_locked`: a locked diode does nothing in its tick.
* `Diode.tick_of_on_of_input`: a diode that is on and still has its input does nothing.
* `Diode.tick_of_on_of_input_gone`: a diode that is on and has lost its input switches off.
* `Diode.tick_of_off_of_input`: a diode that is off and has its input switches on.
* `Diode.tick_of_off_of_input_gone`: **the minimum pulse.** A diode that is off switches on in
  its tick *although its input is gone by then*, and schedules the tick that will switch it
  off again, `delay` game ticks ahead, with the priority `veryHigh`. This is why a pulse
  shorter than the delay of a repeater comes out as long as the delay
  (`Redstone/Theorems/Pulse/RepeaterStretch.lean`).
* `Repeater.tick_of_off_of_input_gone`: the same for a repeater, whose delay is `2 * delay`
  game ticks.
* `Repeater.cycleDelay_four`: using a repeater four times brings its delay back.
* `Repeater.outputSignal_diode`: the output of a repeater is 15 whatever it reads.

Left out: the length of the output pulse as a statement over an arbitrary level ("the output is
on for exactly `2 * delay` game ticks"). Between the two ticks the rest of the level runs, and
such a lemma has to know that nothing else touches the repeater, its input or its scheduled
tick; that is proved for concrete circuits by evaluation.
-/

@[expose] public section

namespace Redstone.Component

namespace Diode

/-- How a program of the model that is a `bind` runs: the first part, then the second from the
level the first one leaves. -/
theorem bind_apply {α β : Type} (m : M α) (k : α → M β) (env : Env) (l : Level) :
    (m >>= k) env l = k (m env l).1 env (m env l).2 := rfl

/-- How `pure` runs: it leaves the level as it is. -/
theorem pure_apply {α : Type} (a : α) (env : Env) (l : Level) : (pure a : M α) env l = (a, l) :=
  rfl

/-- **A locked diode does nothing in its tick.** -/
theorem tick_of_locked (d : Diode) (p : Pos) (env : Env) (l : Level)
    (hlock : d.isLocked p env l = (true, l)) : d.tick p env l = ((), l) := by
  simp [tick, bind_apply, pure_apply, hlock]

/-- **A diode that is on and still has its input does nothing in its tick.** -/
theorem tick_of_on_of_input (d : Diode) (p : Pos) (env : Env) (l : Level)
    (hlock : d.isLocked p env l = (false, l)) (hon : d.shouldTurnOn p env l = (true, l))
    (hp : d.powered = true) : d.tick p env l = ((), l) := by
  simp [tick, bind_apply, pure_apply, hlock, hon, hp]

/-- **A diode that is on and has lost its input switches off in its tick**: the block is set
to its unpowered state (with the flags 2, so the neighbours are told through the shape
updates and the diode's own `onPlace`), and nothing is scheduled. -/
theorem tick_of_on_of_input_gone (d : Diode) (p : Pos) (env : Env) (l : Level)
    (hlock : d.isLocked p env l = (false, l)) (hon : d.shouldTurnOn p env l = (false, l))
    (hp : d.powered = true) :
    d.tick p env l = (discard <| Level.setBlock p (d.setPowered false) 2 : M Unit) env l := by
  simp [tick, bind_apply, hlock, hon, hp]

/-- **A diode that is off and has its input switches on in its tick**, and schedules
nothing. -/
theorem tick_of_off_of_input (d : Diode) (p : Pos) (env : Env) (l : Level)
    (hlock : d.isLocked p env l = (false, l)) (hon : d.shouldTurnOn p env l = (true, l))
    (hp : d.powered = false) :
    d.tick p env l = (discard <| Level.setBlock p (d.setPowered true) 2 : M Unit) env l := by
  simp [tick, bind_apply, pure_apply, hlock, hon, hp]
  rfl

/-- **The minimum pulse.** A diode that is off switches on in its tick even when its input is
gone by then, and schedules the tick that switches it off again, `delay` game ticks ahead and
with the priority `veryHigh`. So the shortest pulse a diode gives is as long as its delay. -/
theorem tick_of_off_of_input_gone (d : Diode) (p : Pos) (env : Env) (l : Level)
    (hlock : d.isLocked p env l = (false, l)) (hon : d.shouldTurnOn p env l = (false, l))
    (hp : d.powered = false) :
    d.tick p env l =
      (do
        discard <| Level.setBlock p (d.setPowered true) 2
        Level.scheduleTick p d.id d.delay .veryHigh : M Unit) env l := by
  simp [tick, bind_apply, hlock, hon, hp]

end Diode

namespace Repeater

/-- The scheduled tick of a repeater is the tick of the diode it is. -/
theorem tick_repeater (s : Blocks.Repeater) : (repeater s).tick = (diode s).tick := rfl

/-- The output of a repeater has strength 15, whatever the strength of its input. -/
theorem outputSignal_diode (s : Blocks.Repeater) (l : Level) (p : Pos) :
    (diode s).outputSignal l p = 15 := rfl

/-- **The minimum pulse of a repeater is its delay.** A repeater at `p` that is off and not
locked switches on in its tick even when its input is gone by then, and schedules the tick
that switches it off again `2 * delay` game ticks ahead: 2, 4, 6 or 8 game ticks. -/
theorem tick_of_off_of_input_gone (s : Blocks.Repeater) (p : Pos) (env : Env) (l : Level)
    (hlock : isLocked s p env l = (false, l))
    (hon : (diode s).shouldTurnOn p env l = (false, l)) (hp : s.powered = false) :
    (diode s).tick p env l =
      (do
        discard <| Level.setBlock p (.repeater { s with powered := true }) 2
        Level.scheduleTick p .repeater (2 * s.delay.val) .veryHigh : M Unit) env l := by
  rw [← delay_diode]
  exact Diode.tick_of_off_of_input_gone (diode s) p env l hlock hon hp

/-- A repeater that is on, not locked, and has lost its input switches off in its tick. -/
theorem tick_of_on_of_input_gone (s : Blocks.Repeater) (p : Pos) (env : Env) (l : Level)
    (hlock : isLocked s p env l = (false, l))
    (hon : (diode s).shouldTurnOn p env l = (false, l)) (hp : s.powered = true) :
    (diode s).tick p env l =
      (discard <| Level.setBlock p (.repeater { s with powered := false }) 2 : M Unit) env l :=
  Diode.tick_of_on_of_input_gone (diode s) p env l hlock hon hp

/-- **A locked repeater keeps its state**: its tick does nothing, whatever its input. -/
theorem tick_of_locked (s : Blocks.Repeater) (p : Pos) (env : Env) (l : Level)
    (hlock : isLocked s p env l = (true, l)) : (diode s).tick p env l = ((), l) :=
  Diode.tick_of_locked (diode s) p env l hlock

/-- Using a repeater four times brings it back to the delay it had: `cycleDelay` has period
four. -/
theorem cycleDelay_four (s : Blocks.Repeater) :
    cycleDelay (cycleDelay (cycleDelay (cycleDelay s))) = s := by
  rcases s with ⟨⟨v, h₁, h₂⟩, facing, locked, powered⟩
  have hv : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 := by omega
  rcases hv with rfl | rfl | rfl | rfl <;> simp [cycleDelay]

end Repeater

end Redstone.Component
