module

public import Redstone.Component.Lamp

/-!
# Lemmas about the redstone lamp

Generic facts about the redstone lamp (`RedstoneLampBlock`), over an arbitrary level, as
opposed to the theorems about concrete circuits in `Redstone/Theorems`. A lamp lights the
moment it sees a signal and goes dark four game ticks after the signal is gone, if it is still
gone then. In the game's code these are two reactions, and each lemma here is about one of
them:

* **A neighbour update** (`neighborChanged`). A dark lamp that has a signal is lit in the same
  reaction, with no scheduled tick in between (`neighborChanged_lights`). A lit lamp that has
  lost its signal stays lit and schedules a tick of its own four game ticks ahead
  (`neighborChanged_schedules`); if such a tick is already waiting, nothing more is scheduled
  (`neighborChanged_of_scheduled`). A lamp that agrees with its signal does nothing
  (`neighborChanged_of_agrees`).
* **The scheduled tick** (`tick`). A lit lamp that still has no signal goes dark
  (`tick_goes_dark`). A lamp that has its signal back stays lit: a signal that returns within
  the four game ticks cancels the switching off (`tick_of_signal`). The tick of a dark lamp
  does nothing (`tick_of_unlit`).

The hypotheses are about what `hasNeighborSignal` answers at the lamp in the level at hand
(`Level.hasNeighborSignalAt env l p`), about the lamp's own state, and about its scheduled
ticks. And a lamp gives no signal itself (`signal_lamp`, `directSignal_lamp`).

Left out: a lemma about the whole delay over an arbitrary level ("the lamp is dark exactly four
game ticks after the signal went"). Between the neighbour update and the tick the rest of the
level runs, so such a lemma needs to know that nothing else touches the lamp or its tick; that
is proved for concrete circuits by evaluation
(`Redstone/Theorems/Basics/LeverLamp.lean`, `Redstone/Theorems/Arithmetic/Decoder.lean`). Also
left out: what `Level.setBlock` then does to the level (the neighbours of a lamp get a shape
update and no neighbour update, flag 2), and the copper bulbs of the same component.
-/

@[expose] public section

namespace Redstone.Component.Lamp

/-! ### Attribute lemmas -/

/-- The behaviour of a redstone lamp is `lamp`. -/
theorem behaviour_redstoneLamp (s : Blocks.RedstoneLamp) : behaviour (.redstoneLamp s) = lamp s :=
  rfl

/-- A redstone lamp gives no signal, lit or not. -/
theorem signal_lamp (s : Blocks.RedstoneLamp) (l : Level) (p : Pos) (d : Direction) :
    (lamp s).signal l p d = 0 := rfl

/-- A redstone lamp gives no strong power, lit or not. -/
theorem directSignal_lamp (s : Blocks.RedstoneLamp) (l : Level) (p : Pos) (d : Direction) :
    (lamp s).directSignal l p d = 0 := rfl

/-! ### Single-reaction lemmas -/

/-- `hasNeighborSignal` only reads the level. -/
theorem hasNeighborSignal_eq (p : Pos) (env : Env) (l : Level) :
    Level.hasNeighborSignal p env l = (l.hasNeighborSignalAt env p, l) := rfl

/-- **A lamp that agrees with its signal does nothing** on a neighbour update: lit with a
signal, or dark without one, it leaves the level as it is. -/
theorem neighborChanged_of_agrees (s : Blocks.RedstoneLamp) (p : Pos) (block : BlockId)
    (moved : Bool) (env : Env) (l : Level) (h : l.hasNeighborSignalAt env p = s.lit) :
    (lamp s).neighborChanged p block moved env l = ((), l) := by
  simp only [lamp, bind, ReaderT.bind, StateT.bind, hasNeighborSignal_eq, h, bne_self_eq_false,
    Bool.false_eq_true, ite_false, pure, ReaderT.pure, StateT.pure]

/-- **A lamp lights at once.** A dark lamp that sees a signal on a neighbour update is replaced
by the lit lamp in that same reaction (`setBlock` with flag 2); no tick is scheduled. -/
theorem neighborChanged_lights (s : Blocks.RedstoneLamp) (p : Pos) (block : BlockId)
    (moved : Bool) (env : Env) (l : Level) (hlit : s.lit = false)
    (h : l.hasNeighborSignalAt env p = true) :
    (lamp s).neighborChanged p block moved env l =
      (discard <| Level.setBlock p (.redstoneLamp ⟨true⟩) 2) env l := by
  obtain ⟨lit⟩ := s
  subst hlit
  simp only [lamp, bind, ReaderT.bind, StateT.bind, hasNeighborSignal_eq, h, Bool.false_bne,
    ite_true, Bool.false_eq_true, ite_false]

/-- **A lamp that loses its signal schedules its tick four game ticks ahead.** A lit lamp that
sees no signal on a neighbour update, and has no tick waiting, stays lit; one scheduled tick of
the lamp is added, due four game ticks after the current game time, and nothing else in the
level changes but the counter that orders the ticks. -/
theorem neighborChanged_schedules (s : Blocks.RedstoneLamp) (p : Pos) (block : BlockId)
    (moved : Bool) (env : Env) (l : Level) (hlit : s.lit = true)
    (h : l.hasNeighborSignalAt env p = false)
    (hsched : l.hasScheduledTick p .redstone_lamp = false) :
    (lamp s).neighborChanged p block moved env l =
      ((), { l with
        subTickCount := l.subTickCount + 1
        ticks := l.ticks ++
          [⟨p, .redstone_lamp, l.gameTime + 4, .normal, l.subTickCount⟩] }) := by
  have hsched' : Level.hasScheduledTick { l with subTickCount := l.subTickCount + 1 } p
      .redstone_lamp = false := hsched
  simp only [lamp, bind, ReaderT.bind, StateT.bind, hasNeighborSignal_eq, h, hlit,
    Bool.true_bne, Bool.not_false, ite_true, Level.scheduleTick, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, monadLift, MonadLift.monadLift, hsched',
    Bool.false_eq_true, ite_false, pure]

/-- **A second loss of signal while the tick is waiting schedules nothing.** A lit lamp that
sees no signal on a neighbour update while a tick of it is already scheduled leaves the level
as it is, but for the counter that orders the ticks: the tick already waiting keeps its time. -/
theorem neighborChanged_of_scheduled (s : Blocks.RedstoneLamp) (p : Pos) (block : BlockId)
    (moved : Bool) (env : Env) (l : Level) (hlit : s.lit = true)
    (h : l.hasNeighborSignalAt env p = false)
    (hsched : l.hasScheduledTick p .redstone_lamp = true) :
    (lamp s).neighborChanged p block moved env l =
      ((), { l with subTickCount := l.subTickCount + 1 }) := by
  have hsched' : Level.hasScheduledTick { l with subTickCount := l.subTickCount + 1 } p
      .redstone_lamp = true := hsched
  simp only [lamp, bind, ReaderT.bind, StateT.bind, hasNeighborSignal_eq, h, hlit,
    Bool.true_bne, Bool.not_false, ite_true, Level.scheduleTick, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, monadLift, MonadLift.monadLift, hsched',
    pure]

/-- **The lamp goes dark in its tick, if the signal is still gone.** The scheduled tick of a
lit lamp that sees no signal replaces it by the dark lamp (`setBlock` with flag 2). -/
theorem tick_goes_dark (s : Blocks.RedstoneLamp) (p : Pos) (env : Env) (l : Level)
    (hlit : s.lit = true) (h : l.hasNeighborSignalAt env p = false) :
    (lamp s).tick p env l = (discard <| Level.setBlock p (.redstoneLamp ⟨false⟩) 2) env l := by
  obtain ⟨lit⟩ := s
  subst hlit
  simp only [lamp, bind, ReaderT.bind, StateT.bind, hasNeighborSignal_eq, h, Bool.not_false,
    Bool.and_self, ite_true]

/-- **A signal that is back when the tick runs cancels the switching off.** The scheduled tick
of a lamp that sees a signal leaves the level as it is: a lamp whose signal was gone for less
than four game ticks stays lit. -/
theorem tick_of_signal (s : Blocks.RedstoneLamp) (p : Pos) (env : Env) (l : Level)
    (h : l.hasNeighborSignalAt env p = true) : (lamp s).tick p env l = ((), l) := by
  simp only [lamp, bind, ReaderT.bind, StateT.bind, hasNeighborSignal_eq, h, Bool.not_true,
    Bool.and_false, Bool.false_eq_true, ite_false, pure, ReaderT.pure, StateT.pure]

/-- The scheduled tick of a dark lamp does nothing. -/
theorem tick_of_unlit (s : Blocks.RedstoneLamp) (p : Pos) (env : Env) (l : Level)
    (hlit : s.lit = false) : (lamp s).tick p env l = ((), l) := by
  simp only [lamp, bind, ReaderT.bind, StateT.bind, hasNeighborSignal_eq, hlit, Bool.false_and,
    Bool.false_eq_true, ite_false, pure, ReaderT.pure, StateT.pure]

end Redstone.Component.Lamp
