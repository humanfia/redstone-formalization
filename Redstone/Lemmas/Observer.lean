module

public import Redstone.Component.Observer

/-!
# Lemmas about the observer

Generic facts about one component, over an arbitrary level; the theorems about concrete
observer circuits are in `Redstone/Theorems/Observer`.

* **Attribute lemmas**: an observer gives 15 while it is powered and nothing otherwise
  (`ownSignal_eq_ite`, `ownSignal_mem`); it gives its signal only to the block behind it, the
  one for which the direction back to the observer is the observer's `facing`
  (`signal_observer`, `signal_of_ne_facing`, `signal_of_unpowered`); and that signal is strong
  power: the direct signal is the same number in every direction
  (`directSignal_observer`, `directSignal_eq_signal`).
* **Single-reaction lemmas** for the shape update, which is where a pulse starts:
  a shape update from the front of an observer that is off, with no tick of the observer
  waiting, schedules exactly one tick two game ticks later and changes nothing else but the
  counter that orders the ticks (`updateShape_front_schedules`). A shape update from any other
  side (`updateShape_of_ne_facing`), to an observer that is on (`updateShape_of_powered`), or
  while a tick is waiting (`updateShape_of_scheduled`) leaves the level as it is. In every case
  the observer itself is returned unchanged (`updateShape_fst`): only its tick switches it.
* **The tick, as a program** (`tick_of_unpowered`, `tick_of_powered`): the tick of an observer
  that is off switches it on, schedules the second tick two game ticks later and tells the
  blocks behind; the tick of an observer that is on switches it off and tells the blocks
  behind, and schedules nothing. Together with `scheduleTick_of_not_scheduled` (what that
  scheduling does to the level) this is the pulse of two game ticks.
* **Placing** (`onPlace_of_observer`, `onPlace_of_unpowered`, `onPlace_of_scheduled`): `onPlace`
  does nothing when the block replaced was an observer, when the observer placed is off, or
  when a tick of the observer is waiting. So an observer that arrives off on the arm of a
  piston is not switched by `onPlace`; what makes it fire after the move is the shape update
  the moving block sends it (`Redstone/Theorems/Observer/MovedByPiston.lean`).

Left out:

* What `Level.setBlock` and the neighbour updates inside the tick do to an arbitrary level:
  they run the reactions of the blocks around, which depend on the whole level. The two tick
  lemmas therefore say which program the tick is, not which level it ends in; the levels are
  computed for concrete circuits by evaluation.
* A lemma for the whole pulse ("on from two to four game ticks after the change in front")
  over an arbitrary level, for the same reason as for the repeater
  (`Redstone/Lemmas/Repeater.lean`): between the scheduling and the tick the rest of the level
  runs.
-/

@[expose] public section

namespace Redstone.Component.Observer

/-! ### Attribute lemmas -/

/-- The own signal of an observer is 15 exactly while it is powered. -/
theorem ownSignal_eq_ite (s : Blocks.Observer) :
    ownSignal s = if s.powered = true then 15 else 0 := by
  cases h : s.powered <;> simp [ownSignal, h]

/-- The own signal of an observer is 0 or 15. -/
theorem ownSignal_mem (s : Blocks.Observer) : ownSignal s ∈ [0, 15] := by
  cases h : s.powered <;> simp [ownSignal, h]

/-- An observer gives a signal only to the block behind it (the direction `d` points from that
block back to the observer, which is the observer's `facing`): 15 while it is powered. -/
theorem signal_eq_ite (s : Blocks.Observer) (d : Direction) :
    signal s d = if s.facing = d ∧ s.powered = true then 15 else 0 := by
  by_cases h : s.facing = d <;> cases h' : s.powered <;> simp [signal, ownSignal, h, h']

/-- An observer gives no signal to a block that is not the one behind it. -/
theorem signal_of_ne_facing (s : Blocks.Observer) (d : Direction) (h : s.facing ≠ d) :
    signal s d = 0 := by
  simp [signal, h]

/-- An observer that is off gives no signal. -/
theorem signal_of_unpowered (s : Blocks.Observer) (d : Direction) (h : s.powered = false) :
    signal s d = 0 := by
  simp [signal_eq_ite, h]

/-- A powered observer gives 15 to the block behind it. -/
theorem signal_of_powered (s : Blocks.Observer) (h : s.powered = true) :
    signal s s.facing = 15 := by
  simp [signal_eq_ite, h]

/-- `getSignal` of the observer block, in any level and at any position. -/
theorem signal_observer (s : Blocks.Observer) (l : Level) (p : Pos) (d : Direction) :
    (observer s).signal l p d = if s.facing = d ∧ s.powered = true then 15 else 0 :=
  signal_eq_ite s d

/-- `getDirectSignal` of the observer block: the same as its signal. -/
theorem directSignal_observer (s : Blocks.Observer) (l : Level) (p : Pos) (d : Direction) :
    (observer s).directSignal l p d = if s.facing = d ∧ s.powered = true then 15 else 0 :=
  signal_eq_ite s d

/-- **The observer gives strong power**: its direct signal is its signal, in every direction.
A conductor behind a powered observer therefore passes the signal on to its own neighbours. -/
theorem directSignal_eq_signal (s : Blocks.Observer) (l : Level) (p : Pos) (d : Direction) :
    (observer s).directSignal l p d = (observer s).signal l p d := rfl

/-- `ownSignal` of the observer block. -/
theorem ownSignal_observer (s : Blocks.Observer) (l : Level) (p : Pos) :
    (observer s).ownSignal l p = if s.powered = true then 15 else 0 :=
  ownSignal_eq_ite s

/-- The behaviour the dispatcher uses for an observer is `observer`. -/
@[simp]
theorem behaviour_observer (s : Blocks.Observer) : behaviour (.observer s) = observer s := rfl

/-! ### Scheduling -/

/-- What `Level.scheduleTick` does for an observer with no tick waiting: one more scheduled
tick, due `delay` game ticks from now with the normal priority, and the counter that orders
the ticks goes up by one. -/
theorem scheduleTick_of_not_scheduled (p : Pos) (delay : ℕ) (env : Env) (l : Level)
    (hsched : l.hasScheduledTick p .observer = false) :
    Level.scheduleTick p .observer delay .normal env l =
      ((), { l with
        subTickCount := l.subTickCount + 1
        ticks := l.ticks ++ [⟨p, .observer, l.gameTime + delay, .normal, l.subTickCount⟩] }) := by
  have hsched' : Level.hasScheduledTick { l with subTickCount := l.subTickCount + 1 } p .observer
      = false := hsched
  simp only [Level.scheduleTick, modify, modifyGet, MonadStateOf.modifyGet, monadLift,
    MonadLift.monadLift, StateT.modifyGet, hsched', pure, Bool.false_eq_true, ite_false]

/-- **`startSignal` schedules the tick that starts the pulse.** With no tick of the observer
waiting, it adds one scheduled tick at `p`, due two game ticks from now, and changes nothing
else but the counter that orders the ticks. -/
theorem startSignal_schedules (p : Pos) (env : Env) (l : Level)
    (hsched : l.hasScheduledTick p .observer = false) :
    startSignal p env l =
      ((), { l with
        subTickCount := l.subTickCount + 1
        ticks := l.ticks ++ [⟨p, .observer, l.gameTime + 2, .normal, l.subTickCount⟩] }) := by
  simp only [startSignal, bind, ReaderT.bind, StateT.bind, get, getThe, MonadStateOf.get, liftM,
    monadLift, MonadLift.monadLift, StateT.get, pure, hsched, Bool.not_false, ↓reduceIte]
  exact scheduleTick_of_not_scheduled p 2 env l hsched

/-- **No second pulse while one is waiting.** With a tick of the observer already waiting,
`startSignal` leaves the level as it is. -/
theorem startSignal_of_scheduled (p : Pos) (env : Env) (l : Level)
    (hsched : l.hasScheduledTick p .observer = true) : startSignal p env l = ((), l) := by
  simp only [startSignal, bind, ReaderT.bind, StateT.bind, get, getThe, MonadStateOf.get, liftM,
    monadLift, MonadLift.monadLift, StateT.get, pure, ReaderT.pure, StateT.pure, hsched,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-! ### The shape update -/

/-- **A change in front of an observer that is off schedules its tick two game ticks later.**
The shape update comes from the direction `d = facing`; the observer is off and has no tick
waiting. Then the observer is returned as it is, one tick of the observer at `p` is scheduled,
due two game ticks from now, and nothing else in the level changes but the counter that orders
the ticks. -/
theorem updateShape_front_schedules (s : Blocks.Observer) (p : Pos) (d : Direction)
    (neighbourPos : Pos) (neighbour : Block) (env : Env) (l : Level) (hfront : s.facing = d)
    (hoff : s.powered = false) (hsched : l.hasScheduledTick p .observer = false) :
    (observer s).updateShape p d neighbourPos neighbour env l =
      (.observer s, { l with
        subTickCount := l.subTickCount + 1
        ticks := l.ticks ++ [⟨p, .observer, l.gameTime + 2, .normal, l.subTickCount⟩] }) := by
  simp only [observer, hfront, hoff, decide_true, Bool.not_false, Bool.and_self, ite_true, bind,
    ReaderT.bind, StateT.bind, startSignal_schedules p env l hsched]
  rfl

/-- A shape update from a side that is not the front of the observer does nothing. -/
theorem updateShape_of_ne_facing (s : Blocks.Observer) (p : Pos) (d : Direction)
    (neighbourPos : Pos) (neighbour : Block) (env : Env) (l : Level) (h : s.facing ≠ d) :
    (observer s).updateShape p d neighbourPos neighbour env l = (.observer s, l) := by
  simp only [observer, h, decide_false, Bool.false_and, Bool.false_eq_true, ite_false]
  rfl

/-- A shape update to an observer that is on does nothing: a change in front during the pulse
is not seen. -/
theorem updateShape_of_powered (s : Blocks.Observer) (p : Pos) (d : Direction)
    (neighbourPos : Pos) (neighbour : Block) (env : Env) (l : Level) (h : s.powered = true) :
    (observer s).updateShape p d neighbourPos neighbour env l = (.observer s, l) := by
  simp only [observer, h, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]
  rfl

/-- A shape update while a tick of the observer is waiting does nothing: two changes in front
within two game ticks give one pulse. -/
theorem updateShape_of_scheduled (s : Blocks.Observer) (p : Pos) (d : Direction)
    (neighbourPos : Pos) (neighbour : Block) (env : Env) (l : Level)
    (hsched : l.hasScheduledTick p .observer = true) :
    (observer s).updateShape p d neighbourPos neighbour env l = (.observer s, l) := by
  by_cases h : s.facing = d ∧ s.powered = false
  · simp only [observer, h.1, h.2, decide_true, Bool.not_false, Bool.and_self, ite_true, bind,
      ReaderT.bind, StateT.bind, startSignal_of_scheduled p env l hsched]
    rfl
  · by_cases hd : s.facing = d
    · have hp : s.powered = true := by simpa [hd] using h
      exact updateShape_of_powered s p d neighbourPos neighbour env l hp
    · exact updateShape_of_ne_facing s p d neighbourPos neighbour env l hd

/-- A shape update never changes the observer itself: the block it returns is the observer as
it was. Only the scheduled tick switches it. -/
theorem updateShape_fst (s : Blocks.Observer) (p : Pos) (d : Direction) (neighbourPos : Pos)
    (neighbour : Block) (env : Env) (l : Level) :
    ((observer s).updateShape p d neighbourPos neighbour env l).1 = .observer s := by
  cases hs : l.hasScheduledTick p .observer
  · by_cases hd : s.facing = d
    · cases hp : s.powered
      · rw [updateShape_front_schedules s p d neighbourPos neighbour env l hd hp hs]
      · rw [updateShape_of_powered s p d neighbourPos neighbour env l hp]
    · rw [updateShape_of_ne_facing s p d neighbourPos neighbour env l hd]
  · rw [updateShape_of_scheduled s p d neighbourPos neighbour env l hs]

/-! ### The tick -/

/-- **The tick of an observer that is off**: it switches on (flags 2: the neighbours get shape
updates, no neighbour updates), schedules the tick that will switch it off two game ticks
later, and tells the blocks behind. -/
theorem tick_of_unpowered (s : Blocks.Observer) (p : Pos) (h : s.powered = false) :
    tick s p = (do
      discard <| Level.setBlock p (.observer { s with powered := true }) 2
      Level.scheduleTick p .observer 2
      updateNeighborsInFront s p) := by
  simp [tick, h]

/-- **The tick of an observer that is on**: it switches off and tells the blocks behind. It
schedules nothing: the pulse is over. -/
theorem tick_of_powered (s : Blocks.Observer) (p : Pos) (h : s.powered = true) :
    tick s p = (do
      discard <| Level.setBlock p (.observer { s with powered := false }) 2
      updateNeighborsInFront s p) := by
  simp [tick, h]

/-! ### Placing and removing -/

/-- `onPlace` does nothing when the block that was there is an observer too (the observer
switching on or off is such a change). -/
theorem onPlace_of_observer (s : Blocks.Observer) (p : Pos) (oldState : Block) (env : Env)
    (l : Level) (h : oldState.is .observer = true) : onPlace s p oldState env l = ((), l) := by
  simp only [onPlace, h, Bool.not_true, Bool.false_eq_true, ite_false]
  rfl

/-- `onPlace` does nothing for an observer that is placed off, whatever was there before: so an
observer set down by a piston is not switched by being placed. -/
theorem onPlace_of_unpowered (s : Blocks.Observer) (p : Pos) (oldState : Block) (env : Env)
    (l : Level) (h : s.powered = false) : onPlace s p oldState env l = ((), l) := by
  by_cases ho : oldState.is .observer = true
  · exact onPlace_of_observer s p oldState env l ho
  · simp only [onPlace, ho, h, Bool.false_and, Bool.false_eq_true, ite_false, Bool.not_false,
      ite_true, bind, ReaderT.bind, StateT.bind, get, getThe, MonadStateOf.get, liftM,
      monadLift, MonadLift.monadLift, StateT.get]
    rfl

/-- `onPlace` does nothing while a tick of the observer is waiting at the position. -/
theorem onPlace_of_scheduled (s : Blocks.Observer) (p : Pos) (oldState : Block) (env : Env)
    (l : Level) (h : l.hasScheduledTick p .observer = true) :
    onPlace s p oldState env l = ((), l) := by
  by_cases ho : oldState.is .observer = true
  · exact onPlace_of_observer s p oldState env l ho
  · simp only [onPlace, ho, h, Bool.not_true, Bool.and_false, Bool.false_eq_true,
      Bool.not_false, bind, ReaderT.bind, StateT.bind, get, getThe, MonadStateOf.get,
      liftM, monadLift, MonadLift.monadLift, StateT.get, pure, ReaderT.pure, StateT.pure,
      ↓reduceIte]

/-- Removing an observer that is off tells nobody. -/
theorem affectNeighborsAfterRemoval_of_unpowered (s : Blocks.Observer) (p : Pos) (env : Env)
    (l : Level) (h : s.powered = false) : affectNeighborsAfterRemoval s p env l = ((), l) := by
  simp only [affectNeighborsAfterRemoval, h, Bool.false_and, Bool.false_eq_true, ite_false, bind,
    ReaderT.bind, StateT.bind, get, getThe, MonadStateOf.get, liftM, monadLift,
    MonadLift.monadLift, StateT.get]
  rfl

end Redstone.Component.Observer
