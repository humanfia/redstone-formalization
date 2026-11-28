module

public import Redstone.Lemmas.Repeater

/-!
# Lemmas about the lock of a repeater

A powered repeater or comparator that points at the side of a repeater locks it. These are
the generic facts about the lock, over an arbitrary level; the latches and flip-flops built
on it are in `Redstone/Theorems/Memory` (`RepeaterLatch`, `DFlipFlop`, `TorchRepeaterTFF`).

* **When a repeater is locked.** `Repeater.isLocked` only reads the level, and its answer is a
  function of the two blocks at the sides of the repeater: `sideSignal env l q dir` is the
  direct signal that the block at `q` gives in the direction `dir.opposite` if it is a
  diode, and zero for every other block (`getControlInputSignal_diodes`,
  `getAlternateSignal_diodes`). The repeater is locked exactly when one of the two side
  signals is positive (`isLocked_eq`, `isLocked_true_iff`); in particular a repeater with no
  diode at either side is not locked (`isLocked_of_no_side_diode`), whatever else is there:
  a lever, a torch or powered dust at the side does not lock.
* **A locked diode ignores its input.** While `isLocked` answers `true`, the scheduled tick
  and the check after a neighbour update leave the level exactly as it is
  (`Diode.tick_of_locked`, `Diode.checkTickOnNeighbor_of_locked`), so neither the block nor
  the scheduled ticks change, whatever the input does. For the repeater, with the lock stated
  through the side signals: `Repeater.tick_of_locked`,
  `Repeater.checkTickOnNeighbor_of_locked`. A locked repeater on a block that carries it also
  ignores every neighbour update (`Diode.neighborChanged_of_locked`).
* **The property `locked`.** `Repeater.updateShape` recomputes the property only for a change
  at a position off the axis of the repeater, and then sets it to the answer of `isLocked`
  (`updateShape_offAxis`); a change in front or behind leaves the state as it is
  (`updateShape_onAxis`). The property never matters to the behaviour: the output of a
  repeater is that of its `powered` property (`signal_repeater` in
  `Redstone/Lemmas/Repeater.lean`), locked or not.

Left out: that a locked repeater keeps its `powered` property over a whole run in an
arbitrary level. Between two reactions of the repeater the rest of the level runs, and what
else may set the block is not bounded by a local hypothesis; for concrete circuits the hold
is proved by evaluation and quiescence.
-/

@[expose] public section

namespace Redstone.Component

namespace Diode

/-- The signal that the block at `q` gives to the side of a repeater, when only diodes count:
the direct signal of a repeater or comparator at `q` in the direction `dir.opposite` (`dir`
points from the repeater to `q`), and zero for every other block. -/
def sideSignal (env : Env) (l : Level) (q : Pos) (dir : Direction) : ℕ :=
  if isDiode (l.blockAt q) then l.directSignalAt env q dir else 0

/-- `getControlInputSignal` with `onlyDiodes` reads the level and answers `sideSignal`. -/
theorem getControlInputSignal_diodes (q : Pos) (dir : Direction) (env : Env) (l : Level) :
    getControlInputSignal q dir true env l = (sideSignal env l q dir, l) := by
  unfold getControlInputSignal Level.getBlock Level.getDirectSignal sideSignal
  by_cases h : isDiode (l.blockAt q) = true <;>
    simp [h, bind, ReaderT.bind, StateT.bind, get, getThe, MonadStateOf.get, liftM, monadLift,
      MonadLift.monadLift, StateT.get, read, readThe, MonadReaderOf.read, ReaderT.read, pure,
      ReaderT.pure, StateT.pure]

/-- `getAlternateSignal` with `sideInputDiodesOnly` reads the level and answers the stronger
of the two side signals. -/
theorem getAlternateSignal_diodes (facing : Direction) (p : Pos) (env : Env) (l : Level) :
    getAlternateSignal facing p true env l =
      (max (sideSignal env l (p.step (clockWise facing)) (clockWise facing))
        (sideSignal env l (p.step (counterClockWise facing)) (counterClockWise facing)), l) := by
  simp [getAlternateSignal, getControlInputSignal_diodes, bind, ReaderT.bind, StateT.bind, pure,
    ReaderT.pure, StateT.pure]

/-- A block that is not a diode gives no side signal. -/
theorem sideSignal_of_not_diode (env : Env) (l : Level) (q : Pos) (dir : Direction)
    (h : isDiode (l.blockAt q) = false) : sideSignal env l q dir = 0 := by
  simp [sideSignal, h]

variable (d : Diode)

/-- **A locked diode does not tick.** While the diode is locked, its scheduled tick leaves the
level as it is: the block keeps its `powered` property whatever its input is. -/
theorem tick_of_locked (p : Pos) (env : Env) (l : Level) (hlock : d.isLocked p env l = (true, l)) :
    d.tick p env l = ((), l) := by
  simp [tick, bind, ReaderT.bind, StateT.bind, hlock, pure, ReaderT.pure, StateT.pure]

/-- **A locked diode does not look at its input.** While the diode is locked, the check after
a neighbour update leaves the level as it is: no tick is scheduled, whatever the input is. -/
theorem checkTickOnNeighbor_of_locked (p : Pos) (env : Env) (l : Level)
    (hlock : d.isLocked p env l = (true, l)) : d.checkTickOnNeighbor p env l = ((), l) := by
  simp [checkTickOnNeighbor, bind, ReaderT.bind, StateT.bind, hlock, pure, ReaderT.pure,
    StateT.pure]

/-- **A locked diode ignores neighbour updates.** A diode that is in the level at `p`, on a
block that carries it, and locked, reacts to a neighbour update by doing nothing. -/
theorem neighborChanged_of_locked (p : Pos) (env : Env) (l : Level)
    (hself : (l.blockAt p).is d.id = true) (hsurvive : canSurvive l p = true)
    (hlock : d.isLocked p env l = (true, l)) : d.neighborChanged p env l = ((), l) := by
  have h := checkTickOnNeighbor_of_locked d p env l hlock
  simp [neighborChanged, Level.getBlock, bind, ReaderT.bind, StateT.bind, get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, pure, ReaderT.pure,
    StateT.pure, hself, hsurvive, h]

end Diode

namespace Repeater

open Diode

/-- The stronger of the two signals that diodes at the sides of the repeater `s` at `p` give
it. -/
def lockSignal (s : Blocks.Repeater) (env : Env) (l : Level) (p : Pos) : ℕ :=
  max (sideSignal env l (p.step (clockWise s.facing.toDirection)) (clockWise s.facing.toDirection))
    (sideSignal env l (p.step (counterClockWise s.facing.toDirection))
      (counterClockWise s.facing.toDirection))

/-- **When a repeater is locked.** `isLocked` reads the level and answers whether a diode at
one of the two sides gives the repeater a direct signal. -/
theorem isLocked_eq (s : Blocks.Repeater) (p : Pos) (env : Env) (l : Level) :
    isLocked s p env l = (decide (lockSignal s env l p > 0), l) := by
  simp [isLocked, lockSignal, getAlternateSignal_diodes, bind, ReaderT.bind, StateT.bind, pure,
    ReaderT.pure, StateT.pure]

/-- `isLocked` does not change the level. -/
theorem isLocked_level (s : Blocks.Repeater) (p : Pos) (env : Env) (l : Level) :
    (isLocked s p env l).2 = l := by
  rw [isLocked_eq]

/-- A repeater is locked exactly when the diode at one of its two sides gives it a signal. -/
theorem isLocked_true_iff (s : Blocks.Repeater) (p : Pos) (env : Env) (l : Level) :
    (isLocked s p env l).1 = true ↔
      0 < sideSignal env l (p.step (clockWise s.facing.toDirection))
          (clockWise s.facing.toDirection) ∨
        0 < sideSignal env l (p.step (counterClockWise s.facing.toDirection))
          (counterClockWise s.facing.toDirection) := by
  rw [isLocked_eq]
  simp only [lockSignal, decide_eq_true_eq, gt_iff_lt]
  omega

/-- **Only diodes lock.** A repeater with no repeater or comparator at either side is not
locked, whatever the blocks at its sides are and whatever signal they give. -/
theorem isLocked_of_no_side_diode (s : Blocks.Repeater) (p : Pos) (env : Env) (l : Level)
    (h₁ : isDiode (l.blockAt (p.step (clockWise s.facing.toDirection))) = false)
    (h₂ : isDiode (l.blockAt (p.step (counterClockWise s.facing.toDirection))) = false) :
    isLocked s p env l = (false, l) := by
  rw [isLocked_eq, lockSignal, sideSignal_of_not_diode _ _ _ _ h₁,
    sideSignal_of_not_diode _ _ _ _ h₂]
  rfl

/-- **A locked repeater does not tick.** While a diode at its side gives the repeater a
signal, its scheduled tick leaves the level as it is: a tick that was scheduled before the
lock came on is lost, and the repeater keeps its state. -/
theorem tick_of_locked (s : Blocks.Repeater) (p : Pos) (env : Env) (l : Level)
    (h : 0 < lockSignal s env l p) : (diode s).tick p env l = ((), l) :=
  Diode.tick_of_locked (diode s) p env l (by
    change isLocked s p env l = _
    rw [isLocked_eq]
    simp [h])

/-- **A locked repeater ignores input changes.** While a diode at its side gives the repeater
a signal, a neighbour update schedules no tick and changes nothing, whatever the input of the
repeater has become. -/
theorem checkTickOnNeighbor_of_locked (s : Blocks.Repeater) (p : Pos) (env : Env) (l : Level)
    (h : 0 < lockSignal s env l p) : (diode s).checkTickOnNeighbor p env l = ((), l) :=
  Diode.checkTickOnNeighbor_of_locked (diode s) p env l (by
    change isLocked s p env l = _
    rw [isLocked_eq]
    simp [h])

/-- A change at a position on the axis of the repeater (its input or its output) leaves the
block state as it is, and so does not touch the property `locked`. -/
theorem updateShape_onAxis (s : Blocks.Repeater) (p : Pos) (dir : Direction) (neighbour : Block)
    (env : Env) (l : Level) (h : dir.axis = s.facing.toDirection.axis) :
    updateShape s p dir neighbour env l = (.repeater s, l) := by
  have hdown : dir ≠ .down := by
    rintro rfl
    generalize s.facing = f at h
    cases f <;> exact absurd h (by decide)
  simp [updateShape, h, hdown, pure, ReaderT.pure, StateT.pure]

/-- **The property `locked` follows the sides.** A change at a position off the axis of the
repeater (a side, or above) sets `locked` to whether a diode at a side gives the repeater a
signal now; nothing else of the state changes, and the level is only read. -/
theorem updateShape_offAxis (s : Blocks.Repeater) (p : Pos) (dir : Direction) (neighbour : Block)
    (env : Env) (l : Level) (hdown : dir ≠ .down) (h : dir.axis ≠ s.facing.toDirection.axis) :
    updateShape s p dir neighbour env l =
      (.repeater { s with locked := decide (lockSignal s env l p > 0) }, l) := by
  simp [updateShape, h, hdown, isLocked_eq, bind, ReaderT.bind, StateT.bind, pure, ReaderT.pure,
    StateT.pure]

/-- The repeater's own reactions do not read the property `locked`: two states that differ
only in it are the same diode up to the block they are (`self`) and the block they become
(`setPowered`), so they have the same delay, the same input and the same lock. -/
theorem diode_locked_irrelevant (s : Blocks.Repeater) (v : Bool) :
    (diode { s with locked := v }).delay = (diode s).delay ∧
      (diode { s with locked := v }).facing = (diode s).facing ∧
      (diode { s with locked := v }).powered = (diode s).powered ∧
      (diode { s with locked := v }).isLocked = (diode s).isLocked ∧
      (diode { s with locked := v }).shouldTurnOn = (diode s).shouldTurnOn :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Repeater

end Redstone.Component
