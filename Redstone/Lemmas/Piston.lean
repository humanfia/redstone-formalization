module

public import Redstone.Component.Piston

/-!
# Lemmas about the piston

Generic facts about the piston base and the moving block, over an arbitrary level, as opposed
to the theorems about concrete circuits in `Redstone/Theorems/PistonBasic`.

* **The power rule, with quasi-connectivity.** `getNeighborSignal` only reads the level, and
  its answer is `neighborSignal` (`getNeighborSignal_eq`): a neighbour other than the one in
  front gives the piston a signal, or the position above the piston receives one
  (`neighborSignal_eq`). The second half is `hasNeighborSignal` of the position above: this is
  quasi-connectivity. A signal from a side is enough (`neighborSignal_of_side`, which needs
  `d ≠ pushDirection`), a signal to the position above is enough (`neighborSignal_of_above`),
  and the block in front never counts (`neighborSignal_eq_false`).
* **Which block event `checkIfExtend` queues.** Event 0 when the piston is retracted, receives
  a signal and can move what is in front (`checkIfExtend_extends`); nothing when it cannot
  (`checkIfExtend_blocked`); nothing when the piston already is as its signal says
  (`checkIfExtend_of_agrees`); event 1 when it is extended, receives no signal and the block two
  in front is not a moving block (`checkIfExtend_retracts`); event 2 or 1, by the rule of
  block dropping, when that block is a moving block (`checkIfExtend_retracts_moving`).
* **The guards of `triggerEvent`.** An extending event that finds no signal is dropped and
  leaves the level alone (`triggerEvent_extend_of_unpowered`); a retracting event that finds a
  signal only writes the extended base back (`triggerEvent_retract_of_powered`).
* **The moving block.** A tick of a moving block that is not yet there adds half a block to
  its progress and changes nothing else (`tick_of_moving`). Its progress goes 0, 1/2, 1 in the
  first two ticks (`progress_steps`); the third tick finds 1 and puts the block down.

Left out: what `moveBlocks` does to an arbitrary level (the positions that
`PistonMotion.resolve` gives belong to `Redstone/Lemmas/PistonMotion.lean`), the branches of
`triggerEvent` that move blocks, and the tick of a moving block that has arrived, which places
a block and sends updates into the rest of the level; they are proved for concrete circuits
by evaluation. Also left out: `checkIfExtend` when the block two in front is a moving block
without a block entity; `Level.getBlockEntity` then asks the environment for a new one, so
the result depends on more than the level.
-/

@[expose] public section

namespace Redstone.Component.Piston

open PistonMotion
open BlockEntities.Piston (from3DDataValue get3DDataValue)

/-! ### Attribute lemmas -/

/-- A sticky piston base has the sticky type, and only it. -/
theorem pistonType_eq_sticky (id : Blocks.PistonBase.Id) :
    pistonType id = .sticky ↔ id = .sticky_piston := by
  cases id <;> simp [pistonType]

/-- A piston base gives no signal. -/
theorem signal_base (id : Blocks.PistonBase.Id) (s : Blocks.PistonBase) (l : Level) (p : Pos)
    (d : Direction) : (base id s).signal l p d = 0 := rfl

/-- The base that fits a head is the extended base of the same kind facing the same way. -/
theorem isFittingBase_pistonBase (h : Blocks.PistonHead) (id : Blocks.PistonBase.Id)
    (b : Blocks.PistonBase) :
    isFittingBase h (.pistonBase id b) =
      (pistonType id = h.type && b.extended && b.facing = h.facing) := rfl

/-! ### The power rule -/

/-- What `getNeighborSignal` answers on the level `l`: a neighbour of the piston at `p`, other
than the one in front of it, gives it a signal; or the block at `p` gives a signal upwards; or
a neighbour of the position above, other than the piston, gives that position a signal. -/
def neighborSignal (env : Env) (l : Level) (p : Pos) (pushDirection : Direction) : Bool :=
  (Direction.values.any fun d => d ≠ pushDirection && l.signalAt env (p.step d) d > 0) ||
    l.signalAt env p .down > 0 ||
    (Direction.values.any fun d => d ≠ .down && l.signalAt env ((p.step .up).step d) d > 0)

/-- The simp set that unfolds the reader-and-state monad of reactions. -/
local macro "monad_simp" : tactic =>
  `(tactic| simp [getNeighborSignal, neighborSignal, Level.hasSignal, Level.getSignal,
      Direction.values, bind, ReaderT.bind, StateT.bind, pure, ReaderT.pure, StateT.pure, get,
      getThe, MonadStateOf.get, StateT.get, read, readThe, MonadReaderOf.read, ReaderT.read,
      liftM, monadLift, MonadLift.monadLift, *])

/-- One signal that `getNeighborSignal` asks for: it is zero, or it is positive, and then the
answer is known and `monad_simp` closes the goal. -/
local macro "qc_step " t:term:max : tactic =>
  `(tactic| (rcases Nat.eq_zero_or_pos $t with h | h; (case inr => monad_simp)))

/-- One of the sides. -/
local macro "qc_side " l:term:max env:term:max p:term:max d:term:max : tactic =>
  `(tactic| qc_step (Level.signalAt $env $l (Pos.step $p $d) $d))

/-- The signals that `getNeighborSignal` asks for after those of the sides, in its order: the
piston's own signal upwards, and the five neighbours of the position above. When all are zero
the answer is known too. -/
local macro "qc_above " l:term:max env:term:max p:term:max : tactic =>
  `(tactic| (qc_step (Level.signalAt $env $l $p .down)
             qc_side $l $env (Pos.step $p .up) .up
             qc_side $l $env (Pos.step $p .up) .north
             qc_side $l $env (Pos.step $p .up) .south
             qc_side $l $env (Pos.step $p .up) .west
             qc_side $l $env (Pos.step $p .up) .east
             monad_simp))

set_option maxHeartbeats 1600000 in
-- Six facings, and for each up to twelve signals, each decided by a run of `simp` over the
-- unfolded loops of `getNeighborSignal`.
/-- **`getNeighborSignal` only reads the level**, and answers `neighborSignal`. -/
theorem getNeighborSignal_eq (p : Pos) (pushDirection : Direction) (env : Env) (l : Level) :
    getNeighborSignal p pushDirection env l = (neighborSignal env l p pushDirection, l) := by
  cases pushDirection
  case down =>
    qc_side l env p .up; qc_side l env p .north; qc_side l env p .south; qc_side l env p .west
    qc_side l env p .east; qc_above l env p
  case up =>
    qc_side l env p .down; qc_side l env p .north; qc_side l env p .south; qc_side l env p .west
    qc_side l env p .east; qc_above l env p
  case north =>
    qc_side l env p .down; qc_side l env p .up; qc_side l env p .south; qc_side l env p .west
    qc_side l env p .east; qc_above l env p
  case south =>
    qc_side l env p .down; qc_side l env p .up; qc_side l env p .north; qc_side l env p .west
    qc_side l env p .east; qc_above l env p
  case west =>
    qc_side l env p .down; qc_side l env p .up; qc_side l env p .north; qc_side l env p .south
    qc_side l env p .east; qc_above l env p
  case east =>
    qc_side l env p .down; qc_side l env p .up; qc_side l env p .north; qc_side l env p .south
    qc_side l env p .west; qc_above l env p

/-- Stepping up and then down leads back. -/
theorem step_up_step_down (p : Pos) : (p.step .up).step .down = p := by
  cases p
  simp [Pos.step]

/-- **The power rule, with quasi-connectivity**: a piston receives a signal when a neighbour
other than the one in front of it gives it one, or when the position above it receives a
signal (`hasNeighborSignal` of that position; the piston itself counts among the neighbours
of that position, as in the game). -/
theorem neighborSignal_eq (env : Env) (l : Level) (p : Pos) (pushDirection : Direction) :
    neighborSignal env l p pushDirection =
      ((Direction.values.any fun d => d ≠ pushDirection && l.signalAt env (p.step d) d > 0) ||
        l.hasNeighborSignalAt env (p.step .up)) := by
  simp [neighborSignal, Level.hasNeighborSignalAt, Direction.values, step_up_step_down,
    Bool.or_assoc]

/-- A signal from a neighbour that is not the one in front powers the piston. -/
theorem neighborSignal_of_side (env : Env) (l : Level) (p : Pos) {pushDirection d : Direction}
    (hd : d ≠ pushDirection) (hs : 0 < l.signalAt env (p.step d) d) :
    neighborSignal env l p pushDirection = true := by
  cases d <;> cases pushDirection <;> simp_all [neighborSignal, Direction.values]

/-- **Quasi-connectivity**: a signal that reaches the position above the piston powers the
piston, whatever its facing. -/
theorem neighborSignal_of_above (env : Env) (l : Level) (p : Pos) (pushDirection : Direction)
    (h : l.hasNeighborSignalAt env (p.step .up) = true) :
    neighborSignal env l p pushDirection = true := by
  rw [neighborSignal_eq, h, Bool.or_true]

/-- **The block in front does not count.** Without a signal from the five other neighbours and
without a signal to the position above, the piston is not powered, whatever the block in front
of it gives. -/
theorem neighborSignal_eq_false (env : Env) (l : Level) (p : Pos) (pushDirection : Direction)
    (hside : ∀ d, d ≠ pushDirection → l.signalAt env (p.step d) d = 0)
    (habove : l.hasNeighborSignalAt env (p.step .up) = false) :
    neighborSignal env l p pushDirection = false := by
  rw [neighborSignal_eq, habove, Bool.or_false, List.any_eq_false]
  intro d _
  by_cases hd : d = pushDirection
  · simp [hd]
  · simp [hd, hside d hd]

/-! ### Which block event `checkIfExtend` queues -/

/-- **A piston that is as its signal says does nothing.** -/
theorem checkIfExtend_of_agrees (id : Blocks.PistonBase.Id) (s : Blocks.PistonBase) (p : Pos)
    (env : Env) (l : Level) (h : neighborSignal env l p s.facing = s.extended) :
    checkIfExtend id s p env l = ((), l) := by
  cases hext : s.extended <;>
    simp_all [checkIfExtend, getNeighborSignal_eq, bind, ReaderT.bind, StateT.bind, pure,
      ReaderT.pure, StateT.pure]

/-- **Event 0: extend.** A retracted piston that receives a signal and can move what is in
front of it queues the block event 0, with its facing as the second number, and does nothing
else. -/
theorem checkIfExtend_extends (id : Blocks.PistonBase.Id) (s : Blocks.PistonBase) (p : Pos)
    (env : Env) (l : Level) (hsig : neighborSignal env l p s.facing = true)
    (hext : s.extended = false)
    (hres : (PistonMotion.resolve l p s.facing true).1 = true)
    (hov : (PistonMotion.resolve l p s.facing true).2.overflow = false) :
    checkIfExtend id s p env l =
      Level.blockEvent p id.toBlockId 0 (get3DDataValue s.facing) env l := by
  simp [checkIfExtend, resolve, getNeighborSignal_eq, hsig, hext, hres, hov, bind, ReaderT.bind,
    StateT.bind, pure, ReaderT.pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get,
    liftM, monadLift, MonadLift.monadLift]

/-- **No event when the blocks cannot move.** A retracted piston that receives a signal but
cannot move what is in front of it (an immovable block, or more than twelve blocks) queues
nothing and leaves the level as it is. -/
theorem checkIfExtend_blocked (id : Blocks.PistonBase.Id) (s : Blocks.PistonBase) (p : Pos)
    (env : Env) (l : Level) (hsig : neighborSignal env l p s.facing = true)
    (hext : s.extended = false)
    (hres : (PistonMotion.resolve l p s.facing true).1 = false)
    (hov : (PistonMotion.resolve l p s.facing true).2.overflow = false) :
    checkIfExtend id s p env l = ((), l) := by
  simp [checkIfExtend, resolve, getNeighborSignal_eq, hsig, hext, hres, hov, bind, ReaderT.bind,
    StateT.bind, pure, ReaderT.pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get,
    liftM, monadLift, MonadLift.monadLift]

/-- **Event 1: retract.** An extended piston that receives no signal, when the block two in
front of it is not a moving block, queues the block event 1 and does nothing else. (The
hypothesis `hblock` is what lets `simp` choose the branch of the match on that block.) -/
theorem checkIfExtend_retracts (id : Blocks.PistonBase.Id) (s : Blocks.PistonBase) (p : Pos)
    (env : Env) (l : Level) (hsig : neighborSignal env l p s.facing = false)
    (hext : s.extended = true)
    (hblock : ∀ m, l.blockAt (relative p s.facing 2) ≠ .movingPiston m) :
    checkIfExtend id s p env l =
      Level.blockEvent p id.toBlockId 1 (get3DDataValue s.facing) env l := by
  simp only [checkIfExtend, getNeighborSignal_eq, hsig, hext, Level.getBlock, bind, ReaderT.bind,
    StateT.bind, pure, ReaderT.pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get,
    liftM, monadLift, MonadLift.monadLift, Bool.not_false, Bool.and_self,
    Bool.false_eq_true, ite_false, ite_true, Bool.not_true, Bool.and_true]

/-- **Event 2: drop the block.** An extended piston that receives no signal, while the block
two in front of it is a moving block of this piston's facing with its block entity `d`: the
piston queues the block event 2 if that block is being pushed out and is less than half way,
or was ticked in this game tick, or the game is in the part of the tick where scheduled ticks
and block events run; otherwise the block event 1. This is how a short pulse makes a sticky
piston leave its block behind. -/
theorem checkIfExtend_retracts_moving (id : Blocks.PistonBase.Id) (s : Blocks.PistonBase)
    (p : Pos) (env : Env) (l : Level) (m : Blocks.MovingPiston) (d : BlockEntities.Piston)
    (hsig : neighborSignal env l p s.facing = false) (hext : s.extended = true)
    (hblock : l.blockAt (relative p s.facing 2) = .movingPiston m) (hm : m.facing = s.facing)
    (hbe : l.blockEntities (relative p s.facing 2) = some (.piston d)) :
    checkIfExtend id s p env l =
      Level.blockEvent p id.toBlockId
        (if d.extending && (decide (d.progressO < 1 / 2) ||
            l.tickedBlockEntities.contains (relative p s.facing 2) || l.handlingTick)
          then 2 else 1)
        (get3DDataValue s.facing) env l := by
  simp [checkIfExtend, getNeighborSignal_eq, movingBlockEntity?, Level.getBlock,
      Level.getBlockEntity, Level.peekBlockEntity, hsig, hext, hblock, hm, hbe, bind,
      ReaderT.bind, StateT.bind, pure, ReaderT.pure, StateT.pure, get, getThe, MonadStateOf.get,
      StateT.get, liftM, monadLift, MonadLift.monadLift]
  split_ifs <;> rfl

/-! ### The guards of `triggerEvent` -/

/-- **An extending event without a signal is dropped.** If the piston receives no signal when
its block event 0 is carried out, nothing happens: the event is refused and the level is as
it was. -/
theorem triggerEvent_extend_of_unpowered (id : Blocks.PistonBase.Id) (s : Blocks.PistonBase)
    (p : Pos) (b1 : ℤ) (env : Env) (l : Level)
    (hsig : neighborSignal env l p s.facing = false) :
    triggerEvent id s p 0 b1 env l = (false, l) := by
  simp [triggerEvent, getNeighborSignal_eq, hsig, bind, ReaderT.bind, StateT.bind, pure,
    ReaderT.pure, StateT.pure]

/-- **A retracting event with a signal only writes the extended base back.** If the piston
receives a signal when its block event 1 or 2 is carried out, the piston does not retract:
the extended base is set again (with flag 2, so without neighbour updates) and the event is
refused. -/
theorem triggerEvent_retract_of_powered (id : Blocks.PistonBase.Id) (s : Blocks.PistonBase)
    (p : Pos) (b0 b1 : ℤ) (env : Env) (l : Level)
    (hsig : neighborSignal env l p s.facing = true) (hb : b0 = 1 ∨ b0 = 2) :
    triggerEvent id s p b0 b1 env l =
      (false, (Level.setBlock p (.pistonBase id { s with extended := true }) 2 512 env l).2) := by
  rcases hb with rfl | rfl <;>
    simp [triggerEvent, getNeighborSignal_eq, hsig, bind, ReaderT.bind, StateT.bind, pure,
      ReaderT.pure, StateT.pure, discard, Functor.discard] <;>
    rfl

/-! ### The moving block -/

/-- **A moving block that is not yet there moves on by half a block.** If the block entity `d`
of the moving block at `p` has progress less than 1, its tick records the old progress, adds
1/2 (never going beyond 1), and changes nothing else in the level. -/
theorem tick_of_moving (p : Pos) (env : Env) (l : Level) (d : BlockEntities.Piston)
    (hbe : l.blockEntities p = some (.piston d)) (hp : d.progress < 1) :
    tick p env l =
      ((), { l with
        blockEntities := l.blockEntities.insert p (.piston
          { d with progressO := d.progress, progress := min (d.progress + 1 / 2) 1 }) }) := by
  simp [tick, movingBlockEntity?, Level.getBlockEntity, Level.peekBlockEntity,
    Level.setBlockEntity, hbe, not_le.mpr hp, bind, ReaderT.bind, StateT.bind, pure,
    ReaderT.pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift,
    MonadLift.monadLift, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]

/-- The progress of a moving block goes from 0 to 1/2 and from 1/2 to 1: after two ticks the
block entity has progress 1, and the third tick finds it there. -/
theorem progress_steps : min ((0 : ℚ) + 1 / 2) 1 = 1 / 2 ∧ min ((1 / 2 : ℚ) + 1 / 2) 1 = 1 := by
  norm_num

end Redstone.Component.Piston
