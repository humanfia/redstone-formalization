module

public import Redstone.Mechanics.Update

/-!
# Power

How a position reads the redstone signal around it (`SignalGetter`). A block gives a signal to
each neighbour (`BehaviourOf.signal`); part of it may be *direct*, or strong
(`BehaviourOf.directSignal`). A conductor, such as stone, emits no signal of its own but passes
on the direct signal it receives from any side.

A direction argument always points from the block that asks to the block that is asked, as in
the game: `getSignal(pos.relative(d), d)` is the signal that the neighbour in direction `d`
gives to `pos`.
-/

@[expose] public section

namespace Redstone

namespace Level

/-- `getDirectSignal(pos, direction)`: the direct signal the block at `p` emits towards
`direction.opposite`. -/
def directSignalAt (env : Env) (l : Level) (p : Pos) (d : Direction) : ℕ :=
  (env.block (l.blockAt p)).directSignal l p d

/-- `getDirectSignalTo(pos)`: the strongest direct signal the block at `p` receives. The game
stops at the first neighbour that gives 15 or more. -/
def directSignalTo (env : Env) (l : Level) (p : Pos) : ℕ :=
  Direction.values.foldl
    (fun best d => if best ≥ 15 then best else max best (l.directSignalAt env (p.step d) d)) 0

/-- `getSignal(pos, direction)`: the signal the block at `p` gives towards `direction.opposite`:
its own signal and, if it is a conductor, the direct signal it receives. -/
def signalAt (env : Env) (l : Level) (p : Pos) (d : Direction) : ℕ :=
  let b := l.blockAt p
  let s := (env.block b).signal l p d
  if b.isConductor then max s (l.directSignalTo env p) else s

/-- `hasNeighborSignal(pos)`: some neighbour of `p` gives it a signal. -/
def hasNeighborSignalAt (env : Env) (l : Level) (p : Pos) : Bool :=
  Direction.values.any fun d => l.signalAt env (p.step d) d > 0

/-- `getBestNeighborSignal(pos)`: the strongest signal a neighbour gives to `p`, at most 15. -/
def bestNeighborSignalAt (env : Env) (l : Level) (p : Pos) : ℕ :=
  Direction.values.foldl
    (fun best d => if best ≥ 15 then 15 else
      let s := l.signalAt env (p.step d) d
      if s ≥ 15 then 15 else max best s) 0

/-- `getBestOwnOrNeighbourSignal(pos)`: the stronger of the best signal a neighbour gives to `p`
and the own signal of the block at `p`, if it is a signal source. -/
def bestOwnOrNeighbourSignalAt (env : Env) (l : Level) (p : Pos) : ℕ :=
  let b := l.blockAt p
  max (l.bestNeighborSignalAt env p)
    (if b.attrs.signalSource then (env.block b).ownSignal l p else 0)

/-- `getDirectSignal(pos, direction)`. -/
def getDirectSignal (p : Pos) (d : Direction) : M ℕ := return (← get).directSignalAt (← read) p d

/-- `getDirectSignalTo(pos)`. -/
def getDirectSignalTo (p : Pos) : M ℕ := return (← get).directSignalTo (← read) p

/-- `getSignal(pos, direction)`. -/
def getSignal (p : Pos) (d : Direction) : M ℕ := return (← get).signalAt (← read) p d

/-- `hasSignal(pos, direction)`. -/
def hasSignal (p : Pos) (d : Direction) : M Bool := return (← getSignal p d) > 0

/-- `hasNeighborSignal(pos)`. -/
def hasNeighborSignal (p : Pos) : M Bool := return (← get).hasNeighborSignalAt (← read) p

/-- `getBestNeighborSignal(pos)`. -/
def getBestNeighborSignal (p : Pos) : M ℕ := return (← get).bestNeighborSignalAt (← read) p

/-- `getBestOwnOrNeighbourSignal(pos)`. -/
def getBestOwnOrNeighbourSignal (p : Pos) : M ℕ :=
  return (← get).bestOwnOrNeighbourSignalAt (← read) p

end Level

end Redstone
