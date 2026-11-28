module

public import Redstone.Mechanics.Tick

/-!
# Observer

Java class: `ObserverBlock` (with `DirectionalBlock`).

An observer watches the block in front of it, in the direction `facing`. When a shape update
arrives from that side while the observer is off, it schedules a tick two game ticks later. That
tick switches the observer on and schedules another one two game ticks later, which switches it
off again. While it is on, the observer gives a signal of 15, as strong power, to the block
behind it only. Each switch sends neighbour updates to the block behind and to that block's
neighbours.

Everything `ObserverBlock` overrides on the server is modelled: `tick`, `updateShape`,
`ownSignal`, `getSignal`, `getDirectSignal`, `onPlace` and `affectNeighborsAfterRemoval`.
`isSignalSource` is an attribute of the generated block states. Left out: `rotate`, `mirror`
and `getStateForPlacement`, which only matter to structures and to players placing the block,
and `shouldRedstoneWireConnectTo`, which belongs to the redstone wire.
-/

@[expose] public section

namespace Redstone.Component.Observer

/-- `updateNeighborsInFront(level, pos, state)`: a neighbour update for the block behind the
observer, then for the neighbours of that block except the observer itself. -/
def updateNeighborsInFront (s : Blocks.Observer) (p : Pos) : M Unit := do
  let oppositePos := p.step s.facing.opposite
  Level.neighborChanged oppositePos .observer
  Level.updateNeighborsAtExceptFromFacing oppositePos .observer (some s.facing)

/-- `startSignal(level, ticks, pos)`: schedules the tick that starts the pulse, unless a tick
of the observer is already waiting. -/
def startSignal (p : Pos) : M Unit := do
  if !(← get).hasScheduledTick p .observer then Level.scheduleTick p .observer 2

/-- `tick`: a powered observer switches off; an unpowered one switches on and schedules the
tick that will switch it off. Both tell the blocks behind. -/
def tick (s : Blocks.Observer) (p : Pos) : M Unit := do
  if s.powered then
    discard <| Level.setBlock p (.observer { s with powered := false }) 2
  else
    discard <| Level.setBlock p (.observer { s with powered := true }) 2
    Level.scheduleTick p .observer 2
  updateNeighborsInFront s p

/-- `ownSignal`: 15 while the observer is powered. -/
def ownSignal (s : Blocks.Observer) : ℕ := if s.powered then 15 else 0

/-- `getSignal(state, level, pos, direction)`: the own signal, towards the block behind only.
`direction` points from the block that asks to the observer. -/
def signal (s : Blocks.Observer) (d : Direction) : ℕ := if s.facing = d then ownSignal s else 0

/-- `onPlace`: an observer placed powered, where another block was and with no tick waiting,
is switched off at once, without shape updates, and tells the blocks behind. -/
def onPlace (s : Blocks.Observer) (p : Pos) (oldState : Block) : M Unit := do
  if !oldState.is .observer then
    if s.powered && !(← get).hasScheduledTick p .observer then
      let newState := { s with powered := false }
      discard <| Level.setBlock p (.observer newState) 18
      updateNeighborsInFront newState p

/-- `affectNeighborsAfterRemoval`: a powered observer removed while its tick is waiting tells
the blocks behind. -/
def affectNeighborsAfterRemoval (s : Blocks.Observer) (p : Pos) : M Unit := do
  if s.powered && (← get).hasScheduledTick p .observer then
    updateNeighborsInFront { s with powered := false } p

/-- The behaviour of an observer. -/
def observer (s : Blocks.Observer) : Behaviour :=
  let self : Block := .observer s
  { Behaviour.inert self with
    signal := fun _ _ d => signal s d
    ownSignal := fun _ _ => ownSignal s
    directSignal := fun _ _ d => signal s d
    tick := tick s
    updateShape := fun p d _ _ => do
      if s.facing = d && !s.powered then startSignal p
      return self
    onPlace := fun p oldState _ => onPlace s p oldState
    affectNeighborsAfterRemoval := fun p _ => affectNeighborsAfterRemoval s p }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .observer s => observer s
  | _ => .inert self

end Redstone.Component.Observer
