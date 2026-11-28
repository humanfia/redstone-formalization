module

public import Redstone.Mechanics.Tick

/-!
# Redstone torch and block of redstone

Java classes: `RedstoneTorchBlock`, `RedstoneWallTorchBlock`, `PoweredBlock` (with
`BaseTorchBlock` and `WallTorchBlock` for the rules of support).

A redstone torch stands on a block or hangs on the side of one. It is lit unless that block
gives it a signal, and it follows a change two game ticks later. While lit it gives a signal of
15 to its neighbours, except to the block it is attached to, and strong power to the block
above it. A torch burns out when it is switched off for the eighth time while the first of
these eight times is at most 60 game ticks old: it stays off, and a tick is scheduled for it
160 game ticks later.

The block of redstone gives a signal of 15 to all its neighbours, and no strong power.

The burn-out list (`RECENT_TOGGLES`) is the field `Level.recentTorchToggles`. In the game it is
a static map from levels to lists, shared by floor and wall torches.

Left out: `levelEvent(1502)` on burn-out (sound and smoke), `animateTick` (particles), and
`getStateForPlacement`, `rotate` and `mirror`, which are not reached by anything modelled.
-/

@[expose] public section

namespace Redstone.Component.Torch

/-- `RECENT_TOGGLE_TIMER`: how long, in game ticks, a toggle stays on the burn-out list. -/
def recentToggleTimer : ℕ := 60

/-- `MAX_RECENT_TOGGLES`: the number of toggles on the list at which a torch burns out. -/
def maxRecentToggles : ℕ := 8

/-- `RESTART_DELAY`: the delay of the tick scheduled when a torch burns out. -/
def restartDelay : ℕ := 160

/-- `TOGGLE_DELAY`: the delay with which a torch follows its input. -/
def toggleDelay : ℕ := 2

/-- The two kinds of redstone torch, with their state. The methods of `RedstoneTorchBlock`
are written once for both; the wall torch overrides some of them. -/
inductive Kind
  /-- `RedstoneTorchBlock`: the torch standing on a block. -/
  | floor (s : Blocks.RedstoneTorch)
  /-- `RedstoneWallTorchBlock`: the torch on the side of a block. -/
  | wall (s : Blocks.RedstoneWallTorch)
  deriving DecidableEq, Repr

namespace Kind

/-- The block state. -/
def toBlock : Kind → Block
  | floor s => .redstoneTorch s
  | wall s => .redstoneWallTorch s

/-- The block (`this` in the game's code). -/
def id (k : Kind) : BlockId := k.toBlock.id

/-- `state.getValue(LIT)`. -/
def lit : Kind → Bool
  | floor s => s.lit
  | wall s => s.lit

/-- `state.setValue(LIT, lit)`. -/
def setLit (lit : Bool) : Kind → Kind
  | floor s => floor { s with lit }
  | wall s => wall { s with lit }

/-- The direction from the torch to the block it is attached to. -/
def attachment : Kind → Direction
  | floor _ => .down
  | wall s => s.facing.toDirection.opposite

end Kind

/-- `canSurvive`. For the floor torch (`BaseTorchBlock`) the block below must support the
centre of its top face (`Block.canSupportCenter`); for the wall torch
(`WallTorchBlock.canSurvive`) the face it hangs on must be sturdy. -/
def canSurvive (k : Kind) (l : Level) (p : Pos) : Bool :=
  let d := k.attachment
  let a := l.supportAttrs (p.step d)
  match k with
  | .floor _ => a.isFaceSturdyCenter d.opposite
  | .wall _ => a.isFaceSturdy d.opposite

/-- `updateShape`: the torch breaks when the block it is attached to no longer supports it. -/
def updateShape (k : Kind) (p : Pos) (d : Direction) : M Block := do
  if d = k.attachment && !canSurvive k (← get) p then return .AIR else return k.toBlock

/-- `ownSignal`. -/
def ownSignal (k : Kind) : ℕ := if k.lit then 15 else 0

/-- `getSignal`: the torch gives its signal to every neighbour but the block it is attached
to. -/
def signal (k : Kind) (d : Direction) : ℕ := if d ≠ k.attachment.opposite then ownSignal k else 0

/-- `getDirectSignal`: strong power for the block above only. -/
def directSignal (k : Kind) (d : Direction) : ℕ := if d = .down then signal k d else 0

/-- `RedstoneTorchBlock.hasNeighborSignal(level, pos, state)`: the block the torch is attached
to gives it a signal. Unlike `Level.hasNeighborSignal`, the other five neighbours do not
count. -/
def hasNeighborSignal (k : Kind) (p : Pos) : M Bool :=
  Level.hasSignal (p.step k.attachment) k.attachment

/-- `notifyNeighbors`: neighbour updates around each of the six neighbours of the torch. -/
def notifyNeighbors (k : Kind) (p : Pos) : M Unit :=
  Direction.values.forM fun d => Level.updateNeighborsAt (p.step d) k.id

/-- `isToggledTooFrequently(level, pos, add)`: with `add`, puts a toggle of the torch at `p`
on the burn-out list; then tells whether the list holds at least eight toggles of that torch. -/
def isToggledTooFrequently (p : Pos) (add : Bool) : M Bool := do
  if add then
    modify fun l => { l with recentTorchToggles := l.recentTorchToggles ++ [(p, l.gameTime)] }
  return ((← get).recentTorchToggles.filter (·.1 == p)).length ≥ maxRecentToggles

/-- The loop at the start of `tick`: drops from the front of the burn-out list the toggles
older than 60 game ticks. It stops at the first one that is recent enough. -/
def dropOldToggles : M Unit :=
  modify fun l => { l with
    recentTorchToggles := l.recentTorchToggles.dropWhile (l.gameTime - ·.2 > recentToggleTimer) }

/-- `tick`: the torch takes the state its input asks for. A torch switched off too often burns
out and schedules a tick 160 game ticks later, for whatever block is at its position by then;
a burnt-out torch does not light up. -/
def tick (k : Kind) (p : Pos) : M Unit := do
  let neighborSignal ← hasNeighborSignal k p
  dropOldToggles
  if k.lit then
    if neighborSignal then
      discard <| Level.setBlock p (k.setLit false).toBlock
      if ← isToggledTooFrequently p true then
        Level.scheduleTick p (← Level.getBlock p).id restartDelay
  else if !neighborSignal then
    if !(← isToggledTooFrequently p false) then
      discard <| Level.setBlock p (k.setLit true).toBlock

/-- `neighborChanged`: when the state does not fit the input, a tick is scheduled, unless one
is about to run in this game tick. -/
def neighborChanged (k : Kind) (p : Pos) : M Unit := do
  if k.lit == (← hasNeighborSignal k p) && !(← get).willTickThisTick p k.id then
    Level.scheduleTick p k.id toggleDelay

/-- The behaviour of a redstone torch of either kind. -/
def torch (k : Kind) : Behaviour :=
  { Behaviour.inert k.toBlock with
    signal := fun _ _ d => signal k d
    ownSignal := fun _ _ => ownSignal k
    directSignal := fun _ _ d => directSignal k d
    canSurvive := canSurvive k
    onPlace := fun p _ _ => notifyNeighbors k p
    affectNeighborsAfterRemoval := fun p moved => do
      if !moved then notifyNeighbors k p
    updateShape := fun p d _ _ => updateShape k p d
    tick := tick k
    neighborChanged := fun p _ _ => neighborChanged k p }

/-- The behaviour of the block of redstone (`PoweredBlock`): a constant signal of 15.
`getSignal` is not overridden, so it returns `ownSignal`. -/
def poweredBlock (self : Block) : Behaviour :=
  { Behaviour.inert self with
    signal := fun _ _ _ => 15
    ownSignal := fun _ _ => 15 }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .redstoneTorch s => torch (.floor s)
  | .redstoneWallTorch s => torch (.wall s)
  | .plain .redstone_block => poweredBlock self
  | _ => .inert self

end Redstone.Component.Torch
