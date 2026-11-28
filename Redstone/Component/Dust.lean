module

public import Redstone.Mechanics.Tick

/-!
# Redstone dust

Java classes: `RedstoneWireBlock`, `RedstoneWireEvaluator`, `DefaultRedstoneWireEvaluator`.

Redstone dust lies on top of a block. Each of its four sides is connected to nothing, to the
side, or up the neighbouring block, and it carries a power from 0 to 15. Its power is the
larger of the strongest signal it receives from blocks other than dust and one less than the
strongest power of the dust around it (next to it, or one level up or down where no conductor
is in the way). It gives its power to the block below it and to the blocks its sides point to.

Only the default evaluator is formalized; the experimental one (`ExperimentalRedstoneWireEvaluator`)
is behind a feature flag that is off.

The kernel evaluates a change of one dust in about 0.2 s (it was 0.45 s): the game sends 42
neighbour updates for it, about ten of them reach dust, and each of those computes the power
again from some twenty blocks. What was measured, what was changed for it here and in the
definitions this file uses, and what is left, is in `docs/proof-feasibility.md` ("Redstone
dust: where the kernel time went"). Nothing more is to be gained in this file: computing the
maxima strictly, sorting the hash set by insertion and testing for a hopper by constructor
each change the 13 s of the 15-dust line by less than 0.3 s.

Not formalized: `getStateForPlacement` is defined (`stateForPlacement`) but nothing uses it,
since placing items is not part of the model; the shapes, particles, `rotate` and `mirror`.
-/

@[expose] public section

namespace Redstone.Component.Dust

open Blocks (RedstoneWire)

/-- `RedstoneSide.isConnected`. -/
def isConnected (s : RedstoneSide) : Bool := s != .none

/-- The value of the property `PROPERTY_BY_DIRECTION.get(d)`. Only horizontal directions have
one; the others give `none`. -/
def side (s : RedstoneWire) : Direction → RedstoneSide
  | .north => s.north
  | .east => s.east
  | .south => s.south
  | .west => s.west
  | _ => .none

/-- `state.setValue(PROPERTY_BY_DIRECTION.get(d), v)`. -/
def setSide (s : RedstoneWire) (d : Direction) (v : RedstoneSide) : RedstoneWire :=
  match d with
  | .north => { s with north := v }
  | .east => { s with east := v }
  | .south => { s with south := v }
  | .west => { s with west := v }
  | _ => s

/-- `defaultBlockState().setValue(POWER, power)`: the dot. -/
def dotState (power : Fin 16) : RedstoneWire := ⟨.none, .none, power, .none, .none⟩

/-- `crossState.setValue(POWER, power)`. -/
def crossState (power : Fin 16) : RedstoneWire := ⟨.side, .side, power, .side, .side⟩

/-- `isCross(state)`: all four sides are connected. -/
def isCross (s : RedstoneWire) : Bool :=
  isConnected s.north && isConnected s.south && isConnected s.east && isConnected s.west

/-- `isDot(state)`: no side is connected. -/
def isDot (s : RedstoneWire) : Bool :=
  !isConnected s.north && !isConnected s.south && !isConnected s.east && !isConnected s.west

/-- `state.is(Blocks.REDSTONE_WIRE)`: the block is redstone dust. This is
`b.is .redstone_wire` (`isWire_eq_is`), read off the constructor of the block state: comparing
block ids is the most expensive thing the kernel does in a neighbour update of dust (three
passes over the whole block inventory, 0.7 ms), and dust asks this of every block around it. -/
def isWire : Block → Bool
  | .redstoneWire _ => true
  | _ => false

theorem isWire_eq_is (b : Block) : isWire b = b.is .redstone_wire := by
  cases b <;> first | rfl | (rename_i i; cases i <;> rfl) | (rename_i i _; cases i <;> rfl)

/-- The block is a trapdoor (`getBlock() instanceof TrapDoorBlock`). -/
def isTrapDoor : Block → Bool
  | .trapDoor _ _ => true
  | .weatheringCopperTrapDoor _ _ => true
  | _ => false

/-- `canSurviveOn(level, pos, state)`: dust can lie on the block `b`. -/
def canSurviveOn (b : Block) : Bool := b.attrs.isFaceSturdy .up || b.is .hopper

/-- `canSurvive`: dust can lie on the block below `p`. -/
def canSurvive (l : Level) (p : Pos) : Bool := canSurviveOn (l.blockAt (p.step .down))

/-- `BlockState.shouldRedstoneWireConnectTo(level, pos, direction)`: dust connects to the block
`b` lying in direction `direction` from it; `none` stands for Java's `null`, used for a block
one level up or down. It is overridden by `RedstoneWireBlock`, `RepeaterBlock` and
`ObserverBlock`; other blocks connect when they are signal sources. -/
def shouldConnectTo (b : Block) (direction : Option Direction) : Bool :=
  match b with
  | .redstoneWire _ => true
  | .repeater s =>
    direction = some s.facing.toDirection || direction = some s.facing.toDirection.opposite
  | .observer s => direction = some s.facing
  | _ => b.attrs.signalSource && direction.isSome

/-- `getConnectingSide(level, pos, direction, canConnectUp)`: how the dust at `p` connects
towards `d`. -/
def connectingSide (l : Level) (p : Pos) (d : Direction) (canConnectUp : Bool) : RedstoneSide :=
  let relPos := p.step d
  let rel := l.blockAt relPos
  if canConnectUp && (isTrapDoor rel || canSurviveOn rel) &&
      shouldConnectTo (l.blockAt (relPos.step .up)) none then
    if rel.attrs.isFaceSturdy d.opposite then .up else .side
  else if !shouldConnectTo rel (some d) &&
      (rel.isConductor || !shouldConnectTo (l.blockAt (relPos.step .down)) none) then .none
  else .side

/-- The block above `p` is not a conductor, so the dust at `p` can connect upwards. -/
def canConnectUp (l : Level) (p : Pos) : Bool := !(l.blockAt (p.step .up)).isConductor

/-- `getMissingConnections(level, state, pos)`: computes the sides of `s` that are not
connected. -/
def missingConnections (l : Level) (s : RedstoneWire) (p : Pos) : RedstoneWire :=
  let up := canConnectUp l p
  Direction.horizontals.foldl
    (fun s d => if !isConnected (side s d) then setSide s d (connectingSide l p d up) else s) s

/-- `getConnectionState(level, state, pos)`: the shape of the dust at `p`. Only the power of
`s` and whether it is a dot matter. A dot that connects to nothing stays a dot; otherwise a
line with one end is extended to the other side, and dust with no connection becomes a cross. -/
def connectionState (l : Level) (s : RedstoneWire) (p : Pos) : RedstoneWire :=
  let wasDot := isDot s
  let s := missingConnections l (dotState s.power) p
  if wasDot && isDot s then s
  else
    let north := isConnected s.north
    let south := isConnected s.south
    let east := isConnected s.east
    let west := isConnected s.west
    let northSouthEmpty := !north && !south
    let eastWestEmpty := !east && !west
    let s := if !west && northSouthEmpty then { s with west := .side } else s
    let s := if !east && northSouthEmpty then { s with east := .side } else s
    let s := if !north && eastWestEmpty then { s with north := .side } else s
    let s := if !south && eastWestEmpty then { s with south := .side } else s
    s

/-- `getStateForPlacement`: the state of dust placed at `p` by a player. Nothing in the model
places items, so this is not used and not tested. -/
def stateForPlacement (l : Level) (p : Pos) : RedstoneWire := connectionState l (crossState 0) p

/-- `updateShape`: the reaction of the dust `s` at `p` to a shape update from direction `d`. -/
def updateShape (s : RedstoneWire) (l : Level) (p : Pos) (d : Direction) (neighbor : Block) :
    Block :=
  match d with
  | .down => if !canSurviveOn neighbor then .AIR else .redstoneWire s
  | .up => .redstoneWire (connectionState l s p)
  | _ =>
    let c := connectingSide l p d (canConnectUp l p)
    if isConnected c == isConnected (side s d) && !isCross s then .redstoneWire (setSide s d c)
    else .redstoneWire (connectionState l (setSide (crossState s.power) d c) p)

/-- `updateIndirectNeighbourShapes`: shape updates for the dust one level down or up from each
connected side, unless there is dust right next to that side. -/
def updateIndirectNeighbourShapes (s : RedstoneWire) (p : Pos) (flags limit : ℕ) : M Unit :=
  Direction.horizontals.forM fun d => do
    if isConnected (side s d) && !isWire (← Level.getBlock (p.step d)) then
      for q in [(p.step d).step .down, (p.step d).step .up] do
        if isWire (← Level.getBlock q) then
          let neighborPos := q.step d.opposite
          Level.Core.neighborShapeChanged Level.runUpdates d.opposite q neighborPos
            (← Level.getBlock neighborPos) flags limit

/-- The environment as it is while `RedstoneWireBlock.shouldSignal` is false: `getSignal` and
`getDirectSignal` of dust return 0. (`isSignalSource` is false as well in the game; it is not
part of the environment, and `getBestNeighborSignal` does not read it.) -/
def muted (env : Env) : Env :=
  { env with
    block := fun b =>
      match b with
      | .redstoneWire _ =>
        { env.block b with signal := fun _ _ _ => 0, directSignal := fun _ _ _ => 0 }
      | _ => env.block b }

/-- `RedstoneWireBlock.getBlockSignal(level, pos)`: the strongest signal `p` receives from its
neighbours when dust gives none. -/
def blockSignal (env : Env) (l : Level) (p : Pos) : ℕ := l.bestNeighborSignalAt (muted env) p

/-- `getWireSignal(pos, state)`: the power of `b` if it is dust. -/
def wireSignal : Block → ℕ
  | .redstoneWire s => s.power
  | _ => 0

/-- `getIncomingWireSignal(level, pos)`: one less than the strongest power of the dust next to
`p`, on top of a neighbouring conductor (unless a conductor covers `p`), or below a neighbour
that is not a conductor. -/
def incomingWireSignal (l : Level) (p : Pos) : ℕ :=
  let best := Direction.horizontals.foldl
    (fun best d =>
      let neighborPos := p.step d
      let neighbor := l.blockAt neighborPos
      let best := max best (wireSignal neighbor)
      if neighbor.isConductor && !(l.blockAt (p.step .up)).isConductor then
        max best (wireSignal (l.blockAt (neighborPos.step .up)))
      else if !neighbor.isConductor then
        max best (wireSignal (l.blockAt (neighborPos.step .down)))
      else best) 0
  best - 1

/-- `calculateTargetStrength(level, pos)`: the power dust at `p` should have. -/
def targetStrength (env : Env) (l : Level) (p : Pos) : ℕ :=
  let signal := blockSignal env l p
  if signal = 15 then signal else max signal (incomingWireSignal l p)

/-- `BlockPos.hashCode` spread as `HashMap.hash` does, reduced to an index of a table with 16
buckets. -/
def hashBucket (p : Pos) : ℕ :=
  let h := (((p.y + p.z * 31) * 31 + p.x) % 4294967296).toNat
  (h ^^^ (h >>> 16)) % 16

/-- The order in which a `HashSet<BlockPos>` iterates over positions added in the order `ps`:
by bucket, then by order of insertion. This holds as long as the set has at most 12 elements
(the table then has 16 buckets) and fewer than 8 in each bucket. -/
def hashSetOrder (ps : List Pos) : List Pos :=
  (List.range 16).flatMap fun b => ps.filter (hashBucket · == b)

/-- `DefaultRedstoneWireEvaluator.updatePowerStrength(level, pos, state, ...)`: gives the dust
at `p` the power it should have and, if it changed, sends neighbour updates around `p` and
around its six neighbours, in the order of a hash set. -/
def updatePowerStrength (p : Pos) (s : RedstoneWire) : M Unit := do
  let target := targetStrength (← read) (← get) p
  if s.power.val ≠ target then
    if (← Level.getBlock p) = .redstoneWire s then
      discard <| Level.setBlock p (.redstoneWire { s with power := Fin.ofNat 16 target }) 2
    (hashSetOrder (p :: Direction.values.map p.step)).forM fun q =>
      Level.updateNeighborsAt q .redstone_wire

/-- `checkCornerChangeAt(level, pos)`: if there is dust at `p`, neighbour updates around it and
around its six neighbours. -/
def checkCornerChangeAt (p : Pos) : M Unit := do
  if isWire (← Level.getBlock p) then
    Level.updateNeighborsAt p .redstone_wire
    Direction.values.forM fun d => Level.updateNeighborsAt (p.step d) .redstone_wire

/-- `updateNeighborsOfNeighboringWires(level, pos)`: `checkCornerChangeAt` for the four
horizontal neighbours, then for the position on top of each neighbour that is a conductor, or
below each one that is not. -/
def updateNeighborsOfNeighboringWires (p : Pos) : M Unit := do
  Direction.horizontals.forM fun d => checkCornerChangeAt (p.step d)
  Direction.horizontals.forM fun d => do
    let target := p.step d
    if (← Level.getBlock target).isConductor then checkCornerChangeAt (target.step .up)
    else checkCornerChangeAt (target.step .down)

/-- `onPlace`: when dust replaces another block, its power is updated, then come neighbour
updates around the positions above and below it (`Direction.Plane.VERTICAL` is up, down), then
`updateNeighborsOfNeighboringWires`. -/
def onPlace (s : RedstoneWire) (p : Pos) (old : Block) : M Unit := do
  if !isWire old then
    updatePowerStrength p s
    [Direction.up, Direction.down].forM fun d =>
      Level.updateNeighborsAt (p.step d) .redstone_wire
    updateNeighborsOfNeighboringWires p

/-- `affectNeighborsAfterRemoval`: unless a piston moved the dust, neighbour updates around its
six neighbours, then `updatePowerStrength` for the removed state (which only sends updates,
since the dust is gone), then `updateNeighborsOfNeighboringWires`. -/
def affectNeighborsAfterRemoval (s : RedstoneWire) (p : Pos) (movedByPiston : Bool) : M Unit := do
  if !movedByPiston then
    Direction.values.forM fun d => Level.updateNeighborsAt (p.step d) .redstone_wire
    updatePowerStrength p s
    updateNeighborsOfNeighboringWires p

/-- `neighborChanged`: dust that lost its support drops (`dropResources`) and is removed;
otherwise its power is updated. -/
def neighborChanged (s : RedstoneWire) (p : Pos) : M Unit := do
  if canSurvive (← get) p then updatePowerStrength p s
  else
    Level.dropResources (.redstoneWire s) p
    discard <| Level.removeBlock p false

/-- `getSignal`: dust gives its power to the block below it and to the neighbours its sides are
connected to, and nothing to the block above it. `d` points from the neighbour that asks to the
dust, so the block below asks with `up`. The connections are computed again from the level, not
read from the state. -/
def signal (s : RedstoneWire) (l : Level) (p : Pos) (d : Direction) : ℕ :=
  if d = .down then 0
  else if s.power.val = 0 then 0
  else if d ≠ .up && !isConnected (side (connectionState l s p) d.opposite) then 0
  else s.power

/-- `updatesOnShapeChange(level, pos, oldState, newState)`: after a click changed the shape,
neighbour updates around each neighbouring conductor whose connection changed. -/
def updatesOnShapeChange (p : Pos) (old new : RedstoneWire) : M Unit :=
  Direction.horizontals.forM fun d => do
    let relPos := p.step d
    if isConnected (side old d) != isConnected (side new d) &&
        (← Level.getBlock relPos).isConductor then
      Level.updateNeighborsAtExceptFromFacing relPos .redstone_wire (some d.opposite)

/-- `useWithoutItem`: a click turns a cross into a dot and a dot into a cross, when the
surroundings allow it. The player may build. -/
def useWithoutItem (s : RedstoneWire) (p : Pos) : M Bool := do
  if isCross s || isDot s then
    let new := if isCross s then dotState s.power else crossState s.power
    let new := connectionState (← get) new p
    if new ≠ s then
      discard <| Level.setBlock p (.redstoneWire new) 3
      updatesOnShapeChange p s new
      return true
  return false

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .redstoneWire s =>
    { Behaviour.inert self with
      signal := signal s
      ownSignal := fun _ _ => s.power
      directSignal := signal s
      canSurvive := canSurvive
      updateShape := fun p d _ neighbor => return updateShape s (← get) p d neighbor
      updateIndirectNeighbourShapes := updateIndirectNeighbourShapes s
      onPlace := fun p old _ => onPlace s p old
      affectNeighborsAfterRemoval := affectNeighborsAfterRemoval s
      neighborChanged := fun p _ _ => neighborChanged s p
      useWithoutItem := fun p _ => useWithoutItem s p }
  | _ => .inert self

end Redstone.Component.Dust
