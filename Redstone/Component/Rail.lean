module

public import Redstone.Mechanics.Tick

/-!
# Rails

Java classes: `BaseRailBlock`, `RailBlock`, `PoweredRailBlock` (powered rail and activator rail),
`DetectorRailBlock`, `RailState`.

A rail lies on a block whose top face is rigid. Its shape says which two of its neighbours it
connects: when a rail is placed it picks a shape from the rails around it (`RailState.place`)
and the rails it then points at turn towards it (`RailState.connectTo`). A plain rail with three
potential connections switches when a signal source next to it changes.

A powered rail or an activator rail is on when it receives a signal itself or is connected,
through at most eight rails of the same block that are on, to one that does
(`findPoweredRailSignal`).

A detector rail looks for a minecart when it is placed and when an entity touches it
(`entityInside`, which the entity units call through `Redstone.Entity.Touch`); it then stays on
and looks again every 20 game ticks until it finds none.

## What is left out

* A boat on a detector rail (pending scenario `detector-not-a-cart-boat`): a boat is never at
  rest, its tick clears `onGround` at once, and boats are not modelled
  (`Redstone.Entity.Still`).
* The fluid tick a waterlogged rail schedules on every shape update (`updateShape`): the rail
  does not schedule it yet (`Level.scheduleFluidTick`), and fluids do not flow.
* `getAnalogOutputSignal` of a detector rail with a command block minecart or a minecart with a
  container on it: the model does not keep the contents of minecarts and returns zero, which is
  right for a plain minecart and for an empty container.
* `getStateForPlacement`, `rotate` and `mirror`, which no update calls.
-/

@[expose] public section

namespace Redstone.Component.Rail

/-- The shapes a straight rail can have (the property `RAIL_SHAPE_STRAIGHT`). -/
abbrev StraightShape :=
  RailShapeNorthSouthEastWestAscendingEastAscendingWestAscendingNorthAscendingSouth

/-- A shape of a straight rail as a value of `RailShape`. -/
def ofStraight : StraightShape → RailShape
  | .north_south => .north_south
  | .east_west => .east_west
  | .ascending_east => .ascending_east
  | .ascending_west => .ascending_west
  | .ascending_north => .ascending_north
  | .ascending_south => .ascending_south

/-- The shape as a shape of a straight rail, if it is not a curve. -/
def toStraight? : RailShape → Option StraightShape
  | .north_south => some .north_south
  | .east_west => some .east_west
  | .ascending_east => some .ascending_east
  | .ascending_west => some .ascending_west
  | .ascending_north => some .ascending_north
  | .ascending_south => some .ascending_south
  | _ => none

/-- `RailShape.isSlope`. -/
def isSlope : RailShape → Bool
  | .ascending_east | .ascending_west | .ascending_north | .ascending_south => true
  | _ => false

/-- `state.getValue(getShapeProperty())`: the shape of a rail. A block that is not a rail has
none; the value given for it is never used. -/
def shapeOf : Block → RailShape
  | .rail s => s.shape
  | .poweredRail _ s => ofStraight s.shape
  | .detectorRail s => ofStraight s.shape
  | _ => .north_south

/-- `state.setValue(getShapeProperty(), shape)`. A straight rail is never given a curve. -/
def setShape (b : Block) (shape : RailShape) : Block :=
  match b with
  | .rail s => .rail { s with shape := shape }
  | .poweredRail i s => (toStraight? shape).elim b fun sh => .poweredRail i { s with shape := sh }
  | .detectorRail s => (toStraight? shape).elim b fun sh => .detectorRail { s with shape := sh }
  | _ => b

/-- `BaseRailBlock.isStraight`: every rail but the plain one. -/
def isStraight (b : Block) : Bool := !b.is .rail

/-- `Block.canSupportRigidBlock(level, pos)`: the top face of the block at `p` is rigid. -/
def canSupportRigidBlock (l : Level) (p : Pos) : Bool :=
  (l.supportAttrs p).isFaceSturdyRigid .up

/-- `BaseRailBlock.isRail(level, pos)`. -/
def isRailAt (l : Level) (p : Pos) : Bool := (l.blockAt p).isRail

/-! ### `RailState` -/

/-- `RailState`: a rail at a position, with the positions it connects to. -/
structure RailState where
  pos : Pos
  state : Block
  connections : List Pos

namespace RailState

/-- `updateConnections(shape)`: the two positions a rail of the given shape at `p` points at. -/
def connectionsOf (p : Pos) : RailShape → List Pos
  | .north_south => [p.step .north, p.step .south]
  | .east_west => [p.step .west, p.step .east]
  | .ascending_east => [p.step .west, (p.step .east).step .up]
  | .ascending_west => [(p.step .west).step .up, p.step .east]
  | .ascending_north => [(p.step .north).step .up, p.step .south]
  | .ascending_south => [p.step .north, (p.step .south).step .up]
  | .south_east => [p.step .east, p.step .south]
  | .south_west => [p.step .west, p.step .south]
  | .north_west => [p.step .west, p.step .north]
  | .north_east => [p.step .east, p.step .north]

/-- The constructor of `RailState`. -/
def new (p : Pos) (state : Block) : RailState := ⟨p, state, connectionsOf p (shapeOf state)⟩

/-- `getRail(pos)`: the rail at `p`, or else above it, or else below it. -/
def getRail (l : Level) (p : Pos) : Option RailState :=
  if isRailAt l p then some (new p (l.blockAt p))
  else if isRailAt l (p.step .up) then some (new (p.step .up) (l.blockAt (p.step .up)))
  else if isRailAt l (p.step .down) then some (new (p.step .down) (l.blockAt (p.step .down)))
  else none

/-- `hasRail(pos)`: there is a rail at `p`, above it or below it. -/
def hasRail (l : Level) (p : Pos) : Bool :=
  isRailAt l p || isRailAt l (p.step .up) || isRailAt l (p.step .down)

/-- `hasConnection(pos)`: one of the connections is in the column of `q`. -/
def hasConnection (r : RailState) (q : Pos) : Bool :=
  r.connections.any fun c => c.x == q.x && c.z == q.z

/-- `removeSoftConnections`: keeps the connections at which there is a rail that points back,
replacing each by the position of that rail. -/
def removeSoftConnections (l : Level) (r : RailState) : RailState :=
  { r with
    connections := r.connections.filterMap fun c =>
      match getRail l c with
      | some rail => if rail.hasConnection r.pos then some rail.pos else none
      | none => none }

/-- `canConnectTo(rail)`, for the rail at `q`. -/
def canConnectTo (r : RailState) (q : Pos) : Bool :=
  r.hasConnection q || r.connections.length != 2

/-- `countPotentialConnections`: the number of horizontal neighbours with a rail. -/
def countPotentialConnections (l : Level) (p : Pos) : ℕ :=
  Direction.horizontals.countP fun d => hasRail l (p.step d)

/-- `hasNeighborRail(pos)`, for the rail at `self`: there is a rail at `q` (or above or below
it) that can connect to `self`. -/
def hasNeighborRail (l : Level) (self q : Pos) : Bool :=
  match getRail l q with
  | none => false
  | some neighbor => (neighbor.removeSoftConnections l).canConnectTo self

/-- The end of `place` and of `connectTo`: a flat straight shape becomes a slope when there is
a rail one block up at one of its ends. -/
def ascend (l : Level) (p : Pos) (shape : Option RailShape) : Option RailShape :=
  let shape :=
    if shape = some .north_south then
      let shape :=
        if isRailAt l ((p.step .north).step .up) then some .ascending_north else shape
      if isRailAt l ((p.step .south).step .up) then some .ascending_south else shape
    else shape
  if shape = some .east_west then
    let shape :=
      if isRailAt l ((p.step .east).step .up) then some .ascending_east else shape
    if isRailAt l ((p.step .west).step .up) then some .ascending_west else shape
  else shape

/-- `connectTo(rail)`: the rail `r` adds the rail at `q` to its connections, takes the shape
that fits them and is put into the level. -/
def connectTo (r : RailState) (q : Pos) : M Unit := do
  let l ← get
  let r := { r with connections := r.connections ++ [q] }
  let n := r.hasConnection (r.pos.step .north)
  let s := r.hasConnection (r.pos.step .south)
  let w := r.hasConnection (r.pos.step .west)
  let e := r.hasConnection (r.pos.step .east)
  let shape : Option RailShape := if n || s then some .north_south else none
  let shape := if w || e then some .east_west else shape
  let shape :=
    if !isStraight r.state then
      let shape := if s && e && !n && !w then some .south_east else shape
      let shape := if s && w && !n && !e then some .south_west else shape
      let shape := if n && w && !s && !e then some .north_west else shape
      if n && e && !s && !w then some .north_east else shape
    else shape
  let shape := (ascend l r.pos shape).getD .north_south
  discard <| Level.setBlock r.pos (setShape r.state shape)

/-- The shape `place` chooses, from which of the four neighbours have a rail that can connect
(`n`, `s`, `w`, `e`). -/
def placeShape (l : Level) (p : Pos) (straight hasSignal : Bool) (default : RailShape)
    (n s w e : Bool) : RailShape :=
  let northOrSouth := n || s
  let westOrEast := w || e
  let shape : Option RailShape :=
    if northOrSouth && !westOrEast then some .north_south else none
  let shape := if westOrEast && !northOrSouth then some .east_west else shape
  let southAndEast := s && e
  let southAndWest := s && w
  let northAndEast := n && e
  let northAndWest := n && w
  let shape :=
    if !straight then
      let shape := if southAndEast && !n && !w then some .south_east else shape
      let shape := if southAndWest && !n && !e then some .south_west else shape
      let shape := if northAndWest && !s && !e then some .north_west else shape
      if northAndEast && !s && !w then some .north_east else shape
    else shape
  let shape :=
    if shape.isNone then
      let shape : Option RailShape :=
        if northOrSouth && westOrEast then some default
        else if northOrSouth then some .north_south
        else if westOrEast then some .east_west
        else none
      if !straight then
        if hasSignal then
          let shape := if southAndEast then some .south_east else shape
          let shape := if southAndWest then some .south_west else shape
          let shape := if northAndEast then some .north_east else shape
          if northAndWest then some .north_west else shape
        else
          let shape := if northAndWest then some .north_west else shape
          let shape := if northAndEast then some .north_east else shape
          let shape := if southAndWest then some .south_west else shape
          if southAndEast then some .south_east else shape
      else shape
    else shape
  (ascend l p shape).getD default

/-- `place(hasSignal, first, defaultShape)` for the rail `state` at `p`: chooses a shape, puts
the rail into the level if it is new (`first`) or changed, and lets the rails it then points at
connect to it. Returns the state chosen. -/
def place (p : Pos) (state : Block) (hasSignal first : Bool) (default : RailShape) :
    M Block := do
  let l ← get
  let n := hasNeighborRail l p (p.step .north)
  let s := hasNeighborRail l p (p.step .south)
  let w := hasNeighborRail l p (p.step .west)
  let e := hasNeighborRail l p (p.step .east)
  let shape := placeShape l p (isStraight state) hasSignal default n s w e
  let state := setShape state shape
  if first || (← Level.getBlock p) != state then
    discard <| Level.setBlock p state
    (connectionsOf p shape).forM fun c => do
      let l ← get
      if let some neighbor := getRail l c then
        let neighbor := neighbor.removeSoftConnections l
        if neighbor.canConnectTo p then neighbor.connectTo p
  return state

end RailState

/-! ### `BaseRailBlock` -/

/-- `canSurvive`: the block below has a rigid top face. -/
def canSurvive (l : Level) (p : Pos) : Bool := canSupportRigidBlock l (p.step .down)

/-- `shouldBeRemoved(pos, level, shape)`: the rail lost its support. For a slope this also asks
for a rigid top face of the block it leans on. -/
def shouldBeRemoved (l : Level) (p : Pos) (shape : RailShape) : Bool :=
  if !canSupportRigidBlock l (p.step .down) then true
  else
    match shape with
    | .ascending_east => !canSupportRigidBlock l (p.step .east)
    | .ascending_west => !canSupportRigidBlock l (p.step .west)
    | .ascending_north => !canSupportRigidBlock l (p.step .north)
    | .ascending_south => !canSupportRigidBlock l (p.step .south)
    | _ => false

/-- `updateDir(level, pos, state, first)`. -/
def updateDir (p : Pos) (state : Block) (first : Bool) : M Block := do
  let hasSignal ← Level.hasNeighborSignal p
  RailState.place p state hasSignal first (shapeOf state)

/-- `updateState(state, level, pos, movedByPiston)`: the rail chooses its shape; a straight rail
then gets a neighbour update of its own. -/
def updateStateOnPlace (state : Block) (p : Pos) (movedByPiston : Bool) : M Block := do
  let state ← updateDir p state true
  if isStraight state then Level.neighborChangedFor state p state.id movedByPiston
  return state

/-- `BaseRailBlock.neighborChanged`: the rail drops and is removed if it lost its support;
otherwise `updateState` is the reaction of the particular rail
(`updateState(state, level, pos, block)`). -/
def neighborChanged (self : Block) (updateState : Pos → BlockId → M Unit) (p : Pos)
    (block : BlockId) (movedByPiston : Bool) : M Unit := do
  let l ← get
  if (l.blockAt p).is self.id then
    if shouldBeRemoved l p (shapeOf self) then
      Level.dropResources self p
      discard <| Level.removeBlock p movedByPiston
    else updateState p block

/-- `BaseRailBlock.affectNeighborsAfterRemoval`. -/
def affectNeighborsAfterRemoval (self : Block) (p : Pos) (movedByPiston : Bool) : M Unit := do
  if !movedByPiston then
    if isSlope (shapeOf self) then Level.updateNeighborsAt (p.step .up) self.id
    if isStraight self then
      Level.updateNeighborsAt p self.id
      Level.updateNeighborsAt (p.step .down) self.id

/-- What the rails have in common: survival, placement and removal. -/
def base (self : Block) (updateState : Pos → BlockId → M Unit) : Behaviour :=
  { Behaviour.inert self with
    canSurvive := canSurvive
    onPlace := fun p old movedByPiston => do
      if !old.is self.id then discard <| updateStateOnPlace self p movedByPiston
    neighborChanged := neighborChanged self updateState
    affectNeighborsAfterRemoval := affectNeighborsAfterRemoval self }

/-! ### `RailBlock` -/

/-- `RailBlock.updateState(state, level, pos, block)`: a rail with three potential connections
chooses its shape again when a signal source next to it changes. -/
def railUpdateState (self : Block) (p : Pos) (block : BlockId) : M Unit := do
  if (Block.default block).attrs.signalSource
      && RailState.countPotentialConnections (← get) p == 3 then
    discard <| updateDir p self false

/-! ### `PoweredRailBlock` -/

/-- `findPoweredRailSignal(level, pos, state, forward, searchDepth)` followed by
`isSameRailWithPower`: looks along the rail of shape `shape` at `p`, in one of its two
directions, for a rail of the block `id` that is on and receives a signal, through rails of that
block that are on. `fuel` is `8 - searchDepth`. -/
def findPoweredRailSignal (env : Env) (l : Level) (id : Blocks.PoweredRail.Id) :
    ℕ → Pos → StraightShape → Bool → Bool
  | 0, _, _, _ => false
  | fuel + 1, p, shape, forward =>
    -- The next position, whether the position below it is tried as well, and whether the
    -- search runs along the x axis.
    let (q, checkBelow, alongX) : Pos × Bool × Bool :=
      match shape with
      | .north_south =>
        (if forward then p.step .south else p.step .north, true, false)
      | .east_west =>
        (if forward then p.step .west else p.step .east, true, true)
      | .ascending_east =>
        if forward then (p.step .west, true, true) else ((p.step .east).step .up, false, true)
      | .ascending_west =>
        if forward then ((p.step .west).step .up, false, true) else (p.step .east, true, true)
      | .ascending_north =>
        if forward then (p.step .south, true, false) else ((p.step .north).step .up, false, false)
      | .ascending_south =>
        if forward then ((p.step .south).step .up, false, false) else (p.step .north, true, false)
    let isSameRailWithPower (q : Pos) : Bool :=
      match l.blockAt q with
      | .poweredRail id' s =>
        let acrossX := s.shape = .north_south || s.shape = .ascending_north
          || s.shape = .ascending_south
        if id' ≠ id then false
        else if alongX && acrossX then false
        else if !alongX && !acrossX then false
        else if !s.powered then false
        else if l.hasNeighborSignalAt env q then true
        else findPoweredRailSignal env l id fuel q s.shape forward
      | _ => false
    isSameRailWithPower q || (checkBelow && isSameRailWithPower (q.step .down))

/-- `PoweredRailBlock.updateState(state, level, pos, block)`: switches the rail on or off. -/
def poweredUpdateState (id : Blocks.PoweredRail.Id) (s : Blocks.PoweredRail) (p : Pos)
    (_block : BlockId) : M Unit := do
  let l ← get
  let env ← read
  let shouldPower := l.hasNeighborSignalAt env p
    || findPoweredRailSignal env l id 8 p s.shape true
    || findPoweredRailSignal env l id 8 p s.shape false
  if shouldPower != s.powered then
    discard <| Level.setBlock p (.poweredRail id { s with powered := shouldPower })
    Level.updateNeighborsAt (p.step .down) id.toBlockId
    if isSlope (ofStraight s.shape) then Level.updateNeighborsAt (p.step .up) id.toBlockId

/-! ### `DetectorRailBlock` -/

/-- Half the width of a minecart, `0.98f / 2.0f`, as a `double`. -/
def minecartHalfWidth : Float := (Float32.ofBits 0x3EFAE148).toFloat

/-- The height of a minecart, `0.7f`, as a `double`. -/
def minecartHeight : Float := (Float32.ofBits 0x3F333333).toFloat

/-- `getInteractingMinecartOfType(level, pos, AbstractMinecart.class, e -> true)` is not empty:
the bounding box of some minecart meets the box `getSearchBB(pos)`. -/
def hasMinecart (l : Level) (p : Pos) : Bool :=
  let x := Float.ofInt p.x
  let y := Float.ofInt p.y
  let z := Float.ofInt p.z
  l.entities.any fun e =>
    match e.data with
    | .minecart _ _ =>
      let c := e.base.pos
      let w := minecartHalfWidth
      c.x - w < Float.ofInt (p.x + 1) - 0.2 && c.x + w > x + 0.2
        && c.y < Float.ofInt (p.y + 1) - 0.2 && c.y + minecartHeight > y
        && c.z - w < Float.ofInt (p.z + 1) - 0.2 && c.z + w > z + 0.2
    | _ => false

/-- `updatePowerToConnected`: a neighbour update for each of the two positions the rail points
at, as if the block there had changed itself. -/
def updatePowerToConnected (p : Pos) (state : Block) : M Unit :=
  (RailState.new p state).connections.forM fun c => do
    let connectionState ← Level.getBlock c
    Level.neighborChangedFor connectionState c connectionState.id false

/-- `checkPressed(level, pos, state)`: switches the detector rail on if a minecart is on it and
off if none is, and asks for another check in 20 game ticks while it is on. -/
def checkPressed (p : Pos) (s : Blocks.DetectorRail) : M Unit := do
  let l ← get
  if canSurvive l p && (l.blockAt p).is .detector_rail then
    let wasPressed := s.powered
    let shouldBePressed := hasMinecart l p
    if shouldBePressed != wasPressed then
      let newState : Block := .detectorRail { s with powered := shouldBePressed }
      discard <| Level.setBlock p newState
      updatePowerToConnected p newState
      Level.updateNeighborsAt p .detector_rail
      Level.updateNeighborsAt (p.step .down) .detector_rail
    if shouldBePressed then Level.scheduleTick p .detector_rail 20
    Level.updateNeighbourForOutputSignal p .detector_rail

/-- The behaviour of a detector rail. -/
def detector (s : Blocks.DetectorRail) : Behaviour :=
  let self : Block := .detectorRail s
  { base self fun _ _ => pure () with
    signal := fun _ _ _ => if s.powered then 15 else 0
    ownSignal := fun _ _ => if s.powered then 15 else 0
    directSignal := fun _ _ d => if s.powered && d = .up then 15 else 0
    -- Zero unless a command block minecart or a container minecart is on the rail; see the
    -- module documentation.
    analogSignal := fun _ _ _ => 0
    entityInside := fun p _ => do
      if !s.powered then checkPressed p s
    tick := fun p => do
      if s.powered then checkPressed p s
    onPlace := fun p old movedByPiston => do
      if !old.is .detector_rail then
        match ← updateStateOnPlace self p movedByPiston with
        | .detectorRail updated => checkPressed p updated
        | _ => pure () }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .rail _ => base self (railUpdateState self)
  | .poweredRail id s => base self (poweredUpdateState id s)
  | .detectorRail s => detector s
  | _ => .inert self

end Redstone.Component.Rail
