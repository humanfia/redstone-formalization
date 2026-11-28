module

public import Redstone.Mechanics.Tick
public import Redstone.Block.FaceShape
public import Redstone.Block.Generated.Tags

/-!
# Blocks that connect to their neighbours: fences, bars and panes, walls, stairs

Java classes: `FenceBlock` and `IronBarsBlock` (with `CrossCollisionBlock`,
`StainedGlassPaneBlock`, `WeatheringCopperBarsBlock`), `WallBlock`, `StairBlock` (with
`WeatheringCopperStairBlock`).

The state of these blocks records what they are joined to. A shape update from a horizontal
neighbour makes a fence, a bar or a pane recompute the arm on that side, and makes a stair
recompute its corner shape. A wall recomputes its four sides, low or tall, and its post, on
every update from a side or from above; for this it reads the bottom face of the collision
shape of the block above.

## What is not modelled

* The fluid tick a waterlogged block schedules on a shape update: fluids do not flow.
* The collision shape of the block above a wall when it comes from a block entity (a moving
  piston, a shulker box) or depends on the position (bamboo, pointed dripstone): the shape of
  the block state is used.
* `FenceBlock.useWithoutItem` (`LeadItem.bindPlayerMobs`): there are no leashed mobs, so the
  action passes, as in the game.
* Random ticks (`WeatheringCopperBarsBlock`, `WeatheringCopperStairBlock`), items used on the
  blocks (waxing, scraping), placement (`getStateForPlacement`), rotation and mirroring.
-/

@[expose] public section

namespace Redstone.Component.Connecting

/-- `Block.isExceptionForConnection(state)`: a block that fences, panes and walls do not join
although its face is sturdy. -/
def isExceptionForConnection (b : Block) : Bool :=
  BlockClass.leavesBlock b.id || b.is .barrier || b.is .carved_pumpkin || b.is .jack_o_lantern ||
    b.is .melon || b.is .pumpkin || BlockTag.shulker_boxes b.id

/-- `neighbourState.isFaceSturdy(level, neighbourPos, d)` for the state a shape update comes
with. The support shape belongs to the state, except for a moving piston, whose shape is read
from the level (`Level.supportAttrs`). -/
def isFaceSturdy (l : Level) (q : Pos) (neighbour : Block) (d : Direction) : Bool :=
  (if neighbour.is .moving_piston then l.supportAttrs q else neighbour.attrs).isFaceSturdy d

/-- `block instanceof FenceGateBlock && FenceGateBlock.connectsToDirection(state, direction)`
for a horizontal direction: the gate lies across the direction, so its end faces it. -/
def isConnectedFenceGate (b : Block) (d : Direction) : Bool :=
  match b with
  | .fenceGate _ s => s.facing.toDirection.axis ≠ d.axis
  | _ => false

/-! ### Fences -/

/-- `FenceBlock.connectsTo(state, faceSolid, direction)` for the fence `self`: it joins a sturdy
face, a fence of its kind (wooden or not) and the end of a fence gate. -/
def fenceConnectsTo (self : BlockId) (b : Block) (faceSolid : Bool) (d : Direction) : Bool :=
  let sameFence := BlockTag.fences b.id &&
    BlockTag.wooden_fences b.id == BlockTag.wooden_fences self
  !isExceptionForConnection b && faceSolid || sameFence || isConnectedFenceGate b d

/-- The fence with the arm in a horizontal direction set (`PROPERTY_BY_DIRECTION`). -/
def setFenceArm (s : Blocks.Fence) (d : Direction) (v : Bool) : Blocks.Fence :=
  match d with
  | .north => { s with north := v }
  | .east => { s with east := v }
  | .south => { s with south := v }
  | .west => { s with west := v }
  | _ => s

/-! ### Bars and panes -/

/-- `IronBarsBlock.attachsTo(state, faceSolid)`: bars and panes join a sturdy face, each other,
and walls. -/
def barsAttachTo (b : Block) (faceSolid : Bool) : Bool :=
  !isExceptionForConnection b && faceSolid || BlockClass.ironBarsBlock b.id || BlockTag.walls b.id

/-- The bars with the arm in a horizontal direction set. -/
def setBarsArm (s : Blocks.IronBars) (d : Direction) (v : Bool) : Blocks.IronBars :=
  match d with
  | .north => { s with north := v }
  | .east => { s with east := v }
  | .south => { s with south := v }
  | .west => { s with west := v }
  | _ => s

/-- The copper bars with the arm in a horizontal direction set. -/
def setCopperBarsArm (s : Blocks.WeatheringCopperBars) (d : Direction) (v : Bool) :
    Blocks.WeatheringCopperBars :=
  match d with
  | .north => { s with north := v }
  | .east => { s with east := v }
  | .south => { s with south := v }
  | .west => { s with west := v }
  | _ => s

/-- The pane with the arm in a horizontal direction set. -/
def setPaneArm (s : Blocks.StainedGlassPane) (d : Direction) (v : Bool) :
    Blocks.StainedGlassPane :=
  match d with
  | .north => { s with north := v }
  | .east => { s with east := v }
  | .south => { s with south := v }
  | .west => { s with west := v }
  | _ => s

/-! ### Walls -/

/-- `WallBlock.connectsTo(state, faceSolid, direction)`: a wall joins walls, a sturdy face,
bars and panes, and the end of a fence gate. -/
def wallConnectsTo (b : Block) (faceSolid : Bool) (d : Direction) : Bool :=
  BlockTag.walls b.id || !isExceptionForConnection b && faceSolid ||
    BlockClass.ironBarsBlock b.id || isConnectedFenceGate b d

/-- `TEST_SHAPE_POST`: the column in the middle that the block above must cover for the post
to be lowered. -/
def testShapePost : FaceShape := .ofBoxes [.ofPixels 7 0 7 9 16 9]

/-- `TEST_SHAPES_WALL`: the strip from the middle to a side that the block above must cover
for that side of the wall to be tall. -/
def testShapeWall : Direction → FaceShape
  | .north => .ofBoxes [.ofPixels 7 0 0 9 16 9]
  | .south => .ofBoxes [.ofPixels 7 0 7 9 16 16]
  | .west => .ofBoxes [.ofPixels 0 0 7 9 16 9]
  | .east => .ofBoxes [.ofPixels 7 0 7 16 16 9]
  | _ => .empty

/-- `WallBlock.isCovered(aboveShape, testShape)`: the shape above covers the test shape. -/
def isCovered (aboveShape testShape : FaceShape) : Bool := testShape.subset aboveShape

/-- `WallBlock.makeWallState`: a side that is connected is tall when the block above covers it,
and low otherwise. -/
def makeWallState (connects : Bool) (aboveShape testShape : FaceShape) : WallSide :=
  if connects then (if isCovered aboveShape testShape then .tall else .low) else .none

/-- `WallBlock.shouldRaisePost(state, topNeighbour, aboveShape)`: the wall has a post when the
wall above has one, when its sides do not make a straight line, or, unless a line of tall
sides runs through it, when the block above asks for a post or covers the middle. -/
def shouldRaisePost (s : Blocks.Wall) (top : Block) (aboveShape : FaceShape) : Bool :=
  let topHasPost := match top with
    | .wall _ t => t.up
    | _ => false
  if topHasPost then true else
  let n := s.north = .none
  let so := s.south = .none
  let e := s.east = .none
  let w := s.west = .none
  let hasCorner := (decide n && so && w && e) || decide n != decide so || decide w != decide e
  if hasCorner then true else
  let hasHighWall := (s.north = .tall && s.south = .tall) || (s.east = .tall && s.west = .tall)
  if hasHighWall then false
  else BlockTag.wall_post_override top.id || isCovered aboveShape testShapePost

/-- The private `WallBlock.updateShape(level, state, topPos, topNeighbour, north, east, south,
west)`: the wall with the given sides connected, under the block `top`. -/
def wallShape (s : Blocks.Wall) (top : Block) (north east south west : Bool) : Blocks.Wall :=
  let aboveShape := (FaceShape.ofIndex top.attrs.collision).faceShape .down
  let s := { s with
    north := makeWallState north aboveShape (testShapeWall .north)
    east := makeWallState east aboveShape (testShapeWall .east)
    south := makeWallState south aboveShape (testShapeWall .south)
    west := makeWallState west aboveShape (testShapeWall .west) }
  { s with up := shouldRaisePost s top aboveShape }

/-- `WallBlock.updateShape`: nothing for an update from below, `topUpdate` for one from above,
`sideUpdate` for one from a side. -/
def wallUpdateShape (s : Blocks.Wall) (l : Level) (p : Pos) (d : Direction) (q : Pos)
    (neighbour : Block) : Blocks.Wall :=
  let side (d' : Direction) (cur : WallSide) : Bool :=
    if d = d' then wallConnectsTo neighbour (isFaceSturdy l q neighbour d.opposite) d.opposite
    else cur ≠ .none
  match d with
  | .down => s
  | .up => wallShape s neighbour (s.north ≠ .none) (s.east ≠ .none) (s.south ≠ .none)
      (s.west ≠ .none)
  | _ => wallShape s (l.blockAt (p.step .up)) (side .north s.north) (side .east s.east)
      (side .south s.south) (side .west s.west)

/-! ### Stairs -/

/-- `Direction.getCounterClockWise` for a horizontal direction. -/
def counterClockWise : Direction → Direction
  | .north => .west
  | .west => .south
  | .south => .east
  | .east => .north
  | d => d

/-- The facing and the half of a block of class `StairBlock` (`StairBlock.isStairs`). -/
def stairs? : Block → Option (Direction × Half)
  | .stair _ s => some (s.facing.toDirection, s.half)
  | .weatheringCopperStair _ s => some (s.facing.toDirection, s.half)
  | _ => none

/-- `StairBlock.canTakeShape(state, level, pos, neighbour)`: the block in direction `d` is not
a stair that faces the same way in the same half. -/
def canTakeShape (facing : Direction) (half : Half) (l : Level) (p : Pos) (d : Direction) : Bool :=
  match stairs? (l.blockAt (p.step d)) with
  | some (f, h) => f ≠ facing || h ≠ half
  | none => true

/-- `StairBlock.getStairsShape(state, level, pos)`: an outer corner when the stair behind turns
away, an inner corner when the stair in front does, and straight otherwise. -/
def stairsShape (facing : Direction) (half : Half) (l : Level) (p : Pos) : StairsShape :=
  let corner (q : Pos) (side : Direction → Direction) : Option Bool :=
    match stairs? (l.blockAt q) with
    | some (f, h) =>
      if h = half && f.axis ≠ facing.axis && canTakeShape facing half l p (side f) then
        some (f = counterClockWise facing)
      else none
    | none => none
  match corner (p.step facing) Direction.opposite with
  | some left => if left then .outer_left else .outer_right
  | none =>
    match corner (p.step facing.opposite) id with
    | some left => if left then .inner_left else .inner_right
    | none => .straight

/-! ### The behaviours -/

/-- The behaviour of a fence, of bars or a pane, of a wall, or of a stair. -/
def behaviour (self : Block) : Behaviour :=
  let horizontal (f : Level → Pos → Direction → Pos → Block → Block) : Behaviour :=
    { Behaviour.inert self with
      updateShape := fun p d q neighbour => do
        if d.IsHorizontal then return f (← get) p d q neighbour else return self }
  let attaches (l : Level) (d : Direction) (q : Pos) (neighbour : Block) : Bool :=
    barsAttachTo neighbour (isFaceSturdy l q neighbour d.opposite)
  match self with
  | .fence id s =>
    horizontal fun l _ d q neighbour =>
      .fence id <| setFenceArm s d <|
        fenceConnectsTo self.id neighbour (isFaceSturdy l q neighbour d.opposite) d.opposite
  | .ironBars id s =>
    horizontal fun l _ d q neighbour => .ironBars id (setBarsArm s d (attaches l d q neighbour))
  | .weatheringCopperBars id s =>
    horizontal fun l _ d q neighbour =>
      .weatheringCopperBars id (setCopperBarsArm s d (attaches l d q neighbour))
  | .stainedGlassPane id s =>
    horizontal fun l _ d q neighbour =>
      .stainedGlassPane id (setPaneArm s d (attaches l d q neighbour))
  | .wall id s =>
    { Behaviour.inert self with
      updateShape := fun p d q neighbour =>
        return .wall id (wallUpdateShape s (← get) p d q neighbour) }
  | .stair id s =>
    horizontal fun l p _ _ _ =>
      .stair id { s with shape := stairsShape s.facing.toDirection s.half l p }
  | .weatheringCopperStair id s =>
    horizontal fun l p _ _ _ =>
      .weatheringCopperStair id { s with shape := stairsShape s.facing.toDirection s.half l p }
  | _ => .inert self

end Redstone.Component.Connecting
