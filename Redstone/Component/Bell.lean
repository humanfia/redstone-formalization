module

public import Redstone.Mechanics.Tick

/-!
# Bell

Java classes: `BellBlock`, `BellBlockEntity`.

A bell rings when the signal it receives appears and when a player uses one of its sides.
Ringing queues a block event and announces `block_change`. A bell hangs from the ceiling, stands
on the floor or is attached to one or two walls, and breaks when it loses its support.

Not modelled:

* What ringing does besides the block event: the swing of the bell, the memory `HEARD_BELL_TIME`
  of the mobs around and the glow of raiders (`BellBlockEntity`). None of it is saved, and none
  of it reaches blocks; see `Redstone.BlockEntities.Bell`.
* `onProjectileHit`: whether the hit rings the bell depends on the height of the point that was
  hit, which the model's hook does not carry.
* `onExplosionHit`: only explosions that trigger blocks (wind charges) ring a bell, and the
  model's hook does not say which explosion it is.
* The height of a player's click: the game refuses a click above 0.8124 of the block's height.
  A click is taken to be at the centre of the face, as the test harness makes it.
-/

@[expose] public section

namespace Redstone.Component.Bell

/-- `getConnectedDirection(state)`: the direction from the block the bell is attached to towards
the bell. -/
def connectedDirection (s : Blocks.Bell) : Direction :=
  match s.attachment with
  | .floor => .up
  | .ceiling => .down
  | _ => s.facing.toDirection.opposite

/-- The block tag `minecraft:unstable_bottom_center`: the fence gates. -/
def unstableBottomCenter (b : Block) : Bool :=
  [BlockId.acacia_fence_gate, .birch_fence_gate, .dark_oak_fence_gate, .pale_oak_fence_gate,
    .jungle_fence_gate, .oak_fence_gate, .spruce_fence_gate, .crimson_fence_gate,
    .warped_fence_gate, .mangrove_fence_gate, .bamboo_fence_gate, .cherry_fence_gate,
    .poplar_fence_gate].contains b.id

/-- `Block.canSupportCenter(level, pos, direction)`: the block at `p` can carry something at the
centre of its face `d`. -/
def canSupportCenter (l : Level) (p : Pos) (d : Direction) : Bool :=
  let b := l.blockAt p
  if d = .down && unstableBottomCenter b then false else b.attrs.isFaceSturdyCenter d

/-- `FaceAttachedHorizontalDirectionalBlock.canAttach(level, pos, direction)`: the neighbour of
`p` in direction `d` has a sturdy face towards `p`. -/
def canAttach (l : Level) (p : Pos) (d : Direction) : Bool :=
  (l.blockAt (p.step d)).attrs.isFaceSturdy d.opposite

/-- `canSurvive`: a ceiling bell needs support at the centre of the block above, any other bell
a sturdy face of the block it is attached to. -/
def canSurvive (s : Blocks.Bell) (l : Level) (p : Pos) : Bool :=
  let d := (connectedDirection s).opposite
  if d = .up then canSupportCenter l (p.step .up) .down else canAttach l p d

/-- The horizontal direction equal to `d`; `north` for a vertical one. -/
def horizontal (d : Direction) : HorizontalDirection :=
  match d with
  | .south => .south
  | .west => .west
  | .east => .east
  | _ => .north

/-- `updateShape`: the bell breaks when its support is gone, and a wall bell changes between one
and two walls. -/
def updateShape (s : Blocks.Bell) (l : Level) (p : Pos) (d : Direction) (neighbour : Block) :
    Block :=
  let support := (connectedDirection s).opposite
  if support = d && !canSurvive s l p && s.attachment ≠ .double_wall then .AIR
  else if d.axis = s.facing.toDirection.axis && s.attachment = .double_wall
      && !neighbour.attrs.isFaceSturdy d then
    .bell { s with attachment := .single_wall, facing := horizontal d.opposite }
  else if d.axis = s.facing.toDirection.axis && s.attachment = .single_wall
      && support.opposite = d && neighbour.attrs.isFaceSturdy s.facing.toDirection then
    .bell { s with attachment := .double_wall }
  else .bell s

/-- `Direction.get3DDataValue`. -/
def dataValue (d : Direction) : ℤ := d.bit

/-- `attemptToRing(ringingEntity, level, pos, direction)`: rings the bell at `p` if it has its
block entity (`BellBlockEntity.onHit`, which queues the block event). Without a direction the
bell is rung in the direction it faces. Returns whether it rang. -/
def attemptToRing (p : Pos) (direction : Option Direction) : M Bool := do
  let some (.bell _) ← Level.getBlockEntity p | return false
  let state ← Level.getBlock p
  let direction := direction.getD <|
    match state with
    | .bell s => s.facing.toDirection
    | _ => .north
  Level.blockEvent p state.id 1 (dataValue direction)
  Level.gameEvent "minecraft:block_change" p
  return true

/-- `isProperHit(state, clickedDirection, clickY)` for a click at half the height of the block:
a floor bell is rung along its axis, a wall bell across it, a ceiling bell from any side. -/
def isProperHit (s : Blocks.Bell) (clicked : Direction) : Bool :=
  if clicked.axis = .y then false
  else
    match s.attachment with
    | .floor => s.facing.toDirection.axis = clicked.axis
    | .single_wall | .double_wall => s.facing.toDirection.axis ≠ clicked.axis
    | .ceiling => true

/-- `useWithoutItem`, that is `onHit(level, state, hit, player, true)`: a proper hit rings the
bell. Returns whether the hit was proper. -/
def use (s : Blocks.Bell) (p : Pos) (face : Direction) : M Bool := do
  if isProperHit s face then
    discard <| attemptToRing p (some face)
    return true
  else return false

/-- The behaviour of a bell. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .bell s =>
    { Behaviour.inert self with
      canSurvive := canSurvive s
      updateShape := fun p d _ neighbour => return updateShape s (← get) p d neighbour
      neighborChanged := fun p _ _ => do
        let signal ← Level.hasNeighborSignal p
        if signal != s.powered then
          if signal then discard <| attemptToRing p none
          discard <| Level.setBlock p (.bell { s with powered := signal })
      useWithoutItem := fun p face => use s p face
      -- `BlockBehaviour.useItemOn` asks for the empty-hand interaction, whatever the item.
      useItemOn := fun p face _ => use s p face
      -- `BaseEntityBlock.triggerEvent` passes the event to the block entity, which accepts the
      -- ring (`BellBlockEntity.triggerEvent`).
      triggerEvent := fun p a _ => return (← Level.getBlockEntity p).isSome && a == 1
      -- `getTicker`: `BellBlockEntity.serverTick` advances the swing, which the model does not
      -- keep; the ticker itself is part of the level.
      ticksBlockEntity := true }
  | _ => .inert self

end Redstone.Component.Bell
