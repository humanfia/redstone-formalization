module

public import Redstone.Mechanics.Tick

/-!
# Buttons

Java classes: `ButtonBlock` (with `FaceAttachedHorizontalDirectionalBlock`), and the two fields
of `BlockSetType` a button reads.

A button is attached to a block. A player presses it; it then gives a signal of 15 to all its
neighbours and strong power to the block it is attached to, and it is released by a scheduled
tick: 20 game ticks later for the stone and polished blackstone buttons, 30 for all the others.
The others (the wooden ones) are also held down by an arrow or a trident that touches them:
the release tick looks for one and, if it finds one, schedules itself again.

## What is left out

* `onExplosionHit`: the method presses the button when `explosion.canTriggerBlocks()` holds
  and then runs `Block.onExplosionHit`. The hook of `Behaviour` does not carry the explosion,
  so it is not overridden here; `explosionHit` is the button's part of the method, to be called
  by the model of explosions.
* Sounds.
* `getStateForPlacement`: there are no block items.

`entityInside` is defined, but nothing in the engine calls it yet: that is for the model of
entities, which decides which blocks an entity is inside of.
-/

@[expose] public section

namespace Redstone.Component.Button

/-- `ticksToStayPressed`, the second argument of the constructor of `ButtonBlock` in `Blocks`:
20 for the two buttons of stone, 30 for the others. -/
def ticksToStayPressed : Blocks.Button.Id → ℕ
  | .stone_button | .polished_blackstone_button => 20
  | _ => 30

/-- `BlockSetType.canButtonBeActivatedByArrows` of the button's type: false for
`BlockSetType.STONE`, which both stone buttons have, and true for the types of all the others. -/
def canButtonBeActivatedByArrows : Blocks.Button.Id → Bool
  | .stone_button | .polished_blackstone_button => false
  | _ => true

/-- `getConnectedDirection(state)`: the direction from the block the button is attached to
towards the button. -/
def connectedDirection (s : Blocks.Button) : Direction :=
  match s.face with
  | .ceiling => .down
  | .floor => .up
  | .wall => s.facing.toDirection

/-- `canSurvive`, that is `canAttach`: the face the button is attached to is sturdy. -/
def canSurvive (s : Blocks.Button) (l : Level) (p : Pos) : Bool :=
  let d := (connectedDirection s).opposite
  (l.blockAt (p.step d)).attrs.isFaceSturdy d.opposite

/-- `updateNeighbours`: neighbour updates around the button and around the block it is attached
to. -/
def updateNeighbours (id : Blocks.Button.Id) (s : Blocks.Button) (p : Pos) : M Unit := do
  Level.updateNeighborsAt p id.toBlockId
  Level.updateNeighborsAt (p.step (connectedDirection s).opposite) id.toBlockId

/-- `press`: the button goes down and its release is scheduled. -/
def press (id : Blocks.Button.Id) (s : Blocks.Button) (p : Pos) : M Unit := do
  discard <| Level.setBlock p (.button id { s with powered := true })
  updateNeighbours id s p
  Level.scheduleTick p id.toBlockId (ticksToStayPressed id)
  Level.gameEvent "minecraft:block_activate" p

/-- `getShape(state).bounds()`, the box of `makeShapes`, in sixteenths of a block: the two
corners `(minX, minY, minZ)` and `(maxX, maxY, maxZ)`. The button is 6 wide, 4 high and 2 thick,
or 1 thick when it is pressed, and lies against the block it is attached to. On a floor or a
ceiling its long side runs along the axis perpendicular to `facing`. -/
def shapeBounds (s : Blocks.Button) : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) :=
  let t := if s.powered then 1 else 2
  match s.face, s.facing with
  | .floor, .north | .floor, .south => ((5, 0, 6), (11, t, 10))
  | .floor, .west | .floor, .east => ((6, 0, 5), (10, t, 11))
  | .ceiling, .north | .ceiling, .south => ((5, 16 - t, 6), (11, 16, 10))
  | .ceiling, .west | .ceiling, .east => ((6, 16 - t, 5), (10, 16, 11))
  | .wall, .north => ((5, 6, 16 - t), (11, 10, 16))
  | .wall, .south => ((5, 6, 0), (11, 10, t))
  | .wall, .west => ((16 - t, 6, 5), (16, 10, 11))
  | .wall, .east => ((0, 6, 5), (t, 10, 11))

/-- The entity types of the subclasses of `AbstractArrow`. -/
def arrowTypes : List String :=
  ["minecraft:arrow", "minecraft:spectral_arrow", "minecraft:trident"]

/-- `entity.getBoundingBox().intersects(state.getShape(level, pos).bounds().move(pos))` for an
arrow: the bounding box of an arrow is 0.5 wide and 0.5 high (`EntityDimensions.makeBoundingBox`
around its position), and `AABB.intersects` compares strictly. -/
def arrowTouches (s : Blocks.Button) (p : Pos) (at' : Vec3) : Bool :=
  let (lo, hi) := shapeBounds s
  let c (base : ℤ) (n : ℕ) : Float := Float.ofInt base + Float.ofNat n / 16
  at'.x - 0.25 < c p.x hi.1 && at'.x + 0.25 > c p.x lo.1 &&
    at'.y < c p.y hi.2.1 && at'.y + 0.5 > c p.y lo.2.1 &&
    at'.z - 0.25 < c p.z hi.2.2 && at'.z + 0.25 > c p.z lo.2.2

/-- The test `firstArrow != null` of `checkPressed`: the button can be activated by arrows and
`getEntitiesOfClass(AbstractArrow.class, ...)` finds an entity in the bounds of its shape. -/
def hasArrow (id : Blocks.Button.Id) (s : Blocks.Button) (l : Level) (p : Pos) : Bool :=
  canButtonBeActivatedByArrows id &&
    l.entities.any fun e => arrowTypes.contains e.data.typeName && arrowTouches s p e.base.pos

/-- `checkPressed`: the button is pressed exactly when an arrow touches it; while one does, the
next check is scheduled. -/
def checkPressed (id : Blocks.Button.Id) (s : Blocks.Button) (p : Pos) : M Unit := do
  let shouldBePressed := hasArrow id s (← get) p
  if shouldBePressed != s.powered then
    discard <| Level.setBlock p (.button id { s with powered := shouldBePressed })
    updateNeighbours id s p
    Level.gameEvent
      (if shouldBePressed then "minecraft:block_activate" else "minecraft:block_deactivate") p
  if shouldBePressed then Level.scheduleTick p id.toBlockId (ticksToStayPressed id)

/-- The button's part of `onExplosionHit`, before `super.onExplosionHit`: an explosion that
triggers blocks (`explosion.canTriggerBlocks()`, given as `canTriggerBlocks`) presses the
button. -/
def explosionHit (id : Blocks.Button.Id) (s : Blocks.Button) (p : Pos) (canTriggerBlocks : Bool) :
    M Unit := do
  if canTriggerBlocks && !s.powered then press id s p

/-- The behaviour of a button. -/
def button (id : Blocks.Button.Id) (s : Blocks.Button) : Behaviour :=
  let self : Block := .button id s
  { Behaviour.inert self with
    ownSignal := fun _ _ => if s.powered then 15 else 0
    signal := fun _ _ _ => if s.powered then 15 else 0
    directSignal := fun _ _ d => if s.powered && connectedDirection s = d then 15 else 0
    canSurvive := canSurvive s
    useWithoutItem := fun p _ => do
      if !s.powered then press id s p
      return true
    affectNeighborsAfterRemoval := fun p moved => do
      if !moved && s.powered then updateNeighbours id s p
    tick := fun p => do
      if s.powered then checkPressed id s p
    entityInside := fun p _ => do
      if canButtonBeActivatedByArrows id && !s.powered then checkPressed id s p
    updateShape := fun p d _ _ => do
      if (connectedDirection s).opposite = d && !canSurvive s (← get) p then return .AIR
      else return self }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .button id s => button id s
  | _ => .inert self

end Redstone.Component.Button
