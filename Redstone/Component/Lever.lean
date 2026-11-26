module

public import Redstone.Mechanics.Tick

/-!
# Lever

Java class: `LeverBlock` (with `FaceAttachedHorizontalDirectionalBlock`).

A lever is attached to a block and is switched by players. While it is on it gives a signal of
15 to all its neighbours, and strong power to the block it is attached to.
-/

@[expose] public section

namespace Redstone.Component.Lever

/-- `getConnectedDirection(state)`: the direction from the block the lever is attached to
towards the lever. -/
def connectedDirection (s : Blocks.Lever) : Direction :=
  match s.face with
  | .ceiling => .down
  | .floor => .up
  | .wall => s.facing.toDirection

/-- `canSurvive`: the face the lever is attached to is sturdy. -/
def canSurvive (s : Blocks.Lever) (l : Level) (p : Pos) : Bool :=
  let d := (connectedDirection s).opposite
  (l.blockAt (p.step d)).attrs.isFaceSturdy d.opposite

/-- `updateNeighbours`: neighbour updates around the lever and around the block it is attached
to. -/
def updateNeighbours (s : Blocks.Lever) (p : Pos) : M Unit := do
  Level.updateNeighborsAt p .lever
  Level.updateNeighborsAt (p.step (connectedDirection s).opposite) .lever

/-- `pull`: switches the lever. -/
def pull (s : Blocks.Lever) (p : Pos) : M Unit := do
  let s := { s with powered := !s.powered }
  discard <| Level.setBlock p (.lever s)
  updateNeighbours s p
  Level.gameEvent (if s.powered then "minecraft:block_activate" else "minecraft:block_deactivate") p

/-- The behaviour of a lever. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .lever s =>
    { Behaviour.inert self with
      signal := fun _ _ _ => if s.powered then 15 else 0
      ownSignal := fun _ _ => if s.powered then 15 else 0
      directSignal := fun _ _ d => if s.powered && connectedDirection s = d then 15 else 0
      canSurvive := canSurvive s
      useWithoutItem := fun p _ => do
        pull s p
        return true
      affectNeighborsAfterRemoval := fun p moved => do
        if !moved && s.powered then updateNeighbours s p
      updateShape := fun p d _ _ => do
        if (connectedDirection s).opposite = d && !canSurvive s (← get) p then return .AIR
        else return self }
  | _ => .inert self

end Redstone.Component.Lever
