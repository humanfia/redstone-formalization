module

public import Redstone.Component.Lever

/-!
# Lemmas about the lever

Generic facts about the lever, over an arbitrary level. The theorems about concrete circuits
are in `Redstone/Theorems`; every gate of `Redstone/Theorems/Logic` has levers as its inputs.

* **Attribute lemmas**: where a lever is attached (`connectedDirection_floor`,
  `connectedDirection_ceiling`, `connectedDirection_wall`); a lever that is on gives 15 to all
  its neighbours and one that is off gives nothing (`signal_lever`); it gives strong power
  into the block it is attached to and to no other block (`directSignal_lever`,
  `directSignal_attachment`, `directSignal_of_ne`). Switching the lever does not move it
  (`connectedDirection_toggle`, `canSurvive_toggle`).
* **Using a lever** is `pull`, and the use is always consumed (`useWithoutItem_lever`). `pull`
  writes the lever with `powered` negated, then sends neighbour updates around the lever and
  around the block it is attached to, then the game event (`pull_eq`); so two uses write the
  state the lever started with (`toggle_toggle`).
* **Support**: a shape update from the block the lever is attached to removes the lever when
  that block no longer has a sturdy face towards it (`updateShape_of_unsupported`); any other
  shape update leaves the lever as it is (`updateShape_of_supported`,
  `updateShape_of_ne`). `updateShape_lever` is the reaction written out.

Left out: what the level looks like after `pull`. `Level.setBlock` and the neighbour updates
run the reactions of all neighbours, so the result depends on the whole neighbourhood; it is
proved for concrete circuits by evaluation (`Redstone/Theorems/Basics/LeverLamp.lean`, and the
first game tick of every theorem in `Redstone/Theorems/Logic`).
-/

@[expose] public section

namespace Redstone.Component.Lever

/-- The lever with `powered` negated: the state a use writes. -/
def toggle (s : Blocks.Lever) : Blocks.Lever := { s with powered := !s.powered }

/-! ### Attribute lemmas -/

/-- A lever on the floor is attached to the block below it. -/
theorem connectedDirection_floor (s : Blocks.Lever) (h : s.face = .floor) :
    connectedDirection s = .up := by
  simp [connectedDirection, h]

/-- A lever on the ceiling is attached to the block above it. -/
theorem connectedDirection_ceiling (s : Blocks.Lever) (h : s.face = .ceiling) :
    connectedDirection s = .down := by
  simp [connectedDirection, h]

/-- A lever on a wall points away from the block it is attached to. -/
theorem connectedDirection_wall (s : Blocks.Lever) (h : s.face = .wall) :
    connectedDirection s = s.facing.toDirection := by
  simp [connectedDirection, h]

/-- Switching a lever does not change where it is attached. -/
@[simp]
theorem connectedDirection_toggle (s : Blocks.Lever) :
    connectedDirection (toggle s) = connectedDirection s := rfl

/-- Switching a lever does not change whether it is supported. -/
@[simp]
theorem canSurvive_toggle (s : Blocks.Lever) (l : Level) (p : Pos) :
    canSurvive (toggle s) l p = canSurvive s l p := rfl

/-- A use negates `powered`. -/
@[simp]
theorem powered_toggle (s : Blocks.Lever) : (toggle s).powered = !s.powered := rfl

/-- Two uses give the state back. -/
@[simp]
theorem toggle_toggle (s : Blocks.Lever) : toggle (toggle s) = s := by
  cases s
  simp [toggle]

/-- **The signal of a lever**: 15 to every neighbour while it is on, nothing while it is off. -/
theorem signal_lever (s : Blocks.Lever) (l : Level) (p : Pos) (d : Direction) :
    (behaviour (.lever s)).signal l p d = if s.powered then 15 else 0 := rfl

/-- The own signal of a lever is its signal. -/
theorem ownSignal_lever (s : Blocks.Lever) (l : Level) (p : Pos) :
    (behaviour (.lever s)).ownSignal l p = if s.powered then 15 else 0 := rfl

/-- **The strong power of a lever**: 15 while it is on, and only into the block it is attached
to. Here `d` points from the block that is asked to the lever, as in
`getDirectSignal(pos, direction)`, so the block the lever is attached to asks with
`connectedDirection s`. -/
theorem directSignal_lever (s : Blocks.Lever) (l : Level) (p : Pos) (d : Direction) :
    (behaviour (.lever s)).directSignal l p d =
      if s.powered = true ∧ connectedDirection s = d then 15 else 0 := by
  change (if (s.powered && decide (connectedDirection s = d)) = true then 15 else 0) = _
  by_cases h : s.powered = true <;> by_cases h' : connectedDirection s = d <;> simp [h, h']

/-- A lever that is on powers the block it is attached to strongly. -/
theorem directSignal_attachment (s : Blocks.Lever) (l : Level) (p : Pos)
    (h : s.powered = true) :
    (behaviour (.lever s)).directSignal l p (connectedDirection s) = 15 := by
  simp [directSignal_lever, h]

/-- A lever gives no strong power to a block it is not attached to. -/
theorem directSignal_of_ne (s : Blocks.Lever) (l : Level) (p : Pos) (d : Direction)
    (h : connectedDirection s ≠ d) : (behaviour (.lever s)).directSignal l p d = 0 := by
  simp [directSignal_lever, h]

/-! ### Using a lever -/

/-- **A use of a lever is `pull`**, and the lever always consumes the use. -/
theorem useWithoutItem_lever (s : Blocks.Lever) (p : Pos) (face : Direction) :
    (behaviour (.lever s)).useWithoutItem p face = (do pull s p; return true) := rfl

/-- **`pull` toggles the lever and updates its neighbours.** It writes the lever with `powered`
negated at `p`, sends neighbour updates around `p` and around the block the lever is attached
to, and sends the game event of the new state. -/
theorem pull_eq (s : Blocks.Lever) (p : Pos) :
    pull s p = (do
      discard <| Level.setBlock p (.lever (toggle s))
      Level.updateNeighborsAt p .lever
      Level.updateNeighborsAt (p.step (connectedDirection s).opposite) .lever
      Level.gameEvent
        (if (toggle s).powered then "minecraft:block_activate" else "minecraft:block_deactivate")
        p) := rfl

/-! ### Support -/

/-- The reaction of a lever to a shape update, written out: the level is read and not
changed. -/
theorem updateShape_lever (s : Blocks.Lever) (p q : Pos) (d : Direction) (b : Block)
    (env : Env) (l : Level) :
    (behaviour (.lever s)).updateShape p d q b env l =
      (if (connectedDirection s).opposite = d ∧ canSurvive s l p = false then .AIR else .lever s,
        l) := by
  change (if ((connectedDirection s).opposite = d && !canSurvive s l p) = true then
    (pure Block.AIR : M Block) else pure (Block.lever s)) env l = _
  by_cases hd : (connectedDirection s).opposite = d <;> cases h : canSurvive s l p <;>
    simp [hd] <;> rfl

/-- **A lever that lost its support becomes air.** A shape update from the block the lever is
attached to, when that block no longer has a sturdy face towards the lever, answers air. -/
theorem updateShape_of_unsupported (s : Blocks.Lever) (p q : Pos) (d : Direction) (b : Block)
    (env : Env) (l : Level) (hd : (connectedDirection s).opposite = d)
    (h : canSurvive s l p = false) :
    (behaviour (.lever s)).updateShape p d q b env l = (.AIR, l) := by
  simp [updateShape_lever, hd, h]

/-- A lever that still has its support stays, whichever neighbour sent the shape update. -/
theorem updateShape_of_supported (s : Blocks.Lever) (p q : Pos) (d : Direction) (b : Block)
    (env : Env) (l : Level) (h : canSurvive s l p = true) :
    (behaviour (.lever s)).updateShape p d q b env l = (.lever s, l) := by
  simp [updateShape_lever, h]

/-- A shape update from a block the lever is not attached to leaves the lever as it is. -/
theorem updateShape_of_ne (s : Blocks.Lever) (p q : Pos) (d : Direction) (b : Block)
    (env : Env) (l : Level) (hd : (connectedDirection s).opposite ≠ d) :
    (behaviour (.lever s)).updateShape p d q b env l = (.lever s, l) := by
  simp [updateShape_lever, hd]

end Redstone.Component.Lever
