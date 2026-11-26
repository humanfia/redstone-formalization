module

public import Redstone.Basic.Direction
public import Redstone.Basic.Signal

/-!
# Blocks

The blocks the formalization knows about, together with the part of their block state that
matters for redstone.

This inventory is provisional. It is meant to be extended as components are formalized, and the
following points are left open on purpose:

* Blocks in motion (the moving piston block) are not represented yet.
* The connection shape of redstone dust is not stored; whether it becomes part of the state or
  is derived from the neighbourhood is to be decided in `Redstone.Component.Dust`.
* Constraints between fields (a repeater faces a horizontal direction, a lever is attached to
  a face that can support it, ...) are not enforced by the type. They will be stated as
  well-formedness predicates on worlds.

No behaviour is defined here: which blocks conduct, which can be pushed and so on belongs to
`Redstone.Mechanics`.
-/

@[expose] public section

namespace Redstone

/-- The two kinds of piston. -/
inductive PistonKind
  | normal
  | sticky
  deriving DecidableEq, Repr, Fintype

/-- The two modes of a comparator. -/
inductive ComparatorMode
  | compare
  | subtract
  deriving DecidableEq, Repr, Fintype

/-- The delay setting of a repeater. The value `n` stands for a delay of `n + 1` redstone
ticks, so the four settings are 1 to 4 redstone ticks. -/
abbrev RepeaterDelay := Fin 4

/-- A block together with its redstone-relevant state. -/
inductive Block
  /-- An empty cell. -/
  | air
  /-- An ordinary opaque full block, such as stone. -/
  | solid
  /-- A full block that pistons cannot move, such as obsidian. -/
  | immovable
  /-- A slime block. -/
  | slime
  /-- A honey block. -/
  | honey
  /-- A block of redstone. -/
  | redstoneBlock
  /-- A lever attached to the neighbouring block in direction `attached`. -/
  | lever (attached : Direction) (on : Bool)
  /-- Redstone dust carrying the signal `power`. -/
  | dust (power : Signal)
  /-- A redstone torch attached to the neighbouring block in direction `attached`. -/
  | torch (attached : Direction) (lit : Bool)
  /-- A repeater whose output points in direction `facing`. -/
  | repeater (facing : Direction) (delay : RepeaterDelay) (powered : Bool) (locked : Bool)
  /-- A comparator whose output points in direction `facing`. -/
  | comparator (facing : Direction) (mode : ComparatorMode) (output : Signal)
  /-- The base of a piston whose head points in direction `facing`. -/
  | piston (kind : PistonKind) (facing : Direction) (extended : Bool)
  /-- The head of an extended piston, pointing in direction `facing`. -/
  | pistonHead (kind : PistonKind) (facing : Direction)
  /-- An observer watching the neighbouring block in direction `facing`. Its output is on the
  opposite side. -/
  | observer (facing : Direction) (powered : Bool)
  deriving DecidableEq, Repr

namespace Block

instance : Inhabited Block := ⟨air⟩

/-- A cell is empty when it holds `air`. -/
def IsAir (b : Block) : Prop := b = air

instance : DecidablePred IsAir := fun b => by
  unfold IsAir
  infer_instance

@[simp]
theorem isAir_air : IsAir air := rfl

end Block

end Redstone
