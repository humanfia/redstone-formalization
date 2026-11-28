module

public import Redstone.Mechanics.Tick

/-!
# Inputs

What reaches the world from outside between two game ticks: a player using a block, a block
being set or destroyed, an entity appearing or disappearing. These are the actions of the
scenarios that the test harness plays on the real server (`tests/FORMAT.md`), and the inputs of
the circuits that theorems are about.

A `Schedule` says which inputs arrive before which tick. `Rules.runSchedule` plays it: the
inputs of a tick are applied in order, then the game tick runs, exactly as the harness does.
-/

@[expose] public section

namespace Redstone

/-- An action on the world from outside. -/
inductive Input
  /-- A player uses the block at `p` with an empty hand on the face `face`
  (`BlockState.useWithoutItem`). -/
  | use (p : Pos) (face : Direction)
  /-- A player uses the item named `item` on the face `face` of the block at `p`
  (`ServerPlayerGameMode.useItemOn`, as far as `Level.useItemOn` models it). -/
  | useItem (p : Pos) (face : Direction) (item : String)
  /-- `Level.setBlock(p, b, flags)`. -/
  | set (p : Pos) (b : Block) (flags : ℕ := UpdateFlag.all)
  /-- `Level.destroyBlock(p, drop)`. -/
  | destroy (p : Pos) (drop : Bool := false)
  /-- The entity with the given index is discarded. -/
  | kill (index : ℕ)
  /-- An entity of the type named `type` is added at `pos`, as `/summon` does, with the saved
  data `nbt` (`EntityType.loadEntityRecursive`, then `addFreshEntity`). -/
  | summon (type : String) (pos : Vec3) (nbt : Nbt := .compound [])

namespace Input

/-- The vector saved as a list of three doubles, such as `Motion`. -/
def vec3? (t : Nbt) : Option Vec3 :=
  match t with
  | .list [.double x, .double y, .double z] =>
    some ⟨.ofBits (.ofNat x), .ofBits (.ofNat y), .ofBits (.ofNat z)⟩
  | _ => none

/-- Applies an input to the level.

A summoned entity takes its velocity and its `OnGround` flag from `nbt` (`Motion`, `OnGround`,
as `Entity.load` reads them); without them it is at rest and not on the ground. Data of the
entity that the game sets when it is summoned and that is not in `nbt` (the private random
numbers of a lightning bolt, for instance) is not modelled; an entity whose data cannot be read
sets `Level.overflow`. -/
def apply : Input → M Unit
  | .use p face => discard <| Level.useWithoutItem p face
  | .useItem p face item => discard <| Level.useItemOn p face item
  | .set p b flags => discard <| Level.setBlock p b flags
  | .destroy p drop => discard <| Level.destroyBlock p drop
  | .kill index => Level.removeEntity index
  | .summon type pos nbt =>
    match EntityData.ofNbt? type nbt with
    | some data =>
      let motion := ((nbt.get? "Motion").bind vec3?).getD ⟨0, 0, 0⟩
      discard <| Level.addEntity ⟨pos, motion, nbt.boolD "OnGround" false⟩ data
    | none => Level.setOverflow

end Input

/-- The inputs of a run: entry `t` of the list holds the inputs that arrive before game tick
`t + 1`, in order. -/
abbrev Schedule := List (List Input)

namespace Schedule

/-- `n` game ticks without input. -/
def idle (n : ℕ) : Schedule := List.replicate n []

/-- `n` game ticks, with the inputs `is` before the first of them. -/
def first (is : List Input) (n : ℕ := 1) : Schedule :=
  match n with
  | 0 => []
  | n + 1 => is :: idle n

end Schedule

namespace Rules

/-- The level after an input. -/
def input (r : Rules) (i : Input) (l : Level) : Level := (r.run i.apply l).2

/-- The level after the inputs `is`, in order, and then one game tick. -/
def stepWith (r : Rules) (is : List Input) (l : Level) : Level :=
  r.step (is.foldl (fun l i => r.input i l) l)

/-- The level after a schedule: for each entry, its inputs and then one game tick. -/
def runSchedule (r : Rules) (s : Schedule) (l : Level) : Level :=
  s.foldl (fun l is => r.stepWith is l) l

end Rules

end Redstone
