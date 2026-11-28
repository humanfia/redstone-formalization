module

public import Redstone.Block.Generated.Attrs
public import Redstone.Block.Generated.BlockEntity
public import Redstone.Block.Generated.Fluid

/-!
# Blocks

The block inventory itself is generated from the server (`Redstone.Block.Generated`): the type
`Block` of block states, `BlockId`, the attributes `Block.attrs` and the block entities. This
file adds the few definitions about blocks that everything else uses.

A block state is written `minecraft:id[prop=value,...]`, with every property listed and the
properties sorted by name.
-/

@[expose] public section

namespace Redstone

namespace BlockId

/-- The block with the given registry name. -/
def ofName? (name : String) : Option BlockId := all.find? (·.name == name)

end BlockId

namespace Block

/-- Air: the state of an empty cell, `Block.default .air` (`AIR_eq_default`). It is written
with its constructor because every read of an empty cell gives it: the kernel would otherwise
go through the whole of `Block.default` each time. -/
def AIR : Block := .plain .air

theorem AIR_eq_default : AIR = Block.default .air := rfl

instance : Inhabited Block := ⟨AIR⟩

/-- `f b` (`pinned_eq`), with `b` evaluated first when it is a block without properties, so
that `f` is applied to the block written out: `f (.plain .stone)`, not `f` of whatever
expression gave the block.

This is for the Lean kernel, which evaluates lazily and remembers results by the term they
came from. A function of a block that is expensive to evaluate (the table of behaviours, which
is a match over every kind of block) is evaluated again for every expression that stands for
the block; applied to the written-out block it is evaluated once for air, once for stone, and
so on. Most cells around a circuit are air or a plain solid block. -/
def pinned.{u} {α : Sort u} (b : Block) (f : Block → α) : α :=
  match b with
  | .plain i => f (.plain i)
  | _ => f b

theorem pinned_eq.{u} {α : Sort u} (b : Block) (f : Block → α) : b.pinned f = f b := by
  cases b <;> rfl

/-- `BlockState.isAir`. There are three kinds of air, so this is weaker than `b = AIR`. -/
def isAir (b : Block) : Bool := b.attrs.air

/-- `BlockState.is(Block)`: the state belongs to the block `id`. -/
def is (b : Block) (id : BlockId) : Bool := b.id == id

/-- `BlockState.isRedstoneConductor`: the block passes on the power it receives. Every signal
query asks this of the block it reads, so it is looked up through `pinned`. -/
def isConductor (b : Block) : Bool := b.pinned fun b => b.attrs.conductor

/-- The block is a rail of some kind (`BaseRailBlock`). -/
def isRail (b : Block) : Bool :=
  b.id == .rail || b.id == .powered_rail || b.id == .detector_rail || b.id == .activator_rail

/-- `BlockState.hasBlockEntity`. -/
def hasBlockEntity (b : Block) : Bool := b.attrs.hasBlockEntity

/-- The state written as a string. -/
def toString (b : Block) : String :=
  match b.toProps with
  | [] => b.id.name
  | props => b.id.name ++ "[" ++ ",".intercalate (props.map fun (k, v) => k ++ "=" ++ v) ++ "]"

instance : ToString Block := ⟨toString⟩

/-- Reads a state from a string. Every property of the block must be given. -/
def parse? (s : String) : Option Block := do
  let (name, rest) :=
    match s.splitOn "[" with
    | [name] => (name, "")
    | [name, rest] => (name, rest.replace "]" "")
    | _ => ("", "")
  let id ← BlockId.ofName? name
  let props := (rest.splitOn ",").filterMap fun (kv : String) =>
    match kv.splitOn "=" with
    | [k, v] => some (k, v)
    | _ => none
  ofProps? id fun k => (props.find? (·.1 == k)).map (·.2)

/-- `getFluidState().createLegacyBlock()`: what is left when the block is removed. This is air,
except for a block that holds a fluid, which leaves the fluid behind.

It is computed from the block's constructor, without strings, so that the kernel can evaluate
the removal of a block. It is the block state named by the attribute `Attrs.fluid`:
`tools/gen/gen_fluid.py` checks this for every block state when it writes `Block.fluidState`. -/
def fluidBlock (b : Block) : Block := b.fluidState.createLegacyBlock

/-- `state.setValue(WATERLOGGED, false)` if the state has the property and it is true. -/
def clearWaterlogged (b : Block) : Block :=
  if b.waterlogged? = some true then b.setWaterlogged false else b

end Block

end Redstone
