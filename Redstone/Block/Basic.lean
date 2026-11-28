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

/-- Air: the state of an empty cell. -/
def AIR : Block := Block.default .air

instance : Inhabited Block := ⟨AIR⟩

/-- `BlockState.isAir`. There are three kinds of air, so this is weaker than `b = AIR`. -/
def isAir (b : Block) : Bool := b.attrs.air

/-- `BlockState.is(Block)`: the state belongs to the block `id`. -/
def is (b : Block) (id : BlockId) : Bool := b.id == id

/-- `BlockState.isRedstoneConductor`: the block passes on the power it receives. -/
def isConductor (b : Block) : Bool := b.attrs.conductor

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
