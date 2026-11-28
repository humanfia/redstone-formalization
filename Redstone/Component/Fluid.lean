module

public import Redstone.Mechanics.Tick

/-!
# Fluids and the blocks they act on

Java classes: `LiquidBlock`, `BubbleColumnBlock`, `MagmaBlock`, `SoulSandBlock`, `SlabBlock`,
`ChainBlock`, `WaterloggedTransparentBlock`, `BarrierBlock`, `LightBlock`, `MangroveRootsBlock`,
`ConduitBlock`, `HeavyCoreBlock`, `CoralBlock`, `BaseCoralPlantTypeBlock` (with
`BaseCoralPlantBlock`, `CoralPlantBlock`, `BaseCoralFanBlock`, `CoralFanBlock`,
`BaseCoralWallFanBlock`, `CoralWallFanBlock`), `WetSpongeBlock`.

* Water and lava (`LiquidBlock`): `onPlace`, `neighborChanged` and `updateShape` ask for a
  fluid tick, after which the fluid flows (`Redstone.Mechanics.Fluid`). Lava next to water
  becomes obsidian or cobblestone, and basalt next to blue ice over soul soil
  (`shouldSpreadLiquid`). A water source over magma or soul sand asks for the block tick that
  starts a bubble column.
* Bubble columns: `tick` (`updateColumn`), `updateShape`, `canSurvive`.
* Coral: a coral block, coral, coral fan or wall fan without water next to it dies after 60 to
  99 game ticks (`tick`, `onPlace`, `updateShape`, with the draw from the level's random number
  generator); coral and fans break when their support goes.
* The other blocks of the list do nothing but hold water: a waterlogged one asks for a fluid
  tick whenever it gets a shape update. Magma, soul sand and the wet sponge do nothing at all
  here.

## What is left out

* `LavaFluid.randomTick`, through `LiquidBlock.randomTick`: lava sets fire to flammable blocks
  near it. It needs which blocks lava ignites and the state of a new fire
  (`BaseFireBlock.getState`), neither of which the model has yet; a random tick of lava sets
  `Level.overflow`. No block gets a random tick while `Level.randomTickSpeed` is zero.
* `BubbleColumnBlock.entityInside` (the column pushes or pulls entities), `MagmaBlock.stepOn`
  (damage to mobs), and the extinguishing and burning of entities in water and lava.
* `WetSpongeBlock.onPlace` dries the sponge only where water evaporates (the Nether); the model
  is the Overworld.
* `ConduitBlockEntity` (the conduit's power acts on players and mobs) and
  `LightBlock.useWithoutItem` (for players that can use game-master blocks).
* `getStateForPlacement`: players do not place blocks.

## Scenarios that wait for other components

A block that holds water asks for a fluid tick in its own `updateShape`, so the scheduled fluid
ticks of a scenario are only right once every block in it does. These scenarios wait under
`tests/pending` for the component of the block named:

* `fluid/into-kelp`, `fluid/flow-at-kelp`, and `extra/adv-sulfur-column-1` and `-2` (which
  agreed with the server while fluid ticks were not compared): kelp asks for a tick of its
  water (`KelpBlock.updateShape`, `Redstone.Component.Vine`).
* `fluid/flow-at-oak_leaves`: leaves schedule the tick that recomputes their distance
  (`LeavesBlock.updateShape`, `Redstone.Component.Ground`).
* `fluid/into-scaffolding`, `fluid/flow-at-scaffolding`: scaffolding schedules its tick
  (`ScaffoldingBlock`, `Redstone.Component.FallingStructure`).
* `fluid/into-oak_sign`: the block entity of a sign ticks (`SignBlock`,
  `Redstone.Component.Attached`).
* `fluid/into-campfire`, `fluid/into-campfire-lit-true`: the block entity of a campfire ticks
  (`CampfireBlock`, `Redstone.Component.SpecialBlock`).
* `extra/adv-sponge-unsupported`: a sponge drains hanging roots, a ladder and a lantern that
  then lose their support (`canSurvive` of `Redstone.Component.Attached`).
-/

@[expose] public section

namespace Redstone.Component.Fluid

/-- `level.getRandom().nextInt(bound)`. -/
def nextInt (bound : ℕ) : M ℕ :=
  modifyGet fun l =>
    let (v, r) := l.random.nextInt bound
    (v, { l with random := r })

/-- `ticks.scheduleTick(pos, Fluids.WATER, Fluids.WATER.getTickDelay(level))`. -/
def scheduleWaterTick (p : Pos) : M Unit := Level.scheduleFluidTick p .water Fluid.water.tickDelay

/-! ### Bubble columns -/

/-- `BubbleColumnBlock.canOccupy(bubbleColumn, state)`: the block is a bubble column or a source
block of water (`FluidTags.BUBBLE_COLUMN_CAN_OCCUPY` holds the water source only). -/
def canOccupy (b : Block) : Bool :=
  match b with
  | .bubbleColumn _ => true
  | .liquid .water s => s.level.val = 0
  | _ => false

/-- The block starts a bubble column in the water above it
(`BlockTags.ENABLES_BUBBLE_COLUMN_DRAG_DOWN` or `ENABLES_BUBBLE_COLUMN_PUSH_UP`): magma or
soul sand. -/
def enablesBubbleColumn (b : Block) : Bool :=
  FluidBlockTag.enables_bubble_column_drag_down b.id ||
    FluidBlockTag.enables_bubble_column_push_up b.id

/-- `BubbleColumnBlock.getColumnState(bubbleColumn, belowState, occupyState)`: what a cell of
the column over `below` becomes. It continues a column below it, starts one over soul sand
(upwards) or magma (downwards), and otherwise a bubble column goes back to water. -/
def getColumnState (below occupy : Block) : Block :=
  if below.is .bubble_column then below
  else if FluidBlockTag.enables_bubble_column_push_up below.id then .bubbleColumn ⟨false⟩
  else if FluidBlockTag.enables_bubble_column_drag_down below.id then .bubbleColumn ⟨true⟩
  else if occupy.is .bubble_column then Block.default .water
  else occupy

/-- The loop of `BubbleColumnBlock.updateColumn`: the cells above take the state `column` for
as long as they are water sources or bubble columns and change by it. The model's world has no
top; `fuel` bounds the height of the column. -/
def updateColumnLoop (column : Block) : ℕ → Pos → M Unit
  | 0, q => do if canOccupy (← Level.getBlock q) then Level.setOverflow
  | fuel + 1, q => do
    if canOccupy (← Level.getBlock q) then
      if ← Level.setBlock q column 2 then updateColumnLoop column fuel (q.step .up)

/-- `BubbleColumnBlock.updateColumn(bubbleColumn, level, occupyAt, occupyState, belowState)`. -/
def updateColumn (p : Pos) (occupy below : Block) : M Unit := do
  if canOccupy occupy then
    let column := getColumnState below occupy
    discard <| Level.setBlock p column 2
    updateColumnLoop column 1024 (p.step .up)

/-- `BubbleColumnBlock.canSurvive`. -/
def bubbleColumnCanSurvive (l : Level) (p : Pos) : Bool :=
  let below := l.blockAt (p.step .down)
  below.is .bubble_column || enablesBubbleColumn below

/-- The behaviour of a bubble column (`BubbleColumnBlock`). -/
def bubbleColumn (self : Block) : Behaviour :=
  { Behaviour.inert self with
    canSurvive := bubbleColumnCanSurvive
    tick := fun p => do updateColumn p self (← Level.getBlock (p.step .down))
    updateShape := fun p d _ neighbour => do
      scheduleWaterTick p
      if !bubbleColumnCanSurvive (← get) p || d = .down ||
          (d = .up && !neighbour.is .bubble_column && canOccupy neighbour) then
        Level.scheduleTick p .bubble_column 5
      return self }

/-! ### Water and lava -/

/-- `LiquidBlock.shouldBubbleColumnOccupy`: the block is a source block of water. -/
def shouldBubbleColumnOccupy (b : Block) : Bool :=
  let fluid := b.fluidState
  fluid.is .water && fluid.isFull

/-- `LiquidBlock.tryScheduleBubbleBlockColumn(ticks, pos, stateBelow)` for the liquid block
`block`. -/
def tryScheduleBubbleBlockColumn (p : Pos) (block : BlockId) (below : Block) : M Unit := do
  if enablesBubbleColumn below then Level.scheduleTick p block 20

/-- `LiquidBlock.shouldSpreadLiquid(level, pos, state)` for a liquid of the kind of `kind`.
Lava with water above it or next to it becomes obsidian (a source) or cobblestone, and lava
over soul soil next to blue ice becomes basalt; then the answer is no. The neighbours are
looked at in the order of `POSSIBLE_FLOW_DIRECTIONS`, each taken backwards: up, north, south,
west, east. -/
def shouldSpreadLiquid (kind : Fluid) (p : Pos) : M Bool := do
  if kind.isLava then
    let overSoulSoil := (← Level.getBlock (p.step .down)).is .soul_soil
    for d in [Direction.up, .north, .south, .west, .east] do
      let q := p.step d
      let l ← get
      if (l.fluidStateAt q).fluid.isWater then
        let product : BlockId := if (l.fluidStateAt p).isSource then .obsidian else .cobblestone
        discard <| Level.setBlock p (Block.default product)
        return false
      if overSoulSoil && (l.blockAt q).is .blue_ice then
        discard <| Level.setBlock p (Block.default .basalt)
        return false
  return true

/-- The behaviour of a block of water or lava (`LiquidBlock`). -/
def liquid (self : Block) : Behaviour :=
  let fluid := self.fluidState
  let react (p : Pos) : M Unit := do
    if ← shouldSpreadLiquid fluid.fluid p then
      Level.scheduleFluidTick p fluid.fluid fluid.fluid.tickDelay
    if shouldBubbleColumnOccupy self then
      tryScheduleBubbleBlockColumn p self.id (← Level.getBlock (p.step .down))
  { Behaviour.inert self with
    onPlace := fun p _ _ => react p
    neighborChanged := fun p _ _ => react p
    tick := fun p => do
      if shouldBubbleColumnOccupy self then
        let below ← Level.getBlock (p.step .down)
        updateColumn p (← Level.getBlock p) below
    updateShape := fun p d _ neighbour => do
      if fluid.isSource || neighbour.fluidState.isSource then
        Level.scheduleFluidTick p fluid.fluid fluid.fluid.tickDelay
      if d = .down && shouldBubbleColumnOccupy self then
        tryScheduleBubbleBlockColumn p self.id neighbour
      return self
    -- `LavaFluid.randomTick`: not modelled.
    randomTick := fun _ => do if fluid.fluid.isLava then Level.setOverflow }

/-! ### Blocks that only hold water -/

/-- The behaviour of a block that does nothing but, perhaps, hold water: `updateShape` asks for
a fluid tick when the block is waterlogged. -/
def waterlogged (self : Block) : Behaviour :=
  { Behaviour.inert self with
    updateShape := fun p _ _ _ => do
      if self.waterlogged? = some true then scheduleWaterTick p
      return self }

/-! ### Coral -/

/-- The dead block of a coral block (`CoralBlock.deadBlock`). -/
def deadCoralBlock? : BlockId → Option BlockId
  | .tube_coral_block => some .dead_tube_coral_block
  | .brain_coral_block => some .dead_brain_coral_block
  | .bubble_coral_block => some .dead_bubble_coral_block
  | .fire_coral_block => some .dead_fire_coral_block
  | .horn_coral_block => some .dead_horn_coral_block
  | _ => none

/-- The dead block of a coral (`CoralPlantBlock.deadBlock`). -/
def deadCoral : Blocks.CoralPlant.Id → Blocks.BaseCoralPlant.Id
  | .tube_coral => .dead_tube_coral
  | .brain_coral => .dead_brain_coral
  | .bubble_coral => .dead_bubble_coral
  | .fire_coral => .dead_fire_coral
  | .horn_coral => .dead_horn_coral

/-- The dead block of a coral fan (`CoralFanBlock.deadBlock`). -/
def deadCoralFan : Blocks.CoralFan.Id → Blocks.BaseCoralFan.Id
  | .tube_coral_fan => .dead_tube_coral_fan
  | .brain_coral_fan => .dead_brain_coral_fan
  | .bubble_coral_fan => .dead_bubble_coral_fan
  | .fire_coral_fan => .dead_fire_coral_fan
  | .horn_coral_fan => .dead_horn_coral_fan

/-- The dead block of a coral wall fan (`CoralWallFanBlock.deadBlock`). -/
def deadCoralWallFan : Blocks.CoralWallFan.Id → Blocks.BaseCoralWallFan.Id
  | .tube_coral_wall_fan => .dead_tube_coral_wall_fan
  | .brain_coral_wall_fan => .dead_brain_coral_wall_fan
  | .bubble_coral_wall_fan => .dead_bubble_coral_wall_fan
  | .fire_coral_wall_fan => .dead_fire_coral_wall_fan
  | .horn_coral_wall_fan => .dead_horn_coral_wall_fan

/-- `CoralBlock.scanForWater`: one of the six neighbours holds water. -/
def waterAround (l : Level) (p : Pos) : Bool :=
  Direction.values.any fun d => (l.fluidStateAt (p.step d)).fluid.isWater

/-- `ticks.scheduleTick(pos, block, 60 + random.nextInt(40))`: the tick at which coral dies. -/
def scheduleDieTick (p : Pos) (block : BlockId) : M Unit := do
  Level.scheduleTick p block (60 + (← nextInt 40))

/-- The behaviour of a coral block (`CoralBlock`), which becomes the block `dead`. -/
def coralBlock (self : Block) (dead : BlockId) : Behaviour :=
  { Behaviour.inert self with
    tick := fun p => do
      if !waterAround (← get) p then discard <| Level.setBlock p (Block.default dead) 2
    updateShape := fun p _ _ _ => do
      if !waterAround (← get) p then scheduleDieTick p self.id
      return self }

/-- `BaseCoralPlantTypeBlock.canSurvive`: the block below has a sturdy top. -/
def coralCanSurvive (l : Level) (p : Pos) : Bool :=
  (l.supportAttrs (p.step .down)).isFaceSturdy .up

/-- `BaseCoralWallFanBlock.canSurvive` for a fan that faces `facing`: the block behind it has a
sturdy face towards it. -/
def wallFanCanSurvive (facing : Direction) (l : Level) (p : Pos) : Bool :=
  (l.supportAttrs (p.step facing.opposite)).isFaceSturdy facing

/-- The behaviour of coral, a coral fan or a coral wall fan, dead or alive
(`BaseCoralPlantTypeBlock` and its subclasses).

* `waterlogged` is the property of the state.
* `dead` is the state the block dies to, for a living one (`deadBlock`, not waterlogged).
* `support` is the direction of the block that holds this one: down, or the back of a wall fan.
* `wall` says that the block is a wall fan, whose `updateShape` does the same things in
  another order.

A living block asks for its death, 60 to 99 game ticks ahead, when it is placed or gets a
shape update with no water in it or around it (`tryScheduleDieTick`). The fluid tick of a
waterlogged living block is asked for twice, by the class and by its superclass; the second
request changes nothing but the counter that orders the ticks. -/
def coral (self : Block) (waterlogged : Bool) (dead : Option Block) (support : Direction)
    (wall : Bool) : Behaviour :=
  let canSurvive (l : Level) (p : Pos) : Bool :=
    if wall then wallFanCanSurvive support.opposite l p else coralCanSurvive l p
  let inWater (l : Level) (p : Pos) : Bool := waterlogged || waterAround l p
  let tryScheduleDieTick (p : Pos) : M Unit := do
    if !inWater (← get) p then scheduleDieTick p self.id
  { Behaviour.inert self with
    canSurvive := canSurvive
    onPlace := fun p _ _ => do if dead.isSome then tryScheduleDieTick p
    tick := fun p => do
      if let some dead := dead then
        if !inWater (← get) p then discard <| Level.setBlock p dead 2
    updateShape := fun p d _ _ => do
      let unsupported := d = support && !canSurvive (← get) p
      if dead.isSome then
        if unsupported then return .AIR
        if wall then
          if waterlogged then scheduleWaterTick p
          tryScheduleDieTick p
        else
          tryScheduleDieTick p
          if waterlogged then scheduleWaterTick p
      if waterlogged then scheduleWaterTick p
      return if unsupported then .AIR else self }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .liquid _ _ => liquid self
  | .bubbleColumn _ => bubbleColumn self
  | .plain id =>
    match deadCoralBlock? id.toBlockId with
    | some dead => coralBlock self dead
    | none => .inert self
  | .baseCoralPlant _ s => coral self s.waterlogged none .down false
  | .baseCoralFan _ s => coral self s.waterlogged none .down false
  | .baseCoralWallFan _ s => coral self s.waterlogged none s.facing.toDirection.opposite true
  | .coralPlant id s =>
    coral self s.waterlogged (some (.baseCoralPlant (deadCoral id) ⟨false⟩)) .down false
  | .coralFan id s =>
    coral self s.waterlogged (some (.baseCoralFan (deadCoralFan id) ⟨false⟩)) .down false
  | .coralWallFan id s =>
    coral self s.waterlogged (some (.baseCoralWallFan (deadCoralWallFan id) ⟨s.facing, false⟩))
      s.facing.toDirection.opposite true
  | _ => waterlogged self

end Redstone.Component.Fluid
