module

public import Redstone.Mechanics.Tick
public import Redstone.Basic.Xoroshiro
public import Redstone.Entity.Still

/-!
# Other blocks that react to redstone or to pistons

Java classes: `AbstractSkullBlock` (with `SkullBlock`, `WallSkullBlock`, `WitherSkullBlock`,
`WitherWallSkullBlock`, `PlayerHeadBlock`, `PlayerWallHeadBlock`, `PiglinWallSkullBlock`),
`SpongeBlock`, `FrostedIceBlock` (with `IceBlock.melt`), `PotentSulfurBlock` (with the
server-side tickers of `PotentSulfurBlockEntity`), `SlimeBlock`, `HoneyBlock`,
`RedStoneOreBlock`.

## What is modelled

* Skulls and heads: `neighborChanged` copies the neighbour signal into `powered`. The server
  gives them no block entity ticker.
* Sponge: `onPlace` and `neighborChanged` absorb the water around it, by the breadth-first
  search of `removeWaterBreadthFirstSearch`, and the sponge becomes a wet sponge.
* Frosted ice: `onPlace`, `tick` and `neighborChanged`, with the draws from the level's random
  generator.
* Potent sulfur: `updateShape`, `onPlace`, `triggerEvent`, which states tick their block
  entity, and the countdown ticker that alternates `dormant` and `erupting`.
* Slime block: `stepOn`, which slows down an entity that walks on it.
* Honey block: `entityInside`, which makes an entity slide down its sides.
* Redstone ore: `stepOn`, which lights it up.

## What is left out

* Fluids do not flow in the model. A sponge that leaves water behind, or ice that melts next to
  an empty cell, is followed on the server by flowing water that the model does not have.
* Light. `FrostedIceBlock.tick` melts only where `getMaxLocalRawBrightness` exceeds
  `11 - age - getLightDampening`; the model takes this to hold, as it does under the open sky
  by day. Frosted ice in the dark does not melt in the game.
* Dimensions. Water evaporates in the Nether (`WATER_EVAPORATES`): there ice leaves air and a
  wet sponge dries when placed. The model is the Overworld.
* `SpongeBlock`: a block that holds water without being a `BucketPickup` is skipped by the
  game. The model takes every block with the property `waterlogged`, except the barrier, to be
  a `SimpleWaterloggedBlock`. Whether a drained block can stay is asked of its own behaviour
  (`canSurvive`). Kelp and seagrass drop nothing; what the plants next to them do when the
  water goes is theirs to model.
* `PotentSulfurBlockEntity`: the tickers that act on entities (`LAUNCH_ENTITY_TICKER`,
  `SERVER_NAUSEA_EFFECT_TICKER`), the client-side tickers and `eruptionTick`. Whether a block
  lets a geyser through is read from its collision shape in an empty world; this is wrong for
  a moving piston, whose shape is that of its block entity. The world seed, from which the
  phase lengths are drawn, is the constant `worldSeed`.
* A ticker bound to another state than the block's. When sulfur is put where a block stood
  whose removal makes a neighbour change (a powered lever next to a skull, say), the shape
  update of that neighbour turns the new sulfur `dry` inside `LevelChunk.setBlockState`, before
  its block entity exists; the outer call then binds the ticker of the state that was asked for
  (`BlockEntity.setBlockState` followed by `updateBlockEntityTicker`). The game so runs the
  countdown ticker of an `erupting` block on a `dry` one, which becomes `dormant` at the next
  multiple of 20 ticks. The model keeps the ticker in the list, as the game does, but runs the
  ticker of the state the block has, which for `dry` does nothing. Modelling this needs the
  level to remember the state each ticker was bound with
  (`tests/pending/scenarios/extra/adv-fuzz-a-020.json`).
* `WitherSkullBlock.setPlacedBy` (building a wither), `getStateForPlacement`: players do not
  place blocks.
* `SlimeBlock.fallOn` and `HoneyBlock.fallOn`: fall damage. That pistons move the blocks
  attached to slime and honey belongs to the piston.
* `RedStoneOreBlock.attack` (players do not hit blocks), `useItemOn`, whose result depends on
  whether the item in hand could be placed, `randomTick`, which puts lit ore out again (random
  ticks are not modelled), and the experience it drops.
-/

@[expose] public section

namespace Redstone.Component.Extra

/-! ### The level's random generator -/

/-- `level.getRandom().nextInt(bound)`. -/
def nextInt (bound : ℕ) : M ℕ :=
  modifyGet fun l =>
    let (v, r) := l.random.nextInt bound
    (v, { l with random := r })

/-- `Mth.nextInt(level.getRandom(), min, max)`: a number from `min` to `max`, both included. -/
def mthNextInt (min max : ℕ) : M ℕ := do
  if min ≥ max then return min else return (← nextInt (max - min + 1)) + min

/-! ### Skulls -/

/-- The property `powered` of a skull or head, and the same state with another value of it. -/
def skullPowered? : Block → Option (Bool × (Bool → Block))
  | .skull i s => some (s.powered, fun v => .skull i { s with powered := v })
  | .wallSkull i s => some (s.powered, fun v => .wallSkull i { s with powered := v })
  | .witherSkull s => some (s.powered, fun v => .witherSkull { s with powered := v })
  | .witherWallSkull s => some (s.powered, fun v => .witherWallSkull { s with powered := v })
  | .playerHead s => some (s.powered, fun v => .playerHead { s with powered := v })
  | .playerWallHead s => some (s.powered, fun v => .playerWallHead { s with powered := v })
  | .piglinWallSkull s => some (s.powered, fun v => .piglinWallSkull { s with powered := v })
  | _ => none

/-- The behaviour of a skull or head (`AbstractSkullBlock`). `getTicker` returns no ticker on
the server. -/
def skull (self : Block) (powered : Bool) (setPowered : Bool → Block) : Behaviour :=
  { Behaviour.inert self with
    neighborChanged := fun p _ _ => do
      let signal ← Level.hasNeighborSignal p
      if signal != powered then discard <| Level.setBlock p (setPowered signal) 2 }

/-! ### Sponge -/

/-- `getFluidState().is(FluidTags.WATER)`: the block holds water, still or flowing. -/
def holdsWater (b : Block) : Bool := b.fluidState.fluid.isWater

/-- The state with the property `waterlogged` set to false, for a state that has it set. -/
def drained? (b : Block) : Option Block :=
  if b.waterlogged? = some true then some (b.setWaterlogged false) else none

/-- The node processor of `SpongeBlock.removeWaterBreadthFirstSearch`: removes the water at `p`.
Returns whether the search goes on from `p` (`ACCEPT`) or not (`SKIP`). -/
def absorbAt (start p : Pos) : M Bool := do
  if p = start then return true
  let state ← Level.getBlock p
  if !holdsWater state then return false
  match state with
  | .liquid _ s =>
    -- `LiquidBlock.pickupBlock` takes a source; the search itself removes flowing water.
    discard <| Level.setBlock p .AIR (if s.level.val = 0 then 11 else 3)
    return true
  | .bubbleColumn _ =>
    -- `BubbleColumnBlock.pickupBlock`
    discard <| Level.setBlock p .AIR 11
    return true
  | _ =>
    if state.is .kelp || state.is .kelp_plant || state.is .seagrass || state.is .tall_seagrass
    then
      discard <| Level.setBlock p .AIR 3
      return true
    else if state.is .barrier then return false
    else
      -- `SimpleWaterloggedBlock.pickupBlock`
      let some dry := drained? state | return false
      discard <| Level.setBlock p dry 3
      if !(← Level.behaviour state).canSurvive (← get) p then
        discard <| Level.destroyBlock p true
      return true

/-- `BlockPos.breadthFirstTraversal` as the sponge uses it: at most 65 positions are accepted,
at most six steps from the sponge, and the neighbours of an accepted position are visited in
the order of `Direction.values`. `queue` holds the positions to visit with their depth. Returns
the number of accepted positions. The queue never holds more than `1 + 6 * 64` entries over the
whole search, which bounds the number of steps. -/
def absorbLoop (start : Pos) : ℕ → List (Pos × ℕ) → List Pos → ℕ → M ℕ
  | _, [], _, count => return count
  | 0, _ :: _, _, count => do
    Level.setOverflow
    return count
  | fuel + 1, (p, depth) :: queue, visited, count => do
    if visited.contains p then absorbLoop start fuel queue visited count
    else if ← absorbAt start p then
      let count := count + 1
      if count ≥ 65 then return count
      let next := if depth < 6 then Direction.values.map fun d => (p.step d, depth + 1) else []
      absorbLoop start fuel (queue ++ next) (p :: visited) count
    else absorbLoop start fuel queue (p :: visited) count

/-- `SpongeBlock.tryAbsorbWater`: the sponge becomes wet if it absorbed any water. -/
def tryAbsorbWater (p : Pos) : M Unit := do
  if (← absorbLoop p 512 [(p, 0)] [] 0) > 1 then
    discard <| Level.setBlock p (.plain .wet_sponge) 2

/-- The behaviour of a sponge (`SpongeBlock`). -/
def sponge (self : Block) : Behaviour :=
  { Behaviour.inert self with
    onPlace := fun p old _ => do
      if !old.is .sponge then tryAbsorbWater p
    neighborChanged := fun p _ _ => tryAbsorbWater p }

/-! ### Frosted ice -/

/-- `FrostedIceBlock.fewerNeigboursThan(level, pos, limit)`: fewer than `limit` of the six
neighbours are frosted ice. -/
def fewerNeighboursThan (l : Level) (p : Pos) (limit : ℕ) : Bool :=
  (Direction.values.filter fun d => (l.blockAt (p.step d)).is .frosted_ice).length < limit

/-- `IceBlock.melt`, in a dimension where water does not evaporate: the ice becomes water. -/
def melt (p : Pos) : M Unit := do
  discard <| Level.setBlock p (Block.default .water) 3
  Level.neighborChanged p .water
  Level.gameEvent "minecraft:block_destroy" p

/-- `FrostedIceBlock.slightlyMelt`: the ice ages, or melts if it is at the last age. Returns
whether it melted. -/
def slightlyMelt (s : Blocks.FrostedIce) (p : Pos) : M Bool := do
  if h : s.age.val < 3 then
    discard <| Level.setBlock p (.frostedIce { s with age := ⟨s.age.val + 1, by omega⟩ }) 2
    return false
  else
    melt p
    return true

/-- `FrostedIceBlock.tick`. The test on the brightness is taken to hold. -/
def frostedIceTick (s : Blocks.FrostedIce) (p : Pos) : M Unit := do
  let draw ← nextInt 3
  if draw = 0 || fewerNeighboursThan (← get) p 4 then
    if ← slightlyMelt s p then
      Direction.values.forM fun d => do
        let q := p.step d
        if let .frostedIce n ← Level.getBlock q then
          if !(← slightlyMelt n q) then Level.scheduleTick q .frosted_ice (← mthNextInt 20 40)
      return
  Level.scheduleTick p .frosted_ice (← mthNextInt 20 40)

/-- The behaviour of frosted ice (`FrostedIceBlock`). -/
def frostedIce (s : Blocks.FrostedIce) : Behaviour :=
  { Behaviour.inert (.frostedIce s) with
    onPlace := fun p _ _ => do Level.scheduleTick p .frosted_ice (← mthNextInt 60 120)
    tick := frostedIceTick s
    neighborChanged := fun p block _ => do
      if block = .frosted_ice && fewerNeighboursThan (← get) p 2 then melt p }

/-! ### Potent sulfur -/

/-- `PotentSulfurBlockEntity.GEYSER_SALT`, as the bits of the `long`. -/
def geyserSalt : ℕ := Xoroshiro.ofLong (-904011478)

/-- `PotentSulfurBlockEntity.geyserPositional(level, pos)`. -/
def geyserPositional (p : Pos) : Xoroshiro :=
  (Xoroshiro.ofSeed (worldSeed ^^^ geyserSalt)).forkAt p

/-- `getFluidState().isSourceOfType(Fluids.WATER)`. -/
def isWaterSource (b : Block) : Bool := b.attrs.fluid == "minecraft:water[level=0]"

/-- `PotentSulfurBlock.isSourceIfFluid`: the block holds no fluid, or a source. -/
def isSourceIfFluid (b : Block) : Bool :=
  b.attrs.fluid.isEmpty || b.attrs.fluid.endsWith "[level=0]"

/-- `PotentSulfurBlock.validBlockState`: the state the sulfur should have, given the blocks
above and below it. The tags `causes_continuous_geyser_eruptions` and
`causes_periodic_geyser_eruptions` hold lava and the magma block. Becoming a geyser resets the
countdown of the block entity. -/
def validBlockState (s : PotentSulfurState) (p : Pos) : M PotentSulfurState := do
  let l ← get
  if !isWaterSource (l.blockAt (p.step .up)) then return .dry
  let below := l.blockAt (p.step .down)
  if below.is .lava && isSourceIfFluid below then return .continuous
  else if below.is .magma_block && isSourceIfFluid below then
    if !(s = .erupting || s = .dormant) then
      if let some (.potentSulfur d) := l.blockEntities p then
        Level.setBlockEntity p (.potentSulfur { d with countdown := -1 })
    return if s = .erupting then s else .dormant
  else return .wet

/-- `PotentSulfurBlockEntity.isGeyserPassableBlock`: air, water, and the blocks whose collision
shape is empty for the geyser. The shape is the one of the block dump (shape 0 is the empty
shape), except for scaffolding, which only collides with what is above it and so never with a
geyser. -/
def isGeyserPassable (b : Block) : Bool :=
  b.isAir || b.is .water || b.is .scaffolding || b.attrs.collision == 0

/-- `PotentSulfurBlockEntity.findNoxiousGasSourceBlock`: the first position above a column of
at most four blocks of source water over the sulfur, if the geyser can pass through it. -/
def findNoxiousGasSourceBlock (l : Level) (origin : Pos) : Option Pos :=
  go 5 (origin.step .up)
where
  /-- Walks up from `p` for at most `n` positions. -/
  go : ℕ → Pos → Option Pos
    | 0, _ => none
    | n + 1, p =>
      let state := l.blockAt p
      if !isWaterSource state || (!state.is .water && !isGeyserPassable state) then
        if state.isAir || isGeyserPassable state then some p else none
      else go n (p.step .up)

/-- `PotentSulfurBlockEntity.SERVER_WAITING_COUNTDOWN_TICKER`, for the sulfur in state `s` at
`p`: every 20 game ticks the countdown goes down, and at zero a dormant geyser erupts and an
erupting one goes dormant. -/
def waitingCountdownTick (s : PotentSulfurState) (p : Pos) : M Unit := do
  let l ← get
  if l.gameTime % 20 ≠ 0 then return
  let some source := findNoxiousGasSourceBlock l p | return
  let some (.potentSulfur d) := l.blockEntities p | return
  let waterBlocks : ℤ := source.y - p.y - 1
  let countdown :=
    if d.countdown ≤ 0 then
      let random := geyserPositional p
      if s = .dormant then 10 * (waterBlocks - 1) + (random.nextIntBetweenInclusive 15 30).1
      else waterBlocks - 1 + (random.nextLong.2.nextIntBetweenInclusive 1 2).1
    else d.countdown
  let countdown := if countdown > 0 then countdown - 1 else countdown
  Level.setBlockEntity p (.potentSulfur { d with countdown := countdown })
  if countdown = 0 then
    let stateToSet : PotentSulfurState := if s = .dormant then .erupting else .dormant
    discard <| Level.setBlock p (.potentSulfur ⟨stateToSet⟩) 3
    if stateToSet = .dormant then Level.gameEvent "minecraft:block_deactivate" p

/-- The behaviour of potent sulfur (`PotentSulfurBlock`). -/
def potentSulfur (s : Blocks.PotentSulfur) : Behaviour :=
  let state := s.potent_sulfur_state
  { Behaviour.inert (.potentSulfur s) with
    -- `getTicker`: every state but `dry` has a server-side ticker.
    ticksBlockEntity := state ≠ .dry
    updateShape := fun p _ _ _ => return .potentSulfur ⟨← validBlockState state p⟩
    onPlace := fun p _ _ => do
      if state = .erupting || state = .continuous then
        Level.blockEvent p .potent_sulfur 0 0
        Level.gameEvent "minecraft:block_activate" p
    -- Sets `eruptionTick`, which the model does not keep.
    triggerEvent := fun _ _ _ => return true
    blockEntityTick := fun p => do
      -- The tickers that launch entities and make them nauseous are left out.
      if state = .dormant || state = .erupting then waitingCountdownTick state p }

/-! ### Slime block -/

/-- `SlimeBlock.stepOn`: an entity that walks on slime without bouncing is slowed down. Entities
of the model never step carefully (`isSteppingCarefully` is sneaking). -/
def slimeStepOn (index : ℕ) : M Unit :=
  Level.modifyEntity index fun e =>
    let m := e.base.motion
    let absDeltaY := m.y.abs
    if absDeltaY < 0.1 then
      let scale := 0.4 + absDeltaY * 0.2
      { e with base := { e.base with motion := ⟨m.x * scale, m.y * 1.0, m.z * scale⟩ } }
    else e

/-! ### Honey block -/

/-- `0.98F` as a `double`. -/
def drag : Float := (Float32.ofBits 0x3f7ae148).toFloat

/-- `HoneyBlock.getOldDeltaY`. -/
def honeyOldDeltaY (deltaY : Float) : Float := deltaY / drag + 0.08

/-- `HoneyBlock.getNewDeltaY`. -/
def honeyNewDeltaY (deltaY : Float) : Float := (deltaY - 0.08) * drag

/-- `HoneyBlock.isSlidingDown(pos, entity)` for an entity whose width is the `float` `width`:
the entity is in the air, below the top of the block, falling, and at the side of the block. -/
def honeyIsSlidingDown (p : Pos) (e : Entity) (width : Float32) : Bool :=
  if e.base.onGround then false
  else if e.base.pos.y > Float.ofInt p.y + 0.9375 - 1.0E-7 then false
  else if honeyOldDeltaY e.base.motion.y ≥ -0.08 then false
  else
    let dx := (Float.ofInt p.x + 0.5 - e.base.pos.x).abs
    let dz := (Float.ofInt p.z + 0.5 - e.base.pos.z).abs
    let overlapDistance := 0.4375 + (width / 2.0).toFloat
    dx + 1.0E-7 > overlapDistance || dz + 1.0E-7 > overlapDistance

/-- `HoneyBlock.doesEntityDoHoneyBlockSlideEffects`: living entities, minecarts, primed TNT and
boats. -/
def honeySlideEffects (e : Entity) : Bool :=
  match e.data with
  | .minecart _ _ | .tnt _ => true
  | .other type _ =>
    type.endsWith "_boat" || type.endsWith "_raft" ||
      ((Entity.Still.typeInfo? type).map (·.living)).getD false
  | _ => false

/-- `HoneyBlock.entityInside`: an entity that falls along the side of the block slides down
slowly (`doSlideMovement`) and its fall distance is reset. For the entities that show it
(`maybeDoSlideEffects`) the level's random generator is drawn from twice, for the sound and
for the particles. An entity whose width the model does not know sets `Level.overflow`. -/
def honeyEntityInside (p : Pos) (index : ℕ) : M Unit := do
  let some e := (← get).entity? index | return
  let some info := Entity.Still.info? e | Level.setOverflow
  if honeyIsSlidingDown p e info.width then
    let m := e.base.motion
    let old := honeyOldDeltaY m.y
    let motion : Vec3 :=
      if old < -0.13 then
        let horizontalReductionFactor := -0.05 / old
        ⟨m.x * horizontalReductionFactor, honeyNewDeltaY (-0.05), m.z * horizontalReductionFactor⟩
      else ⟨m.x, honeyNewDeltaY (-0.05), m.z⟩
    Level.modifyEntity index fun e =>
      { e with base := { e.base with motion := motion } }.resetFallDistance
    if honeySlideEffects e then
      discard <| nextInt 5
      discard <| nextInt 5

/-! ### Redstone ore -/

/-- `RedStoneOreBlock.interact`: the ore lights up. `spawnParticles` draws two numbers from the
level's random generator for every side of the block that is not covered by a block that hides
it (`isSolidRender`), on the server as well. -/
def redstoneOreInteract (id : Blocks.RedStoneOre.Id) (s : Blocks.RedStoneOre) (p : Pos) :
    M Unit := do
  for d in Direction.values do
    if !(← Level.getBlock (p.step d)).attrs.solidRender then
      modify fun l => { l with random := l.random.nextFloat24.2.nextFloat24.2 }
  if !s.lit then discard <| Level.setBlock p (.redStoneOre id { s with lit := true })

/-- The behaviour of redstone ore (`RedStoneOreBlock`): an entity that steps on it lights it
up. -/
def redstoneOre (id : Blocks.RedStoneOre.Id) (s : Blocks.RedStoneOre) : Behaviour :=
  { Behaviour.inert (.redStoneOre id s) with
    stepOn := fun p _ => redstoneOreInteract id s p }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .plain .sponge => sponge self
  | .plain .slime_block => { Behaviour.inert self with stepOn := fun _ i => slimeStepOn i }
  | .plain .honey_block => { Behaviour.inert self with entityInside := honeyEntityInside }
  | .redStoneOre id s => redstoneOre id s
  | .frostedIce s => frostedIce s
  | .potentSulfur s => potentSulfur s
  | _ =>
    match skullPowered? self with
    | some (powered, setPowered) => skull self powered setPowered
    | none => .inert self

end Redstone.Component.Extra
