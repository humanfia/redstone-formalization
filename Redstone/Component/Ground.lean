module

public import Redstone.Mechanics.Tick
public import Redstone.Block.Generated.Tags
public import Redstone.Entity.Still
public import Redstone.Component.RandomTicked

/-!
# Ground and foliage, and the blocks that stay inert

Java classes: `FarmlandBlock`, `PathBlock`, `LeavesBlock` (with `TintedParticleLeavesBlock`,
`UntintedParticleLeavesBlock`, `MangroveLeavesBlock`), `SnowyBlock` (with `GrassBlock`,
`MyceliumBlock`, through `SpreadingSnowyBlock`), `NyliumBlock`, `HugeMushroomBlock`, `MudBlock`,
`RootedDirtBlock`; and, found by the audit below, `BeaconBlock`, `EndGatewayBlock`,
`EndPortalBlock`, `TrialSpawnerBlock`, `VaultBlock`, `AmethystBlock`, `PumpkinBlock`,
`CraftingTableBlock` (with `SmithingTableBlock`), `CartographyTableBlock`, `LoomBlock`,
`StonecutterBlock`, `EnchantingTableBlock`.

* Farmland and a dirt path turn to dirt under a solid block. A shape update from above
  schedules a tick one game tick later (`updateShape`), and the tick puts dirt there
  (`turnToBaseBlock`) and announces `block_change`. Farmland stays under the blocks of the tag
  `maintains_farmland` (crops, stems, fence gates and a moving piston), a path under a fence
  gate.
* Leaves keep in `distance` how far they are from a log (the tag
  `prevents_nearby_leaf_decay`), at most 7. A shape update schedules a tick one game tick
  later unless the neighbour is a log and the distance is already 1; the tick computes the
  distance afresh from the six neighbours. So the removal of a log runs through the leaves one
  step per game tick. Waterlogged leaves schedule the fluid tick of their water on every shape
  update. Leaves that are not persistent and at distance 7 decay on a random tick.
* Grass, podzol and mycelium are `snowy` when the block above is snow, a snow block or powder
  snow.
* A block of a huge mushroom closes the face towards a neighbour of its own kind.
* Farmland dries and gets wet on random ticks (`FarmlandBlock.randomTick`).

## What is not modelled

* `Block.pushEntitiesUp`: an entity inside the top sixteenth of farmland or of a path that turns
  to dirt is lifted by the game. Here that sets `Level.overflow`.
* `fallOn` (farmland trampled by a mob or a player, hay softening a fall): the model has no
  such hook, and no mobs or players as entities.
* The random ticks that need the dampening of light between two blocks
  (`LightEngine.getLightDampeningInto`): grass and mycelium dying and spreading
  (`SpreadingSnowyBlock.randomTick`) and nylium turning to netherrack (`NyliumBlock.randomTick`)
  set `Level.overflow`. Rain on farmland (`isRainingAt`): the world of the model has the biome
  of the test harness, the void, where it never rains.
* Bone meal (`BonemealableBlock`: grass, nylium, rooted dirt, mangrove leaves, moss,
  netherrack) and every other `ItemStack.useOn` (a hoe, a shovel).
* Placement (`getStateForPlacement`), particles and sounds.
* An entity inside an end portal or an end gateway would travel to another dimension:
  `Level.overflow`.
* A vault that is not `inactive` and a trial spawner that is not `inactive` or that has been
  given something to spawn: their block entities look for players, spawn mobs and eject loot.
  `Level.overflow`. An inactive vault and an inactive trial spawner without spawn data do
  nothing, since no player is in the world, and that is modelled.
* Carving a pumpkin with shears (`PumpkinBlock.useItemOn`) drops seeds as an item entity with
  a random motion, from a loot table: `Level.overflow`.
* The beacon's beam, its pyramid and its effects on players: none of it changes a block or
  draws from the level's random number generator, and the block entity's data is not kept.
* The cooldown counter of an end gateway, which is not saved: see `gatewayTick`.

## Scenarios still pending

`tests/pending/scenarios/ground` holds what the server does and the model does not yet:

* `ground-item-pushed-up`: an item on a path and on farmland that turn to dirt
  (`Block.pushEntitiesUp`); the model sets `Level.overflow`.
* `gateway-loaded-mid-cooldown`: an end gateway loaded with an age just past a multiple of
  2400, which has no cooldown in the game (see `gatewayTick`).
* `plants-dark-room`: crops and mushrooms in a closed room. It waits for block light
  (`Redstone.World.Light`, whose stub answers 15); see `Redstone.Component.Supported`.

## The blocks that stay inert

`python3 tools/gen/list_inert.py` lists the classes whose blocks no component covers, computed
from `Redstone/Block/Generated/families.json` and `tools/gen/components.json`; with `--hooks`
it prints the methods each class and its superclasses declare. This is that list for
Minecraft 26.3 after this component took the classes named above: 15 classes, 288 blocks.
"Nothing" means that the class declares no method beyond the constructor, the codec, the state
definition, placement, rotation, rendering, particles, path finding and bone meal, none of
which changes the level in a game tick of the model.

Each entry gives the Java class, its blocks, what it overrides, and why inert is right.

* `Block` (182 blocks: stone, planks, ores, wool, concrete, ...). Overrides nothing: it is
  `BlockBehaviour` itself.
* `AirBlock` (air, void_air, cave_air). `getRenderShape`, `getShape`: the shape is in `Attrs`.
* `RotatedPillarBlock` (60 blocks: logs, wood, pillars, basalt, ...). `rotate`, through
  `rotatePillar`: structure rotation only.
* `HayBlock` (hay_block; a `RotatedPillarBlock`). `fallOn`: the fall damage of living entities;
  the model has no such hook and no mobs.
* `GlazedTerracottaBlock` (16 blocks; a `HorizontalDirectionalBlock`). Nothing.
* `HalfTransparentBlock` (blue_ice). `skipRendering`: client only.
* `TransparentBlock` (glass). `getVisualShape`, `getShadeBrightness`,
  `propagatesSkylightDown`: rendering and light; what the light needs is in `Attrs`.
* `StainedGlassBlock` (16 blocks; a `TransparentBlock`). `getColor` of `BeaconBeamBlock`: the
  colour of a beacon beam, which is rendering.
* `TintedGlassBlock` (tinted_glass; a `TransparentBlock`). `getLightDampening`,
  `propagatesSkylightDown`: light attributes (`Redstone.World.Light`).
* `CryingObsidianBlock` (crying_obsidian). `animateTick`: particles.
* `BonemealableFeaturePlacerBlock` (moss_block, pale_moss_block). Bone meal only:
  `ItemStack.useOn` and the dispenser's bone meal place a world-generation feature, which is
  not modelled (see `Redstone.Component.Dispenser`).
* `NetherrackBlock` (netherrack). Bone meal only, as above.
* `StructureVoidBlock` (structure_void). `getShape`, `getRenderShape`, `getShadeBrightness`:
  the shape is in `Attrs`.
* `JigsawBlock` (jigsaw; block entity `jigsaw`, no ticker). `newBlockEntity`, `useWithoutItem`,
  `canAttach`: `useWithoutItem` opens the editing screen for a player who may use operator
  blocks and changes nothing in the level; `canAttach` is world generation.
* `TestInstanceBlock` (test_instance_block; block entity `test_instance_block`, no ticker).
  `newBlockEntity`, `useWithoutItem`: as the jigsaw, a screen for operators. Running a game
  test from it is not modelled (see `Redstone.Component.CommandBlock`).

`BaseEntityBlock`, the superclass of the blocks with a block entity, overrides `triggerEvent`
to pass a block event to the block entity (`BlockEntity.triggerEvent`, false unless the block
entity says otherwise). Of the inert blocks none queues a block event.

### What the audit found

Classes that no component covered and that override a hook the model has. They are now in this
component:

* **Block entity tickers** (`getTicker`; the list of tickers is compared with the server after
  every tick): `BeaconBlock` (`BeaconBlockEntity.tick`), `EndGatewayBlock`
  (`TheEndGatewayBlockEntity.portalTick`), `TrialSpawnerBlock` (`TrialSpawner.tickServer`),
  `VaultBlock` (`VaultBlockEntity.Server.tick`). `EnchantingTableBlock.getTicker` is null on the
  server, and `EndPortalBlock`, `JigsawBlock` and `TestInstanceBlock` have none. The other two
  classes with a ticker that the foundation had left unassigned, `ConduitBlock` and
  `SpawnerBlock`, belong to `Redstone.Component.Fluid` and `Redstone.Component.Loot`.
* **`TheEndGatewayBlockEntity.portalTick`** counts the age of the gateway and queues the block
  event `(1, 0)` every 2400 ticks of age (`triggerCooldown`), which the block entity accepts.
* **`AmethystBlock.onProjectileHit`** draws the pitch of the chime from the level's random
  number generator. `BuddingAmethystBlock` extends `AmethystBlock`, so the block reaches this
  component by its class chain; its behaviour is that of `Redstone.Component.RandomTicked` with
  the chime added. `AmethystClusterBlock` extends it too and belongs to
  `Redstone.Component.Attached`, **which does not have the chime yet**.
* **`entityInside`** of `EndPortalBlock` and `EndGatewayBlock` (portal travel, excluded).
* **`useItemOn`** of `PumpkinBlock` (shears) and of `VaultBlock` (a key in an active vault).
* **`useWithoutItem`** of the work stations (`CraftingTableBlock`, `SmithingTableBlock`,
  `CartographyTableBlock`, `LoomBlock`, `StonecutterBlock`, `EnchantingTableBlock`,
  `BeaconBlock`): the player opens a menu, nothing changes in the level, and the action is
  consumed.
-/

@[expose] public section

namespace Redstone.Component.Ground

/-! ### Farmland and paths -/

/-- The top sixteenth of the cell `p`: where the collision shape of dirt exceeds the one of
farmland and of a path. -/
def raisedBox (p : Pos) : AABB := (⟨0.0, 0.9375, 0.0, 1.0, 1.0, 1.0⟩ : AABB).atBlock p

/-- `Block.pushEntitiesUp(state, newState, level, pos)` for farmland or a path that becomes a
full block: the entities in the part that is added are moved up. The model does not move them:
if there is one, or an entity whose box it does not know, `Level.overflow` is set. Without
entities nothing happens. -/
def pushEntitiesUp (p : Pos) : M Unit := do
  let touched := (← get).entities.any fun e =>
    match Entity.Still.boundingBox? e with
    | some box => box.intersects (raisedBox p)
    | none => true
  if touched then Level.setOverflow

/-- `turnToBaseBlock(sourceEntity, state, level, pos)` of `FarmlandBlock` and `PathBlock`, whose
base block is dirt: the block becomes dirt and `block_change` is announced. -/
def turnToBaseBlock (p : Pos) : M Unit := do
  pushEntitiesUp p
  let newState : Block := .plain .dirt
  discard <| Level.setBlock p newState
  Level.gameEvent "minecraft:block_change" p { affectedState := some newState }

/-- `FarmlandBlock.shouldMaintainFarmland(level, pos)`. -/
def shouldMaintainFarmland (l : Level) (p : Pos) : Bool :=
  BlockTag.maintains_farmland (l.blockAt (p.step .up)).id

/-- `FarmlandBlock.canSurvive`: the block above is not solid, or it is one that maintains
farmland. -/
def farmlandCanSurvive (l : Level) (p : Pos) : Bool :=
  !(l.blockAt (p.step .up)).attrs.solid || shouldMaintainFarmland l p

/-- `PathBlock.canSurvive`: the block above is not solid, or it is a fence gate. -/
def pathCanSurvive (l : Level) (p : Pos) : Bool :=
  let above := l.blockAt (p.step .up)
  !above.attrs.solid || BlockClass.fenceGateBlock above.id

/-- `updateShape` of `FarmlandBlock` and `PathBlock`: when the block above changes and the block
cannot stay, a tick is scheduled one game tick later. -/
def groundUpdateShape (self : Block) (canSurvive : Level → Pos → Bool) (p : Pos)
    (d : Direction) : M Block := do
  if d = .up && !canSurvive (← get) p then Level.scheduleTick p self.id 1
  return self

/-- `FarmlandBlock.isNearWater(level, pos)`: there is water within four blocks horizontally, at
the height of the farmland or one above. -/
def isNearWater (l : Level) (p : Pos) : Bool :=
  (List.range 9).any fun dx => (List.range 2).any fun dy => (List.range 9).any fun dz =>
    (l.blockAt ⟨p.x + dx - 4, p.y + dy, p.z + dz - 4⟩).fluidState.fluid.isWater

/-- `FarmlandBlock.randomTick`: farmland near water becomes wet at once; otherwise it dries by
one step, and dry farmland that no plant maintains turns to dirt. Rain is left out: it never
rains in the void. -/
def farmlandRandomTick (s : Blocks.Farmland) (p : Pos) : M Unit := do
  let l ← get
  if !isNearWater l p then
    if h : 0 < s.moisture.val then
      let moisture : Fin 8 := ⟨s.moisture.val - 1, by omega⟩
      discard <| Level.setBlock p (.farmland { s with moisture }) 2
    else if !shouldMaintainFarmland l p then turnToBaseBlock p
  else if s.moisture.val < 7 then
    discard <| Level.setBlock p (.farmland { s with moisture := 7 }) 2

/-- The behaviour of farmland. -/
def farmland (s : Blocks.Farmland) : Behaviour :=
  let self : Block := .farmland s
  { Behaviour.inert self with
    canSurvive := farmlandCanSurvive
    updateShape := fun p d _ _ => groundUpdateShape self farmlandCanSurvive p d
    tick := fun p => do
      if !farmlandCanSurvive (← get) p then turnToBaseBlock p
    randomTick := farmlandRandomTick s }

/-- The behaviour of a dirt path. Its tick does not ask again whether the path can stay. -/
def path : Behaviour :=
  let self : Block := .plain .dirt_path
  { Behaviour.inert self with
    canSurvive := pathCanSurvive
    updateShape := fun p d _ _ => groundUpdateShape self pathCanSurvive p d
    tick := turnToBaseBlock }

/-! ### Leaves -/

/-- The properties `distance`, `persistent` and `waterlogged` of leaves, of any of the four
families. -/
def leaves? : Block → Option (IntRange 1 7 × Bool × Bool)
  | .leaves s => some (s.distance, s.persistent, s.waterlogged)
  | .tintedParticleLeaves _ s => some (s.distance, s.persistent, s.waterlogged)
  | .untintedParticleLeaves _ s => some (s.distance, s.persistent, s.waterlogged)
  | .mangroveLeaves s => some (s.distance, s.persistent, s.waterlogged)
  | _ => none

/-- `state.setValue(DISTANCE, distance)` for leaves. -/
def setDistance (b : Block) (distance : IntRange 1 7) : Block :=
  match b with
  | .leaves s => .leaves { s with distance }
  | .tintedParticleLeaves id s => .tintedParticleLeaves id { s with distance }
  | .untintedParticleLeaves id s => .untintedParticleLeaves id { s with distance }
  | .mangroveLeaves s => .mangroveLeaves { s with distance }
  | _ => b

/-- `LeavesBlock.getDistanceAt(state)`: 0 for a log, the distance of leaves, and 7 for
anything else. (Only leaves have the property `DISTANCE`; the `distance` of scaffolding is
another property.) -/
def getDistanceAt (b : Block) : ℕ :=
  if BlockTag.prevents_nearby_leaf_decay b.id then 0
  else
    match leaves? b with
    | some (distance, _, _) => distance.val
    | none => 7

/-- The distance `LeavesBlock.updateDistance(state, level, pos)` gives: one more than the least
distance among the six neighbours, at most 7. -/
def newDistance (l : Level) (p : Pos) : ℕ :=
  Direction.values.foldl (fun n d => min n (getDistanceAt (l.blockAt (p.step d)) + 1)) 7

/-- `LeavesBlock.updateDistance(state, level, pos)`. -/
def updateDistance (self : Block) (l : Level) (p : Pos) : Block :=
  match IntRange.ofNat? 1 7 (newDistance l p) with
  | some distance => setDistance self distance
  | none => self

/-- `Fluids.WATER.getTickDelay(level)`. -/
def waterTickDelay : ℕ := 5

/-- The behaviour of leaves with the given properties. -/
def leaves (self : Block) (distance : IntRange 1 7) (persistent waterlogged : Bool) :
    Behaviour :=
  { Behaviour.inert self with
    updateShape := fun p _ _ neighbour => do
      if waterlogged then Level.scheduleFluidTick p .water waterTickDelay
      let distanceFromNeighbor := getDistanceAt neighbour + 1
      if distanceFromNeighbor != 1 || distance.val != distanceFromNeighbor then
        Level.scheduleTick p self.id 1
      return self
    tick := fun p => do
      discard <| Level.setBlock p (updateDistance self (← get) p)
    -- `decaying(state)`; the game only gives the random tick to such leaves.
    randomTick := fun p => do
      if !persistent && distance.val == 7 then
        Level.dropResources self p
        discard <| Level.removeBlock p false }

/-! ### Snowy ground and huge mushrooms -/

/-- `SnowyBlock.updateShape`: the block above decides `snowy`. `setSnowy` gives the state with
that property. -/
def snowy (self : Block) (setSnowy : Bool → Block) (randomTicks : Bool) : Behaviour :=
  { Behaviour.inert self with
    updateShape := fun _ d _ neighbour =>
      return if d = .up then setSnowy (BlockTag.snow neighbour.id) else self
    -- `SpreadingSnowyBlock.randomTick` needs the dampening of light.
    randomTick := fun _ => if randomTicks then Level.setOverflow else pure () }

/-- `state.setValue(PROPERTY_BY_DIRECTION.get(d), value)` for a block of a huge mushroom. -/
def setFace (s : Blocks.HugeMushroom) (d : Direction) (value : Bool) : Blocks.HugeMushroom :=
  match d with
  | .down => { s with down := value }
  | .up => { s with up := value }
  | .north => { s with north := value }
  | .south => { s with south := value }
  | .west => { s with west := value }
  | .east => { s with east := value }

/-- The behaviour of a block of a huge mushroom (`HugeMushroomBlock.updateShape`). -/
def hugeMushroom (id : Blocks.HugeMushroom.Id) (s : Blocks.HugeMushroom) : Behaviour :=
  let self : Block := .hugeMushroom id s
  { Behaviour.inert self with
    updateShape := fun _ d _ neighbour =>
      return if neighbour.id == self.id then .hugeMushroom id (setFace s d false) else self }

/-! ### Blocks found by the audit -/

/-- A block whose `useWithoutItem` opens a menu: nothing changes in the level, and the action
is consumed (`InteractionResult.SUCCESS`). -/
def menu (self : Block) : Behaviour :=
  { Behaviour.inert self with useWithoutItem := fun _ _ => return true }

/-- The behaviour of a beacon. `BeaconBlockEntity.tick` follows the beam and the pyramid and
gives effects to players; none of this is kept, but the ticker is part of the level. -/
def beacon : Behaviour :=
  { menu (.plain .beacon) with ticksBlockEntity := true }

/-- `BlockEntity.setChanged(level, pos, state)` for the gateway at `p`: the comparators around
are told. -/
def gatewaySetChanged (p : Pos) : M Unit := Level.updateNeighbourForOutputSignal p .end_gateway

/-- `TheEndGatewayBlockEntity.portalTick`: the gateway grows older, and every 2400 ticks of age
it starts its cooldown, which queues a block event (`triggerCooldown`). The block entity is
marked as changed (`setChanged`) when the beam of its first 200 ticks ends, when the cooldown
starts (once by `triggerCooldown` and once by the tick) and when it ends 40 ticks later.

The cooldown counter is not saved and not kept here: it is taken to run from the last multiple
of 2400 the age passed. That is so for a gateway the model has ticked through that age; a
gateway that is loaded with an age just past such a multiple has no cooldown in the game. -/
def gatewayTick (p : Pos) : M Unit := do
  let some (.endGateway data) ← Level.peekBlockEntity p | return
  let age := data.age + 1
  Level.setBlockEntity p (.endGateway { data with age })
  if age % 2400 == 0 then
    Level.blockEvent p .end_gateway 1 0
    gatewaySetChanged p
    gatewaySetChanged p
  else if age == 200 || (age % 2400 == 40 && 2400 ≤ age) then gatewaySetChanged p

/-- The behaviour of an end gateway. -/
def endGateway : Behaviour :=
  { Behaviour.inert (.plain .end_gateway) with
    ticksBlockEntity := true
    blockEntityTick := gatewayTick
    -- `TheEndGatewayBlockEntity.triggerEvent`: the event 1 starts the cooldown.
    triggerEvent := fun p a _ => return (← Level.getBlockEntity p).isSome && a == 1
    -- `setAsInsidePortal`: travel to another place, not modelled.
    entityInside := fun _ _ => Level.setOverflow }

/-- The behaviour of an end portal: an entity inside would travel to the End. -/
def endPortal : Behaviour :=
  { Behaviour.inert (.plain .end_portal) with entityInside := fun _ _ => Level.setOverflow }

/-- The behaviour of a trial spawner. `TrialSpawner.tickServer`: an inactive spawner that has
nothing to spawn stays as it is (`TrialSpawnerState.tickAndGetNext`: no display entity can be
made); every other state looks for players and spawns mobs, which is not modelled. -/
def trialSpawner (s : Blocks.TrialSpawner) : Behaviour :=
  { Behaviour.inert (.trialSpawner s) with
    ticksBlockEntity := true
    blockEntityTick := fun p => do
      let idle := match ← Level.peekBlockEntity p with
        | some (.trialSpawner data) => !data.hasSpawnData
        | _ => false
      if s.trial_spawner_state != .inactive || !idle then Level.setOverflow }

/-- The behaviour of a vault. `VaultBlockEntity.Server.tick`: an inactive vault looks for
players, finds none and stays inactive; the other states end in a change of state, a new
display item or ejected loot, which is not modelled. `useItemOn` on an active vault tries the
item as a key. -/
def vault (s : Blocks.Vault) : Behaviour :=
  { Behaviour.inert (.vault s) with
    ticksBlockEntity := true
    blockEntityTick := fun _ => do
      if s.vault_state != .inactive then Level.setOverflow
    useItemOn := fun _ _ _ => do
      if s.vault_state == .active then
        Level.setOverflow
        return true
      else return false }

/-- `AmethystBlock.onProjectileHit`: the chime, whose pitch is `level.getRandom().nextFloat()`. -/
def chime : M Unit := modify fun l => { l with random := l.random.nextFloat24.2 }

/-- The behaviour of a pumpkin: shears carve it (`PumpkinBlock.useItemOn`), which drops seeds
as an item entity; that is not modelled. -/
def pumpkin : Behaviour :=
  { Behaviour.inert (.plain .pumpkin) with
    useItemOn := fun _ _ item => do
      if item == "minecraft:shears" then
        Level.setOverflow
        return true
      else return false }

/-! ### The behaviours -/

/-- The behaviour of the blocks of this component. Nylium, mud and rooted dirt do nothing
outside random ticks and bone meal. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .farmland s => farmland s
  | .leaves s => leaves self s.distance s.persistent s.waterlogged
  | .tintedParticleLeaves _ s => leaves self s.distance s.persistent s.waterlogged
  | .untintedParticleLeaves _ s => leaves self s.distance s.persistent s.waterlogged
  | .mangroveLeaves s => leaves self s.distance s.persistent s.waterlogged
  | .grass s => snowy self (fun snowy => .grass { s with snowy }) true
  | .mycelium s => snowy self (fun snowy => .mycelium { s with snowy }) true
  | .snowy s => snowy self (fun snowy => .snowy { s with snowy }) false
  | .hugeMushroom id s => hugeMushroom id s
  | .trialSpawner s => trialSpawner s
  | .vault s => vault s
  | .loom _ | .stonecutter _ => menu self
  | .plain id =>
    match id with
    | .dirt_path => path
    | .warped_nylium | .crimson_nylium =>
      -- `NyliumBlock.randomTick` needs the dampening of light.
      { Behaviour.inert self with randomTick := fun _ => Level.setOverflow }
    | .beacon => beacon
    | .end_gateway => endGateway
    | .end_portal => endPortal
    | .amethyst_block => { Behaviour.inert self with onProjectileHit := fun _ _ _ _ => chime }
    | .budding_amethyst =>
      { RandomTicked.behaviour self with onProjectileHit := fun _ _ _ _ => chime }
    | .pumpkin => pumpkin
    | .crafting_table | .smithing_table | .cartography_table | .enchanting_table => menu self
    | _ => .inert self
  | _ => .inert self

end Redstone.Component.Ground
