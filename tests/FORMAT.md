# Differential test formats

The Lean model is checked against a real Minecraft 26.3 server. A *scenario* describes a small
world and what is done to it; the server runs it and records a *trace*; the Lean model runs the
same scenario and must reproduce the trace exactly. Traces are produced only by the server and
are never edited by hand.

Files: `tests/scenarios/<unit>/<name>.json` and `tests/traces/<unit>/<name>.trace.json`.

## Conventions

* Positions are `[x, y, z]` integers relative to the scenario origin. The origin of every
  scenario is the absolute position `(0, 0, 0)` of the overworld, so scenario coordinates **are**
  world coordinates. The origin is chunk-aligned (x, y and z are multiples of 16): the chunk of a
  position is `(floor(x/16), floor(z/16))`, which matters because the drain order of scheduled
  ticks depends on chunk boundaries, and anything that depends on absolute positions (hash
  iteration orders, position seeds) can be computed from scenario coordinates.
* The world is an empty void (flat world with one layer of air, biome `minecraft:the_void`,
  build height y = -64 .. 319). The harness runs the scenarios of one invocation one after
  another in the same place. After each scenario it removes every block, block entity, entity,
  scheduled tick and block event again, and before each scenario it checks that the world is
  empty; it refuses to continue otherwise. The same chunks (x and z from -8 to 15) are loaded
  and entity-ticking for every scenario; a `box` must lie within x, z = -96 .. 223.
* A block state is written `minecraft:id[prop=value,...]` with **all** properties listed,
  sorted by property name; a block with no properties is written `minecraft:id`.
* Directions are `down`, `up`, `north`, `south`, `west`, `east`.
* A `double` in a trace is a string of 16 hex digits, the raw IEEE bits (`Double.doubleToRawLongBits`),
  and a `float` is 8 hex digits. In scenarios a number may be written as a JSON number or in
  this hex form.
* Random ticks are disabled (`random_tick_speed` 0), mob spawning is off (`spawn_mobs` and the
  other spawn rules false), weather is clear and does not change (`advance_weather` false), the
  day time is 6000 and does not advance (`advance_time` false), and destroyed blocks drop nothing
  (`block_drops` false; loot tables are not modelled), unless the scenario's `settings` say
  otherwise. All other game rules have their default values; the difficulty is easy.
* What is pinned at the start of every scenario, so that a trace depends on the scenario only
  (recording a scenario twice, alone or among others, gives byte-identical traces):
  * the level game time is set to 0, so frame `t` has `gameTime` `t`, and tick `t` runs with game
    time `t`;
  * the level `RandomSource` (a `LegacyRandomSource`) is reseeded with `setSeed(0)` before the
    setup and **again after the setup, immediately before frame 0**: tick 1 starts from seed 0;
  * `Level.randValue` (the generator of random-tick positions) is set to 0;
  * the entity id counter is set to 0 and the player of the `use` actions is created first (it
    is never added to the world), so entity ids are the same in every run;
  * `RandomSource.create()` (the private random of every entity, among others) normally takes
    its seed from the clock. During a scenario the `k`-th such call on the server thread
    (`k` = 1, 2, ...) gets the seed `k * 0x9E3779B97F4A7C15` (wrapping 64-bit multiplication).
    The first calls are made by the construction of the player, the later ones by whatever the
    game constructs, in order (every entity makes one for its private random when constructed);
  * the list of recent redstone torch toggles (burn-out) is cleared;
  * `Level.skyDarken`, which the game only recomputes at the start of a tick, is recomputed from
    the scenario's clock and weather, so the actions of tick 1 do not see the sky of the previous
    scenario;
  * between two ticks the harness waits until the light engine (a separate thread) is idle, and
    runs all queued main-thread tasks, so nothing depends on thread timing.

## Scenario

```json
{
  "name": "lever-lamp",
  "ticks": 20,
  "box": {"min": [0, 0, 0], "max": [4, 2, 4]},
  "settings": {"dayTime": 6000},
  "fill": [{"min": [0, 0, 0], "max": [4, 0, 4], "state": "minecraft:stone"}],
  "blocks": [
    {"pos": [1, 1, 1], "state": "minecraft:lever[face=floor,facing=north,powered=false]"},
    {"pos": [2, 1, 1], "state": "minecraft:hopper[enabled=true,facing=down]", "nbt": "{TransferCooldown:0}"}
  ],
  "entities": [{"type": "minecraft:item", "pos": [1.5, 2.0, 1.5], "nbt": "{Item:{id:\"minecraft:stone\",count:1}}"}],
  "actions": [
    {"tick": 2, "type": "use", "pos": [1, 1, 1], "face": "up"},
    {"tick": 9, "type": "set", "pos": [3, 1, 1], "state": "minecraft:redstone_block", "flags": 3},
    {"tick": 12, "type": "destroy", "pos": [3, 1, 1], "drop": false},
    {"tick": 14, "type": "summon", "entity": {"type": "minecraft:tnt", "pos": [2.5, 3.0, 2.5]}}
  ]
}
```

* The file is read strictly: an unknown key is an error, and so is a block state that is not
  written in the canonical form above (the error message gives the canonical form).
* `box` is the observed region (both corners included). Everything the scenario places or acts
  on must lie inside it (entities excepted), and the scenario should be built so that nothing
  leaves it; the harness prints a warning when it finds blocks outside the box afterwards.
* `settings` (all optional): `dayTime` (ticks of the overworld clock, default 6000),
  `advanceTime` (default false), `weather` (`"clear"`, `"rain"` or `"thunder"`, default clear;
  the rain and thunder levels are set to 0 or 1 at once), `randomTickSpeed` (default 0),
  `blockDrops` (default false).
* `fill` is applied first, then `blocks`; later entries overwrite earlier ones. `nbt` is SNBT
  for the block entity (loaded into the freshly created block entity as `/setblock` does).
  Initial blocks are placed **silently**: no `onPlace`, no neighbour or shape updates, no
  scheduled ticks. The initial world is exactly what the scenario says. Precisely, each write is
  `Level.setBlock(pos, state, 786)` (flags `UPDATE_CLIENTS | UPDATE_KNOWN_SHAPE |
  UPDATE_SKIP_BLOCK_ENTITY_SIDEEFFECTS | UPDATE_SKIP_ON_PLACE`), which still creates the block
  entity and maintains heightmaps, light and points of interest. After the placement the harness
  checks that no tick and no block event is pending, and fails the scenario otherwise.
* The writes happen in the order listed; a `fill` iterates x, then y, then z (z innermost). A
  write to a position that an earlier write filled first removes the earlier block and its block
  entity. This order is observable: block entities tick in the order in which they were created.
  Air is never placed.
* `entities` are added after the blocks, in order, as `/summon` does (`nbt` is SNBT; a mob
  without `nbt` gets `finalizeSpawn`). Entity positions may lie outside the box.
* The lists `actions` must be sorted by `tick` (1 .. `ticks`).
* Frame 0 is the world right after setup. Then for `t = 1 .. ticks`: the actions with
  `tick == t` are applied in the order listed, the server runs one full game tick, and frame
  `t` is recorded.
* Actions:
  * `use`: a player uses the block with an empty hand: exactly
    `BlockState.useWithoutItem(level, player, hit)`. The player is a creative-mode `ServerPlayer`
    with a dummy connection that is **not** in the world (it is not ticked, is found by no entity
    query, and never closes a container it opened). `hit` is the centre of `face` of the block
    (block centre plus half the face normal), direction `face`, `inside` false. Before the click
    the player is moved: for a horizontal face to feet position (x + 0.5 + 2nx, y, z + 0.5 + 2nz),
    looking at the block horizontally (its direction is the opposite of `face`); for `up` to
    (x + 0.5, y + 1, z + 0.5), yaw 0, pitch 90; for `down` to (x + 0.5, y - 2, z + 0.5), yaw 0,
    pitch -90.
  * `use_item`: the same with one `item` (an item id) in the main hand, using the sequence of the
    game's own test helper: `BlockState.useItemOn`; if that does not consume the action and asks
    for the empty-hand interaction, `useWithoutItem`; if still not consumed, `ItemStack.useOn`.
    The hand is emptied afterwards.
  * `set`: `Level.setBlock(pos, state, flags)`; `flags` defaults to 3.
  * `destroy`: `Level.destroyBlock(pos, drop)`; `drop` defaults to false. Nothing drops unless
    `settings.blockDrops` is true as well.
  * `summon`: adds an entity, as in `entities`.
  * `kill`: discards the entity with index `entity` (see below).

## Trace

```json
{
  "scenario": "lever-lamp",
  "version": "26.3",
  "frames": [
    {
      "tick": 0,
      "gameTime": 0,
      "blocks": {"1,1,1": "minecraft:lever[face=floor,facing=north,powered=false]"},
      "blockEntities": {"2,1,1": {"type": "minecraft:hopper", "nbt": {"c": {"TransferCooldown": 0}}}},
      "blockEntityTickers": [[2, 1, 1]],
      "scheduled": [{"pos": [1, 1, 1], "block": "minecraft:repeater", "delay": 2, "priority": -1}],
      "blockEvents": [{"pos": [1, 1, 1], "block": "minecraft:piston", "a": 0, "b": 2}],
      "entities": [{"index": 0, "type": "minecraft:item", "pos": ["...", "...", "..."],
                    "motion": ["...", "...", "..."], "onGround": true, "nbt": {"c": {}}}]
    }
  ]
}
```

* The file has one frame per line; keys are always in the order shown.
* Frame 0 is complete: it is the whole initial state (all non-air blocks in the box, all block
  entities, all entities, scheduled ticks and block events).
* `gameTime`: the level game time when the frame was taken; it equals `tick`.
* `blocks`: frame 0 lists every non-air position in the box. Later frames list only the
  positions whose state differs from the previous frame (a block that became air appears as
  `minecraft:air`). Keys are `"x,y,z"`, ordered by x, then y, then z.
* `blockEntities`: same delta convention (an entry appears when the block entity is new or its
  type or data changed); a removed block entity appears as `null`. Same key order. `nbt` is the
  block entity's saved data (`saveWithoutMetadata`: no `x`, `y`, `z`, `id`) as typed JSON.
* NBT as typed JSON: an int tag is a JSON number, a string tag a JSON string, a list tag a JSON
  array, and every other tag an object with exactly one key: `{"b": n}` byte, `{"s": n}` short,
  `{"l": "decimal"}` long, `{"f": "8 hex digits"}` float bits, `{"d": "16 hex digits"}` double
  bits, `{"B": [n, ...]}` byte array, `{"I": [n, ...]}` int array, `{"L": ["decimal", ...]}`
  long array, `{"c": {...}}` compound with its keys sorted. The top level is a compound, so
  `nbt` always has the form `{"c": {...}}`. (NBT in scenarios stays SNBT.)
* `blockEntityTickers`: the positions (inside the box) of the level's ticking block entities,
  complete in every frame, in the exact order in which `Level.tickBlockEntities` will go through
  them in the next tick: `Level.blockEntityTickers` followed by `pendingBlockEntityTickers`,
  without the entries whose ticker `isRemoved()`. Block entities without a server-side ticker
  (a chest, for instance) are not in the list. The key comes between `blockEntities` and
  `scheduled`.
* `scheduled`: every pending scheduled block tick inside the box, complete in every frame, in
  the order the server would run them (trigger time, then priority, then order of scheduling).
  `delay` is trigger time minus the current game time; `priority` is the numeric value of the
  `TickPriority` (-3 .. 3).
* `fluidTicks`: the pending scheduled fluid ticks inside the box, same form with `fluid` (a
  fluid id such as `minecraft:flowing_water`) in place of `block`. The key is **present only
  when the list is not empty**, between `scheduled` and `blockEvents`.
* `blockEvents`: the pending block events inside the box, complete in every frame, in order.
  (Block events run in the tick that queued them, so this is normally empty.)
* `entities`: every entity in the world that is not removed, inside the box or not, complete in
  every frame, ordered by `index`. `index` counts the entities in order of creation (entity id)
  among those that were in the world after the setup, after an action or at a frame, starting
  at 0; an entity that is created and removed within one tick never gets an index. Passengers
  are entities of their own. `pos` and `motion` are hex doubles. `nbt` is the entity's saved
  data (`saveWithoutId`) as typed JSON without `UUID`, `Pos`, `Motion`, `OnGround`; the list
  `attributes` and the `modifiers` lists inside it are sorted by their `id` (the server writes
  them in the order of an identity hash map, which changes from run to run).

## Block dump

`tools/harness/run.sh dump` writes `$MC_REPORTS/blockdump.json`, from which the Lean block
inventory is generated:

```json
{
  "version": "26.3",
  "shapes": [[["...", "...", "...", "...", "...", "..."]]],
  "blocks": [{
    "id": "minecraft:repeater",
    "classes": ["RepeaterBlock", "DiodeBlock", "HorizontalDirectionalBlock", "Block"],
    "blockEntity": null,
    "properties": [{"name": "delay", "kind": "int", "values": ["1", "2", "3", "4"]}],
    "default": 3,
    "states": [{"id": 8704, "values": [0, 0, 0, 0], "attrs": {}}]
  }],
  "blockEntityTypes": [{"id": "minecraft:hopper", "class": "HopperBlockEntity"}],
  "entityTypes": [{"id": "minecraft:item", "class": "ItemEntity", "width": "...", "height": "..."}],
  "items": [{"id": "minecraft:stone", "maxStackSize": 64}]
}
```

* `classes` is the Java class of the block followed by its superclasses up to `Block`.
* `properties` are in the order of the block's state definition; `kind` is `bool`, `int` or
  `enum` (with `enumClass`). `values` are in the property's own order.
* `states` are in registry order; `id` is the global block state id (the one of the vanilla
  `blocks.json` report); `values` gives, for each property, the index of its value. `default` is
  the index of the default state in `states`.
* `blockEntity` is the id of the block entity type that accepts the block's default state, or
  null.
* `attrs` per state: `air`, `conductor` (`isRedstoneConductor`), `solid`, `solidRender`,
  `replaceable`, `signalSource`, `analog`, `randomlyTicks`, `hasBlockEntity` (booleans);
  `push` (piston push reaction, lower case); `destroySpeed` (float); `light` (emission);
  `sturdyFull`, `sturdyCenter`, `sturdyRigid` (6-bit masks of `isFaceSturdy`, bit order down,
  up, north, south, west, east); `fluid` (the block state string of
  `state.getFluidState().createLegacyBlock()` in the canonical format, e.g.
  `minecraft:water[level=0]`; absent when the fluid state is empty);
  `collision`, `outline`, `supportShape` (indices into `shapes`). `destroySpeed` is a hex float.
  Queries that take a position are made at `BlockPos.ZERO` of an empty world
  (`EmptyBlockGetter`); an attribute whose query throws would be left out (none does in 26.3).
* A shape is a list of boxes `[minX, minY, minZ, maxX, maxY, maxZ]` in hex doubles, in the order
  of `VoxelShape.forAllBoxes`; shape 0 is the empty shape.
* `blockEntityTypes[].class` and `entityTypes[].class` are simple Java class names;
  `minecraft:player` has `class` null (it cannot be created from its type). `width` and `height`
  are hex floats.

## The Lean runner

`lake exe difftest [scenario files or directories]` runs scenarios through the Lean model and
compares it with their traces after every tick; without arguments it runs everything under
`tests/scenarios`, which is what `lake test` and the CI do.

* The model takes its initial state from frame 0 of the trace, so it never reads `fill`,
  `blocks` or `entities`. From the scenario it uses `ticks`, `box`, `actions` and, of the
  `settings`, `dayTime`, `advanceTime` and `weather`.
* It supports the actions `use`, `use_item`, `set` and `destroy`. A scenario with `summon` or
  `kill` cannot be run yet.
* After every tick it compares: `gameTime`; the block state and the block entity of every
  position in the box; `blockEntityTickers`; `scheduled`; `blockEvents`; and the entities.
  Block entities and entities are compared after decoding the server's NBT into the model's
  types (`ofNbt?`), so data the model does not represent is not compared. In particular a
  block entity or entity type whose model is still an empty structure always compares equal.
  A model type may also keep data that the game does not save (the openers counter of a chest,
  for instance). A trace cannot show such data, so those fields are reset before the comparison
  (`Redstone.Component.Container.savedData`).
* `tests/pending/scenarios` and `tests/pending/traces` hold scenarios that have been recorded
  but that the model does not reproduce yet. They are not run by `lake test`. Run them with
  `lake exe difftest tests/pending/scenarios/<unit>` and move them to `tests/scenarios` and
  `tests/traces` once they pass.
