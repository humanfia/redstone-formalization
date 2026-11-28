module

public import Redstone.Mechanics.Behaviour
public import Redstone.Entity.Tnt.Tables
public import Redstone.Entity.Geometry

/-!
# Changing blocks, and the updates that follow

The operations of `Level` through which blocks act on the world: `setBlock` with its update
flags, neighbour updates, shape updates, scheduling ticks and block events. They follow
`Level.setBlock`, `LevelChunk.setBlockState` and `CollectingNeighborUpdater`.

## The neighbour updater

Updates are not delivered recursively. The first update requested starts the updater, which
then runs until nothing is left; updates requested meanwhile are collected and run later, most
recent request first, as `CollectingNeighborUpdater` does. In the game this is a loop inside
the first call. Here the operations that request updates are first written against an abstract
action `kick`, "run the updater if it was idle" (namespace `Level.Core`); the loop `runUpdates`
is then defined using them with a `kick` that does nothing, which is right because the updater
is busy for as long as the loop runs; and finally the operations are given their real meaning
by taking `kick := runUpdates`.

## What is left out

* Drops (the section "Drops" below). While the game rule `block_drops` is off, which is the
  default, nothing drops and only the random numbers the game draws are modelled. With the rule
  on, a broken block drops its loot as item entities and its experience as experience orbs, with
  these gaps, each of which sets `Level.overflow`:
  * loot tables the generator does not evaluate (`Entity.Tnt.brokenChanceLoot` lists them:
    tables that read a block entity or a neighbour, weighted choices), which also set it while
    the rule is off;
  * the silverfish of an infested block, a mob: it appears as an entity the model does not
    move;
  * an experience orb that appears inside a block whose collision shape does not enclose it,
    which the game moves to a free place (`ExperienceOrb.unstuckIfPossible`), and one next to
    a block a piston is moving.
* Among the entities of one entity section, a dropped item or orb is placed as if it had been
  made before the entities were ticked (`Entities.Physics.sectionEntry`), also when an
  exploding entity made it. This is the order in which items and orbs meet others to merge
  with.
* Drops that do not come through here. Some components remove a block where the game first
  calls `dropResources`, and so drop nothing and draw nothing, whatever the game rule says:
  redstone dust, repeaters, comparators and rails that lose their support (`neighborChanged` in
  `Component.Dust`, `Component.Diode`, `Component.Comparator`, `Component.Rail`), and the candle
  of a candle cake (`Component.AnalogSource.popResource`, which only draws).

The scenarios of `tests/pending/scenarios/drops` wait for these and for two other parts of the
model: `support-diodes` and `explode-wiring` for the components above; `piston-direct-*` and
`piston-pushed` for a moving piston that pushes the item the block in its way dropped
(`Component.Piston`: a moving block pushes no entity, and `Level.overflow` is set);
`explode-twice` for an explosion that reaches item entities (`Entity.Tnt`); `destroy-infested`
for the silverfish.

Also left out:

* `setBlock` on a cell of an empty chunk section fails in the game when the new state is air.
  Here it only fails when the state does not change, which differs for the three kinds of air.
* Light, heightmaps and points of interest.
-/

@[expose] public section

namespace Redstone

/-! ### Update flags

The flags of `setBlock` (`Block.UPDATE_*`), as bit positions. -/

namespace UpdateFlag

/-- Send neighbour updates. -/
def neighbors : ℕ := 0
/-- Do not send shape updates. -/
def knownShape : ℕ := 4
/-- Do not drop items when a shape update destroys a block. -/
def suppressDrops : ℕ := 5
/-- The block is being moved by a piston. -/
def moveByPiston : ℕ := 6
/-- Redstone wire ignores the shape updates. -/
def skipShapeUpdateOnWire : ℕ := 7
/-- Do not run the side effects of removing a block entity. -/
def skipBlockEntitySideEffects : ℕ := 8
/-- Do not call `onPlace`. -/
def skipOnPlace : ℕ := 9

/-- `UPDATE_ALL`: neighbour updates and shape updates. The default of `setBlock`. -/
def all : ℕ := 3

end UpdateFlag

/-- `max-chained-neighbor-updates`: updates requested beyond this number in one run of the
updater are dropped. -/
def maxChainedNeighborUpdates : ℕ := 1000000

namespace Level

/-! ### Reading -/

/-- The block at `p`. -/
def getBlock (p : Pos) : M Block := return (← get).blockAt p

/-- The closed behaviour of a block state. -/
def behaviour (b : Block) : M (BehaviourOf (StateM Level)) := return (← read).block b

/-- Records that a bound of the model was reached. -/
def setOverflow : M Unit := modify fun l => { l with overflow := true }

/-! ### Block entities -/

/-- The block entity at `p`, if there is one now (`LevelChunk.getBlockEntity(pos, CHECK)`). -/
def peekBlockEntity (p : Pos) : M (Option BlockEntity) := return (← get).blockEntities p

/-- Replaces the data of the block entity at `p`. -/
def setBlockEntity (p : Pos) (be : BlockEntity) : M Unit :=
  modify fun l => { l with blockEntities := l.blockEntities.insert p be }

/-- Stops ticking the block entity at `p`. -/
def removeBlockEntityTicker (p : Pos) : M Unit :=
  modify fun l => { l with
    blockEntityTickers := l.blockEntityTickers.erase p
    pendingBlockEntityTickers := l.pendingBlockEntityTickers.erase p }

/-- Starts ticking the block entity at `p`, unless it is ticked already. A ticker added while
block entities are being ticked starts on the next game tick. -/
def addBlockEntityTicker (p : Pos) : M Unit :=
  modify fun l =>
    if l.blockEntityTickers.contains p || l.pendingBlockEntityTickers.contains p then l
    else if l.tickingBlockEntities then
      { l with pendingBlockEntityTickers := l.pendingBlockEntityTickers ++ [p] }
    else { l with blockEntityTickers := l.blockEntityTickers ++ [p] }

/-- `Level.getBlockEntity(pos)`, which is `LevelChunk.getBlockEntity(pos, IMMEDIATE)`: the block
entity at `p`. If there is none although the block at `p` has one, it is created on the spot.
This happens while a block is being placed: the reactions of the block it replaces
(`affectNeighborsAfterRemoval`) run before `LevelChunk.setBlockState` creates the block entity
of the new block, and they can send it a neighbour update. -/
def getBlockEntity (p : Pos) : M (Option BlockEntity) := do
  if let some be ← peekBlockEntity p then return some be
  let state ← getBlock p
  if !state.hasBlockEntity then return none
  let b ← behaviour state
  let some be := b.newBlockEntity | return none
  setBlockEntity p be
  if b.ticksBlockEntity then addBlockEntityTicker p
  return some be

/-- Removes the block entity at `p`. -/
def removeBlockEntity (p : Pos) : M Unit := do
  modify fun l => { l with blockEntities := l.blockEntities.erase p }
  removeBlockEntityTicker p

/-! ### Scheduled ticks and block events -/

/-- `scheduleTick(pos, block, delay, priority)`. Nothing is scheduled if a tick of the same
block at the same position is already waiting. -/
def scheduleTick (p : Pos) (block : BlockId) (delay : ℕ) (priority : TickPriority := .normal) :
    M Unit :=
  modify fun l =>
    let t : ScheduledTick := ⟨p, block, l.gameTime + delay, priority, l.subTickCount⟩
    let l := { l with subTickCount := l.subTickCount + 1 }
    if l.hasScheduledTick p block then l else { l with ticks := l.ticks ++ [t] }

/-- `scheduleTick(pos, fluid, delay)`: schedules a fluid tick. Nothing is scheduled if a tick of
the same fluid at the same position is already waiting. The counter that orders the ticks is
the one block ticks use (`Level.nextSubTickCount`). -/
def scheduleFluidTick (p : Pos) (fluid : Fluid) (delay : ℕ) (priority : TickPriority := .normal) :
    M Unit :=
  modify fun l =>
    let t : ScheduledFluidTick := ⟨p, fluid, l.gameTime + delay, priority, l.subTickCount⟩
    let l := { l with subTickCount := l.subTickCount + 1 }
    if l.hasScheduledFluidTick p fluid then l else { l with fluidTicks := l.fluidTicks ++ [t] }

/-- `blockEvent(pos, block, a, b)`: queues a block event, unless the same one is queued. -/
def blockEvent (p : Pos) (block : BlockId) (a b : ℤ) : M Unit :=
  modify fun l =>
    let e : BlockEvent := ⟨p, block, a, b⟩
    if l.blockEvents.contains e then l else { l with blockEvents := l.blockEvents ++ [e] }

/-- `gameEvent(event, pos, context)`: announces an event to vibration listeners. -/
def gameEvent (event : String) (p : Pos) (context : GameEventContext := {}) : M Unit := do
  (← read).gameEvent event p context

/-! ### Entities -/

/-- Adds an entity and returns its index. -/
def addEntity (base : Entities.Base) (data : EntityData) : M ℕ :=
  modifyGet fun l =>
    (l.nextEntityIndex,
      { l with
        entities := l.entities ++ [⟨l.nextEntityIndex, base, data⟩]
        nextEntityIndex := l.nextEntityIndex + 1 })

/-- Removes the entity with the given index. -/
def removeEntity (index : ℕ) : M Unit :=
  modify fun l => { l with entities := l.entities.filter (·.index != index) }

/-- Changes the entity with the given index. -/
def modifyEntity (index : ℕ) (f : Entity → Entity) : M Unit :=
  modify fun l =>
    { l with entities := l.entities.map fun e => if e.index == index then f e else e }

/-! ### Random sources -/

/-- `RandomSource.create()`: a new random number generator that is not the private one of an
entity. The game seeds it from the clock; the test harness makes the seed of the `k`-th
generator created on the server thread `k * 0x9E3779B97F4A7C15` (`tests/FORMAT.md`).

The first generator is that of the player of the tests, and every entity makes one when it is
constructed: the entity with index `i` has the generator number `i + 2`
(`Redstone.Entity.randomOfId`, which is what the entity units use for the private generator of
an entity, without calling this). The generators made here come on top of those and are counted
in `Level.randomSourceCount`. So the number of a new generator is one more than the player's,
the entities' and the earlier ones made here together.

This is exact as long as no generator was made between two entities: one made here does not
move the numbers of the entities created after it, which still follow `randomOfId`. Nothing
calls this yet. -/
def createRandomSource : M JavaRandom :=
  modifyGet fun l =>
    let k := 1 + l.nextEntityIndex + l.randomSourceCount + 1
    (.ofSeed (k * 0x9E3779B97F4A7C15 % 2 ^ 64),
      { l with randomSourceCount := l.randomSourceCount + 1 })

/-! ### Drops

What a block leaves behind when it is destroyed (`Block.dropResources`, and for an explosion
`BlockBehaviour.onExplosionHit`): the stacks of its loot table, each as an item entity
(`Block.popResource`), and what `spawnAfterBreak` adds, experience orbs
(`ExperienceOrb.award`) or a silverfish.

Everything here is decided by the game rule `block_drops` (`Level.blockDrops`). While it is
off, the game makes no entity, but it still draws from the level's random number generator:
three numbers for every stack and the experience of an ore. Those draws are all the model does
then, and they involve no floating point arithmetic. -/

/-- `level.getRandom().nextInt(bound)`. -/
def nextRandomInt (bound : ℕ) : M ℕ :=
  modifyGet fun l =>
    let (v, r) := l.random.nextInt bound
    (v, { l with random := r })

/-- `level.getRandom().nextDouble()`. -/
def nextRandomDouble : M Float :=
  modifyGet fun l =>
    let (v, r) := l.random.nextDouble53
    (Float.ofNat v * Float.ofBits 0x3ca0000000000000, { l with random := r })

/-- `Entity.random` of the entity that is created next, after the constructor of `Entity` has
drawn the UUID from it. The harness seeds the generator of the entity with id `n` with
`n * 0x9E3779B97F4A7C15`, and the entity with index `i` has id `i + 2`; this is
`Entity.randomAfterUuid`, which is defined above this module. -/
def newEntityRandom : M JavaRandom := do
  let id := (← get).nextEntityIndex + 2
  return (fun (r : JavaRandom) => (r.next 32).2)^[4] (.ofSeed ((id * 0x9E3779B97F4A7C15) % 2 ^ 64))

/-- `Block.getDrops(state, level, pos, blockEntity)`: the stacks that the block `state` at `p`
drops when it is broken without tool and without breaker (a block that lost its support, for
instance), with the block entity it had. `p` and `be` are not used: loot that depends on them
is not evaluated.

While the game rule `block_drops` is off, only the number of stacks is computed, which is all
`dropResources` needs then: the result has the right length, and every stack in it is a
placeholder, `ItemStack.empty`. With the rule on, the stacks are those of the loot table
(`Entity.Tnt.brokenDrops`, `ChanceLoot.drops`); a stack of the table that is empty is in the
list, as in the game.

The loot may depend on chance (`Entity.Tnt.brokenChanceLoot`): the loot table then draws from
its own random sequence, `Level.lootSequences`, which starts from the world seed the first time
the table is used. A block whose loot the model cannot evaluate (see
`Entity.Tnt.brokenChanceLoot` for which) sets `Level.overflow` and gives no stack. -/
def getDrops (state : Block) (_p : Pos) (_be : Option BlockEntity := none) :
    M (List ItemStack) :=
  match Entity.Tnt.brokenChanceLoot state with
  | some table => modifyGet fun l =>
    let sequence := (l.lootSequences.lookup table.key).getD table.newSequence
    if l.blockDrops then
      let (found, sequence) := table.drops sequence
      (found.map fun (item, count) => ItemStack.of item count, { l with
        lootSequences := (table.key, sequence) :: l.lootSequences.filter (·.1 != table.key) })
    else
      let (n, sequence) := table.stackCount sequence
      (List.replicate n ItemStack.empty, { l with
        lootSequences := (table.key, sequence) :: l.lootSequences.filter (·.1 != table.key) })
  | none =>
    match Entity.Tnt.brokenDropStacks state with
    | some n => do
      if (← get).blockDrops then
        match Entity.Tnt.brokenDrops state with
        | some drops => pure (drops.map fun (item, count) => ItemStack.of item count)
        | none => do
          setOverflow
          pure []
      else pure (List.replicate n ItemStack.empty)
    | none => do
      setOverflow
      pure []

/-- `new ItemEntity(level, x, y, z, stack)`, `setDefaultPickUpDelay()` and `addFreshEntity`: the
stack lies at `pos` with the small random velocity the constructor gives it, and cannot be
picked up for 10 ticks. The constructor draws from the entity's own generator: the bobbing
offset, the rotation and the two horizontal components of the velocity. This is what
`Entity.Item.spawnAtLocation` does for an entity that drops something. -/
def addItemEntity (pos : Vec3) (stack : ItemStack) : M Unit := do
  let r ← newEntityRandom
  let r := r.nextFloat24.2
  let (yaw, r) := r.nextFloat24
  let (dx, r) := r.nextDouble53
  let (dz, r) := r.nextDouble53
  let toDouble (n : ℕ) : Float := Float.ofNat n * Float.ofBits 0x3ca0000000000000
  let scale := Float.ofBits 0x3fc999999999999a
  let shift := Float.ofBits 0x3fb999999999999a
  let motion : Vec3 := ⟨toDouble dx * scale - shift, scale, toDouble dz * scale - shift⟩
  let data : Entities.Item :=
    { item := stack.id, count := stack.count, hasComponents := stack.hasComponents
      pickupDelay := 10
      yRot := ((Float32.ofNat yaw / 16777216) * 360).toBits.toNat
      phys := { random := some r, sectionEntry := ((← get).gameTime, 0) } }
  discard <| addEntity ⟨pos, motion, false⟩ (.item data)

/-- `Block.popResource(level, pos, stack)` for a stack of `count` of `item`: the stack becomes
an item entity at a random place in the middle of the block at `p`. The three coordinates are
drawn from the level's random number generator before the game looks at the stack or at the
game rule `block_drops`; then, if the stack is not empty and the rule is on, the entity is
made (`addItemEntity`). An explosion drops what it collected through this
(`ServerExplosion.interactWithBlocks`). -/
def popResource (p : Pos) (item : String) (count : ℕ) : M Unit := do
  if (← get).blockDrops then
    -- `Mth.nextDouble(random, -0.25, 0.25)`
    let dx := (← nextRandomDouble) * 0.5 + (-0.25)
    let dy := (← nextRandomDouble) * 0.5 + (-0.25)
    let dz := (← nextRandomDouble) * 0.5 + (-0.25)
    let stack := ItemStack.of item count
    -- `EntityTypes.ITEM.getHeight() / 2.0` is 0.125
    if !stack.isEmpty then
      addItemEntity
        ⟨Float.ofInt p.x + 0.5 + dx, Float.ofInt p.y + 0.5 + dy - 0.125, Float.ofInt p.z + 0.5 + dz⟩
        stack
  else modify fun l => { l with random := (·.nextDouble53.2)^[3] l.random }

/-! #### Experience -/

/-- `ExperienceOrb.getExperienceValue(maxValue)`: the value of the largest kind of orb that is
worth at most `maxValue`. -/
def experienceValue (maxValue : ℕ) : ℕ :=
  if maxValue ≥ 2477 then 2477
  else if maxValue ≥ 1237 then 1237
  else if maxValue ≥ 617 then 617
  else if maxValue ≥ 307 then 307
  else if maxValue ≥ 149 then 149
  else if maxValue ≥ 73 then 73
  else if maxValue ≥ 37 then 37
  else if maxValue ≥ 17 then 17
  else if maxValue ≥ 7 then 7
  else if maxValue ≥ 3 then 3
  else 1

/-- The place of an experience orb in the order in which `EntitySectionStorage` goes through
the entities of a region; see `Entity.Item.sectionKey`, of which this is the case of an orb. -/
def orbSectionKey (e : Entity) (d : Entities.ExperienceOrb) : List ℤ :=
  let p := e.base.pos
  [Phys.floor p.x / 16, (Phys.floor p.z / 16) % 2 ^ 22, (Phys.floor p.y / 16) % 2 ^ 20,
    d.phys.sectionEntry.1, d.phys.sectionEntry.2, e.index]

/-- `ExperienceOrb.tryMergeToExisting(level, pos, value)` for the centre of the block at `p`:
a number below 40 is drawn from the level's generator, and the first orb of the same value
whose id differs from it by a multiple of 40 and whose box meets the cube of side 1 around the
centre takes one more orb in (`count`) and is young again. Returns whether there was one. -/
def tryMergeToExistingOrb (p : Pos) (value : ℕ) : M Bool := do
  let id ← nextRandomInt 40
  let l ← get
  let cx := Float.ofInt p.x + 0.5
  let cy := Float.ofInt p.y + 0.5
  let cz := Float.ofInt p.z + 0.5
  -- the box of an orb is 0.5 wide and high; `AABB.intersects` of it and `AABB.ofSize(pos, 1, 1, 1)`
  let meets (q : Vec3) : Bool :=
    q.x - 0.25 < cx + 0.5 && q.x + 0.25 > cx - 0.5 && q.y < cy + 0.5 && q.y + 0.5 > cy - 0.5 &&
      q.z - 0.25 < cz + 0.5 && q.z + 0.25 > cz - 0.5
  let found := l.entities.foldl (init := (none : Option (List ℤ × ℕ))) fun best e =>
    match e.data with
    | .experienceOrb d =>
      if ((e.index : ℤ) + 2 - id) % 40 == 0 && d.value == (value : ℤ) && meets e.base.pos then
        let key := orbSectionKey e d
        match best with
        | some (k, _) => if key < k then some (key, e.index) else best
        | none => some (key, e.index)
      else best
    | _ => best
  match found with
  | some (_, i) =>
    modifyEntity i fun e =>
      match e.data with
      | .experienceOrb d =>
        { e with data := .experienceOrb { d with count := d.count + 1, age := 0 } }
      | _ => e
    return true
  | none => return false

/-- `new ExperienceOrb(level, pos, Vec3.ZERO, value)` and `addFreshEntity`, for `pos` the centre
of the block at `p`: an orb worth `value` with a random velocity, drawn like its rotation from
its own generator.

An orb that appears inside a block is moved to the nearest place where it fits, within a
quarter of a block (`unstuckIfPossible`). That search is not modelled. What is modelled is the
case of a block whose collision shape encloses the orb with that margin, such as the full cube
of an ore that is being broken: then there is no such place and the orb stays. For any other
shape that the orb meets, for a shape that is not that of the block state, and next to a block
that a piston is moving, `Level.overflow` is set. -/
def addExperienceOrb (p : Pos) (value : ℕ) : M Unit := do
  let r ← newEntityRandom
  let (yaw, r) := r.nextFloat24
  let (dx, r) := r.nextDouble53
  let (dy, r) := r.nextDouble53
  let (dz, r) := r.nextDouble53
  let toDouble (n : ℕ) : Float := Float.ofNat n * Float.ofBits 0x3ca0000000000000
  let scale := Float.ofBits 0x3fc999999999999a
  let shift := Float.ofBits 0x3fb999999999999a
  let motion : Vec3 :=
    ⟨(toDouble dx * scale - shift) * 2.0, toDouble dy * scale * 2.0,
      (toDouble dz * scale - shift) * 2.0⟩
  let l ← get
  -- `level.noCollision(getBoundingBox())`, in coordinates relative to the block: the box of the
  -- orb is the cube from (0.25, 0.5, 0.25) to (0.75, 1, 0.75), which only this block can meet
  let state := l.blockAt p
  let boxes := (Entity.Tnt.collisionGrid state.attrs.collision).boxes
  let meets := boxes.any fun (x0, y0, z0, x1, y1, z1) =>
    x0 < 0.75 && x1 > 0.25 && y0 < 1.0 && y1 > 0.5 && z0 < 0.75 && z1 > 0.25
  -- `findFreePosition`: the centres at which the orb does not meet the box inflated by 0.25
  let encloses := boxes.any fun (x0, y0, z0, x1, y1, z1) =>
    x0 - 0.25 ≤ 0.25 && x1 + 0.25 ≥ 0.75 && y0 - 0.25 ≤ 0.5 && y1 + 0.25 ≥ 1.0 &&
      z0 - 0.25 ≤ 0.25 && z1 + 0.25 ≥ 0.75
  if Entity.Tnt.hasDynamicCollision state.id || (meets && !encloses) ||
      Direction.updateOrder.any (fun d => (l.blockAt (p.step d)).is .moving_piston) then
    setOverflow
  let data : Entities.ExperienceOrb :=
    { value := value
      yRot := ((Float32.ofNat yaw / 16777216) * 360).toBits.toNat
      phys := { random := some r, sectionEntry := (l.gameTime, 0) } }
  discard <| addEntity
    ⟨⟨Float.ofInt p.x + 0.5, Float.ofInt p.y + 0.5, Float.ofInt p.z + 0.5⟩, motion, false⟩
    (.experienceOrb data)

/-- The loop of `ExperienceOrb.awardWithDirection`. `fuel` bounds the number of orbs; the
amount is enough. -/
def awardExperienceLoop (p : Pos) : ℕ → ℕ → M Unit
  | 0, _ => pure ()
  | fuel + 1, amount => do
    if amount = 0 then return
    let value := experienceValue amount
    if !(← tryMergeToExistingOrb p value) then addExperienceOrb p value
    awardExperienceLoop p fuel (amount - value)

/-- `ExperienceOrb.award(level, Vec3.atCenterOf(pos), amount)`: `amount` experience appears at
the centre of the block at `p`, as orbs of the largest values that fit, each of which either
joins an orb that is already there or is new. The game rule `block_drops` is not asked: a
furnace that is removed releases its experience through this whatever the rule says. -/
def awardExperience (p : Pos) (amount : ℕ) : M Unit := awardExperienceLoop p amount amount

/-- `Block.popExperience(level, pos, amount)`: the experience of a broken block, if the game
rule `block_drops` is on. -/
def popExperience (p : Pos) (amount : ℕ) : M Unit := do
  if (← get).blockDrops then awardExperience p amount

/-- `InfestedBlock.spawnInfestation(level, pos)`: a silverfish appears in the block at `p`. A
silverfish is a mob, which the model does not move: the entity is there, as an entity of a
kind the model knows nothing about, and `Level.overflow` is set. -/
def spawnInfestation (p : Pos) : M Unit := do
  discard <| addEntity
    ⟨⟨Float.ofInt p.x + 0.5, Float.ofInt p.y, Float.ofInt p.z + 0.5⟩, ⟨0, 0, 0⟩, false⟩
    (.other "minecraft:silverfish")
  setOverflow

/-- `BlockState.spawnAfterBreak(level, pos, ItemStack.EMPTY, dropExperience)`: what the block
`state` that was at `p` releases besides its loot (`Entity.Tnt.afterBreak`). The classes that
override the method are `DropExperienceBlock`, `RedStoneOreBlock`, the sculk blocks,
`SpawnerBlock` and `InfestedBlock` (`Redstone.Component.Loot`).

The amount of experience is drawn from the level's random number generator whether or not the
game rule `block_drops` is on (`Block.tryDropExperience`); the rule only decides whether orbs
appear. There is no tool, so no enchantment changes the amount
(`EnchantmentHelper.processBlockExperience`) or keeps the silverfish in. -/
def spawnAfterBreak (state : Block) (p : Pos) (dropExperience : Bool) : M Unit :=
  match Entity.Tnt.afterBreak state.id with
  | .nothing => pure ()
  | .experience amount => do
    if dropExperience && amount > 0 then popExperience p amount
  | .uniformExperience min max => do
    if dropExperience then
      -- `UniformInt.sample`: `random.nextInt(max - min + 1) + min`
      let amount := (← nextRandomInt (max - min + 1)) + min
      if amount > 0 then popExperience p amount
  | .spawner => do
    if dropExperience then
      let a ← nextRandomInt 15
      let b ← nextRandomInt 15
      popExperience p (15 + a + b)
  | .infested => do
    if (← get).blockDrops then spawnInfestation p

/-- `Block.dropResources(state, level, pos, blockEntity)`: the block `state` that is being
destroyed at `p`, with the block entity `be` it had, drops the stacks of its loot (`getDrops`),
each through `popResource`, and then what `spawnAfterBreak` adds.

While the game rule `block_drops` is off nothing appears, but the level's random number
generator advances as in the game: by the three coordinates of every stack, and by what
`spawnAfterBreak` draws. -/
def dropResources (state : Block) (p : Pos) (be : Option BlockEntity := none) : M Unit := do
  let drops ← getDrops state p be
  if (← get).blockDrops then drops.forM fun stack => popResource p stack.id stack.count
  else modify fun l => { l with random := (·.nextDouble53.2)^[3 * drops.length] l.random }
  spawnAfterBreak state p true

/-- `BlockState.getDrops` as `BlockBehaviour.onExplosionHit` calls it: the stacks, as item and
count, that the block `state` at `p` drops when an explosion destroys it, with the block entity
it had. `p` and `be` are not used: loot that depends on them is not evaluated.

This is for an exploded block what `getDrops` is for a broken one: the explosion
(`Entity.Tnt.onExplosionHit`) only calls it. The stacks come from `Entity.Tnt.explosionDrops`
or, where they depend on chance, from the loot table (`Entity.Tnt.brokenChanceLoot`, which is
the same for an explosion), drawing from the table's random sequence. A stack of the table
that is empty is in the list, with count zero. A block whose drops neither can give (they
depend on a block entity or on the neighbours) sets `Level.overflow` and gives no stack.

Just before it asks for the drops, the game calls `spawnAfterBreak` without experience, which
only matters for an infested block when blocks drop: its silverfish. The explosion does not
make that call (`Level.spawnAfterBreak` is there for it), so this case sets `Level.overflow`
here. -/
def getExplosionDrops (state : Block) (_p : Pos) (_be : Option BlockEntity := none) :
    M (List (String × ℕ)) := do
  if (← get).blockDrops && Entity.Tnt.afterBreak state.id == .infested then setOverflow
  match Entity.Tnt.explosionDrops state with
  | some drops => pure drops
  | none =>
    match Entity.Tnt.brokenChanceLoot state with
    | some table => modifyGet fun l =>
      let sequence := (l.lootSequences.lookup table.key).getD table.newSequence
      let (found, sequence) := table.drops sequence
      (found, { l with
        lootSequences := (table.key, sequence) :: l.lootSequences.filter (·.1 != table.key) })
    | none => do
      setOverflow
      pure []

/-! ### Operations that request updates -/

/-- Adds an update to the neighbour updater (the first half of `addAndRun`). Returns whether
the updater was idle, in which case the caller has to run it. -/
def enqueueUpdate (u : NeighborUpdate) : M Bool :=
  modifyGet fun l =>
    let idle := l.updateCount == 0
    let l' := { l with updateCount := l.updateCount + 1 }
    if l.updateCount ≥ maxChainedNeighborUpdates then (idle, l')
    else if idle then (idle, { l' with updateStack := u :: l'.updateStack })
    else (idle, { l' with updatesAdded := l'.updatesAdded ++ [u] })

namespace Core

variable (kick : M Unit)

/-- `addAndRun`. -/
def addAndRun (u : NeighborUpdate) : M Unit := do
  if ← enqueueUpdate u then kick

/-- `updateNeighborsAtExceptFromFacing(pos, block, skip)`: tells the six neighbours of `p`,
except the one in direction `skip`, that `block` changed. -/
def updateNeighborsAtExceptFromFacing (p : Pos) (block : BlockId) (skip : Option Direction) :
    M Unit :=
  addAndRun kick (.multi p block skip (if Direction.updateOrder.head? = skip then 1 else 0))

/-- `updateNeighborsAt(pos, block)`: tells the six neighbours of `p` that `block` changed. -/
def updateNeighborsAt (p : Pos) (block : BlockId) : M Unit :=
  updateNeighborsAtExceptFromFacing kick p block none

/-- `neighborChanged(pos, block, orientation)`: tells the block at `p` that `block` changed. -/
def neighborChanged (p : Pos) (block : BlockId) : M Unit := addAndRun kick (.simple p block)

/-- `neighborChanged(state, pos, block, orientation, movedByPiston)`: as `neighborChanged`, but
the update is delivered to the behaviour of `state`. -/
def neighborChangedFor (state : Block) (p : Pos) (block : BlockId) (movedByPiston : Bool) :
    M Unit :=
  addAndRun kick (.full state p block movedByPiston)

/-- `neighborShapeChanged(direction, pos, neighborPos, neighborState, flags, limit)`: a shape
update for the block at `p`, whose neighbour in direction `dir` has become `neighborState`. -/
def neighborShapeChanged (dir : Direction) (p neighborPos : Pos) (neighborState : Block)
    (flags limit : ℕ) : M Unit :=
  addAndRun kick (.shape dir neighborState p neighborPos flags limit)

/-- `BlockState.updateNeighbourShapes(level, pos, flags, limit)`: shape updates for the six
neighbours of the block `state` at `p`. -/
def updateNeighbourShapes (state : Block) (p : Pos) (flags limit : ℕ) : M Unit :=
  Direction.shapeOrder.forM fun d =>
    neighborShapeChanged kick d.opposite (p.step d) p state flags limit

/-- `updateNeighbourForOutputSignal(pos, block)`: tells the comparators that read the block at
`p`, directly or through a conductor, that it changed. -/
def updateNeighbourForOutputSignal (p : Pos) (block : BlockId) : M Unit :=
  Direction.horizontals.forM fun d => do
    let q := p.step d
    let s ← getBlock q
    if s.is .comparator then neighborChangedFor kick s q block false
    else if s.isConductor then
      let q := q.step d
      let s ← getBlock q
      if s.is .comparator then neighborChangedFor kick s q block false

/-- `LevelChunk.setBlockState(pos, state, flags)`: puts `state` at `p`, takes care of the block
entity and runs `affectNeighborsAfterRemoval` and `onPlace`. Returns the old state, or `none`
if nothing was done or the block was replaced again meanwhile. -/
def setBlockInChunk (p : Pos) (state : Block) (flags : ℕ) : M (Option Block) := do
  let old ← getBlock p
  if old = state then return none
  modify (·.setBlockRaw p state)
  let blockChanged := old.id != state.id
  let moved := flags.testBit UpdateFlag.moveByPiston
  let oldB ← behaviour old
  let newB ← behaviour state
  if blockChanged && old.hasBlockEntity && !newB.keepsBlockEntity old then
    if !flags.testBit UpdateFlag.skipBlockEntitySideEffects && (← peekBlockEntity p).isSome then
      oldB.preRemoveSideEffects p
    removeBlockEntity p
  if (blockChanged || state.isRail) && (flags.testBit UpdateFlag.neighbors || moved) then
    oldB.affectNeighborsAfterRemoval p moved
  if !(← getBlock p).is state.id then return none
  if !flags.testBit UpdateFlag.skipOnPlace then newB.onPlace p old moved
  if state.hasBlockEntity && (← getBlock p).is state.id then
    -- `blockEntity.isValidBlockState(state)`: the block entity is of the type of the block's.
    -- The types are compared by constructor, which is the same as by `typeName`.
    let valid (be : BlockEntity) := (BlockEntity.new? state.id).any (·.ctorIdx == be.ctorIdx)
    if ((← peekBlockEntity p).any valid) then
      if newB.ticksBlockEntity then addBlockEntityTicker p else removeBlockEntityTicker p
    else
      removeBlockEntity p
      if let some be := newB.newBlockEntity then
        setBlockEntity p be
        if newB.ticksBlockEntity then addBlockEntityTicker p
  return some old

/-- `Level.setBlock(pos, state, flags, limit)`. Returns whether the block was changed. -/
def setBlock (p : Pos) (state : Block) (flags : ℕ := UpdateFlag.all) (limit : ℕ := 512) :
    M Bool := do
  let some old ← setBlockInChunk p state flags | return false
  if (← getBlock p) = state then
    if flags.testBit UpdateFlag.neighbors then
      updateNeighborsAt kick p old.id
      if state.attrs.analog then updateNeighbourForOutputSignal kick p state.id
    if !flags.testBit UpdateFlag.knownShape && limit > 0 then
      -- `flags & ~(UPDATE_NEIGHBORS | UPDATE_SUPPRESS_DROPS)`
      let flags := flags &&& 0x3de
      (← behaviour old).updateIndirectNeighbourShapes p flags (limit - 1)
      updateNeighbourShapes kick state p flags (limit - 1)
      (← behaviour state).updateIndirectNeighbourShapes p flags (limit - 1)
  return true

/-- `Level.destroyBlock(pos, drop, breaker, limit)`: breaks the block at `p`. With `drop` the
block drops what it holds (`dropResources`): its loot and experience if the game rule
`block_drops` is on, and otherwise nothing, though the level's random number generator advances
as it does in the game. Returns whether a block was broken. -/
def destroyBlock (p : Pos) (drop : Bool) (limit : ℕ := 512) : M Bool := do
  let state ← getBlock p
  if state.isAir then return false
  if drop then dropResources state p (← peekBlockEntity p)
  let destroyed ← setBlock kick p state.fluidBlock UpdateFlag.all limit
  if destroyed then gameEvent "minecraft:block_destroy" p { affectedState := some state }
  return destroyed

/-- `Level.removeBlock(pos, movedByPiston)`. -/
def removeBlock (p : Pos) (movedByPiston : Bool) : M Bool := do
  setBlock kick p (← getBlock p).fluidBlock (if movedByPiston then 67 else 3)

/-- `Block.updateOrDestroy(state, newState, level, pos, flags, limit)`. -/
def updateOrDestroy (state newState : Block) (p : Pos) (flags limit : ℕ) : M Unit := do
  if newState ≠ state then
    if newState.isAir then
      discard <| destroyBlock kick p (!flags.testBit UpdateFlag.suppressDrops) limit
    else
      -- `flags & ~UPDATE_SUPPRESS_DROPS`
      discard <| setBlock kick p newState (flags &&& 0x3df) limit

/-- `NeighborUpdater.executeShapeUpdate`: delivers a shape update. -/
def executeShapeUpdate (dir : Direction) (p neighborPos : Pos) (neighborState : Block)
    (flags limit : ℕ) : M Unit := do
  let cur ← getBlock p
  if flags.testBit UpdateFlag.skipShapeUpdateOnWire && cur.is .redstone_wire then return
  let new ← (← behaviour cur).updateShape p dir neighborPos neighborState
  updateOrDestroy kick cur new p flags limit

/-- `NeighborUpdates.runNext`: runs the next step of an update. Returns the update with which
to continue, or `none` when it is finished. -/
def runNext : NeighborUpdate → M (Option NeighborUpdate)
  | .shape dir neighborState p neighborPos flags limit => do
    executeShapeUpdate kick dir p neighborPos neighborState flags limit
    return none
  | .simple p block => do
    (← behaviour (← getBlock p)).neighborChanged p block false
    return none
  | .full state p block moved => do
    (← behaviour state).neighborChanged p block moved
    return none
  | .multi source block skip idx => do
    let some d := Direction.updateOrder[idx]? | return none
    let q := source.step d
    (← behaviour (← getBlock q)).neighborChanged q block false
    let idx := idx + 1
    let idx := if skip.isSome && Direction.updateOrder[idx]? = skip then idx + 1 else idx
    if idx < Direction.updateOrder.length then return some (.multi source block skip idx)
    else return none

end Core

/-! ### The updater's loop -/

/-- The level itself (`pinWorld_eq`), with its world evaluated as far as its constructor.

This is for the Lean kernel, which evaluates lazily: a change to another field of the level,
`{ l with updateCount := _ }`, leaves the world as the unevaluated `l.world`, and after `n` such
changes a read of a block goes back through all `n` of them, every time. The updater's loop
changes the level several times for each update it delivers, so without this the cost of a
run of updates that changes no block grows with the square of its length (12000 updates in
empty air: no end within a minute; see `docs/proof-feasibility.md`). -/
def pinWorld (l : Level) : Level :=
  match l.world with
  | ⟨cells, noAir⟩ => { l with world := ⟨cells, noAir⟩ }

theorem pinWorld_eq (l : Level) : l.pinWorld = l := rfl

/-- The loop of `CollectingNeighborUpdater.runUpdates`, bounded by `fuel` steps. Each step
moves the updates added meanwhile to the top of the stack, first added on top, and runs the
next step of the update that is then on top. -/
def runUpdatesLoop : ℕ → M Unit
  | 0 =>
    modify fun l =>
      { l with updateStack := [], updatesAdded := [], updateCount := 0, overflow := true }
  | fuel + 1 => do
    let l ← get
    match l.updatesAdded ++ l.updateStack with
    | [] => set { l with updateStack := [], updatesAdded := [], updateCount := 0 }
    | u :: rest =>
      set { l.pinWorld with updateStack := u :: rest, updatesAdded := [] }
      let next ← Core.runNext setOverflow u
      modify fun l => { l with updateStack := next.toList ++ rest }
      runUpdatesLoop fuel

/-- Runs the neighbour updater until nothing is left. Every update takes at most six steps and
at most `maxChainedNeighborUpdates` updates are accepted, so the bound is never reached. -/
def runUpdates : M Unit := runUpdatesLoop (6 * maxChainedNeighborUpdates + 1)

/-! ### The operations, with the updater in place -/

@[inherit_doc Core.updateNeighborsAt]
def updateNeighborsAt (p : Pos) (block : BlockId) : M Unit :=
  Core.updateNeighborsAt runUpdates p block

@[inherit_doc Core.updateNeighborsAtExceptFromFacing]
def updateNeighborsAtExceptFromFacing (p : Pos) (block : BlockId) (skip : Option Direction) :
    M Unit :=
  Core.updateNeighborsAtExceptFromFacing runUpdates p block skip

@[inherit_doc Core.neighborChanged]
def neighborChanged (p : Pos) (block : BlockId) : M Unit := Core.neighborChanged runUpdates p block

@[inherit_doc Core.neighborChangedFor]
def neighborChangedFor (state : Block) (p : Pos) (block : BlockId) (movedByPiston : Bool) :
    M Unit :=
  Core.neighborChangedFor runUpdates state p block movedByPiston

@[inherit_doc Core.updateNeighbourShapes]
def updateNeighbourShapes (state : Block) (p : Pos) (flags : ℕ) (limit : ℕ := 512) : M Unit :=
  Core.updateNeighbourShapes runUpdates state p flags limit

@[inherit_doc Core.updateNeighbourForOutputSignal]
def updateNeighbourForOutputSignal (p : Pos) (block : BlockId) : M Unit :=
  Core.updateNeighbourForOutputSignal runUpdates p block

@[inherit_doc Core.setBlock]
def setBlock (p : Pos) (state : Block) (flags : ℕ := UpdateFlag.all) (limit : ℕ := 512) : M Bool :=
  Core.setBlock runUpdates p state flags limit

@[inherit_doc Core.destroyBlock]
def destroyBlock (p : Pos) (drop : Bool) (limit : ℕ := 512) : M Bool :=
  Core.destroyBlock runUpdates p drop limit

@[inherit_doc Core.removeBlock]
def removeBlock (p : Pos) (movedByPiston : Bool) : M Bool :=
  Core.removeBlock runUpdates p movedByPiston

@[inherit_doc Core.updateOrDestroy]
def updateOrDestroy (state newState : Block) (p : Pos) (flags : ℕ) (limit : ℕ := 512) : M Unit :=
  Core.updateOrDestroy runUpdates state newState p flags limit

/-! ### Players -/

/-- A player uses the block at `p` with an empty hand on the given face. -/
def useWithoutItem (p : Pos) (face : Direction) : M Bool := do
  (← behaviour (← getBlock p)).useWithoutItem p face

/-- A player uses the item named `item` on the given face of the block at `p`
(`ServerPlayerGameMode.useItemOn`). The block is asked first (`BlockState.useItemOn`); a block
that does not consume the action answers `TRY_WITH_EMPTY_HAND`, as `BlockBehaviour.useItemOn`
does by default (`Behaviour.tryEmptyHand`), and the game then tries the empty-hand interaction
of the same block state (`BlockState.useWithoutItem`). What the item would do by itself after
that (`ItemStack.useOn`, placing a block for instance) is not modelled. -/
def useItemOn (p : Pos) (face : Direction) (item : String) : M Bool := do
  let b ← behaviour (← getBlock p)
  if (← b.useItemOn p face item) then return true
  if b.tryEmptyHand face item then b.useWithoutItem p face else return false

end Level

end Redstone
