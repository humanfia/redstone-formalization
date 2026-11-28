module

public import Redstone.Entity.ItemDrop
public import Redstone.Entity.Still

/-!
# Blocks with a behaviour of their own

Java classes: `CampfireBlock` with `CampfireBlockEntity`, `PowderSnowBlock`, `WebBlock`,
`NetherPortalBlock` with `PortalShape`, `CarvedPumpkinBlock` with `BlockPattern`,
`DriedGhastBlock`, `TurtleEggBlock`, `FrogspawnBlock`, `SnifferEggBlock`.

* A **campfire** has four slots for food. While it is lit, every item in a slot cooks for the
  time of its recipe (600 game ticks) and is then thrown out as an item entity
  (`CampfireBlockEntity.cookTick`); while it is not, the progress of every slot goes back by two
  per game tick (`cooldownTick`). As long as something changes, the comparators around are
  updated every tick (`BlockEntity.setChanged`), although a campfire has no comparator output.
  A player puts food in with `use_item`, and puts a lit campfire out with a shovel. A campfire
  on a hay bale is a signal fire (`updateShape`). A waterlogged campfire schedules the fluid
  tick of its water when a neighbour changes. Replacing the campfire throws its food out.
* A **cobweb** and **powder snow** slow down the entities inside them
  (`Entity.makeStuckInBlock`, in `Redstone.Entity.Physics`). Powder snow also draws from the
  level's random number generator for a particle when the entity moves sideways.
* A **nether portal** block disappears when a neighbour in its plane changes to something that
  is not a portal and the frame around it is no longer complete (`PortalShape.findAnyShape`).
* A **carved pumpkin** or jack o'lantern that is placed looks for the blocks of a snow golem,
  an iron golem or a copper golem around it (`BlockPattern.find`).
* A **dried ghast** takes up water in four steps of a scheduled tick, or dries again, and
  schedules the fluid tick of its water like the campfire.
* **Turtle eggs** are trampled by living entities that step on them, one chance in a hundred
  per step.
* **Frogspawn** stays only on a water source with no fluid in its own cell; when it is placed
  it schedules its hatching at a random time; a falling block that touches it breaks it.
* A **sniffer egg** cracks twice and then hatches, each step a scheduled tick whose delay is
  drawn when the state is placed.

## What is left out

Everything that makes a mob sets `Level.overflow`, since mobs are not modelled: the golem a
carved pumpkin completes, the happy ghast of a soaked dried ghast, the tadpoles of frogspawn
and the sniffer of a sniffer egg. So does every entity that touches a nether portal (it would
leave for the nether).

* **A burning projectile lights a campfire** (`CampfireBlock.onProjectileHit`). The model keeps
  no fire of entities (`Entities.Projectile`), so it cannot tell whether the projectile burns:
  a projectile that hits a campfire that could be lit sets `Level.overflow`. Nothing calls the
  hook yet anyway, as projectiles do not fly in the model.
* **Water that flows into a campfire or a dried ghast** (`placeLiquid`) is defined here
  (`placeLiquid`), with the fluid tick scheduled through `Level.scheduleFluidTick`, but nothing
  calls it until fluids flow (`Redstone.Mechanics.Fluid`).
* Lighting a campfire with flint and steel or a fire charge, and a water bucket or a splash
  potion putting it out: these are `ItemStack.useOn` and potions, which are not modelled.
* The damage a lit campfire does to the living entities inside it, and the freezing of living
  entities in powder snow: both set `Level.overflow`. For the other entities the freezing and
  extinguishing in powder snow (`InsideBlockEffectApplier`) are left out silently, and so is a
  burning entity breaking powder snow: fire and freezing of entities are not kept.
* The collision shape of powder snow depends on the entity (`PowderSnowBlock.getCollisionShape`:
  none for an item, a full cube for a falling block, most of a cube for anything that has
  fallen more than 2.5 blocks). `Redstone.Entity.Physics` does not have it and sets
  `Level.overflow` when a moving entity comes near powder snow, so what powder snow does to an
  entity is defined here but cannot be observed yet. The shape by which an entity touches
  powder snow (`getEntityInsideCollisionShape`) is that collision shape if it is not empty;
  `Redstone.Entity.Touch` takes the full cube, which is only right as long as the collision
  shape is empty, and has to change together with `Redstone.Entity.Physics`.
* Primed TNT and minecarts move by code of their own, which has no speed multiplier:
  `Level.makeStuckInBlock` sets `Level.overflow` for them.
* The random ticks of turtle eggs (hatching, which depends on the time of day through an
  environment attribute) set `Level.overflow`. Those of a nether portal (zombified piglins) do
  nothing here: the game asks `isSpawningMonsters()` before it draws a number, and the world
  of the tests has the spawn rules off (`tests/FORMAT.md`). The level has no field for these
  rules, so in a world where monsters spawn the model would be one draw short.
* Cats and ocelots step carefully when they crouch, which the model does not know: one of them
  on turtle eggs sets `Level.overflow`.
* Sounds, particles and the cooking recipes' experience.

## Scenarios that wait in `tests/pending/scenarios/special-block`

* `web-tnt`, `web-cart-fall`, `web-cart-rail`: primed TNT and minecarts in a cobweb. They need
  the stuck speed in `Redstone.Entity.PrimedTnt` and `Redstone.Entity.Minecart` (see above).
* `snow-*` (nine scenarios): items, falling blocks, TNT and minecarts in powder snow. They need
  the collision shape of powder snow in `Redstone.Entity.Physics` (see above).
* `campfire-arrow-burning`: a burning arrow shot at a campfire. It needs the flight of
  projectiles, and their fire.
* `campfire-water-source-forms`, `ghast-water-source-forms`: a water source forms in the cell of
  a campfire or a dried ghast between two sources. They need the flow of fluids, which has to
  call `placeLiquid`.
* `ghast-random-ticks`: a dried ghast soaking and drying. It needs the random ticks of the
  chunks (`Redstone.Mechanics.RandomTick`), which give the ghast its scheduled ticks.
* `pumpkin-snow-golem`, `pumpkin-iron-golem`, `pumpkin-copper-golem`, `pumpkin-golem-nearby`,
  `pumpkin-copper-far` and `portal-item`: a golem is built, or an item falls into a portal. The
  model sets `Level.overflow` at the right tick and will not do more: mobs and other dimensions
  are not modelled.
-/

@[expose] public section

namespace Redstone.Component.SpecialBlock

/-! ### The level's random number generator -/

/-- `level.getRandom().nextFloat()` where the value is only used for a sound. -/
def skipFloat : M Unit := modify fun l => { l with random := l.random.nextFloat24.2 }

/-- `level.getRandom().nextBoolean()`. -/
def nextBool : M Bool :=
  modifyGet fun l =>
    let (v, r) := l.random.nextBool
    (v, { l with random := r })

/-- `Fluids.WATER.getTickDelay(level)`. -/
def waterTickDelay : ℕ := 5

/-! ### Entities -/

/-- The entity is a `LivingEntity`. Only entities the model does not move can be. An entity of a
type the model has no table entry for counts as not living. -/
def isLiving (e : Entity) : Bool :=
  match e.data with
  | .other type _ => (Entity.Still.typeInfo? type).any (·.living)
  | _ => false

/-! ### Campfire -/

/-- The recipes of type `campfire_cooking`: ingredient and result. All of them take 600 game
ticks (`cookingTime`). -/
def campfireRecipes : List (String × String) :=
  [("minecraft:potato", "minecraft:baked_potato"),
    ("minecraft:beef", "minecraft:cooked_beef"),
    ("minecraft:chicken", "minecraft:cooked_chicken"),
    ("minecraft:cod", "minecraft:cooked_cod"),
    ("minecraft:mutton", "minecraft:cooked_mutton"),
    ("minecraft:porkchop", "minecraft:cooked_porkchop"),
    ("minecraft:rabbit", "minecraft:cooked_rabbit"),
    ("minecraft:salmon", "minecraft:cooked_salmon"),
    ("minecraft:kelp", "minecraft:dried_kelp")]

/-- The cooking time of every campfire recipe. -/
def campfireCookingTime : ℤ := 600

/-- The item tag `minecraft:douses_campfires`: the shovels. -/
def dousesCampfires : List String :=
  ["minecraft:diamond_shovel", "minecraft:stone_shovel", "minecraft:golden_shovel",
    "minecraft:netherite_shovel", "minecraft:wooden_shovel", "minecraft:iron_shovel",
    "minecraft:copper_shovel"]

/-- The block entity of the campfire at `p`. -/
def getCampfire (p : Pos) : M (Option BlockEntities.Campfire) := do
  match ← Level.getBlockEntity p with
  | some (.campfire d) => return some d
  | _ => return none

/-- `BlockEntity.setChanged(level, pos, state)`: the comparators that could read the block are
told. -/
def setChanged (p : Pos) (block : BlockId) : M Unit := Level.updateNeighbourForOutputSignal p block

/-- One slot of `CampfireBlockEntity.cookTick`: the item in the slot cooks one tick more; when
its time is up, the result of its recipe (or the item itself if it has none) is thrown out
(`Containers.dropItemStack`) and the slot is emptied. The progress of the slot stays as it is.
Returns whether there was an item. -/
def cookSlot (state : Block) (p : Pos) (slot : ℕ) : M Bool := do
  let some d ← getCampfire p | return false
  let stack := d.items.getItem slot
  if stack.isEmpty then return false
  let progress := d.cookingProgress.getD slot 0 + 1
  let d := { d with cookingProgress := d.cookingProgress.set slot progress }
  if progress ≥ d.cookingTime.getD slot 0 then
    let result :=
      match campfireRecipes.lookup stack.item with
      | some r => ItemStack.of r
      | none => stack
    ItemDrop.dropItemStack p result
    Level.setBlockEntity p (.campfire { d with items := d.items.setItem slot .empty })
    Level.gameEvent "minecraft:block_change" p { affectedState := some state }
  else Level.setBlockEntity p (.campfire d)
  return true

/-- `CampfireBlockEntity.cookTick`: the ticker of a lit campfire. -/
def cookTick (state : Block) (p : Pos) : M Unit := do
  let changed ← (List.range BlockEntities.Campfire.numSlots).mapM (cookSlot state p)
  if changed.any id then setChanged p state.id

/-- `CampfireBlockEntity.cooldownTick`: the ticker of a campfire that is not lit. The progress
of every slot goes back by two, between zero and the cooking time of the slot. -/
def cooldownTick (state : Block) (p : Pos) : M Unit := do
  let some d ← getCampfire p | return
  if d.cookingProgress.any (· > 0) then
    let cool (progress time : ℤ) : ℤ :=
      -- `Mth.clamp(progress - 2, 0, time)`
      if progress > 0 then (if progress - 2 < 0 then 0 else min (progress - 2) time) else progress
    Level.setBlockEntity p (.campfire { d with
      cookingProgress := List.zipWith cool d.cookingProgress d.cookingTime })
    setChanged p state.id

/-- `CampfireBlockEntity.placeFood(level, sourceEntity, placeItem)` by a player: one item of the
kind goes into the first empty slot. Returns whether there was room. -/
def placeFood (state : Block) (p : Pos) (item : String) : M Bool := do
  let some d ← getCampfire p | return false
  let some slot := d.items.findIdx? ItemStack.isEmpty | return false
  Level.setBlockEntity p (.campfire { d with
    cookingTime := d.cookingTime.set slot campfireCookingTime
    cookingProgress := d.cookingProgress.set slot 0
    items := d.items.setItem slot (.of item) })
  Level.gameEvent "minecraft:block_change" p
    { sourceEntity := some .player, affectedState := some state }
  -- `markUpdated`
  setChanged p state.id
  return true

/-- `CampfireBlock.useItemOn` by a player holding `item`. Food goes on the fire, lit or not, and
the action is consumed even when there is no room; a shovel puts a lit campfire out. -/
def campfireUseItemOn (id : Blocks.Campfire.Id) (s : Blocks.Campfire) (p : Pos) (item : String) :
    M Bool := do
  if (← getCampfire p).isSome && (campfireRecipes.lookup item).isSome then
    discard <| placeFood (.campfire id s) p item
    return true
  if dousesCampfires.contains item && s.lit then
    -- `douse(player, level, pos, state)`
    Level.gameEvent "minecraft:block_change" p { sourceEntity := some .player }
    discard <| Level.setBlock p (.campfire id { s with lit := false })
    return true
  return false

/-- `CampfireBlock.placeLiquid(level, pos, state, fluidState)`: water flows into a campfire,
which becomes waterlogged and goes out. Returns whether the campfire took the fluid. -/
def campfirePlaceLiquid (id : Blocks.Campfire.Id) (s : Blocks.Campfire) (p : Pos)
    (fluid : FluidState) : M Bool := do
  if s.waterlogged || fluid.fluid != .water then return false
  if s.lit then Level.gameEvent "minecraft:block_change" p
  discard <| Level.setBlock p (.campfire id { s with waterlogged := true, lit := false })
  Level.scheduleFluidTick p fluid.fluid waterTickDelay
  return true

/-- The behaviour of a campfire or soul campfire. -/
def campfire (id : Blocks.Campfire.Id) (s : Blocks.Campfire) : Behaviour :=
  let self : Block := .campfire id s
  { Behaviour.inert self with
    -- `getTicker`: `cookTick` when lit, `cooldownTick` otherwise
    ticksBlockEntity := true
    blockEntityTick := fun p => if s.lit then cookTick self p else cooldownTick self p
    updateShape := fun p dir _ neighbour => do
      if s.waterlogged then Level.scheduleFluidTick p .water waterTickDelay
      -- `isSmokeSource`
      if dir = .down then return .campfire id { s with signal_fire := neighbour.is .hay_block }
      else return self
    useItemOn := fun p _ item => campfireUseItemOn id s p item
    onProjectileHit := fun _ _ _ _ => do
      -- a burning projectile would light the campfire; whether it burns is not known
      if !s.lit && !s.waterlogged then Level.setOverflow
    -- a lit campfire hurts the living entities inside it
    entityInside := fun _ i => do
      let some e ← Level.getEntity i | return
      if s.lit && isLiving e then Level.setOverflow
    -- `Containers.dropContents(level, pos, getItems())`
    preRemoveSideEffects := fun p => do
      if let some (.campfire d) ← Level.peekBlockEntity p then ItemDrop.dropContents p d.items }

/-! ### Cobweb and powder snow -/

/-- `WebBlock.entityInside`: the entity is slowed to a quarter of its speed sideways and a
twentieth of it vertically. The weaving effect of a living entity is not known. -/
def webEntityInside (i : ℕ) : M Unit :=
  Level.makeStuckInBlock i ⟨0.25, Phys.f 0x3d4ccccd, 0.25⟩

/-- `PowderSnowBlock.entityInside`: an entity that is not living, or a living one whose feet are
in powder snow, is slowed down, and when it moves sideways the level's random number generator
decides whether a snowflake appears, and where. -/
def powderSnowEntityInside (i : ℕ) : M Unit := do
  let some e ← Level.getEntity i | return
  -- `entity.getInBlockState().is(this)`
  if !isLiving e || ((← get).blockAt e.base.pos.blockPos).is .powder_snow then
    -- a living entity freezes, and is hurt once it is frozen
    if isLiving e then Level.setOverflow
    Level.makeStuckInBlock i ⟨Phys.f 0x3f666666, 1.5, Phys.f 0x3f666666⟩
    -- `getKnownMovement()` is the velocity of an entity that is no player
    let motion := e.base.motion
    if motion.x != 0.0 || motion.z != 0.0 then
      if ← nextBool then
        -- two `Mth.randomBetween` for the speed of the particle
        skipFloat
        skipFloat

/-! ### Nether portal -/

/-- The position `n` blocks from `p` in direction `d` (`BlockPos.relative(direction, n)`). -/
def relative (p : Pos) (d : Direction) (n : ℤ) : Pos :=
  match d with
  | .west => { p with x := p.x - n }
  | .east => { p with x := p.x + n }
  | .down => { p with y := p.y - n }
  | .up => { p with y := p.y + n }
  | .north => { p with z := p.z - n }
  | .south => { p with z := p.z + n }

namespace PortalShape

/-- `PortalShape.FRAME`: the block tag `minecraft:nether_portal_frame`, which is obsidian. -/
def isFrame (b : Block) : Bool := b.is .obsidian

/-- `PortalShape.isEmpty(state)`: air, fire (the block tag `minecraft:fire`) or a portal
block. -/
def isEmpty (b : Block) : Bool :=
  b.isAir || b.is .fire || b.is .soul_fire || b.is .nether_portal

/-- `MAX_WIDTH` and `MAX_HEIGHT`. -/
def maxSize : ℕ := 21

/-- The loop of `getDistanceUntilEdgeAboveFrame`, from the distance `width` on, for at most
`fuel` more blocks. -/
def distanceLoop (l : Level) (p : Pos) (d : Direction) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, width =>
    let q := relative p d width
    let state := l.blockAt q
    if !isEmpty state then (if isFrame state then width else 0)
    else if !isFrame (l.blockAt (q.step .down)) then 0
    else distanceLoop l p d fuel (width + 1)

/-- `getDistanceUntilEdgeAboveFrame(level, pos, direction)`: how many empty blocks with frame
below them lie between `p` and the frame block that ends the row in direction `d`; zero if the
row does not end in the frame within 21 blocks. -/
def getDistanceUntilEdgeAboveFrame (l : Level) (p : Pos) (d : Direction) : ℕ :=
  distanceLoop l p d (maxSize + 1) 0

/-- The descent of `calculateBottomLeft`: down for as long as the block below is empty, but not
below `minY`. -/
def descend (l : Level) (minY : ℤ) : ℕ → Pos → Pos
  | 0, p => p
  | fuel + 1, p =>
    if p.y > minY && isEmpty (l.blockAt (p.step .down)) then descend l minY fuel (p.step .down)
    else p

/-- `calculateBottomLeft(level, rightDir, pos)`: the lower left corner of the inside of the
frame around `p`, if the bottom row is closed on the left. The world of the tests begins at
`y = -64` (`level.getMinY()`). -/
def calculateBottomLeft (l : Level) (rightDir : Direction) (p : Pos) : Option Pos :=
  let minY := max (-64) (p.y - maxSize)
  let p := descend l minY maxSize p
  let leftDir := rightDir.opposite
  let edge := getDistanceUntilEdgeAboveFrame l p leftDir
  if edge = 0 then none else some (relative p leftDir ((edge : ℤ) - 1))

/-- `calculateWidth(level, bottomLeft, rightDir)`: the width of the inside, or zero if it is
not between 2 and 21. -/
def calculateWidth (l : Level) (bottomLeft : Pos) (rightDir : Direction) : ℕ :=
  let width := getDistanceUntilEdgeAboveFrame l bottomLeft rightDir
  if 2 ≤ width && width ≤ maxSize then width else 0

/-- One row of `getDistanceUntilTop`: the cells of the row from `i` on. Returns whether all of
them are empty, and the portal blocks counted up to the first that is not. -/
def scanRow (l : Level) (row : Pos) (rightDir : Direction) : ℕ → ℕ → Bool × ℕ
  | 0, _ => (true, 0)
  | fuel + 1, i =>
    let state := l.blockAt (relative row rightDir i)
    if !isEmpty state then (false, 0)
    else
      let (ok, count) := scanRow l row rightDir fuel (i + 1)
      (ok, count + (if state.is .nether_portal then 1 else 0))

/-- `getDistanceUntilTop`: the rows of the inside from the row `height` on, for at most `fuel`
more rows. A row counts when the frame is on both of its sides and all its cells are empty.
Returns the number of rows that count and the number of portal blocks seen, those of the row
that did not count included. -/
def distanceUntilTop (l : Level) (bottomLeft : Pos) (rightDir : Direction) (width : ℕ) :
    ℕ → ℕ → ℕ × ℕ
  | 0, height => (height, 0)
  | fuel + 1, height =>
    let row := relative bottomLeft .up height
    if !isFrame (l.blockAt (relative row rightDir (-1))) then (height, 0)
    else if !isFrame (l.blockAt (relative row rightDir width)) then (height, 0)
    else
      let (ok, count) := scanRow l row rightDir width 0
      if !ok then (height, count)
      else
        let (top, more) := distanceUntilTop l bottomLeft rightDir width fuel (height + 1)
        (top, count + more)

/-- `hasTopFrame`: the row above the inside is frame. -/
def hasTopFrame (l : Level) (bottomLeft : Pos) (rightDir : Direction) (width height : ℕ) : Bool :=
  (List.range width).all fun i =>
    isFrame (l.blockAt (relative (relative bottomLeft .up height) rightDir i))

/-- `PortalShape.findAnyShape(level, pos, axis).isComplete()`: the block at `p` lies inside a
frame of obsidian in the plane of `axis`, between 2 and 21 blocks wide and between 3 and 21
high, and every cell inside is a portal block. -/
def isComplete (l : Level) (p : Pos) (axis : AxisXZ) : Bool :=
  let rightDir : Direction :=
    match axis with
    | .x => .west
    | .z => .south
  match calculateBottomLeft l rightDir p with
  | none => false
  | some bottomLeft =>
    let width := calculateWidth l bottomLeft rightDir
    if width = 0 then false
    else
      let (top, count) := distanceUntilTop l bottomLeft rightDir width maxSize 0
      -- `calculateHeight`
      let height :=
        if 3 ≤ top && top ≤ maxSize && hasTopFrame l bottomLeft rightDir width top then top else 0
      3 ≤ height && count = width * height

end PortalShape

/-- The behaviour of a nether portal block. -/
def netherPortal (s : Blocks.NetherPortal) : Behaviour :=
  let self : Block := .netherPortal s
  { Behaviour.inert self with
    updateShape := fun p dir _ neighbour => do
      let wrongAxis :=
        match s.axis, dir.axis with
        | .x, .z | .z, .x => true
        | _, _ => false
      if !wrongAxis && !neighbour.is .nether_portal && !PortalShape.isComplete (← get) p s.axis then
        return .AIR
      else return self
    -- `setAsInsidePortal`: the entity leaves for the nether, which is not modelled
    entityInside := fun _ _ => Level.setOverflow }

/-! ### Carved pumpkin -/

/-- A `BlockPattern` of depth one: its rows from top to bottom, each a list of predicates from
left to right. -/
abbrev Pattern := List (List (Block → Bool))

namespace Pattern

/-- `Direction.getUnitVec3i()`. -/
def unit : Direction → ℤ × ℤ × ℤ
  | .west => (-1, 0, 0)
  | .east => (1, 0, 0)
  | .down => (0, -1, 0)
  | .up => (0, 1, 0)
  | .north => (0, 0, -1)
  | .south => (0, 0, 1)

/-- `BlockPattern.translateAndRotate(pos, forwards, up, right, down, 0)`: the cell `right`
columns to the right and `down` rows below the corner `p` of a pattern that looks along
`forwards` with its top towards `top`. -/
def translateAndRotate (p : Pos) (forwards top : Direction) (right down : ℕ) : Pos :=
  let (fx, fy, fz) := unit forwards
  let (ux, uy, uz) := unit top
  -- `forwardsVector.cross(upVector)`
  let (rx, ry, rz) : ℤ × ℤ × ℤ := (fy * uz - fz * uy, fz * ux - fx * uz, fx * uy - fy * ux)
  ⟨p.x + ux * -(down : ℤ) + rx * right, p.y + uy * -(down : ℤ) + ry * right,
    p.z + uz * -(down : ℤ) + rz * right⟩

/-- `BlockPattern.matches(testPos, forwards, up, cache)` is not null. -/
def matchesAt (pattern : Pattern) (l : Level) (p : Pos) (forwards top : Direction) : Bool :=
  pattern.zipIdx.all fun (row, down) =>
    row.zipIdx.all fun (test, right) =>
      test (l.blockAt (translateAndRotate p forwards top right down))

/-- `BlockPattern.find(level, origin)` is not null: the pattern is found with its corner in the
cube that begins at `origin` and is as large as the pattern's longest side, in one of its 24
orientations. -/
def find (pattern : Pattern) (l : Level) (origin : Pos) : Bool :=
  let width := (pattern.map List.length).foldl max 0
  let dist := max (max width pattern.length) 1
  let offsets := List.range dist
  offsets.any fun dx => offsets.any fun dy => offsets.any fun dz =>
    let p : Pos := ⟨origin.x + dx, origin.y + dy, origin.z + dz⟩
    Direction.values.any fun forwards => Direction.values.any fun top =>
      top != forwards && top != forwards.opposite && pattern.matchesAt l p forwards top

end Pattern

/-- `PUMPKINS_PREDICATE`. -/
def isPumpkin (b : Block) : Bool := b.is .carved_pumpkin || b.is .jack_o_lantern

/-- The block tag `minecraft:copper`. -/
def isCopper (b : Block) : Bool :=
  b.is .copper_block || b.is .exposed_copper || b.is .weathered_copper || b.is .oxidized_copper ||
    b.is .waxed_copper_block || b.is .waxed_exposed_copper || b.is .waxed_weathered_copper ||
    b.is .waxed_oxidized_copper

/-- `getOrCreateSnowGolemFull`. -/
def snowGolemFull : Pattern :=
  [[isPumpkin], [(·.is .snow_block)], [(·.is .snow_block)]]

/-- `getOrCreateIronGolemFull`. -/
def ironGolemFull : Pattern :=
  let iron (b : Block) : Bool := b.is .iron_block
  [[Block.isAir, isPumpkin, Block.isAir], [iron, iron, iron], [Block.isAir, iron, Block.isAir]]

/-- `getOrCreateCopperGolemFull`. -/
def copperGolemFull : Pattern := [[isPumpkin], [isCopper]]

/-- The behaviour of a carved pumpkin or jack o'lantern: `trySpawnGolem` when it is placed. The
game looks for the three patterns near the pumpkin, in every orientation; a golem is a mob,
so finding one of them sets `Level.overflow`. -/
def carvedPumpkin (id : Blocks.CarvedPumpkin.Id) (s : Blocks.CarvedPumpkin) : Behaviour :=
  let self : Block := .carvedPumpkin id s
  { Behaviour.inert self with
    onPlace := fun p old _ => do
      if old.id != self.id then
        let l ← get
        if snowGolemFull.find l p || ironGolemFull.find l p || copperGolemFull.find l p then
          Level.setOverflow }

/-! ### Dried ghast -/

/-- `DriedGhastBlock.HYDRATION_TICK_DELAY`. -/
def hydrationTickDelay : ℕ := 5000

/-- `DriedGhastBlock.placeLiquid(level, pos, state, fluidState)`: water flows into a dried
ghast. Returns whether the block took the fluid. -/
def driedGhastPlaceLiquid (s : Blocks.DriedGhast) (p : Pos) (fluid : FluidState) : M Bool := do
  if s.waterlogged || fluid.fluid != .water then return false
  discard <| Level.setBlock p (.driedGhast { s with waterlogged := true })
  Level.scheduleFluidTick p fluid.fluid waterTickDelay
  return true

/-- The behaviour of a dried ghast. -/
def driedGhast (s : Blocks.DriedGhast) : Behaviour :=
  let self : Block := .driedGhast s
  { Behaviour.inert self with
    updateShape := fun p _ _ _ => do
      if s.waterlogged then Level.scheduleFluidTick p .water waterTickDelay
      return self
    tick := fun p => do
      if s.waterlogged then
        -- `tickWaterlogged`
        if h : s.hydration.val < 3 then
          discard <| Level.setBlock p
            (.driedGhast { s with hydration := ⟨s.hydration.val + 1, by omega⟩ })
            2
          Level.gameEvent "minecraft:block_change" p { affectedState := some self }
        else
          -- `spawnGhastling`: a happy ghast, which is a mob
          discard <| Level.removeBlock p false
          Level.setOverflow
      else if h : s.hydration.val > 0 then
        have := s.hydration.isLt
        discard <| Level.setBlock p
          (.driedGhast { s with hydration := ⟨s.hydration.val - 1, by omega⟩ }) 2
        Level.gameEvent "minecraft:block_change" p { affectedState := some self }
    randomTick := fun p => do
      if (s.waterlogged || s.hydration.val > 0) && !(← get).hasScheduledTick p .dried_ghast then
        Level.scheduleTick p .dried_ghast hydrationTickDelay }

/-! ### Turtle eggs -/

/-- `TurtleEggBlock.decreaseEggs`: one egg breaks; the last one takes the block with it. -/
def decreaseEggs (s : Blocks.TurtleEgg) (p : Pos) : M Unit := do
  skipFloat
  if h : s.eggs.val ≤ 1 then discard <| Level.destroyBlock p false
  else
    discard <| Level.setBlock p
      (.turtleEgg { s with eggs := ⟨s.eggs.val - 1, by omega, by have := s.eggs.le_hi; omega⟩ }) 2
    Level.gameEvent "minecraft:block_destroy" p { affectedState := some (.turtleEgg s) }

/-- The behaviour of turtle eggs. -/
def turtleEgg (s : Blocks.TurtleEgg) : Behaviour :=
  let self : Block := .turtleEgg s
  { Behaviour.inert self with
    -- `destroyEgg(level, state, pos, entity, 100)` unless the entity steps carefully
    stepOn := fun p i => do
      let some e ← Level.getEntity i | return
      -- `canDestroyEgg`: a living entity that is neither a turtle nor a bat (the game rule
      -- `mob_griefing` is on)
      let type := e.data.typeName
      if isLiving e && type != "minecraft:turtle" && type != "minecraft:bat" then
        -- `isSteppingCarefully` of a crouching cat
        if type == "minecraft:cat" || type == "minecraft:ocelot" then Level.setOverflow
        else if (← ItemDrop.nextInt 100) == 0 then decreaseEggs s p
    -- hatching depends on the time of day through an environment attribute
    randomTick := fun _ => Level.setOverflow }

/-! ### Frogspawn -/

/-- `FrogspawnBlock.mayPlaceOn(level, pos.below())`: the block below holds a water source (the
fluid tag `minecraft:supports_frogspawn`; the block tag of that name is empty) and the cell of
the frogspawn holds no fluid. -/
def frogspawnCanSurvive (l : Level) (p : Pos) : Bool :=
  (l.fluidStateAt (p.step .down)).fluid == .water && (l.fluidStateAt p).isEmpty

/-- The behaviour of frogspawn. -/
def frogspawn : Behaviour :=
  let self : Block := .plain .frogspawn
  { Behaviour.inert self with
    canSurvive := frogspawnCanSurvive
    -- `getFrogspawnHatchDelay`: `random.nextInt(3600, 12000)`
    onPlace := fun p _ _ => do
      Level.scheduleTick p .frogspawn (3600 + (← ItemDrop.nextInt 8400))
    updateShape := fun p _ _ _ => do
      if frogspawnCanSurvive (← get) p then return self else return .AIR
    tick := fun p => do
      let survives := frogspawnCanSurvive (← get) p
      discard <| Level.destroyBlock p false
      -- `hatchFrogspawn`: tadpoles, which are mobs
      if survives then Level.setOverflow
    entityInside := fun p i => do
      let some e ← Level.getEntity i | return
      if let .fallingBlock _ := e.data then discard <| Level.destroyBlock p false }

/-! ### Sniffer egg -/

/-- The behaviour of a sniffer egg. Every state that is placed, the cracked ones included,
schedules the next step: a third of the hatching time (which is halved on moss, the block tag
`minecraft:sniffer_egg_hatch_boost`) plus up to 300 game ticks. -/
def snifferEgg (s : Blocks.SnifferEgg) : Behaviour :=
  let self : Block := .snifferEgg s
  { Behaviour.inert self with
    onPlace := fun p _ _ => do
      let boosted := ((← get).blockAt (p.step .down)).is .moss_block
      Level.gameEvent "minecraft:block_place" p { affectedState := some self }
      Level.scheduleTick p .sniffer_egg
        ((if boosted then 4000 else 8000) + (← ItemDrop.nextInt 300))
    tick := fun p => do
      -- the pitch of the sound
      skipFloat
      if h : s.hatch.val < 2 then
        discard <| Level.setBlock p (.snifferEgg { s with hatch := ⟨s.hatch.val + 1, by omega⟩ }) 2
      else
        discard <| Level.destroyBlock p false
        -- a sniffer, which is a mob
        Level.setOverflow }

/-! ### The component -/

/-- `LiquidBlockContainer.placeLiquid(level, pos, state, fluidState)` for the blocks of this
component that override it: water flowing into the block `state` at `p`. `none` for the other
blocks. Nothing calls this yet: fluids do not flow (`Redstone.Mechanics.Fluid`). -/
def placeLiquid (state : Block) (p : Pos) (fluid : FluidState) : Option (M Bool) :=
  match state with
  | .campfire id s => some (campfirePlaceLiquid id s p fluid)
  | .driedGhast s => some (driedGhastPlaceLiquid s p fluid)
  | _ => none

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .campfire id s => campfire id s
  | .plain .cobweb => { Behaviour.inert self with entityInside := fun _ i => webEntityInside i }
  | .plain .powder_snow =>
    { Behaviour.inert self with entityInside := fun _ i => powderSnowEntityInside i }
  | .netherPortal s => netherPortal s
  | .carvedPumpkin id s => carvedPumpkin id s
  | .driedGhast s => driedGhast s
  | .turtleEgg s => turtleEgg s
  | .plain .frogspawn => frogspawn
  | .snifferEgg s => snifferEgg s
  | _ => .inert self

end Redstone.Component.SpecialBlock
