module

public import Redstone.Basic.Random
public import Redstone.Basic.Loot
public import Redstone.World.Basic
public import Redstone.Entity.Basic

/-!
# Levels

The full state of a world between two moments of the game (`ServerLevel`): the blocks, the
block entities, the scheduled ticks, the pending block events, the entities, the clock and the
random number generator, together with the working state of the neighbour updater.

Only one dimension is modelled, every chunk is loaded and ticking, and there are no build
limits.

The level has the state of the parts of the game that are not modelled yet, so that adding them
does not change this structure: the scheduled fluid ticks, the seed of the random ticks and the
game rules `random_tick_speed` and `block_drops`. With their default values (no fluid tick,
speed zero, no drops) these parts do nothing.
-/

@[expose] public section

namespace Redstone

/-- The priority of a scheduled tick (`TickPriority`). Higher priorities run first. -/
inductive TickPriority
  | extremelyHigh
  | veryHigh
  | high
  | normal
  | low
  | veryLow
  | extremelyLow
  deriving DecidableEq, Repr

namespace TickPriority

/-- The value of the priority, from `-3` (runs first) to `3` (runs last). -/
def value : TickPriority → ℤ
  | extremelyHigh => -3
  | veryHigh => -2
  | high => -1
  | normal => 0
  | low => 1
  | veryLow => 2
  | extremelyLow => 3

/-- `TickPriority.byValue`. -/
def ofValue (v : ℤ) : TickPriority :=
  if v ≤ -3 then extremelyHigh else if v = -2 then veryHigh else if v = -1 then high
  else if v = 0 then normal else if v = 1 then low else if v = 2 then veryLow else extremelyLow

end TickPriority

/-- A scheduled tick (`ScheduledTick<T>`) of a block (`T` is `Block`) or of a fluid (`T` is
`Fluid`). -/
structure ScheduledTickOf (α : Type) where
  pos : Pos
  /-- `type`: the block or the fluid that asked for the tick. The tick does nothing if another
  one is there when it runs. -/
  type : α
  /-- The game time at which the tick is due. -/
  trigger : ℕ
  priority : TickPriority
  /-- A counter that orders ticks of equal time and priority by when they were scheduled. The
  block ticks and the fluid ticks of a level draw it from the same counter. -/
  order : ℕ
  deriving DecidableEq, Repr

/-- A scheduled block tick (`ScheduledTick<Block>`). -/
abbrev ScheduledTick := ScheduledTickOf BlockId

/-- A scheduled fluid tick (`ScheduledTick<Fluid>`). -/
abbrev ScheduledFluidTick := ScheduledTickOf Fluid

namespace ScheduledTickOf

variable {α : Type}

/-- The block that asked for a block tick. -/
abbrev block (t : ScheduledTick) : BlockId := t.type

/-- The fluid that asked for a fluid tick. -/
abbrev fluid (t : ScheduledFluidTick) : Fluid := t.type

/-- `INTRA_TICK_DRAIN_ORDER`: by priority, then by scheduling order. -/
def intraLE (a b : ScheduledTickOf α) : Bool :=
  a.priority.value < b.priority.value || (a.priority.value == b.priority.value && a.order ≤ b.order)

/-- `DRAIN_ORDER`: by due time, then by priority, then by scheduling order. -/
def drainLE (a b : ScheduledTickOf α) : Bool :=
  a.trigger < b.trigger || (a.trigger == b.trigger && a.intraLE b)

/-- The chunk a tick belongs to. Ticks are queued per chunk. -/
def chunk (t : ScheduledTickOf α) : ℤ × ℤ := (t.pos.x / 16, t.pos.z / 16)

end ScheduledTickOf

/-- A pending block event (`BlockEventData`), such as a piston's order to extend. -/
structure BlockEvent where
  pos : Pos
  block : BlockId
  a : ℤ
  b : ℤ
  deriving DecidableEq, Repr

/-- An entry of the neighbour updater's stack (`CollectingNeighborUpdater.NeighborUpdates`). -/
inductive NeighborUpdate
  /-- The block at `pos` is told that its neighbour in direction `dir`, at `neighborPos`, now
  has the state `neighborState`. -/
  | shape (dir : Direction) (neighborState : Block) (pos neighborPos : Pos) (flags limit : ℕ)
  /-- The block at `pos` is told that a neighbour changed; `block` is the block that changed. -/
  | simple (pos : Pos) (block : BlockId)
  /-- As `simple`, but delivered to `state` whatever is at `pos` by then. -/
  | full (state : Block) (pos : Pos) (block : BlockId) (movedByPiston : Bool)
  /-- The neighbours of `source` are told, one after the other, that `block` changed. `idx` is
  the position in `Direction.updateOrder` of the next one. -/
  | multi (source : Pos) (block : BlockId) (skip : Option Direction) (idx : ℕ)
  deriving DecidableEq, Repr

/-- The weather of the overworld. Only the three settled states are modelled: the rain level and
the thunder level of the game are `0` or `1`, never in between. -/
inductive Weather
  | clear
  | rain
  | thunder
  deriving DecidableEq, Repr

/-- The state of a world. -/
structure Level where
  /-- The block at each position. -/
  world : World
  /-- The block entity at each position: a finite map, read as a function
  (`l.blockEntities p`). -/
  blockEntities : PosMap BlockEntity
  /-- The positions of the block entities that are ticked, in ticking order. -/
  blockEntityTickers : List Pos
  /-- Tickers added while block entities are being ticked; they join the list on the next tick. -/
  pendingBlockEntityTickers : List Pos
  /-- Block entities are being ticked right now. -/
  tickingBlockEntities : Bool
  /-- `ServerLevel.isHandlingTick()`: the level is in the first part of a game tick, in which
  scheduled ticks and block events run. It is false while entities and block entities are
  ticked, and between game ticks. -/
  handlingTick : Bool := false
  /-- The positions of the block entities ticked in the current game tick, or in the last one
  when no game tick is running. It is emptied when `handlingTick` ends, just before entities
  and block entities are ticked. When `handlingTick` is false, a block entity that records the
  time of its last tick (`PistonMovingBlockEntity.lastTicked`) was last ticked at the current
  game time exactly when its position is in this list. -/
  tickedBlockEntities : List Pos := []
  /-- The scheduled ticks that are waiting. No two have the same position and block. -/
  ticks : List ScheduledTick
  /-- The scheduled ticks collected for the current game tick that have not run yet. -/
  ticksToRun : List ScheduledTick
  /-- The counter from which `ScheduledTick.order` is drawn. -/
  subTickCount : ℕ
  /-- The pending block events, in order, without repetition. -/
  blockEvents : List BlockEvent
  /-- The living entities, in the order in which they are ticked. -/
  entities : List Entity
  /-- The index the next entity will get. -/
  nextEntityIndex : ℕ
  /-- The game time: the number of game ticks the level has run. -/
  gameTime : ℕ
  /-- The level's random number generator. -/
  random : JavaRandom
  /-- The server's random sequences (`RandomSequences`) that have been used, by key: the
  generator each loot table draws from. A sequence that is not in the list has not been used
  yet, and starts from the world seed and its key (`ChanceLoot.newSequence`). -/
  lootSequences : List (String × Xoroshiro) := []
  /-- The neighbour updater's stack; the head is the top. -/
  updateStack : List NeighborUpdate
  /-- The updates added while the top of the stack was running. -/
  updatesAdded : List NeighborUpdate
  /-- The number of updates added since the updater started running; zero when it is idle. -/
  updateCount : ℕ
  /-- Set when a computation was cut short because a bound of the model was reached: the
  nesting depth of block reactions or the length of a loop. A level with this flag is not a
  faithful image of the game any more. -/
  overflow : Bool
  /-- `RedstoneTorchBlock.RECENT_TOGGLES` for this level: the position and game time of the
  recent times a redstone torch was switched off, oldest first. It decides when a torch burns
  out. The game keeps it outside the level and does not save it. -/
  recentTorchToggles : List (Pos × ℕ) := []
  /-- The overworld clock (`WorldClocks.OVERWORLD`, `totalTicks`): the time of day is this value
  modulo 24000. -/
  dayTime : ℕ := 6000
  /-- The game rule `advance_time`: the overworld clock advances by one every game tick. -/
  advanceTime : Bool := false
  /-- The weather. It does not change. -/
  weather : Weather := .clear
  /-- The blocks as the light engine last saw them. The light engine runs between two game
  ticks, so light read during a game tick is the light of the world as it was when the tick
  began. `Level.tick` copies `world` here; a level that is built by hand and used before its
  first tick has to set both. -/
  lightWorld : World := world
  /-- The containers whose menu the player of the `use` actions has open (`containerMenu`): the
  positions of the chests or the barrel on which closing the menu will call `stopOpen`. Empty
  when the player has no menu open, or one whose container does not count its viewers. -/
  playerMenu : List Pos := []
  /-- The scheduled fluid ticks that are waiting (`ServerLevel.fluidTicks`). No two have the same
  position and fluid. -/
  fluidTicks : List ScheduledFluidTick := []
  /-- The scheduled fluid ticks collected for the current game tick that have not run yet. -/
  fluidTicksToRun : List ScheduledFluidTick := []
  /-- `Level.randValue`, as an unsigned 32-bit number: the seed from which `getBlockRandomPos`
  draws the positions of the random ticks. -/
  randValue : ℕ := 0
  /-- The game rule `random_tick_speed`: how many blocks of every chunk section get a random
  tick in a game tick. With zero there are no random ticks. -/
  randomTickSpeed : ℕ := 0
  /-- The game rule `block_drops`: a block that is broken drops its loot. Drops are not
  modelled: with the rule on, `Level.dropResources` and `Level.popResource` (the drops of a
  broken block and of an exploded one) set `overflow`. -/
  blockDrops : Bool := false
  /-- The corners of a box that contains every block that can get a random tick. The game goes
  through the sections of the loaded chunks; the model has no chunks, so a level in which
  random ticks are to run has to name the region. Without it no block gets a random tick. -/
  randomTickBox : Option (Pos × Pos) := none
  /-- How many times `RandomSource.create()` has been called since the level was loaded. The
  game gives every such generator a seed that depends on how many were made before; entities
  with a generator of their own are seeded this way (`Level.createRandomSource`). -/
  randomSourceCount : ℕ := 0
  /-- The game rule `fire_spread_radius_around_player`: fire spreads, burns blocks and goes out
  only within this distance of a player, and everywhere if the value is -1
  (`ServerLevel.canSpreadFireAround`). There is no player in the model, so fire is active only
  with -1; with the default of the game it burns for ever and does nothing else. -/
  fireSpreadRadiusAroundPlayer : ℤ := 128
  /-- The block state for which the game bound the ticker of a block entity, where that is not
  the state at its position any more (`LevelChunk.updateBlockEntityTicker` binds the ticker
  when the block entity is added, and a ticker keeps running after the block changed to
  another state of the same block). Positions that are not listed tick with the state that is
  there. Nothing reads or writes this field yet: every block entity ticks with the state at
  its position. -/
  blockEntityTickerStates : List (Pos × Block) := []
  deriving Repr

namespace Level

/-- The level with no blocks, no entities and nothing pending, at game time zero. -/
def empty : Level where
  world := .empty
  blockEntities := .empty
  blockEntityTickers := []
  pendingBlockEntityTickers := []
  tickingBlockEntities := false
  ticks := []
  ticksToRun := []
  subTickCount := 0
  blockEvents := []
  entities := []
  nextEntityIndex := 0
  gameTime := 0
  random := .ofSeed 0
  updateStack := []
  updatesAdded := []
  updateCount := 0
  overflow := false

instance : Inhabited Level := ⟨empty⟩

/-- The block at `p` (`getBlockState`). -/
def blockAt (l : Level) (p : Pos) : Block := l.world.blockAt p

/-- The attributes that decide what the block at `p` can support (`BlockState.isFaceSturdy`,
which reads `getBlockSupportShape(level, pos)`). They are the attributes of the block state,
except for a `moving_piston`, whose shape comes from its block entity
(`PistonMovingBlockEntity.getCollisionShape`):

* for the base of a piston that is retracting (`isSourcePiston`, not `extending`) the shape
  contains that of the extended base, so whatever the extended base supports is supported, the
  face at its back in particular; the head that is still moving in is not taken into account;
* a moved block that has arrived (`progress` is 1) has its own shape;
* any other `moving_piston` is treated as supporting nothing. -/
def supportAttrs (l : Level) (p : Pos) : Attrs :=
  let b := l.blockAt p
  match b, l.blockEntities p with
  | .movingPiston _, some (.piston e) =>
    if e.isSourcePiston then
      match e.movedState with
      | .pistonBase id s =>
        if e.extending then b.attrs else (Block.pistonBase id { s with extended := true }).attrs
      | _ => b.attrs
    else if e.progress ≥ 1 then e.movedState.attrs
    else b.attrs
  | _, _ => b.attrs

/-- Replaces the block at `p` and nothing else: no reactions, no updates. -/
def setBlockRaw (l : Level) (p : Pos) (b : Block) : Level := { l with world := l.world.set p b }

/-- `hasScheduledTick`: a tick of `block` at `p` is waiting. Ticks collected for the current
game tick do not count. -/
def hasScheduledTick (l : Level) (p : Pos) (block : BlockId) : Bool :=
  l.ticks.any fun t => t.pos == p && t.block == block

/-- `willTickThisTick`: a tick of `block` at `p` was collected for the current game tick and has
not run yet. -/
def willTickThisTick (l : Level) (p : Pos) (block : BlockId) : Bool :=
  l.ticksToRun.any fun t => t.pos == p && t.block == block

/-- `hasScheduledTick` for fluids: a tick of `fluid` at `p` is waiting. -/
def hasScheduledFluidTick (l : Level) (p : Pos) (fluid : Fluid) : Bool :=
  l.fluidTicks.any fun t => t.pos == p && t.fluid == fluid

/-- `BlockGetter.getFluidState(pos)`: the fluid held by the block at `p`. -/
def fluidStateAt (l : Level) (p : Pos) : FluidState := (l.blockAt p).fluidState

/-- The entity with the given index, if it is alive. -/
def entity? (l : Level) (index : ℕ) : Option Entity := l.entities.find? (·.index == index)

end Level

/-! ### The order in which due ticks run -/

namespace ScheduledTickOf

variable {α : Type}

/-- Inserts a tick into a queue sorted by `drainLE`. -/
def insertSorted (t : ScheduledTickOf α) : List (ScheduledTickOf α) → List (ScheduledTickOf α)
  | [] => [t]
  | u :: us => if t.drainLE u then t :: u :: us else u :: insertSorted t us

/-- The ticks in `DRAIN_ORDER`: the order in which a trace lists the scheduled ticks. -/
def sortTicks (ts : List (ScheduledTickOf α)) : List (ScheduledTickOf α) :=
  ts.foldl (fun acc t => insertSorted t acc) []

/-- Adds a tick to the queue of its chunk, creating the queue if needed. -/
def addToQueues (t : ScheduledTickOf α) :
    List ((ℤ × ℤ) × List (ScheduledTickOf α)) → List ((ℤ × ℤ) × List (ScheduledTickOf α))
  | [] => [(t.chunk, [t])]
  | (c, q) :: qs => if c = t.chunk then (c, insertSorted t q) :: qs else (c, q) :: addToQueues t qs

/-- The queue whose first tick comes first in `intraLE`, and the other queues. Empty queues are
dropped. -/
def pickQueue : List (List (ScheduledTickOf α)) →
    Option (List (ScheduledTickOf α) × List (List (ScheduledTickOf α)))
  | [] => none
  | [] :: qs => pickQueue qs
  | (t :: ts) :: qs =>
    match pickQueue qs with
    | none => some (t :: ts, [])
    | some ([], rest) => some (t :: ts, rest)
    | some (u :: us, rest) =>
      if t.intraLE u then some (t :: ts, (u :: us) :: rest) else some (u :: us, (t :: ts) :: rest)

/-- Splits a queue into its longest prefix of ticks that come no later than `bound`. -/
def takeUpTo (bound : Option (ScheduledTickOf α)) :
    List (ScheduledTickOf α) → List (ScheduledTickOf α) × List (ScheduledTickOf α)
  | [] => ([], [])
  | t :: ts =>
    if bound.all t.intraLE then
      let (a, b) := takeUpTo bound ts
      (t :: a, b)
    else ([], t :: ts)

/-- Merges the per-chunk queues of due ticks as `LevelTicks.drainContainers` does: take the
queue whose head comes first, drain it for as long as its head does not come after the head of
the next best queue, and repeat. -/
def mergeQueues : ℕ → List (List (ScheduledTickOf α)) → List (ScheduledTickOf α)
  | 0, _ => []
  | fuel + 1, qs =>
    match pickQueue qs with
    | none => []
    | some ([], _) => []
    | some (t :: ts, rest) =>
      let bound := (pickQueue rest).bind fun (q, _) => q.head?
      let (taken, left) := takeUpTo bound ts
      t :: taken ++ mergeQueues fuel (left :: rest)

/-- The ticks among `ticks` that are due at time `now`, in the order in which the game runs
them. When every due tick is due exactly at `now` this is the order of `intraLE`; ticks that
are overdue are favoured only within their own chunk. -/
def dueInOrder (now : ℕ) (ticks : List (ScheduledTickOf α)) : List (ScheduledTickOf α) :=
  let due := ticks.filter (·.trigger ≤ now)
  let queues := due.foldl (fun qs t => addToQueues t qs) []
  mergeQueues due.length (queues.map (·.2))

end ScheduledTickOf

end Redstone
