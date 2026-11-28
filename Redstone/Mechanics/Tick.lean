module

public import Redstone.Mechanics.Power
public import Redstone.Mechanics.Fluid
public import Redstone.Mechanics.RandomTick

/-!
# Game ticks

One game tick of the level (`ServerLevel.tick`). The phases that matter for redstone run in
this order:

1. the overworld clock advances (if the game rule `advance_time` is set), and so does the game
   time; the light engine has caught up with the blocks since the previous tick;
2. the scheduled block ticks that are due run, at most 65536 of them;
3. the scheduled fluid ticks that are due run, with the same limit;
4. the chunks are ticked (`ServerChunkCache.tick`): the random ticks;
5. the block events run, including those queued while running them;
6. the entities are ticked;
7. the block entities are ticked.

A fluid tick makes water and lava flow (`Redstone.Mechanics.Fluid`). Phase 4 gives the
blocks their random ticks (`Redstone.Mechanics.RandomTick`). In a level without
scheduled fluid ticks and with the game rule `random_tick_speed` at zero phases 3 and 4 leave
the level as it is (`runFluidTicks_of_empty`, `tickChunks_of_speed_zero`), so circuits that
have neither never look into them.

The weather cycle, the world border, raids and mob spawning are left out.

Actions of players reach the server between two ticks, so a tick is the unit of time at which
the world can be observed.
-/

@[expose] public section

namespace Redstone

namespace Level

/-- `ServerLevel.tickBlock`: runs a scheduled tick, unless the block is no longer there. -/
def tickBlock (t : ScheduledTick) : M Unit := do
  let state ← getBlock t.pos
  if state.is t.block then (← behaviour state).tick t.pos

/-- `ServerLevel.MAX_SCHEDULED_TICKS_PER_TICK`: how many scheduled ticks of one kind (block or
fluid) are collected in one game tick. `LevelTicks.collectTicks` stops taking ticks from the
chunks' queues once it has this many; the others stay scheduled and run in a later game
tick. -/
def maxScheduledTicksPerTick : ℕ := 65536

/-- `LevelTicks.tick`: collects the scheduled ticks that are due, at most
`maxScheduledTicksPerTick`, and runs them in order. Ticks scheduled meanwhile wait for a later
game tick, even with delay zero. -/
def runScheduledTicks : M Unit := do
  let l ← get
  let due := (ScheduledTickOf.dueInOrder l.gameTime l.ticks).take maxScheduledTicksPerTick
  set { l with ticks := l.ticks.filter (!due.contains ·), ticksToRun := due }
  due.forM fun t => do
    modify fun l => { l with ticksToRun := l.ticksToRun.tail }
    tickBlock t
  modify fun l => { l with ticksToRun := [] }

/-- `LevelTicks.tick` for the fluid ticks: collects the scheduled fluid ticks that are due, at
most `maxScheduledTicksPerTick`, and runs them in order (`tickFluid`). -/
def runFluidTicks : M Unit := do
  let l ← get
  let due := (ScheduledTickOf.dueInOrder l.gameTime l.fluidTicks).take maxScheduledTicksPerTick
  set { l with fluidTicks := l.fluidTicks.filter (!due.contains ·), fluidTicksToRun := due }
  due.forM fun t => do
    modify fun l => { l with fluidTicksToRun := l.fluidTicksToRun.tail }
    tickFluid t
  modify fun l => { l with fluidTicksToRun := [] }

/-- In a level without scheduled fluid ticks the fluid-tick phase leaves the level as it is. -/
theorem runFluidTicks_of_empty (env : Env) (l : Level) (h : l.fluidTicks = [])
    (h' : l.fluidTicksToRun = []) : (runFluidTicks.run env).run l = ((), l) := by
  obtain ⟨⟩ := l
  simp only at h h'
  subst h h'
  rfl

/-- `ServerLevel.runBlockEvents`, bounded by `fuel` events: runs the block events in order
until none is left. -/
def runBlockEventsLoop : ℕ → M Unit
  | 0 => do
    if !(← get).blockEvents.isEmpty then setOverflow
  | fuel + 1 => do
    let l ← get
    match l.blockEvents with
    | [] => pure ()
    | e :: rest =>
      set { l with blockEvents := rest }
      let state ← getBlock e.pos
      if state.is e.block then discard <| (← behaviour state).triggerEvent e.pos e.a e.b
      runBlockEventsLoop fuel

/-- The bound on the number of block events run in one game tick. The game has none. -/
def maxBlockEvents : ℕ := 1000000

/-- Runs the block events. -/
def runBlockEvents : M Unit := runBlockEventsLoop maxBlockEvents

/-- Ticks the entities that were alive when the phase began, in order, skipping those removed
meanwhile. -/
def tickEntities : M Unit := do
  let indices := (← get).entities.map (·.index)
  indices.forM fun i => do
    if let some e := (← get).entity? i then ((← read).entity e).tick i

/-- `Level.tickBlockEntities`: ticks the block entities in the order in which their tickers
were added. -/
def tickBlockEntities : M Unit := do
  modify fun l => { l with
    tickingBlockEntities := true
    blockEntityTickers := l.blockEntityTickers ++ l.pendingBlockEntityTickers
    pendingBlockEntityTickers := [] }
  let tickers := (← get).blockEntityTickers
  tickers.forM fun p => do
    let l ← get
    if l.blockEntityTickers.contains p && (l.blockEntities p).isSome then
      modify fun l => { l with tickedBlockEntities := p :: l.tickedBlockEntities }
      (← behaviour (← getBlock p)).blockEntityTick p
  modify fun l => { l with tickingBlockEntities := false }

/-- One game tick. -/
def tick : M Unit := do
  modify fun l => { l with
    gameTime := l.gameTime + 1
    handlingTick := true
    dayTime := if l.advanceTime then l.dayTime + 1 else l.dayTime
    lightWorld := l.world }
  runScheduledTicks
  runFluidTicks
  tickChunks
  runBlockEvents
  modify fun l => { l with handlingTick := false, tickedBlockEntities := [] }
  tickEntities
  tickBlockEntities

end Level

/-- How deep reactions may nest before the model gives up and sets `Level.overflow`. -/
def maxDepth : ℕ := 512

namespace Rules

/-- Runs an action on a level under the rules `r`. -/
def run {α : Type} (r : Rules) (x : M α) (l : Level) : α × Level := (x.run (r.env maxDepth)).run l

/-- The level after one game tick. -/
def step (r : Rules) (l : Level) : Level := (r.run Level.tick l).2

/-- The level after `n` game ticks. -/
def steps (r : Rules) (n : ℕ) (l : Level) : Level := (r.step)^[n] l

end Rules

end Redstone
