module

public import Redstone.Mechanics.Power

/-!
# Game ticks

One game tick of the level (`ServerLevel.tick`). The phases that matter for redstone run in
this order:

1. the overworld clock advances (if the game rule `advance_time` is set), and so does the game
   time; the light engine has caught up with the blocks since the previous tick;
2. the scheduled block ticks that are due run;
3. the block events run, including those queued while running them;
4. the entities are ticked;
5. the block entities are ticked.

The weather cycle, the world border, raids, random ticks, mob spawning and fluid ticks are left
out. The game runs at most 65536 scheduled ticks per game tick; this limit is not modelled.

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

/-- `LevelTicks.tick`: collects the scheduled ticks that are due and runs them in order. Ticks
scheduled meanwhile wait for a later game tick, even with delay zero. -/
def runScheduledTicks : M Unit := do
  let l ← get
  let due := ScheduledTick.dueInOrder l.gameTime l.ticks
  set { l with ticks := l.ticks.filter (!due.contains ·), ticksToRun := due }
  due.forM fun t => do
    modify fun l => { l with ticksToRun := l.ticksToRun.tail }
    tickBlock t
  modify fun l => { l with ticksToRun := [] }

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
      (← behaviour (← getBlock p)).blockEntityTick p
  modify fun l => { l with tickingBlockEntities := false }

/-- One game tick. -/
def tick : M Unit := do
  modify fun l => { l with
    gameTime := l.gameTime + 1
    dayTime := if l.advanceTime then l.dayTime + 1 else l.dayTime
    lightWorld := l.world }
  runScheduledTicks
  runBlockEvents
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
