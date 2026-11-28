module

public import Redstone.Mechanics.Update

/-!
# Random ticks

`ServerChunkCache.tickChunks` with `ServerLevel.tickChunk`: in every game tick, every section
of every ticking chunk gives a random tick to `random_tick_speed` of its blocks, chosen with
`Level.randValue`; a block with `isRandomlyTicking` reacts with `randomTick`
(`BehaviourOf.randomTick`), and so does its fluid.

This is a stub: no block gets a random tick yet. The state the phase needs is in place:
`Level.randomTickSpeed` (the game rule, zero by default), `Level.randValue` and
`Level.randomTickBox` (the region to go through, since the model has no chunks). The phase
runs between the fluid ticks and the block events (`Level.tick`), and does nothing when the
speed is zero (`Level.tickChunks_of_speed_zero`), which every recorded scenario has so far.
With a positive speed the game would tick blocks and the model cannot follow: the phase sets
`Level.overflow`.

Thunder, precipitation (ice and snow forming, cauldrons filling) and mob spawning, which the
game does in the same pass over the chunks, are not modelled.
-/

@[expose] public section

namespace Redstone

namespace Level

/-- The random ticks of one game tick, for a positive `random_tick_speed`. A stub: no block is
ticked, and `Level.overflow` is set, since the game would have ticked some. -/
def randomTicks : M Unit := setOverflow

/-- `ServerChunkCache.tickChunks`: the random ticks of one game tick. With the game rule
`random_tick_speed` at zero nothing is drawn and nothing happens. -/
def tickChunks : M Unit := do
  if (← get).randomTickSpeed = 0 then pure () else randomTicks

/-- With `random_tick_speed` at zero the random-tick phase leaves the level as it is. -/
theorem tickChunks_of_speed_zero (env : Env) (l : Level) (h : l.randomTickSpeed = 0) :
    (tickChunks.run env).run l = ((), l) := by
  change (if l.randomTickSpeed = 0 then (pure () : M Unit) else randomTicks) env l = ((), l)
  rw [h]
  rfl

end Level

end Redstone
