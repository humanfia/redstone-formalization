module

public import Redstone.Mechanics.Tick

/-!
# Lemmas about the phases of a game tick

A phase of `Level.tick` that has nothing to work on leaves the level as it is. The same facts
for the fluid ticks and the random ticks are next to their definitions
(`Level.runFluidTicks_of_empty`, `Level.tickChunks_of_speed_zero`).
-/

@[expose] public section

namespace Redstone

namespace Level

/-- In a level without scheduled ticks the block-tick phase leaves the level as it is. -/
theorem runScheduledTicks_of_empty (env : Env) (l : Level) (h : l.ticks = [])
    (h' : l.ticksToRun = []) : (runScheduledTicks.run env).run l = ((), l) := by
  obtain ⟨⟩ := l
  simp only at h h'
  subst h h'
  rfl

/-- With no block event queued, the loop of the block-event phase stops at once. -/
theorem runBlockEventsLoop_of_empty (fuel : ℕ) (env : Env) (l : Level) (h : l.blockEvents = []) :
    ((runBlockEventsLoop (fuel + 1)).run env).run l = ((), l) := by
  obtain ⟨⟩ := l
  simp only at h
  subst h
  rfl

/-- In a level without block events the block-event phase leaves the level as it is. -/
theorem runBlockEvents_of_empty (env : Env) (l : Level) (h : l.blockEvents = []) :
    (runBlockEvents.run env).run l = ((), l) :=
  runBlockEventsLoop_of_empty 999999 env l h

end Level

end Redstone
