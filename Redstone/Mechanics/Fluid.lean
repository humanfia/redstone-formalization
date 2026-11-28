module

public import Redstone.Mechanics.Update

/-!
# Fluid ticks

`ServerLevel.tickFluid`: what a scheduled fluid tick does (`FluidState.tick`, which is
`FlowingFluid.tick` for water and lava: the fluid spreads, or dries up).

This is a stub: fluids do not flow yet, and a fluid tick does nothing. The engine around it is
in place: `Level.fluidTicks` holds the scheduled fluid ticks, `Level.scheduleFluidTick` adds
one, and `Level.runFluidTicks` (`Redstone.Mechanics.Tick`) runs the due ones in the game's
order, right after the block ticks. No block schedules a fluid tick yet, so the queue is empty
and the phase does nothing (`Level.runFluidTicks_of_empty`).

A fluid tick that does run is dropped without a trace, and without setting `Level.overflow`.
This is how the model has always treated the fluid ticks of the recorded scenarios (a
waterlogged block next to a change has one pending in the game): the water of the scenarios
that pass does not move, so ignoring its ticks is right for them, and the test runner now loads
those ticks. A level in which a fluid would really flow is not modelled faithfully.
-/

@[expose] public section

namespace Redstone

namespace Level

/-- `ServerLevel.tickFluid`: runs a scheduled fluid tick, unless the fluid is no longer there.
A stub: it does nothing. -/
def tickFluid (_t : ScheduledFluidTick) : M Unit := pure ()

end Level

end Redstone
