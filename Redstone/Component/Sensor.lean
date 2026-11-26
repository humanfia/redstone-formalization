module

public import Redstone.Mechanics.Tick

/-!
# Target, lightning rod and daylight detector

Java classes: `TargetBlock`, `LightningRodBlock`, `DaylightDetectorBlock`.

To be formalized: the signal of a target hit by a projectile, the pulse of a lightning rod, and
the daylight detector in both modes.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Sensor

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Sensor
