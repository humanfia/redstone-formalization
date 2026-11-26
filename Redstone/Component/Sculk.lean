module

public import Redstone.Mechanics.Tick

/-!
# Sculk sensors and shriekers

Java classes: `SculkSensorBlock`, `SculkShriekerBlock`, `SculkCatalystBlock`.

To be formalized: vibrations: which game events are heard, how far, the frequency and the signal
of the sensor, the calibrated sensor, and the shrieker.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Sculk

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

/-- The reaction of vibration listeners to the game event named `event` at `p`. -/
def onGameEvent (_event : String) (_p : Pos) : M Unit := pure ()

end Redstone.Component.Sculk
