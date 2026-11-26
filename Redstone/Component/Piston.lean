module

public import Redstone.Mechanics.Tick

/-!
# Pistons

Java classes: `PistonBaseBlock`, `PistonHeadBlock`, `MovingPistonBlock`.

To be formalized: the piston base, the head and the moving block; when a piston wants to extend
or retract, quasi-connectivity, the block events, and the moving block entity. Which blocks move
is in `Redstone.Mechanics.PistonMotion`.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Piston

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Piston
