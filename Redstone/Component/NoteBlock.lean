module

public import Redstone.Mechanics.Tick

/-!
# Note block

Java classes: `NoteBlock`.

To be formalized: playing on a rising edge of power, the note and the instrument.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.NoteBlock

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.NoteBlock
