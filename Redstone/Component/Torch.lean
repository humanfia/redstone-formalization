module

public import Redstone.Mechanics.Tick

/-!
# Redstone torch and block of redstone

Java classes: `RedstoneTorchBlock`, `RedstoneWallTorchBlock`, `PoweredBlock`.

To be formalized: inversion of the attachment block's power, the delay, the block powered above,
burnout, the wall torch, and the block of redstone as a constant source.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Torch

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Torch
