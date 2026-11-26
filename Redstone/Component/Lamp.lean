module

public import Redstone.Mechanics.Tick

/-!
# Redstone lamp and copper bulb

Java classes: `RedstoneLampBlock`, `CopperBulbBlock`.

A redstone lamp lights up as soon as it receives a signal and goes out four game ticks after
the signal is gone.

To be formalized: the copper bulb, which toggles on a rising edge and can be read by a
comparator. It is inert for now.
-/

@[expose] public section

namespace Redstone.Component.Lamp

/-- The behaviour of a redstone lamp. -/
def lamp (s : Blocks.RedstoneLamp) : Behaviour :=
  let self : Block := .redstoneLamp s
  { Behaviour.inert self with
    neighborChanged := fun p _ _ => do
      if s.lit != (← Level.hasNeighborSignal p) then
        if s.lit then Level.scheduleTick p .redstone_lamp 4
        else discard <| Level.setBlock p (.redstoneLamp { s with lit := true }) 2
    tick := fun p => do
      if s.lit && !(← Level.hasNeighborSignal p) then
        discard <| Level.setBlock p (.redstoneLamp { s with lit := false }) 2 }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .redstoneLamp s => lamp s
  | _ => .inert self

end Redstone.Component.Lamp
