module

public import Redstone.Mechanics.Tick

/-!
# Redstone lamp and copper bulb

Java classes: `RedstoneLampBlock`, `CopperBulbBlock`, `WeatheringCopperBulbBlock`.

A redstone lamp lights up as soon as it receives a signal and goes out four game ticks after
the signal is gone.

A copper bulb remembers in `powered` whether it receives a signal, and switches its light each
time the signal appears. A comparator reads 15 from a lit bulb. The eight copper bulbs (four
stages of oxidation, waxed or not) behave alike.

The oxidation of the unwaxed bulbs (`WeatheringCopperBulbBlock.randomTick`) is in
`Redstone.Component.Weathering`. Not modelled: the sounds.
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

/-- The value of the property `lit` of a copper bulb, of either family. -/
def bulbLit? : Block → Option Bool
  | .weatheringCopperBulb _ s => some s.lit
  | .copperBulb _ s => some s.lit
  | _ => none

/-- `CopperBulbBlock.checkAndFlip(state, level, pos)` for the bulb with the given `lit` and
`powered`, where `mk lit powered` is the state of the same block with these values. When the
signal differs from `powered`, the bulb records it, and switches its light if the signal has
just appeared. -/
def checkAndFlip (mk : Bool → Bool → Block) (lit powered : Bool) (p : Pos) : M Unit := do
  let signal ← Level.hasNeighborSignal p
  if signal != powered then
    let lit := if !powered then !lit else lit
    discard <| Level.setBlock p (mk lit signal)

/-- The behaviour of a copper bulb with the given `lit` and `powered`, where `mk lit powered` is
the state of the same block with these values (`CopperBulbBlock`). -/
def bulb (mk : Bool → Bool → Block) (lit powered : Bool) : Behaviour :=
  let self : Block := mk lit powered
  { Behaviour.inert self with
    onPlace := fun p old _ => do
      if old.id != self.id then checkAndFlip mk lit powered p
    neighborChanged := fun p _ _ => checkAndFlip mk lit powered p
    -- `getAnalogOutputSignal` reads the state that is at the position.
    analogSignal := fun l p _ => if bulbLit? (l.blockAt p) = some true then 15 else 0 }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .redstoneLamp s => lamp s
  | .weatheringCopperBulb id s => bulb (fun lit powered => .weatheringCopperBulb id ⟨lit, powered⟩)
      s.lit s.powered
  | .copperBulb id s => bulb (fun lit powered => .copperBulb id ⟨lit, powered⟩) s.lit s.powered
  | _ => .inert self

end Redstone.Component.Lamp
