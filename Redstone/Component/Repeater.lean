module

public import Redstone.Component.Diode

/-!
# Repeater

Java classes: `RepeaterBlock` (with `DiodeBlock`, see `Redstone.Component.Diode`).

A repeater passes the signal at its input on to its output at full strength, after a delay of
two, four, six or eight game ticks (the property `delay`, one to four). A pulse that is shorter
than the delay is extended to the length of the delay. A powered repeater or comparator that
points at the side of a repeater locks it: a locked repeater keeps its state whatever its
input does. Using a repeater moves it to the next delay.

Not formalized: `getStateForPlacement` and `setPlacedBy` (placement of the item by a player),
`shouldRedstoneWireConnectTo` (it belongs to the redstone wire) and `animateTick` (client only).
-/

@[expose] public section

namespace Redstone.Component.Repeater

/-- `RepeaterBlock.isLocked`: a diode at one of the two sides gives the repeater a direct
signal. Other signal sources at the sides do not count (`sideInputDiodesOnly`). -/
def isLocked (s : Blocks.Repeater) (p : Pos) : M Bool :=
  return (← Diode.getAlternateSignal s.facing.toDirection p true) > 0

/-- `RepeaterBlock.getDelay`: twice the property `delay`. -/
def getDelay (s : Blocks.Repeater) : ℕ := s.delay.val * 2

/-- `state.cycle(DELAY)`: the next delay, from four back to one. -/
def cycleDelay (s : Blocks.Repeater) : Blocks.Repeater :=
  { s with delay := ⟨s.delay.val % 4 + 1, by omega, by have := s.delay.le_hi; omega⟩ }

/-- The repeater state `s` as a diode. -/
def diode (s : Blocks.Repeater) : Diode where
  id := .repeater
  self := .repeater s
  facing := s.facing.toDirection
  powered := s.powered
  setPowered v := .repeater { s with powered := v }
  delay := getDelay s
  isLocked := isLocked s
  shouldTurnOn p := return (← Diode.getInputSignal s.facing.toDirection p) > 0
  outputSignal _ _ := 15

/-- `RepeaterBlock.updateShape`: the repeater breaks when the block below cannot carry it any
more; a change at a position off its axis (the sides, and above) recomputes `locked`. -/
def updateShape (s : Blocks.Repeater) (p : Pos) (directionToNeighbour : Direction)
    (neighbourState : Block) : M Block := do
  if directionToNeighbour = .down && !Diode.canSurviveOn neighbourState then return .AIR
  else if directionToNeighbour.axis ≠ s.facing.toDirection.axis then
    return .repeater { s with locked := ← isLocked s p }
  else return .repeater s

/-- The behaviour of a repeater. -/
def repeater (s : Blocks.Repeater) : Behaviour :=
  { (diode s).behaviour with
    updateShape := fun p d _ neighbourState => updateShape s p d neighbourState
    useWithoutItem := fun p _ => do
      -- the player of the tests may build (`player.getAbilities().mayBuild`)
      discard <| Level.setBlock p (.repeater (cycleDelay s))
      return true }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .repeater s => repeater s
  | _ => .inert self

end Redstone.Component.Repeater
