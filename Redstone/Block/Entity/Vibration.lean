module

public import Redstone.Basic.Nbt

/-!
# Vibration data

The data of a `VibrationSystem`, which the block entities of sculk sensors and sculk shriekers
carry: the vibration that is travelling to the listener, the time it still needs, and the
candidate chosen among the game events heard in the current game tick (`VibrationSystem.Data`,
`VibrationSelector`, `VibrationInfo`).

Floating point values are kept as their IEEE bits, so that the data can be compared.
-/

@[expose] public section

namespace Redstone

/-- The entity that caused a game event (`GameEvent.Context.sourceEntity`). -/
inductive GameEventSource
  /-- A player. Players are not entities of the model. -/
  | player
  /-- The entity with the given index. -/
  | entity (index : ℕ)
  deriving DecidableEq, Repr

namespace BlockEntities

/-- A vibration (`VibrationInfo`). -/
structure VibrationInfo where
  /-- The registry name of the game event. -/
  gameEvent : String
  /-- The distance from the origin to the listener, a `float`, as its bits. -/
  distance : ℕ
  /-- The first coordinate of the origin, a `double`, as its bits. -/
  x : ℕ
  /-- The second coordinate of the origin. -/
  y : ℕ
  /-- The third coordinate of the origin. -/
  z : ℕ
  /-- The entity that caused the event (`uuid`, `entity`). -/
  source : Option GameEventSource
  deriving DecidableEq, Repr

namespace VibrationInfo

/-- The bits of a float tag. -/
def floatBits? : Nbt → Option ℕ
  | .float bits => some bits
  | _ => none

/-- The bits of a double tag. -/
def doubleBits? : Nbt → Option ℕ
  | .double bits => some bits
  | _ => none

/-- Reads a vibration from its saved NBT (`VibrationInfo.CODEC`). The saved data only tells
that there was a source entity, by its UUID; it is read as a player, the only source the tests
have. The owner of a projectile is not kept. -/
def ofNbt? (t : Nbt) : Option VibrationInfo := do
  let event ← (← t.get? "game_event").toString?
  let distance ← floatBits? (← t.get? "distance")
  match ← (← t.get? "pos").toList? with
  | [x, y, z] =>
    return ⟨event, distance, ← doubleBits? x, ← doubleBits? y, ← doubleBits? z,
      (t.get? "source").map fun _ => .player⟩
  | _ => none

/-- Reads the optional field `event` of a compound. -/
def ofField? (t : Nbt) : Option (Option VibrationInfo) :=
  match t.get? "event" with
  | none => some none
  | some e => (ofNbt? e).map some

end VibrationInfo

/-- The data of a vibration listener (`VibrationSystem.Data`). -/
structure VibrationData where
  /-- `currentVibration`: the vibration that is travelling to the listener. -/
  currentVibration : Option VibrationInfo
  /-- `travelTimeInTicks`: the game ticks it still needs. -/
  travelTimeInTicks : ℕ
  /-- `selectionStrategy` (`VibrationSelector.currentVibrationData`): the best candidate heard
  so far, with the game time at which it was heard. -/
  selector : Option (VibrationInfo × ℕ)
  deriving DecidableEq, Repr, Inhabited

namespace VibrationData

/-- Reads the data from its saved NBT (`VibrationSystem.Data.CODEC`). -/
def ofNbt? (t : Nbt) : Option VibrationData := do
  let current ← VibrationInfo.ofField? t
  let sel ← t.get? "selector"
  let candidate ← VibrationInfo.ofField? sel
  return ⟨current, (t.intD "event_delay" 0).toNat,
    candidate.map fun c => (c, (sel.intD "tick" 0).toNat)⟩

/-- Reads the field `listener` of a block entity; when it is absent the data is fresh. -/
def ofField? (t : Nbt) : Option VibrationData :=
  match t.get? "listener" with
  | none => some default
  | some l => ofNbt? l

end VibrationData

end BlockEntities

end Redstone
