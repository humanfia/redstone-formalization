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
  /-- An entity known only by the UUID of a saved vibration (`VibrationInfo.uuid`, four ints),
  which names no entity of the world: `VibrationInfo.getEntity` finds nothing. -/
  | saved (uuid : List ℤ)
  deriving DecidableEq, Repr

namespace GameEventSource

/-- The UUID of the player of the tests (`tests/FORMAT.md`), as the four ints of its NBT form. -/
def playerUuid : List ℤ := [0, 0, 0, 1]

/-- `VibrationInfo.getEntity(level)`: the entity behind a vibration when it arrives. A vibration
made in this run keeps a reference to its entity. One read from saved data only has the UUID,
which is looked up among the entities of the world; the player of the tests is not in the world
and the UUIDs of the other entities are not in the model, so nothing is found. -/
def resolve : Option GameEventSource → Option GameEventSource
  | some (saved _) => none
  | s => s

end GameEventSource

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

/-- The source of a saved vibration (`source`, a UUID as an int array). Saved data only has the
UUID, whoever it names: a vibration read from it is not one a live player caused, even with the
UUID of the player of the tests (`GameEventSource.resolve`). The vibrations a player causes
during a run are written by the server with that UUID; `VibrationInfo.saved` gives the model's
data the same form before the two are compared. -/
def sourceOfNbt? : Nbt → Option GameEventSource
  | .intArray uuid => some (.saved uuid)
  | _ => none

/-- Reads a vibration from its saved NBT (`VibrationInfo.CODEC`). The owner of a projectile is
not kept. -/
def ofNbt? (t : Nbt) : Option VibrationInfo := do
  let event ← (← t.get? "game_event").toString?
  let distance ← floatBits? (← t.get? "distance")
  match ← (← t.get? "pos").toList? with
  | [x, y, z] =>
    return ⟨event, distance, ← doubleBits? x, ← doubleBits? y, ← doubleBits? z,
      (t.get? "source").bind sourceOfNbt?⟩
  | _ => none

/-- Reads the optional field `event` of a compound. -/
def ofField? (t : Nbt) : Option (Option VibrationInfo) :=
  match t.get? "event" with
  | none => some none
  | some e => (ofNbt? e).map some

/-- The vibration as the game saves it: of a player that caused it only the UUID is written
(`VibrationInfo.CODEC`, `uuid`). -/
def saved (v : VibrationInfo) : VibrationInfo :=
  match v.source with
  | some .player => { v with source := some (.saved GameEventSource.playerUuid) }
  | _ => v

end VibrationInfo

/-- The data of a vibration listener (`VibrationSystem.Data`). -/
structure VibrationData where
  /-- `currentVibration`: the vibration that is travelling to the listener. -/
  currentVibration : Option VibrationInfo
  /-- `travelTimeInTicks`: the game ticks it still needs. -/
  travelTimeInTicks : ℕ
  /-- `selectionStrategy` (`VibrationSelector.currentVibrationData`): the best candidate heard
  so far, with the game time at which it was heard. -/
  selector : Option (VibrationInfo × ℤ)
  deriving DecidableEq, Repr, Inhabited

namespace VibrationData

/-- Reads the data from its saved NBT (`VibrationSystem.Data.CODEC`). -/
def ofNbt? (t : Nbt) : Option VibrationData := do
  let current ← VibrationInfo.ofField? t
  let sel ← t.get? "selector"
  let candidate ← VibrationInfo.ofField? sel
  return ⟨current, (t.intD "event_delay" 0).toNat,
    candidate.map fun c => (c, sel.intD "tick" 0)⟩

/-- Reads the field `listener` of a block entity; when it is absent the data is fresh. -/
def ofField? (t : Nbt) : Option VibrationData :=
  match t.get? "listener" with
  | none => some default
  | some l => ofNbt? l

/-- The data as the game saves it (`VibrationInfo.saved`). -/
def saved (d : VibrationData) : VibrationData :=
  { d with
    currentVibration := d.currentVibration.map (·.saved)
    selector := d.selector.map fun (v, tick) => (v.saved, tick) }

end VibrationData

end BlockEntities

end Redstone
