module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State
public import Redstone.Block.Entity.StoredItem

/-!
# Block entity `minecraft:jukebox`

The data that the model keeps of the block entity `JukeboxBlockEntity`: the record in the
jukebox and the state of its `JukeboxSongPlayer`.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:jukebox` block entity. -/
structure Jukebox where
  /-- `item`: the record in the jukebox, if there is one. -/
  record : Option StoredItem
  /-- `jukeboxSongPlayer`: `none` when no song is playing (`song == null`), otherwise
  `ticksSinceSongStarted`. The song is always that of the record. -/
  song : Option ℕ
  deriving DecidableEq, Repr, Inhabited

namespace Jukebox

/-- Reads the data from NBT that the server saved (`saveAdditional`), which has
`ticks_since_song_started` exactly when a song is playing. -/
def ofNbt? (t : Nbt) : Option Jukebox :=
  some
    { record := (t.get? "RecordItem").bind StoredItem.ofNbt?
      song := ((t.get? "ticks_since_song_started").bind Nbt.toInt?).map Int.toNat }

end Jukebox

end Redstone.BlockEntities
