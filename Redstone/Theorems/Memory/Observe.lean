import Redstone.Proof.Circuit

/-!
# What the memory circuits observe

The theorems of `Redstone/Theorems/Memory` read the state of a circuit off its blocks. These
are the readers: each gives the property that carries the state of one kind of block at a
position, and `none` when another block is there, so that a theorem that says `some true`
also says which block is at the position.

All of them only look at `Level.blockAt`, so `Level.blockAt_advance` removes a `Level.advance`
under them.
-/

namespace Redstone.Theorems.Memory

/-- The repeater at `p`: its properties `powered` and `locked`. -/
def repeaterAt? (l : Level) (p : Pos) : Option (Bool × Bool) :=
  match l.blockAt p with
  | .repeater s => some (s.powered, s.locked)
  | _ => none

/-- Whether the redstone lamp at `p` is lit. -/
def lampAt? (l : Level) (p : Pos) : Option Bool :=
  match l.blockAt p with
  | .redstoneLamp s => some s.lit
  | _ => none

/-- Whether the redstone torch at `p`, on the floor or on a wall, is lit. -/
def torchAt? (l : Level) (p : Pos) : Option Bool :=
  match l.blockAt p with
  | .redstoneTorch s => some s.lit
  | .redstoneWallTorch s => some s.lit
  | _ => none

/-- Whether the lever at `p` is on. -/
def leverAt? (l : Level) (p : Pos) : Option Bool :=
  match l.blockAt p with
  | .lever s => some s.powered
  | _ => none

/-- Whether the button at `p` is pressed. -/
def buttonAt? (l : Level) (p : Pos) : Option Bool :=
  match l.blockAt p with
  | .button _ s => some s.powered
  | _ => none

/-- Whether the comparator at `p` is powered. -/
def comparatorAt? (l : Level) (p : Pos) : Option Bool :=
  match l.blockAt p with
  | .comparator s => some s.powered
  | _ => none

/-- Whether the observer at `p` is powered. -/
def observerAt? (l : Level) (p : Pos) : Option Bool :=
  match l.blockAt p with
  | .observer s => some s.powered
  | _ => none

/-- The copper bulb at `p`, of either family: its properties `lit` and `powered`. -/
def bulbAt? (l : Level) (p : Pos) : Option (Bool × Bool) :=
  match l.blockAt p with
  | .copperBulb _ s => some (s.lit, s.powered)
  | .weatheringCopperBulb _ s => some (s.lit, s.powered)
  | _ => none

end Redstone.Theorems.Memory
