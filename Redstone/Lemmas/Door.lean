module

public import Redstone.Component.Door

/-!
# Lemmas about doors, trapdoors and fence gates

Generic facts about the three blocks that open when they receive a signal, over an arbitrary
level. The theorem about a concrete level is `Redstone/Theorems/PistonDoor/LeverDoors.lean`.

* **Attribute lemmas.** Iron doors and iron trapdoors are the ones that cannot be opened by
  hand (`DoorId.canOpenByHand_eq_false_iff`, `TrapDoorId.canOpenByHand_eq_false_iff`): using
  one does nothing (`DoorBlock.useWithoutItem_iron`, `TrapDoorBlock.useWithoutItem_iron`).
* **Single-reaction lemmas.** The reaction of each block to a neighbour update, under a
  hypothesis about the signal it reads:
  * when the signal agrees with the `powered` property, nothing happens
    (`TrapDoorBlock.neighborChanged_of_agrees`, `FenceGateBlock.neighborChanged_of_agrees`,
    `DoorBlock.neighborChanged_of_agrees`);
  * when it differs, the block writes one new state, with `open` and `powered` both set to
    the signal, with flag 2 (clients are told, neighbours are not), and makes its sound exactly
    when `open` changes (`…neighborChanged_of_differs`). So **`open` follows the signal**
    whatever it was before: a wooden door opened by hand closes when its signal goes away;
  * a door ignores updates that come from a door of its own kind
    (`DoorBlock.neighborChanged_of_same_block`): that is what keeps its two halves from
    answering each other for ever;
  * a door reads the signal of both its halves (the hypothesis of the door lemmas is about
    `DoorBlock.signalAt`), and **the other half follows through a shape update**
    (`DoorBlock.updateShape_copies`): a half that is told about the other half takes over its
    state, keeping only its own `half`.

Left out: a lemma that says what the one `Level.setBlock` of a reaction does to an arbitrary
level. It sends shape updates to the six neighbours, and what they do depends on what they
are; for a concrete level it is evaluated (`LeverDoors.lean`).
-/

@[expose] public section

namespace Redstone.Component.Door

/-! ### Attribute lemmas -/

namespace DoorId

/-- Only the iron door cannot be opened by hand. -/
theorem canOpenByHand_eq_false_iff (k : DoorId) :
    k.canOpenByHand = false ↔ k = .plain .iron_door := by
  constructor
  · intro h
    unfold canOpenByHand at h
    split at h
    · rfl
    · cases h
  · rintro rfl
    rfl

/-- The block of a door state is read back as that door and that state. -/
theorem door?_block (k : DoorId) (s : Blocks.Door) : door? (k.block s) = some (k, s) := by
  cases k <;> rfl

end DoorId

namespace TrapDoorId

/-- Only the iron trapdoor cannot be opened by hand. -/
theorem canOpenByHand_eq_false_iff (k : TrapDoorId) :
    k.canOpenByHand = false ↔ k = .plain .iron_trapdoor := by
  constructor
  · intro h
    unfold canOpenByHand at h
    split at h
    · rfl
    · cases h
  · rintro rfl
    rfl

end TrapDoorId

/-! ### Trapdoors -/

namespace TrapDoorBlock

/-- A player who uses an iron trapdoor changes nothing. -/
theorem useWithoutItem_iron (s : Blocks.TrapDoor) (p : Pos) (env : Env) (l : Level) :
    useWithoutItem (.plain .iron_trapdoor) s p env l = (false, l) := rfl

/-- **A trapdoor that agrees with its signal does nothing.** -/
theorem neighborChanged_of_agrees (k : TrapDoorId) (s : Blocks.TrapDoor) (p : Pos) (env : Env)
    (l : Level) (h : l.hasNeighborSignalAt env p = s.powered) :
    neighborChanged k s p env l = ((), l) := by
  have hs : Level.hasNeighborSignal p env l = (s.powered, l) := by
    rw [← h]
    rfl
  simp only [neighborChanged, bind, ReaderT.bind, StateT.bind, hs, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte]
  rfl

/-- **`open` follows the signal.** A trapdoor whose signal differs from its `powered` property
writes one new state, in which `open` and `powered` are the signal, and makes its sound if
that changes `open`. If it is waterlogged it then asks for a tick of its water. -/
theorem neighborChanged_of_differs (k : TrapDoorId) (s : Blocks.TrapDoor) (p : Pos) (env : Env)
    (l : Level) (h : l.hasNeighborSignalAt env p = !s.powered) :
    neighborChanged k s p env l =
      (do
        if s.open != !s.powered then
          playSound
          Level.gameEvent (openEvent (!s.powered)) p
        discard <| Level.setBlock p
          (k.block { s with «open» := !s.powered, powered := !s.powered }) 2
        if s.waterlogged then
          Level.scheduleFluidTick p .water Fluid.water.tickDelay : M Unit) env l := by
  have hs : Level.hasNeighborSignal p env l = (!s.powered, l) := by
    rw [← h]
    rfl
  simp only [neighborChanged, bind, ReaderT.bind, StateT.bind, hs, Bool.not_bne_self,
    ↓reduceIte]

end TrapDoorBlock

/-! ### Fence gates -/

namespace FenceGateBlock

/-- **A fence gate that agrees with its signal does nothing.** -/
theorem neighborChanged_of_agrees (id : Blocks.FenceGate.Id) (s : Blocks.FenceGate) (p : Pos)
    (env : Env) (l : Level) (h : l.hasNeighborSignalAt env p = s.powered) :
    neighborChanged id s p env l = ((), l) := by
  have hs : Level.hasNeighborSignal p env l = (s.powered, l) := by
    rw [← h]
    rfl
  simp only [neighborChanged, bind, ReaderT.bind, StateT.bind, hs, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte]
  rfl

/-- **`open` follows the signal.** A fence gate whose signal differs from its `powered`
property writes one new state, in which `open` and `powered` are the signal, and then makes
its sound if that changed `open`. -/
theorem neighborChanged_of_differs (id : Blocks.FenceGate.Id) (s : Blocks.FenceGate) (p : Pos)
    (env : Env) (l : Level) (h : l.hasNeighborSignalAt env p = !s.powered) :
    neighborChanged id s p env l =
      (do
        discard <| Level.setBlock p
          (.fenceGate id { s with powered := !s.powered, «open» := !s.powered }) 2
        if s.open != !s.powered then
          playSound
          Level.gameEvent (openEvent (!s.powered)) p : M Unit) env l := by
  have hs : Level.hasNeighborSignal p env l = (!s.powered, l) := by
    rw [← h]
    rfl
  simp only [neighborChanged, bind, ReaderT.bind, StateT.bind, hs, Bool.bne_not_self,
    ↓reduceIte]

end FenceGateBlock

/-! ### Doors -/

namespace DoorBlock

/-- The position of the other half of a door. -/
def other (s : Blocks.Door) (p : Pos) : Pos := p.step (if s.half = .lower then .up else .down)

/-- The signal a door looks at: that of either of its halves. -/
def signalAt (s : Blocks.Door) (p : Pos) (env : Env) (l : Level) : Bool :=
  l.hasNeighborSignalAt env p || l.hasNeighborSignalAt env (other s p)

/-- A player who uses an iron door changes nothing. -/
theorem useWithoutItem_iron (s : Blocks.Door) (p : Pos) (env : Env) (l : Level) :
    useWithoutItem (.plain .iron_door) s p env l = (false, l) := rfl

/-- The signal of both halves, as the door reads it. -/
theorem signal_eq (s : Blocks.Door) (p : Pos) (env : Env) (l : Level) :
    (Level.hasNeighborSignal p <||> Level.hasNeighborSignal (other s p) : M Bool) env l =
      (signalAt s p env l, l) := by
  have h₁ : Level.hasNeighborSignal p env l = (l.hasNeighborSignalAt env p, l) := rfl
  have h₂ : Level.hasNeighborSignal (other s p) env l =
      (l.hasNeighborSignalAt env (other s p), l) := rfl
  simp only [orM, bind, ReaderT.bind, StateT.bind, h₁, signalAt]
  cases hb : l.hasNeighborSignalAt env p
  · exact h₂
  · rfl

/-- **A door that agrees with its signal does nothing.** -/
theorem neighborChanged_of_agrees (k : DoorId) (s : Blocks.Door) (p : Pos) (block : BlockId)
    (env : Env) (l : Level) (h : signalAt s p env l = s.powered) :
    neighborChanged k s p block env l = ((), l) := by
  have hs := signal_eq s p env l
  rw [h] at hs
  unfold other at hs
  simp only [neighborChanged, bind, ReaderT.bind, StateT.bind, hs, bne_self_eq_false,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- **A door ignores updates from a door of its own kind**, whatever its signal. -/
theorem neighborChanged_of_same_block (k : DoorId) (s : Blocks.Door) (p : Pos) (block : BlockId)
    (env : Env) (l : Level) (h : (k.block s).is block = true) :
    neighborChanged k s p block env l = ((), l) := by
  have hs := signal_eq s p env l
  unfold other at hs
  simp only [neighborChanged, bind, ReaderT.bind, StateT.bind, hs, h, Bool.not_true,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- **`open` follows the signal.** A door half that is updated by another kind of block and
whose signal (that of either half) differs from its `powered` property makes its sound if
`open` changes, and writes one new state, in which `open` and `powered` are the signal. -/
theorem neighborChanged_of_differs (k : DoorId) (s : Blocks.Door) (p : Pos) (block : BlockId)
    (env : Env) (l : Level) (hb : (k.block s).is block = false)
    (h : signalAt s p env l = !s.powered) :
    neighborChanged k s p block env l =
      (do
        if (!s.powered) != s.open then
          playSound
          Level.gameEvent (openEvent (!s.powered)) p
        discard <| Level.setBlock p
          (k.block { s with powered := !s.powered, «open» := !s.powered }) 2 : M Unit) env l := by
  have hs := signal_eq s p env l
  rw [h] at hs
  unfold other at hs
  simp only [neighborChanged, bind, ReaderT.bind, StateT.bind, hs, hb, Bool.not_false,
    Bool.not_bne_self, Bool.and_self, ↓reduceIte]

/-- **The other half follows.** A half that receives a shape update from the cell of the other
half, where a door state of the other half stands, takes over that state and keeps its own
`half`. The level is only read. -/
theorem updateShape_copies (k k' : DoorId) (s s' : Blocks.Door) (p : Pos) (env : Env) (l : Level)
    (h : s'.half ≠ s.half) :
    updateShape k s p (if s.half = .lower then .up else .down) (k'.block s') env l =
      (k'.block { s' with half := s.half }, l) := by
  have hd := DoorId.door?_block k' s'
  cases hh : s.half <;> simp_all [updateShape, Direction.axis] <;> rfl

end DoorBlock

end Redstone.Component.Door
