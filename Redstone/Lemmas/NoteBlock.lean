module

public import Redstone.Component.NoteBlock

/-!
# Lemmas about the note block

Generic facts about one component, over an arbitrary level.

* **Attribute lemmas.** Using a note block raises its note by one, from 24 back to 0
  (`cycleNote_note_val`), and leaves the instrument and `powered` alone; 25 uses bring the
  note back (`cycleNote_iterate_25`). The instruments that work above a note block are the
  seven mob heads (`worksAboveNoteBlock_iff`). `setInstrument` changes only the instrument
  (`setInstrument_note`, `setInstrument_powered`): a mob head above wins
  (`setInstrument_of_head_above`), otherwise the block below decides
  (`setInstrument_of_no_head_above`).
* **The play guard** (`playNote_of_blocked`, `playNote_of_air_above`, `playNote_of_head`): a
  note block with a block above that is not air, and whose instrument is not a mob head, does
  not play: the level is left as it is. With air above, or with a mob-head instrument, it
  queues its block event and announces `note_block_play`.
* **The edges** (`neighborChanged_of_agrees`, `neighborChanged_rising`,
  `neighborChanged_falling`): a neighbour update that finds the signal equal to `powered`
  does nothing. A rising edge plays and then sets `powered`; a falling edge only clears
  `powered`. So the note block plays once per rising edge.
* **The block event** (`triggerEvent_of_custom_head`, `triggerEvent_of_not_custom_head`):
  with the instrument of a player head nothing happens (the model has no custom sound);
  otherwise the level's random generator is advanced by one `nextLong` and nothing else
  changes.

Left out: which level `Level.setBlock` leaves after the edge (it runs the shape updates of
the neighbours, an observer among them), and what the listeners of the game event do. The
edge lemmas therefore say which program the reaction is; `neighborChanged_of_agrees` and the
blocked play guard are statements about the level.
-/

@[expose] public section

namespace Redstone.Component.NoteBlock

/-! ### Attribute lemmas -/

/-- Using a note block raises the note by one, and from 24 it goes back to 0. -/
theorem cycleNote_note_val (s : Blocks.Note) :
    (cycleNote s).note.val = (s.note.val + 1) % 25 := by
  simp [cycleNote, Fin.val_add]

/-- Using a note block does not change its instrument. -/
@[simp]
theorem cycleNote_instrument (s : Blocks.Note) : (cycleNote s).instrument = s.instrument := rfl

/-- Using a note block does not change `powered`. -/
@[simp]
theorem cycleNote_powered (s : Blocks.Note) : (cycleNote s).powered = s.powered := rfl

/-- The note after `n` uses. -/
theorem cycleNote_iterate_note_val (s : Blocks.Note) (n : ℕ) :
    (cycleNote^[n] s).note.val = (s.note.val + n) % 25 := by
  induction n with
  | zero => simp [Nat.mod_eq_of_lt s.note.isLt]
  | succ n ih =>
    rw [Function.iterate_succ_apply', cycleNote_note_val, ih]
    omega

/-- `n` uses change nothing but the note. -/
theorem cycleNote_iterate_rest (s : Blocks.Note) (n : ℕ) :
    (cycleNote^[n] s).instrument = s.instrument ∧ (cycleNote^[n] s).powered = s.powered := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih

/-- **25 uses bring a note block back to the note it had.** -/
theorem cycleNote_iterate_25 (s : Blocks.Note) : cycleNote^[25] s = s := by
  have h₁ := cycleNote_iterate_note_val s 25
  have h₂ := cycleNote_iterate_rest s 25
  generalize cycleNote^[25] s = t at h₁ h₂
  obtain ⟨ti, tn, tp⟩ := t
  obtain ⟨si, sn, sp⟩ := s
  simp only at h₁ h₂
  obtain ⟨rfl, rfl⟩ := h₂
  have : tn = sn := Fin.ext (by have := sn.isLt; omega)
  rw [this]

/-- The instruments that work above a note block are those of the seven mob heads. -/
theorem worksAboveNoteBlock_iff (i : NoteBlockInstrument) :
    worksAboveNoteBlock i = true ↔
      i ∈ [.zombie, .skeleton, .creeper, .dragon, .wither_skeleton, .piglin, .custom_head] := by
  cases i <;> simp [worksAboveNoteBlock]

/-- Only the instrument of a player head has a custom sound. -/
theorem hasCustomSound_iff (i : NoteBlockInstrument) :
    hasCustomSound i = true ↔ i = .custom_head := by
  simp [hasCustomSound]

/-- `setInstrument` does not change the note. -/
@[simp]
theorem setInstrument_note (l : Level) (p : Pos) (s : Blocks.Note) :
    (setInstrument l p s).note = s.note := by
  unfold setInstrument
  dsimp only
  split <;> rfl

/-- `setInstrument` does not change `powered`. -/
@[simp]
theorem setInstrument_powered (l : Level) (p : Pos) (s : Blocks.Note) :
    (setInstrument l p s).powered = s.powered := by
  unfold setInstrument
  dsimp only
  split <;> rfl

/-- A mob head above the note block gives its instrument. -/
theorem setInstrument_of_head_above (l : Level) (p : Pos) (s : Blocks.Note)
    (h : worksAboveNoteBlock (l.blockAt (p.step .up)).instrument = true) :
    (setInstrument l p s).instrument = (l.blockAt (p.step .up)).instrument := by
  simp [setInstrument, h]

/-- Without a mob head above, the block below gives the instrument; a mob head below counts
as `harp`. -/
theorem setInstrument_of_no_head_above (l : Level) (p : Pos) (s : Blocks.Note)
    (h : worksAboveNoteBlock (l.blockAt (p.step .up)).instrument = false) :
    (setInstrument l p s).instrument =
      if worksAboveNoteBlock (l.blockAt (p.step .down)).instrument = true then .harp
      else (l.blockAt (p.step .down)).instrument := by
  simp [setInstrument, h]

/-! ### The play guard -/

/-- **A block above silences the note block**: when the instrument is not that of a mob head
and the block above is not air, `playNote` leaves the level as it is: no block event, no game
event. -/
theorem playNote_of_blocked (s : Blocks.Note) (p : Pos) (env : Env) (l : Level)
    (hinst : worksAboveNoteBlock s.instrument = false)
    (habove : (l.blockAt (p.step .up)).isAir = false) : playNote s p env l = ((), l) := by
  simp only [playNote, hinst, Bool.false_or, Level.getBlock, bind, ReaderT.bind, StateT.bind, get,
    getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, pure,
    ReaderT.pure, StateT.pure, habove, Bool.false_eq_true, ↓reduceIte]

/-- With air above, the note block plays: it queues its block event and announces
`note_block_play`. -/
theorem playNote_of_air_above (s : Blocks.Note) (p : Pos) (env : Env) (l : Level)
    (habove : (l.blockAt (p.step .up)).isAir = true) :
    playNote s p env l =
      (do Level.blockEvent p .note_block 0 0
          Level.gameEvent "minecraft:note_block_play" p : M Unit) env l := by
  simp only [playNote, Level.getBlock, bind, ReaderT.bind, StateT.bind, get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, pure, ReaderT.pure,
    StateT.pure, habove, Bool.or_true, ite_true]

/-- With the instrument of a mob head the note block plays whatever is above it. -/
theorem playNote_of_head (s : Blocks.Note) (p : Pos) (env : Env) (l : Level)
    (hinst : worksAboveNoteBlock s.instrument = true) :
    playNote s p env l =
      (do Level.blockEvent p .note_block 0 0
          Level.gameEvent "minecraft:note_block_play" p : M Unit) env l := by
  simp only [playNote, hinst, Bool.true_or, ↓reduceIte, Level.getBlock, bind, ReaderT.bind,
    StateT.bind, get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get,
    pure, ReaderT.pure, StateT.pure]

/-- What queuing the block event of a note block does to the level: the event is added at the
end, unless the same event is already queued. -/
theorem blockEvent_note (p : Pos) (env : Env) (l : Level) :
    Level.blockEvent p .note_block 0 0 env l =
      ((), if l.blockEvents.contains ⟨p, .note_block, 0, 0⟩ then l
        else { l with blockEvents := l.blockEvents ++ [⟨p, .note_block, 0, 0⟩] }) := rfl

/-! ### The edges -/

/-- **No edge, no reaction.** A neighbour update that finds the signal at the note block equal
to its `powered` property leaves the level as it is. -/
theorem neighborChanged_of_agrees (s : Blocks.Note) (p : Pos) (b : BlockId) (m : Bool) (env : Env)
    (l : Level) (h : l.hasNeighborSignalAt env p = s.powered) :
    (behaviour (.note s)).neighborChanged p b m env l = ((), l) := by
  simp only [behaviour, Level.hasNeighborSignal, bind, ReaderT.bind, StateT.bind, get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, pure, ReaderT.pure,
    StateT.pure, read, readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ↓reduceIte, h, bne_self_eq_false, Bool.false_eq_true]

/-- **A rising edge plays the note, once, and sets `powered`.** -/
theorem neighborChanged_rising (s : Blocks.Note) (p : Pos) (b : BlockId) (m : Bool) (env : Env)
    (l : Level) (hoff : s.powered = false) (hsig : l.hasNeighborSignalAt env p = true) :
    (behaviour (.note s)).neighborChanged p b m env l =
      (do playNote s p
          discard <| Level.setBlock p (.note { s with powered := true }) : M Unit) env l := by
  simp only [behaviour, Level.hasNeighborSignal, bind, ReaderT.bind, StateT.bind, get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, pure, ReaderT.pure,
    StateT.pure, read, readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ↓reduceIte, hsig, hoff, bne_iff_ne, ne_eq, Bool.true_eq_false, not_false_eq_true]

/-- **A falling edge does not play**: it only clears `powered`. -/
theorem neighborChanged_falling (s : Blocks.Note) (p : Pos) (b : BlockId) (m : Bool) (env : Env)
    (l : Level) (hon : s.powered = true) (hsig : l.hasNeighborSignalAt env p = false) :
    (behaviour (.note s)).neighborChanged p b m env l =
      (discard <| Level.setBlock p (.note { s with powered := false }) : M Unit) env l := by
  simp only [behaviour, Level.hasNeighborSignal, bind, ReaderT.bind, StateT.bind, get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, pure, ReaderT.pure,
    StateT.pure, read, readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ↓reduceIte, hsig, hon, bne_iff_ne, ne_eq, Bool.false_eq_true, not_false_eq_true]

/-! ### Using the block, and the block event -/

/-- Using a note block sets the block with the next note and plays that note. -/
theorem use_eq (s : Blocks.Note) (p : Pos) :
    use s p = (do
      discard <| Level.setBlock p (.note (cycleNote s))
      playNote (cycleNote s) p) := rfl

/-- With the instrument of a player head the block event does nothing and answers `false`. -/
theorem triggerEvent_of_custom_head (s : Blocks.Note) (env : Env) (l : Level)
    (h : s.instrument = .custom_head) : triggerEvent s env l = (false, l) := by
  simp only [triggerEvent, hasCustomSound, h, decide_true, ite_true]
  rfl

/-- With any other instrument the block event answers `true`, and all it changes in the level
is the random generator: one `nextLong`, two draws of 32 bits. -/
theorem triggerEvent_of_not_custom_head (s : Blocks.Note) (env : Env) (l : Level)
    (h : s.instrument ≠ .custom_head) :
    triggerEvent s env l = (true, { l with random := ((l.random.next 32).2.next 32).2 }) := by
  simp only [triggerEvent, hasCustomSound, h, decide_false, Bool.false_eq_true, ite_false]
  rfl

end Redstone.Component.NoteBlock
