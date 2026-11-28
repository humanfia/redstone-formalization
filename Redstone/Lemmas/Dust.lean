module

public import Redstone.Component.Dust
public import Redstone.Lemmas.Conduction

/-!
# Lemmas about redstone dust

Generic facts about redstone dust (`Redstone/Component/Dust.lean`, the game's
`RedstoneWireBlock` and `DefaultRedstoneWireEvaluator`), over an arbitrary level.

* **What dust gives** (attribute lemmas about `Dust.signal`): nothing to the block above it
  (`signal_down`), its power to the block below it (`signal_up`), its power to a side it is
  connected to (`signal_of_connected`) and nothing to a side it is not connected to
  (`signal_of_not_connected`); never more than its power (`signal_le`), which is at most 15.
* **What dust receives from other dust.** `wireReach l p d` is the strongest dust that reaches
  the dust at `p` from the horizontal direction `d`: the dust next to it, or the dust one level
  up on a neighbouring conductor (unless a conductor covers `p`: this is the *diagonal cut*),
  or the dust one level down behind a neighbour that is not a conductor.
  `incomingWireSignal_eq` says that `getIncomingWireSignal` is the largest of the four, less
  one; `pred_le_incomingWireSignal`, `incomingWireSignal_le` and `incomingWireSignal_le_14` are
  the bounds that follow, and `wireReach_of_covered` is the cut: under a conductor, with a
  conductor as the neighbour, only the dust at the same level is seen.
* **The power dust should have.** `targetStrength_eq_max`: the power is the larger of the
  strongest signal from blocks other than dust and one less than the strongest dust around it,
  `max (blockSignal) (incomingWireSignal)`; it is at most 15 (`targetStrength_le`); next to a
  source of 15 it is 15 (`targetStrength_of_source`); with no signal from other blocks and one
  strongest neighbour of power `k` it is `k - 1` (`targetStrength_of_wire`): **dust loses one
  unit of power per block**.
* **Dust is silent while dust computes its power** (`RedstoneWireBlock.shouldSignal`, the
  environment `muted`): a piece of dust gives no signal and no direct signal
  (`signalAt_muted_wire`, `directSignalAt_muted_wire`), every other block answers as it does
  otherwise (`muted_block_of_not_wire`). So a conductor without a signal of its own, each of
  whose neighbours is dust or gives it no strong power, gives nothing to dust
  (`signalAt_muted_of_fed_by_dust`): **a block powered only by dust (weakly) does not power
  dust**. Dust is not a conductor (`isConductor_wire`).
* **Single-reaction lemmas.** Dust whose power already is what it should be does nothing in
  `updatePowerStrength` (`updatePowerStrength_of_eq`) and so nothing on a neighbour update, as
  long as it is supported (`neighborChanged_of_settled`).

Left out:

* The decay along a straight line of `n ≤ 15` pieces as one statement by induction ("in a
  level at rest the `i`-th piece has power `16 - i`"). The step is `targetStrength_of_wire`;
  the induction needs, for every piece of the line, what the other fifteen positions around it
  hold and that nothing else gives it a signal, which is a description of a whole level. That
  is proved for concrete lines by evaluation: `Redstone/Theorems/Basics/DustDecay.lean` and
  `Redstone/Theorems/Wire/DustRange.lean`.
* What `updatePowerStrength` does when the power *changes*: it sets the block and then runs
  neighbour updates around seven positions, each of which may reach any block of the level.
* The shape of dust (`connectionState`) in terms of the blocks around it: `connectingSide` is
  a case distinction over attributes of three blocks per side, used as it is.
-/

@[expose] public section

namespace Redstone.Component.Dust

open Blocks (RedstoneWire)

/-! ### What dust gives -/

/-- **Dust gives nothing to the block above it** (which asks with `down`). -/
theorem signal_down (s : RedstoneWire) (l : Level) (p : Pos) : signal s l p .down = 0 := by
  simp [signal]

/-- **Dust gives its power to the block below it** (which asks with `up`), whatever its
shape. -/
theorem signal_up (s : RedstoneWire) (l : Level) (p : Pos) : signal s l p .up = s.power.val := by
  by_cases h : s.power.val = 0 <;> simp [signal, h]

/-- Dust without power gives no signal. -/
theorem signal_of_power_zero (s : RedstoneWire) (l : Level) (p : Pos) (d : Direction)
    (h : s.power.val = 0) : signal s l p d = 0 := by
  by_cases hd : d = .down <;> simp [signal, h, hd]

/-- Dust never gives more than its power. -/
theorem signal_le (s : RedstoneWire) (l : Level) (p : Pos) (d : Direction) :
    signal s l p d ≤ s.power.val := by
  unfold signal
  split_ifs <;> omega

/-- Dust never gives more than 15. -/
theorem signal_le_fifteen (s : RedstoneWire) (l : Level) (p : Pos) (d : Direction) :
    signal s l p d ≤ 15 :=
  le_trans (signal_le s l p d) (by omega)

/-- **Dust gives its power to a side it is connected to.** The neighbour asks with `d`, so it
lies in direction `d.opposite` from the dust; the connection is computed from the level
(`connectionState`), as the game does. -/
theorem signal_of_connected (s : RedstoneWire) (l : Level) (p : Pos) (d : Direction)
    (hd : d ≠ .down) (h : isConnected (side (connectionState l s p) d.opposite) = true) :
    signal s l p d = s.power.val := by
  by_cases h0 : s.power.val = 0 <;> simp [signal, hd, h, h0]

/-- **Dust gives nothing to a side it is not connected to**: a line of dust does not power the
blocks it runs past. -/
theorem signal_of_not_connected (s : RedstoneWire) (l : Level) (p : Pos) (d : Direction)
    (hu : d ≠ .up) (h : isConnected (side (connectionState l s p) d.opposite) = false) :
    signal s l p d = 0 := by
  by_cases hd : d = .down <;> by_cases h0 : s.power.val = 0 <;> simp [signal, hd, hu, h, h0]

/-! ### What dust receives from other dust -/

/-- The power of dust is at most 15. -/
theorem wireSignal_le (b : Block) : wireSignal b ≤ 15 := by
  unfold wireSignal
  split
  · omega
  · exact Nat.zero_le _

/-- The power of a piece of dust, as `getWireSignal` reads it. -/
@[simp]
theorem wireSignal_wire (s : RedstoneWire) : wireSignal (.redstoneWire s) = s.power.val := rfl

/-- The strongest dust that reaches the dust at `p` from the horizontal direction `d`: the
dust next to it; the dust on top of the neighbour, if the neighbour is a conductor and no
conductor covers `p`; the dust below the neighbour's place, if the neighbour is not a
conductor. This is one round of the loop of `getIncomingWireSignal`. -/
def wireReach (l : Level) (p : Pos) (d : Direction) : ℕ :=
  max (wireSignal (l.blockAt (p.step d)))
    (if (l.blockAt (p.step d)).isConductor && !(l.blockAt (p.step .up)).isConductor then
      wireSignal (l.blockAt ((p.step d).step .up))
    else if !(l.blockAt (p.step d)).isConductor then
      wireSignal (l.blockAt ((p.step d).step .down))
    else 0)

/-- The dust next to `p` reaches it. -/
theorem wireSignal_le_wireReach (l : Level) (p : Pos) (d : Direction) :
    wireSignal (l.blockAt (p.step d)) ≤ wireReach l p d :=
  Nat.le_max_left ..

/-- No dust reaches with more than 15. -/
theorem wireReach_le (l : Level) (p : Pos) (d : Direction) : wireReach l p d ≤ 15 := by
  unfold wireReach
  have h₁ := wireSignal_le (l.blockAt (p.step d))
  have h₂ := wireSignal_le (l.blockAt ((p.step d).step .up))
  have h₃ := wireSignal_le (l.blockAt ((p.step d).step .down))
  split_ifs <;> omega

/-- **The diagonal cut.** When a conductor covers the dust at `p` and the neighbour in
direction `d` is a conductor, the dust on top of that neighbour does not reach `p`: only the
block at the same level counts (and a conductor is not dust). -/
theorem wireReach_of_covered (l : Level) (p : Pos) (d : Direction)
    (hup : (l.blockAt (p.step .up)).isConductor = true)
    (hn : (l.blockAt (p.step d)).isConductor = true) :
    wireReach l p d = wireSignal (l.blockAt (p.step d)) := by
  simp [wireReach, hup, hn]

/-- Up a step: the dust on top of a neighbouring conductor reaches `p` when no conductor
covers `p`. -/
theorem wireSignal_up_le_wireReach (l : Level) (p : Pos) (d : Direction)
    (hup : (l.blockAt (p.step .up)).isConductor = false)
    (hn : (l.blockAt (p.step d)).isConductor = true) :
    wireSignal (l.blockAt ((p.step d).step .up)) ≤ wireReach l p d := by
  simp [wireReach, hup, hn]

/-- Down a step: the dust one level down behind a neighbour that is not a conductor reaches
`p`. This is the direction in which a staircase of slabs or glass carries a signal: the upper
dust reads the lower one, and not the other way round. -/
theorem wireSignal_down_le_wireReach (l : Level) (p : Pos) (d : Direction)
    (hn : (l.blockAt (p.step d)).isConductor = false) :
    wireSignal (l.blockAt ((p.step d).step .down)) ≤ wireReach l p d := by
  simp [wireReach, hn]

private theorem foldl_max_wireReach (l : Level) (p : Pos) (ds : List Direction) (b : ℕ) :
    ds.foldl
      (fun best d =>
        let neighborPos := p.step d
        let neighbor := l.blockAt neighborPos
        let best := max best (wireSignal neighbor)
        if neighbor.isConductor && !(l.blockAt (p.step .up)).isConductor then
          max best (wireSignal (l.blockAt (neighborPos.step .up)))
        else if !neighbor.isConductor then
          max best (wireSignal (l.blockAt (neighborPos.step .down)))
        else best) b =
      ds.foldl (fun best d => max best (wireReach l p d)) b := by
  congr 1
  funext best d
  simp only [wireReach]
  split_ifs <;> omega

/-- **`getIncomingWireSignal` is one less than the strongest dust that reaches the position**
from the four horizontal directions. -/
theorem incomingWireSignal_eq (l : Level) (p : Pos) :
    incomingWireSignal l p =
      max (max (max (wireReach l p .north) (wireReach l p .east)) (wireReach l p .south))
        (wireReach l p .west) - 1 := by
  unfold incomingWireSignal
  rw [foldl_max_wireReach]
  simp [Direction.horizontals]

/-- Dust of power `k` that reaches `p` gives it at least `k - 1`. -/
theorem pred_le_incomingWireSignal (l : Level) (p : Pos) (d : Direction)
    (hd : d ∈ Direction.horizontals) : wireReach l p d - 1 ≤ incomingWireSignal l p := by
  rw [incomingWireSignal_eq]
  simp only [Direction.horizontals, List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> omega

/-- If no dust reaches `p` with more than `k`, it receives at most `k - 1` from dust. -/
theorem incomingWireSignal_le (l : Level) (p : Pos) (k : ℕ)
    (h : ∀ d ∈ Direction.horizontals, wireReach l p d ≤ k) : incomingWireSignal l p ≤ k - 1 := by
  rw [incomingWireSignal_eq]
  have h₁ := h .north (by simp [Direction.horizontals])
  have h₂ := h .east (by simp [Direction.horizontals])
  have h₃ := h .south (by simp [Direction.horizontals])
  have h₄ := h .west (by simp [Direction.horizontals])
  omega

/-- **Dust alone never gives 15**: what a position receives from dust is at most 14. -/
theorem incomingWireSignal_le_14 (l : Level) (p : Pos) : incomingWireSignal l p ≤ 14 :=
  incomingWireSignal_le l p 15 fun d _ => wireReach_le l p d

/-! ### The power dust should have -/

/-- `getBlockSignal` is at most 15. -/
theorem blockSignal_le (env : Env) (l : Level) (p : Pos) : blockSignal env l p ≤ 15 :=
  Level.bestNeighborSignalAt_le_fifteen ..

/-- **The power of dust is the larger of the strongest signal from blocks other than dust and
one less than the strongest dust around it.** The game writes the case of a signal of 15
separately; it is the same, since dust alone gives at most 14. -/
theorem targetStrength_eq_max (env : Env) (l : Level) (p : Pos) :
    targetStrength env l p = max (blockSignal env l p) (incomingWireSignal l p) := by
  have h := incomingWireSignal_le_14 l p
  unfold targetStrength
  simp only
  split_ifs with h15 <;> omega

/-- The power dust should have is at most 15. -/
theorem targetStrength_le (env : Env) (l : Level) (p : Pos) : targetStrength env l p ≤ 15 := by
  have h₁ := blockSignal_le env l p
  have h₂ := incomingWireSignal_le_14 l p
  rw [targetStrength_eq_max]
  omega

/-- **Next to a source the power is 15.** If a neighbour of `p` gives 15 while dust is silent
(a lever, a lit torch, a powered repeater at its output, a strongly powered block), the dust
at `p` should have power 15. -/
theorem targetStrength_of_source (env : Env) (l : Level) (p : Pos) (d : Direction)
    (h : 15 ≤ l.signalAt (muted env) (p.step d) d) : targetStrength env l p = 15 := by
  have h₁ : blockSignal env l p = 15 := Level.bestNeighborSignalAt_eq_fifteen _ l p d h
  have h₂ := incomingWireSignal_le_14 l p
  rw [targetStrength_eq_max]
  omega

/-- **Dust loses one unit of power per block.** If no block other than dust gives the position
`p` a signal, and the strongest dust that reaches `p` has power `k` (some dust reaches it
with `k` from the horizontal direction `d`, and none with more), the dust at `p` should have
power `k - 1`. -/
theorem targetStrength_of_wire (env : Env) (l : Level) (p : Pos) (d : Direction) (k : ℕ)
    (hsig : blockSignal env l p = 0) (hd : d ∈ Direction.horizontals)
    (hk : wireReach l p d = k) (hle : ∀ e ∈ Direction.horizontals, wireReach l p e ≤ k) :
    targetStrength env l p = k - 1 := by
  have h₁ := pred_le_incomingWireSignal l p d hd
  have h₂ := incomingWireSignal_le l p k hle
  rw [targetStrength_eq_max, hsig]
  omega

/-- **The end of the range.** Dust that no other block gives a signal, and that no dust reaches
with a power of more than 1, should have no power: this is the sixteenth piece of a line. -/
theorem targetStrength_eq_zero (env : Env) (l : Level) (p : Pos)
    (hsig : blockSignal env l p = 0) (h : ∀ e ∈ Direction.horizontals, wireReach l p e ≤ 1) :
    targetStrength env l p = 0 := by
  have h₂ := incomingWireSignal_le l p 1 h
  rw [targetStrength_eq_max, hsig]
  omega

/-! ### Dust is silent while dust computes its power -/

/-- Redstone dust is not a conductor, in any of its states. -/
theorem isConductor_wire (s : RedstoneWire) : (Block.redstoneWire s).isConductor = false := by
  obtain ⟨e, n, pw, so, w⟩ := s
  cases e <;> cases n <;> cases so <;> cases w <;> fin_cases pw <;> rfl

/-- While dust is silent, every block other than dust answers as it does otherwise. -/
theorem muted_block_of_not_wire (env : Env) (b : Block) (h : isWire b = false) :
    (muted env).block b = env.block b := by
  unfold muted
  cases b <;> first | rfl | exact absurd h (by simp [isWire])

/-- **While dust is silent, a piece of dust gives no direct signal.** -/
theorem directSignalAt_muted_wire (env : Env) (l : Level) (q : Pos) (d : Direction)
    (h : isWire (l.blockAt q) = true) : l.directSignalAt (muted env) q d = 0 := by
  unfold Level.directSignalAt muted
  cases hb : l.blockAt q <;> first | rfl | (rw [hb] at h; exact absurd h (by simp [isWire]))

/-- **While dust is silent, a piece of dust gives no signal.** -/
theorem signalAt_muted_wire (env : Env) (l : Level) (q : Pos) (d : Direction)
    (h : isWire (l.blockAt q) = true) : l.signalAt (muted env) q d = 0 := by
  cases hb : l.blockAt q with
  | redstoneWire s =>
    have hc : (l.blockAt q).isConductor = false := by rw [hb]; exact isConductor_wire s
    rw [Level.signalAt_of_not_conductor _ l q d hc, hb]
    rfl
  | _ => rw [hb] at h; exact absurd h (by simp [isWire])

/-- **A block powered only by dust does not power dust.** Let the block at `q` be a conductor
without a signal of its own (stone, a lamp), and let each of its six neighbours be dust or
give it no direct signal. Then, while dust computes its power, `q` gives no signal: dust that
runs into the block does not make dust on its other sides glow. (The block does give a signal
to everything else: `Level.signalAt_of_conductor` with the direct signal of the dust.) -/
theorem signalAt_muted_of_fed_by_dust (env : Env) (l : Level) (q : Pos) (d : Direction)
    (hc : (l.blockAt q).isConductor = true)
    (hs : ((muted env).block (l.blockAt q)).signal l q d = 0)
    (hn : ∀ e, isWire (l.blockAt (q.step e)) = true ∨
      l.directSignalAt (muted env) (q.step e) e = 0) :
    l.signalAt (muted env) q d = 0 :=
  Level.signalAt_conductor_eq_zero _ l q d hc hs fun e =>
    (hn e).elim (directSignalAt_muted_wire env l _ e) id

/-- The signal from blocks other than dust is zero exactly when, with dust silent, no
neighbour gives a signal. -/
theorem blockSignal_eq_zero_iff (env : Env) (l : Level) (p : Pos) :
    blockSignal env l p = 0 ↔ ∀ d, l.signalAt (muted env) (p.step d) d = 0 :=
  Level.bestNeighborSignalAt_eq_zero_iff ..

/-! ### Single-reaction lemmas -/

/-- **Dust that has the power it should have does nothing.** `updatePowerStrength` leaves the
level as it is: no block is set and no neighbour is told. -/
theorem updatePowerStrength_of_eq (p : Pos) (s : RedstoneWire) (env : Env) (l : Level)
    (h : s.power.val = targetStrength env l p) : updatePowerStrength p s env l = ((), l) := by
  simp only [updatePowerStrength, bind, ReaderT.bind, StateT.bind, read, readThe,
    MonadReaderOf.read, ReaderT.read, get, getThe, MonadStateOf.get, liftM, monadLift,
    MonadLift.monadLift, StateT.get, pure, ReaderT.pure, StateT.pure, h, ne_eq,
    not_true_eq_false, ite_false]

/-- **A neighbour update of supported dust that has the power it should have changes
nothing.** -/
theorem neighborChanged_of_settled (p : Pos) (s : RedstoneWire) (env : Env) (l : Level)
    (hsurvive : canSurvive l p = true) (h : s.power.val = targetStrength env l p) :
    neighborChanged s p env l = ((), l) := by
  have := updatePowerStrength_of_eq p s env l h
  simp only [neighborChanged, bind, ReaderT.bind, StateT.bind, get, getThe, MonadStateOf.get,
    liftM, monadLift, MonadLift.monadLift, StateT.get, pure, hsurvive, ite_true]
  exact this

end Redstone.Component.Dust
