module

public import Redstone.Component.Rail

/-!
# Lemmas about rails

Generic facts about the rails as blocks, over an arbitrary level; the theorems about concrete
layouts are in `Redstone/Theorems/RailMisc`.

* **Attribute lemmas.** A straight rail keeps its shape through `toStraight?` and is never
  given a curve (`toStraight?_ofStraight`, `setShape_poweredRail_of_curve`); every shape
  connects exactly two positions (`RailState.length_connectionsOf`).
* **The search of a powered rail.** `findPoweredRailSignal` is the search a powered rail or an
  activator rail makes for a rail of its own block that is on and receives a signal. For a
  flat line along the x axis, in either direction:
  * `findPoweredRailSignal_of_line`: if the next `k` rails of the line are on, the `k`-th of
    them receives a signal and `k` is at most the fuel, the search succeeds;
  * `findPoweredRailSignal_of_no_signal`: if none of the next `fuel` rails of the line
    receives a signal, and no rail of the kind lies below them, the search fails, whatever
    lies further along the line. With the fuel 8 that `poweredUpdateState` gives it, this is
    the depth bound: a rail is switched on by a source at most eight rails away, so a source
    carries nine rails in each direction including the one it touches, and the tenth stays
    off.
* **A single reaction.** `poweredUpdateState_of_agrees`: a rail whose `powered` property
  already is what the signal and the two searches call for does nothing.

Left out:

* The same two lemmas for a line along the z axis and for slopes. The proof is the same case
  by case; the concrete layouts with a slope are evaluated in
  `Redstone/Theorems/RailMisc/PoweredRailSlope.lean`.
* The converse of `findPoweredRailSignal_of_line` in general (the search fails exactly when no
  source is within reach): a rail below the line, or a rail of the line that is off, makes
  the statement longer than the function.
* What `poweredUpdateState` does when the rail disagrees: it sets the block and updates the
  neighbours, and what those do depends on the whole level.
-/

@[expose] public section

namespace Redstone.Component.Rail

/-! ### Attribute lemmas -/

/-- A shape of a straight rail is read back as it was written. -/
@[simp]
theorem toStraight?_ofStraight (s : StraightShape) : toStraight? (ofStraight s) = some s := by
  cases s <;> rfl

/-- Giving a powered rail a shape of a straight rail sets that shape. -/
theorem setShape_poweredRail (id : Blocks.PoweredRail.Id) (s : Blocks.PoweredRail)
    (shape : StraightShape) :
    setShape (.poweredRail id s) (ofStraight shape) =
      .poweredRail id { s with shape := shape } := by
  simp [setShape]

/-- A powered rail is never given a curve: `setShape` with a shape that is not straight leaves
it as it is. -/
theorem setShape_poweredRail_of_curve (id : Blocks.PoweredRail.Id) (s : Blocks.PoweredRail)
    (shape : RailShape) (h : toStraight? shape = none) :
    setShape (.poweredRail id s) shape = .poweredRail id s := by
  simp [setShape, h]

/-- Every shape connects exactly two positions. -/
theorem RailState.length_connectionsOf (p : Pos) (shape : RailShape) :
    (RailState.connectionsOf p shape).length = 2 := by
  cases shape <;> rfl

/-- A flat shape is not a slope. -/
theorem isSlope_east_west : isSlope (ofStraight .east_west) = false := rfl

/-! ### The search of a powered rail -/

/-- The direction in which `findPoweredRailSignal` walks along a flat rail of shape
`east_west`: west when `forward` is set, east otherwise. -/
def searchDirectionX (forward : Bool) : Direction := if forward then .west else .east

/-- The position `i` cells further along the search from `p`, for a flat line along the x
axis. -/
def alongX (forward : Bool) (p : Pos) (i : ℕ) : Pos := (·.step (searchDirectionX forward))^[i] p

/-- One more rail along the search is one rail along the search from the next cell. -/
theorem alongX_succ (forward : Bool) (p : Pos) (i : ℕ) :
    alongX forward p (i + 1) = alongX forward (p.step (searchDirectionX forward)) i :=
  Function.iterate_succ_apply ..

/-- The first position along the search is the next cell in the direction of the search. -/
theorem alongX_one (forward : Bool) (p : Pos) :
    alongX forward p 1 = p.step (searchDirectionX forward) := rfl

/-- With no fuel the search fails. -/
@[simp]
theorem findPoweredRailSignal_zero (env : Env) (l : Level) (id : Blocks.PoweredRail.Id) (p : Pos)
    (shape : StraightShape) (forward : Bool) :
    findPoweredRailSignal env l id 0 p shape forward = false := by
  simp [findPoweredRailSignal]

/-- One step of the search along a flat line: when the next cell holds a rail of the same
block and of shape `east_west` that is on, the search succeeds if that rail receives a signal
or the search from it does. -/
theorem findPoweredRailSignal_step_of_on (env : Env) (l : Level) (id : Blocks.PoweredRail.Id)
    (fuel : ℕ) (p : Pos) (forward : Bool) (s : Blocks.PoweredRail)
    (hb : l.blockAt (p.step (searchDirectionX forward)) = .poweredRail id s)
    (hp : s.powered = true) (hs : s.shape = .east_west)
    (h : l.hasNeighborSignalAt env (p.step (searchDirectionX forward)) = true ∨
      findPoweredRailSignal env l id fuel (p.step (searchDirectionX forward)) .east_west forward
        = true) :
    findPoweredRailSignal env l id (fuel + 1) p .east_west forward = true := by
  cases forward <;>
    simp only [searchDirectionX, Bool.false_eq_true, ite_true, ite_false] at hb h <;>
    rcases h with h | h <;>
    simp [findPoweredRailSignal, hb, hp, hs, h]

/-- **A source within reach is found.** Let the next `k` cells along a flat line from `p` hold
rails of the block `id` and of shape `east_west` that are on, let the `k`-th of them receive a
signal, and let `1 ≤ k ≤ fuel`. Then the search from `p` succeeds. With the fuel 8 of
`poweredUpdateState`: a rail at most eight rails from a source is switched on. -/
theorem findPoweredRailSignal_of_line (env : Env) (l : Level) (id : Blocks.PoweredRail.Id)
    (forward : Bool) (fuel : ℕ) :
    ∀ (p : Pos) (k : ℕ), 1 ≤ k → k ≤ fuel →
      (∀ i, 1 ≤ i → i ≤ k → ∃ s, l.blockAt (alongX forward p i) = .poweredRail id s ∧
        s.powered = true ∧ s.shape = .east_west) →
      l.hasNeighborSignalAt env (alongX forward p k) = true →
      findPoweredRailSignal env l id fuel p .east_west forward = true := by
  induction fuel with
  | zero => intro p k h1 h2; omega
  | succ fuel ih =>
    intro p k h1 h2 hline hsrc
    obtain ⟨s, hb, hp, hs⟩ := hline 1 (le_refl 1) h1
    rw [alongX_one] at hb
    refine findPoweredRailSignal_step_of_on env l id fuel p forward s hb hp hs ?_
    rcases Nat.eq_or_lt_of_le h1 with hk | hk
    · left
      rw [← hk, alongX_one] at hsrc
      exact hsrc
    · right
      refine ih (p.step (searchDirectionX forward)) (k - 1) (by omega) (by omega) ?_ ?_
      · intro i hi1 hi2
        have := hline (i + 1) (by omega) (by omega)
        rwa [alongX_succ] at this
      · have hk' : k = (k - 1) + 1 := by omega
        rw [hk', alongX_succ] at hsrc
        exact hsrc

/-- One step of the search along a flat line: when the next cell holds a rail of shape
`east_west` that receives no signal, and the cell below it holds no powered rail or activator
rail, the search succeeds only if the search from that rail does. -/
theorem findPoweredRailSignal_step_of_no_signal (env : Env) (l : Level)
    (id : Blocks.PoweredRail.Id) (fuel : ℕ) (p : Pos) (forward : Bool)
    (id' : Blocks.PoweredRail.Id) (s : Blocks.PoweredRail)
    (hb : l.blockAt (p.step (searchDirectionX forward)) = .poweredRail id' s)
    (hs : s.shape = .east_west)
    (hsig : l.hasNeighborSignalAt env (p.step (searchDirectionX forward)) = false)
    (hbelow : ∀ id'' s'',
      l.blockAt ((p.step (searchDirectionX forward)).step .down) ≠ .poweredRail id'' s'')
    (hrec : findPoweredRailSignal env l id fuel (p.step (searchDirectionX forward)) .east_west
      forward = false) :
    findPoweredRailSignal env l id (fuel + 1) p .east_west forward = false := by
  cases forward <;>
    simp only [searchDirectionX, Bool.false_eq_true, ite_true, ite_false]
      at hb hsig hbelow hrec <;>
    · simp only [findPoweredRailSignal, hb, hs, hsig, hrec, Bool.false_eq_true, ite_true,
        ite_false]
      split <;> simp_all

/-- **The depth bound.** Let the next `fuel` cells along a flat line from `p` hold powered
rails or activator rails of shape `east_west`, none of which receives a signal, with no such
rail in the cells below them. Then the search from `p` fails, whatever lies further along the
line: a source more than `fuel` rails away is not found. `poweredUpdateState` searches with
the fuel 8, so the ninth rail beyond the one a source touches stays off. -/
theorem findPoweredRailSignal_of_no_signal (env : Env) (l : Level) (id : Blocks.PoweredRail.Id)
    (forward : Bool) (fuel : ℕ) :
    ∀ (p : Pos),
      (∀ i, 1 ≤ i → i ≤ fuel → ∃ id' s, l.blockAt (alongX forward p i) = .poweredRail id' s ∧
        s.shape = .east_west ∧ l.hasNeighborSignalAt env (alongX forward p i) = false ∧
        ∀ id'' s'', l.blockAt ((alongX forward p i).step .down) ≠ .poweredRail id'' s'') →
      findPoweredRailSignal env l id fuel p .east_west forward = false := by
  induction fuel with
  | zero => intro p _; exact findPoweredRailSignal_zero ..
  | succ fuel ih =>
    intro p hline
    obtain ⟨id', s, hb, hs, hsig, hbelow⟩ := hline 1 (le_refl 1) (by omega)
    rw [alongX_one] at hb hsig hbelow
    refine findPoweredRailSignal_step_of_no_signal env l id fuel p forward id' s hb hs hsig
      hbelow (ih _ ?_)
    intro i hi1 hi2
    have := hline (i + 1) (by omega) (by omega)
    rwa [alongX_succ] at this

/-! ### A single reaction -/

/-- **A rail that agrees with its signal does nothing.** If the `powered` property of a powered
rail or an activator rail already is what its own signal and the two searches call for,
`poweredUpdateState` leaves the level as it is. -/
theorem poweredUpdateState_of_agrees (id : Blocks.PoweredRail.Id) (s : Blocks.PoweredRail)
    (p : Pos) (block : BlockId) (env : Env) (l : Level)
    (h : (l.hasNeighborSignalAt env p || findPoweredRailSignal env l id 8 p s.shape true
      || findPoweredRailSignal env l id 8 p s.shape false) = s.powered) :
    poweredUpdateState id s p block env l = ((), l) := by
  simp only [poweredUpdateState, bind, ReaderT.bind, StateT.bind, get, getThe, MonadStateOf.get,
    liftM, monadLift, MonadLift.monadLift, StateT.get, read, readThe, MonadReaderOf.read,
    ReaderT.read, pure, ReaderT.pure, StateT.pure, h, bne_self_eq_false, Bool.false_eq_true,
    ite_false]

end Redstone.Component.Rail
