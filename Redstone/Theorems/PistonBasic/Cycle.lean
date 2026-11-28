import Redstone.Proof.Circuit

/-!
# A cycle certificate for clocks with pistons

`Rules.Cycle l period dc` (`Redstone/Proof/Quiescent.lean`) says that `period` game ticks take
the level `l` to itself moved on in time: every field of the level is the same, the times
shifted. A clock with a piston cannot have such a certificate. Every stroke of a piston draws
a number from the random number generator of the level, for the pitch of its sound
(`Redstone.Component.Piston.nextFloat`), so after one period the generator is in another state,
and `Level.shift` leaves the generator alone.

`CycleUpToRandom l period dc` is the certificate without that field: `period` game ticks take
`l` to itself moved on in time, with *some* state of the random number generator. Everything
else is the same: blocks, block entities, scheduled ticks with their delays and their order,
pending block events, counters.

Like `Rules.Cycle`, this is one period and not periodicity for ever. To go from one period to
all of them one would need that a game tick commutes with the time shift
(`Rules.periodic_of_shiftInvariant`) and, here, that the blocks do not depend on the random
number generator. Neither is proved.

Used by `StickyPistonClock.lean` and `TwoPistonClock.lean`.
-/

namespace Redstone.Theorems.PistonBasic

/-- `period` game ticks take `l` to itself, moved on in time by `period` game ticks with `dc`
more ticks scheduled, except for the state of the random number generator. -/
def CycleUpToRandom (l : Level) (period dc : ℕ) : Prop :=
  ∃ random, rules.steps period l = { l.shift period dc with random := random }

/-- After one period the blocks are where they were. -/
theorem CycleUpToRandom.blockAt {l : Level} {period dc : ℕ} (h : CycleUpToRandom l period dc)
    (p : Pos) : (rules.steps period l).blockAt p = l.blockAt p := by
  obtain ⟨random, h⟩ := h
  rw [h]
  rfl

assert_standard_axioms CycleUpToRandom.blockAt

/-- After one period the model has reached a bound only if it had before. -/
theorem CycleUpToRandom.overflow {l : Level} {period dc : ℕ} (h : CycleUpToRandom l period dc) :
    (rules.steps period l).overflow = l.overflow := by
  obtain ⟨random, h⟩ := h
  rw [h]
  rfl

assert_standard_axioms CycleUpToRandom.overflow

end Redstone.Theorems.PistonBasic
