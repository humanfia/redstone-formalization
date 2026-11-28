import Redstone.Proof.Circuit

/-!
# Cycle certificates for levels with hoppers

A cycle certificate of the foundation (`Rules.Cycle`) says that one period takes a level to
itself, shifted in time by `Level.shift`. That shift moves the game time and the due times of
scheduled ticks, and leaves the block entities alone. A hopper records the game time at which
it was last ticked (`tickedGameTime`), so a level with a hopper never comes back to itself in
that sense, and `Rules.Cycle` is false for every clock made of hoppers
(`Bounce.not_cycle_without_stamps` is an instance).

This file extends the shift: `shift l dt dc` is `l.shift dt dc` with the time stamp of every
ticking hopper moved on by `dt` as well, and `Cycle` is the certificate with that shift. The
stamp is only ever compared with the stamp of another hopper (`Container.tryMoveInItem`: a
hopper that receives an item while empty waits 7 game ticks, not 8, if it was ticked no earlier
than the sender), so a level and its shift behave alike; that last claim is not proved here.

As in the foundation, a certificate is one period, checked by comparing two checkpoints. It is
*not* a proof that the level repeats for ever. `periodic_of_commute` is the conditional
statement, for any shift: if a game tick commutes with the shift on the levels of one period,
the level after `k` periods is the level shifted `k` times. Its hypothesis is not proved for
any component.

Left out: hoppers that are not in the list of ticking block entities (the game has none), and
a position listed twice there (its stamp would be moved twice).
-/

namespace Redstone.Theorems.Hopper

/-- The block entity with its time stamp moved on by `dt` game ticks, if it is a hopper. -/
def shiftStamp (dt : ℕ) : BlockEntity → BlockEntity
  | .hopper h => .hopper { h with tickedGameTime := h.tickedGameTime + dt }
  | be => be

/-- The block entities with the time stamps of the hoppers at the positions `ps` moved on by
`dt` game ticks. -/
def shiftStamps (dt : ℕ) (m : PosMap BlockEntity) (ps : List Pos) : PosMap BlockEntity :=
  ps.foldl (fun m p =>
    match m p with
    | some be => m.insert p (shiftStamp dt be)
    | none => m) m

/-- The same level `dt` game ticks later, after `dc` more ticks have been scheduled:
`Level.shift`, and the time stamp of every ticking hopper moved on by `dt` as well. -/
def shift (l : Level) (dt dc : ℕ) : Level :=
  { l.shift dt dc with blockEntities := shiftStamps dt l.blockEntities l.blockEntityTickers }

@[simp]
theorem blockAt_shift (l : Level) (dt dc : ℕ) : (shift l dt dc).blockAt = l.blockAt := rfl

@[simp]
theorem world_shift (l : Level) (dt dc : ℕ) : (shift l dt dc).world = l.world := rfl

@[simp]
theorem overflow_shift (l : Level) (dt dc : ℕ) : (shift l dt dc).overflow = l.overflow := rfl

@[simp]
theorem gameTime_shift (l : Level) (dt dc : ℕ) : (shift l dt dc).gameTime = l.gameTime + dt :=
  rfl

/-- A **cycle certificate with hopper time stamps**: `period` game ticks take the level `l` to
itself, shifted in time by the period (`shift`), with `dc` more ticks scheduled. For
checkpoints this is one comparison: `Level.eq_of_beqBlocks (by circuit_decide)`.

It says that the level repeats once; see `periodic_of_commute`. -/
def Cycle (l : Level) (period dc : ℕ) : Prop := rules.steps period l = shift l period dc

/-- If a game tick commutes with a map `σ` of levels on the first `m` levels of the run from
`l`, then so do `i` game ticks, for `i` up to `m`. -/
theorem steps_commute (r : Rules) (σ : Level → Level) {l : Level} {m : ℕ}
    (hinv : ∀ i < m, r.step (σ (r.steps i l)) = σ (r.step (r.steps i l))) (i : ℕ) (hi : i ≤ m) :
    r.steps i (σ l) = σ (r.steps i l) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Rules.steps_add, ih (Nat.le_of_succ_le hi), Rules.steps, Function.iterate_one,
      hinv i hi, Rules.steps_add]
    rfl

/-- From a cycle certificate to periodicity for ever, for any shift `σ` of levels: **if** a
game tick commutes with every iterate of `σ` on the levels of one period, then the level after
`k` periods is the level shifted `k` times. With `σ := (shift · period dc)` and a `Cycle` this
is the statement for a clock of hoppers; the hypothesis is not proved here. -/
theorem periodic_of_commute (r : Rules) (σ : Level → Level) {l : Level} {period : ℕ}
    (hc : r.steps period l = σ l)
    (hinv : ∀ k, ∀ i < period, r.step (σ^[k] (r.steps i l)) = σ^[k] (r.step (r.steps i l)))
    (k : ℕ) : r.steps (k * period) l = σ^[k] l := by
  induction k with
  | zero =>
    rw [Nat.zero_mul, Rules.steps, Function.iterate_zero, Function.iterate_zero]
  | succ k ih =>
    rw [Nat.succ_mul, Rules.steps_add, ih, steps_commute r (σ^[k]) (hinv k) period le_rfl, hc,
      ← Function.iterate_succ_apply]

end Redstone.Theorems.Hopper
