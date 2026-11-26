module

public import Mathlib.Tactic

/-!
# The game's random number generator

`LegacyRandomSource`, the 48-bit linear congruential generator of `java.util.Random`. The level
owns one (`Level.random`), and blocks draw from it, so its state is part of the state of the
world.
-/

@[expose] public section

namespace Redstone

/-- The state of a `LegacyRandomSource`: a 48-bit seed. -/
structure JavaRandom where
  seed : ℕ
  deriving DecidableEq, Repr, Inhabited

namespace JavaRandom

/-- `2 ^ 48 - 1`. -/
def mask : ℕ := 2 ^ 48 - 1

/-- The generator obtained from `setSeed(s)`, for `s` a 64-bit value given as a natural number. -/
def ofSeed (s : ℕ) : JavaRandom := ⟨(s ^^^ 0x5DEECE66D) &&& mask⟩

/-- `next(bits)` as an unsigned number below `2 ^ bits`, for `bits ≤ 32`. -/
def next (r : JavaRandom) (bits : ℕ) : ℕ × JavaRandom :=
  let s := (r.seed * 0x5DEECE66D + 0xB) &&& mask
  (s >>> (48 - bits), ⟨s⟩)

/-- `nextBoolean()`. -/
def nextBool (r : JavaRandom) : Bool × JavaRandom :=
  let (v, r) := r.next 1
  (v != 0, r)

/-- The rejection loop of `nextInt(bound)` for a bound that is not a power of two. A draw is
rejected with probability below one half, so the fuel is never used up in practice. -/
def nextIntLoop (bound : ℕ) : ℕ → JavaRandom → ℕ × JavaRandom
  | 0, r => (0, r)
  | fuel + 1, r =>
    let (bits, r) := r.next 31
    let val := bits % bound
    -- Java tests `bits - val + (bound - 1) < 0` in 32-bit arithmetic, which is an overflow test.
    if bits - val + (bound - 1) < 2 ^ 31 then (val, r) else nextIntLoop bound fuel r

/-- `nextInt(bound)` for `0 < bound < 2 ^ 31`: a number below `bound`. -/
def nextInt (r : JavaRandom) (bound : ℕ) : ℕ × JavaRandom :=
  if bound &&& (bound - 1) = 0 then
    let (v, r) := r.next 31
    ((bound * v) >>> 31, r)
  else
    nextIntLoop bound 128 r

/-- `nextFloat()` as the numerator of a fraction with denominator `2 ^ 24`. -/
def nextFloat24 (r : JavaRandom) : ℕ × JavaRandom := r.next 24

/-- `nextDouble()` as the numerator of a fraction with denominator `2 ^ 53`. -/
def nextDouble53 (r : JavaRandom) : ℕ × JavaRandom :=
  let (hi, r) := r.next 26
  let (lo, r) := r.next 27
  (hi <<< 27 + lo, r)

end JavaRandom

end Redstone
