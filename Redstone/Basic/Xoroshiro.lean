module

public import Redstone.Basic.Pos

/-!
# The game's other random generator

`XoroshiroRandomSource` (the generator `Xoroshiro128PlusPlus`), with what the game derives from
it:

* the positional generators (`XoroshiroPositionalRandomFactory`). Potent sulfur draws the length
  of a geyser's phases from a generator that depends only on the world seed and on the position
  of the block;
* the server's random sequences (`RandomSequences`): one generator for each key, made on first
  use from the world seed and the key. A loot table draws from the sequence named after it, so
  these generators are part of the state of the world (`Level.lootSequences`).

A `long` is represented by the natural number below `2 ^ 64` with the same bits.
-/

@[expose] public section

namespace Redstone

/-- The seed of the world (`WorldOptions.seed`; `level-seed` in `server.properties`). The
harness sets it to 0. -/
def worldSeed : ℕ := 0

/-- The state of a `Xoroshiro128PlusPlus`: two 64-bit words. -/
structure Xoroshiro where
  lo : ℕ
  hi : ℕ
  deriving DecidableEq, Repr, Inhabited

namespace Xoroshiro

/-- `2 ^ 64`. -/
def two64 : ℕ := 2 ^ 64

/-- The bits of a `long` given as an integer. -/
def ofLong (v : ℤ) : ℕ := (v % (2 ^ 64 : ℤ)).toNat

/-- `RandomSupport.GOLDEN_RATIO_64`. -/
def goldenRatio : ℕ := 0x9E3779B97F4A7C15

/-- `RandomSupport.SILVER_RATIO_64`. -/
def silverRatio : ℕ := 0x6A09E667F3BCC909

/-- `Long.rotateLeft(x, k)` for `0 < k < 64`. -/
def rotl (x k : ℕ) : ℕ := ((x <<< k) % two64) ||| (x >>> (64 - k))

/-- `new Xoroshiro128PlusPlus(seedLo, seedHi)`: the all-zero state is replaced. -/
def ofSeeds (lo hi : ℕ) : Xoroshiro :=
  if lo ||| hi = 0 then ⟨goldenRatio, silverRatio⟩ else ⟨lo, hi⟩

/-- `RandomSupport.mixStafford13`. -/
def mixStafford13 (z : ℕ) : ℕ :=
  let z := ((z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9) % two64
  let z := ((z ^^^ (z >>> 27)) * 0x94D049BB133111EB) % two64
  z ^^^ (z >>> 31)

/-- `new XoroshiroRandomSource(seed)`, through `RandomSupport.upgradeSeedTo128bit`. -/
def ofSeed (seed : ℕ) : Xoroshiro :=
  let lo := seed ^^^ silverRatio
  let hi := (lo + goldenRatio) % two64
  ofSeeds (mixStafford13 lo) (mixStafford13 hi)

/-- The generator of a new random sequence (`RandomSequences.createSequence` with the defaults:
salt 0, the world seed and the key both included): `RandomSupport.upgradeSeedTo128bitUnmixed`
of the world seed, combined with the hash of the key of the sequence, each half mixed.
`hashLo` and `hashHi` are `RandomSupport.seedFromHashOf(key)`: the first and the second eight
bytes, big-endian, of the MD5 hash of the key (e.g. `minecraft:blocks/short_grass`). -/
def sequence (seed hashLo hashHi : ℕ) : Xoroshiro :=
  let lo := seed ^^^ silverRatio
  let hi := (lo + goldenRatio) % two64
  ofSeeds (mixStafford13 (lo ^^^ hashLo)) (mixStafford13 (hi ^^^ hashHi))

/-- `Xoroshiro128PlusPlus.nextLong()`. -/
def nextLong (r : Xoroshiro) : ℕ × Xoroshiro :=
  let s0 := r.lo
  let s1 := r.hi
  let result := (rotl ((s0 + s1) % two64) 17 + s0) % two64
  let s1 := s1 ^^^ s0
  (result, ⟨rotl s0 49 ^^^ s1 ^^^ ((s1 <<< 21) % two64), rotl s1 28⟩)

/-- `XoroshiroRandomSource.nextInt()` as an unsigned 32-bit number: the low half of a `long`. -/
def nextBits32 (r : Xoroshiro) : ℕ × Xoroshiro :=
  let (v, r) := r.nextLong
  (v % 2 ^ 32, r)

/-- The loop of `nextInt(bound)` that redraws while the low half of the product is below
`threshold`. A draw is rejected with probability below one half, so the fuel is never used up
in practice. -/
def nextIntLoop (bound threshold : ℕ) : ℕ → ℕ → Xoroshiro → ℕ × Xoroshiro
  | 0, product, r => (product >>> 32, r)
  | fuel + 1, product, r =>
    if product % 2 ^ 32 < threshold then
      let (bits, r) := r.nextBits32
      nextIntLoop bound threshold fuel (bits * bound) r
    else (product >>> 32, r)

/-- `XoroshiroRandomSource.nextInt(bound)` for `0 < bound < 2 ^ 31`: a number below `bound`. -/
def nextInt (r : Xoroshiro) (bound : ℕ) : ℕ × Xoroshiro :=
  let (bits, r) := r.nextBits32
  let product := bits * bound
  if product % 2 ^ 32 < bound then nextIntLoop bound ((2 ^ 32 - bound) % bound) 128 product r
  else (product >>> 32, r)

/-- `XoroshiroRandomSource.nextFloat()` as the numerator of a fraction with denominator
`2 ^ 24`: the high 24 bits of a `long`. -/
def nextFloat24 (r : Xoroshiro) : ℕ × Xoroshiro :=
  let (v, r) := r.nextLong
  (v >>> 40, r)

/-- `RandomSource.nextIntBetweenInclusive(min, max)`. -/
def nextIntBetweenInclusive (r : Xoroshiro) (min max : ℕ) : ℕ × Xoroshiro :=
  let (v, r) := r.nextInt (max - min + 1)
  (v + min, r)

/-- `Mth.getSeed(x, y, z)`, as the bits of the resulting `long`. The product `x * 3129871` is
computed in 32 bits. -/
def positionSeed (p : Pos) : ℕ :=
  let xTerm : ℤ := (p.x * 3129871 + 2 ^ 31) % 2 ^ 32 - 2 ^ 31
  let seed := ofLong xTerm ^^^ ofLong (p.z * 116129781) ^^^ ofLong p.y
  let seed := (seed * seed * 42317861 + seed * 11) % two64
  -- `seed >> 16` keeps the sign.
  if seed ≥ 2 ^ 63 then (seed >>> 16) ||| (0xFFFF <<< 48) else seed >>> 16

/-- `forkPositional().at(pos)`: the generator of a position. -/
def forkAt (r : Xoroshiro) (p : Pos) : Xoroshiro :=
  let (seedLo, r) := r.nextLong
  let (seedHi, _) := r.nextLong
  ofSeeds (positionSeed p ^^^ seedLo) seedHi

end Xoroshiro

end Redstone
