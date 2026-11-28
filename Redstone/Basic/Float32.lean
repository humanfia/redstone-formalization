module

public import Mathlib.Tactic

/-!
# Single precision arithmetic, on rational numbers

Java computes with `float` in a few places that decide a redstone signal: the fullness of a
container (`AbstractContainerMenu.getRedstoneSignalFromContainer`), the page of a lectern, the
cooking progress of a furnace. Lean's own `Float32` is of no use there for a proof: the kernel
cannot evaluate it.

Every `float` operation of the game gives the `float` nearest to the exact result, ties going
to the even mantissa (IEEE 754 round to nearest even). So the model computes the exact result
as a rational number and rounds it with `roundFloat` after each operation, in the order of the
game's code. All of it is arithmetic on integers the kernel evaluates directly (`Nat.log2`,
`Nat.gcd` and the operations of `ℚ` built on them).

## What is left out

`roundFloat` is the rounding of the normal range of `float`: numbers whose size is between
`2 ^ -126` and `2 ^ 128`. It knows nothing of subnormal numbers, of overflow to infinity or of
NaN. The signals computed with it stay far inside that range.

The namespace is `Redstone.F32`, not `Redstone.Float32`: inside `namespace Redstone` the latter
would stand in front of Lean's own `Float32`, which the entities of the model compute with.
-/

@[expose] public section

namespace Redstone.F32

/-- The integer `e` with `2 ^ e ≤ q < 2 ^ (e + 1)`, for a positive rational `q`. -/
def floorLog2 (q : ℚ) : ℤ :=
  let e : ℤ := (Nat.log2 q.num.toNat : ℤ) - (Nat.log2 q.den : ℤ)
  if (2 : ℚ) ^ e ≤ q then e else e - 1

/-- The `float` nearest to a positive rational number, ties going to the even mantissa: the
number is written as `scaled * ulp` with `2 ^ 23 ≤ scaled < 2 ^ 24`, and `scaled` is rounded to
an integer. -/
def roundPos (q : ℚ) : ℚ :=
  let ulp : ℚ := (2 : ℚ) ^ (floorLog2 q - 23)
  let scaled := q / ulp
  let lower := ⌊scaled⌋
  let rest := scaled - lower
  let mantissa : ℤ :=
    if rest < 1 / 2 then lower
    else if rest > 1 / 2 then lower + 1
    else if lower % 2 = 0 then lower
    else lower + 1
  mantissa * ulp

/-- The `float` nearest to a rational number, ties going to the even mantissa, as every
arithmetic operation of the game rounds its result. Only meant for numbers in the range of
normal floats. -/
def roundFloat (q : ℚ) : ℚ :=
  if q = 0 then 0 else if q < 0 then -roundPos (-q) else roundPos q

end Redstone.F32
