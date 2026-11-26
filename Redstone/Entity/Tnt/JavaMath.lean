module

public import Mathlib.Tactic

/-!
# `Math.sin` and `Math.cos` of the Java virtual machine

The game computes the initial velocity of a primed TNT with `Math.sin` and `Math.cos`. Java only
requires these to be within one unit in the last place of the exact value, so the result is that
of the virtual machine's own routine, not of the C library. On x86-64, HotSpot uses the
routines of `StubGenerator::generate_libmSin` and `generate_libmCos` (an algorithm of Intel's
LIBM), in the interpreter as well as in compiled code. They are reproduced here operation by
operation in `double` arithmetic, so that the model does not depend on the C library, and the
values agree bit for bit with a server that runs on x86-64 HotSpot.

The argument is reduced to `x = N * pi/32 + r` with `|r| <= pi/64`, and the result is
assembled from a table of `sin` and `cos` at the multiples of `pi/32` and two polynomials in
`r`. `cos x` is the same computation with `N + 16` in place of `N`.

Only the main path of the routines is reproduced, which they take for
`2^-252 <= |x| < 90112`; this covers every argument the game passes for primed TNT, an angle in
`[0, 2 pi)`. Zero is treated apart. For other arguments the functions here are not those of
the virtual machine.
-/

@[expose] public section

namespace Redstone.Entity.Tnt.JavaMath

/-- The table `Ctable` of the routines: for each `M` from 0 to 63, with `B = M * pi/32`, the four
`double`s `cos B - sigma`, the high part of `sin B`, the low part of `sin B`, and `sigma`, the
power of two closest to `cos B`; given by their bits. -/
def ctable : Array UInt64 := #[
  0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x3ff0000000000000,
  0xbf73b92e176d6d31, 0x3fb917a6bc29b42c, 0xbc3e2718e0000000, 0x3ff0000000000000,
  0xbf93ad06011469fb, 0x3fc8f8b83c69a60b, 0xbc626d19c0000000, 0x3ff0000000000000,
  0xbfa60bea939d225a, 0x3fd294062ed59f06, 0xbc75d28da0000000, 0x3ff0000000000000,
  0xbfb37ca1866b95cf, 0x3fd87de2a6aea963, 0xbc672cede0000000, 0x3ff0000000000000,
  0xbfbe3a6873fa1279, 0x3fde2b5d3806f63b, 0x3c5e0d8920000000, 0x3ff0000000000000,
  0xbfc592675bc57974, 0x3fe1c73b39ae68c8, 0x3c8b25dd20000000, 0x3ff0000000000000,
  0xbfcd0dfe53aba2fd, 0x3fe44cf325091dd6, 0x3c68076a20000000, 0x3ff0000000000000,
  0x3fca827999fcef32, 0x3fe6a09e667f3bcd, 0xbc8bdd3420000000, 0x3fe0000000000000,
  0x3fc133cc94247758, 0x3fe8bc806b151741, 0xbc82c5e120000000, 0x3fe0000000000000,
  0x3fac73b39ae68c87, 0x3fea9b66290ea1a3, 0x3c39f630e0000000, 0x3fe0000000000000,
  0xbf9d4a2c7f909c4e, 0x3fec38b2f180bdb1, 0xbc76e0b180000000, 0x3fe0000000000000,
  0xbfbe087565455a75, 0x3fed906bcf328d46, 0x3c7457e620000000, 0x3fe0000000000000,
  0x3fa4a03176acf82d, 0x3fee9f4156c62dda, 0x3c8760b1e0000000, 0x3fd0000000000000,
  0xbfac1d1f0e5967d5, 0x3fef6297cff75cb0, 0x3c75621720000000, 0x3fd0000000000000,
  0xbf9ba1650f592f50, 0x3fefd88da3d12526, 0xbc887df640000000, 0x3fc0000000000000,
  0x0000000000000000, 0x3ff0000000000000, 0x0000000000000000, 0x0000000000000000,
  0x3f9ba1650f592f50, 0x3fefd88da3d12526, 0xbc887df640000000, 0xbfc0000000000000,
  0x3fac1d1f0e5967d5, 0x3fef6297cff75cb0, 0x3c75621720000000, 0xbfd0000000000000,
  0xbfa4a03176acf82d, 0x3fee9f4156c62dda, 0x3c8760b1e0000000, 0xbfd0000000000000,
  0x3fbe087565455a75, 0x3fed906bcf328d46, 0x3c7457e620000000, 0xbfe0000000000000,
  0x3f9d4a2c7f909c4e, 0x3fec38b2f180bdb1, 0xbc76e0b180000000, 0xbfe0000000000000,
  0xbfac73b39ae68c87, 0x3fea9b66290ea1a3, 0x3c39f630e0000000, 0xbfe0000000000000,
  0xbfc133cc94247758, 0x3fe8bc806b151741, 0xbc82c5e120000000, 0xbfe0000000000000,
  0xbfca827999fcef32, 0x3fe6a09e667f3bcd, 0xbc8bdd3420000000, 0xbfe0000000000000,
  0x3fcd0dfe53aba2fd, 0x3fe44cf325091dd6, 0x3c68076a20000000, 0xbff0000000000000,
  0x3fc592675bc57974, 0x3fe1c73b39ae68c8, 0x3c8b25dd20000000, 0xbff0000000000000,
  0x3fbe3a6873fa1279, 0x3fde2b5d3806f63b, 0x3c5e0d8920000000, 0xbff0000000000000,
  0x3fb37ca1866b95cf, 0x3fd87de2a6aea963, 0xbc672cede0000000, 0xbff0000000000000,
  0x3fa60bea939d225a, 0x3fd294062ed59f06, 0xbc75d28da0000000, 0xbff0000000000000,
  0x3f93ad06011469fb, 0x3fc8f8b83c69a60b, 0xbc626d19c0000000, 0xbff0000000000000,
  0x3f73b92e176d6d31, 0x3fb917a6bc29b42c, 0xbc3e2718e0000000, 0xbff0000000000000,
  0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0xbff0000000000000,
  0x3f73b92e176d6d31, 0xbfb917a6bc29b42c, 0x3c3e2718e0000000, 0xbff0000000000000,
  0x3f93ad06011469fb, 0xbfc8f8b83c69a60b, 0x3c626d19c0000000, 0xbff0000000000000,
  0x3fa60bea939d225a, 0xbfd294062ed59f06, 0x3c75d28da0000000, 0xbff0000000000000,
  0x3fb37ca1866b95cf, 0xbfd87de2a6aea963, 0x3c672cede0000000, 0xbff0000000000000,
  0x3fbe3a6873fa1279, 0xbfde2b5d3806f63b, 0xbc5e0d8920000000, 0xbff0000000000000,
  0x3fc592675bc57974, 0xbfe1c73b39ae68c8, 0xbc8b25dd20000000, 0xbff0000000000000,
  0x3fcd0dfe53aba2fd, 0xbfe44cf325091dd6, 0xbc68076a20000000, 0xbff0000000000000,
  0xbfca827999fcef32, 0xbfe6a09e667f3bcd, 0x3c8bdd3420000000, 0xbfe0000000000000,
  0xbfc133cc94247758, 0xbfe8bc806b151741, 0x3c82c5e120000000, 0xbfe0000000000000,
  0xbfac73b39ae68c87, 0xbfea9b66290ea1a3, 0xbc39f630e0000000, 0xbfe0000000000000,
  0x3f9d4a2c7f909c4e, 0xbfec38b2f180bdb1, 0x3c76e0b180000000, 0xbfe0000000000000,
  0x3fbe087565455a75, 0xbfed906bcf328d46, 0xbc7457e620000000, 0xbfe0000000000000,
  0xbfa4a03176acf82d, 0xbfee9f4156c62dda, 0xbc8760b1e0000000, 0xbfd0000000000000,
  0x3fac1d1f0e5967d5, 0xbfef6297cff75cb0, 0xbc75621720000000, 0xbfd0000000000000,
  0x3f9ba1650f592f50, 0xbfefd88da3d12526, 0x3c887df640000000, 0xbfc0000000000000,
  0x0000000000000000, 0xbff0000000000000, 0x0000000000000000, 0x0000000000000000,
  0xbf9ba1650f592f50, 0xbfefd88da3d12526, 0x3c887df640000000, 0x3fc0000000000000,
  0xbfac1d1f0e5967d5, 0xbfef6297cff75cb0, 0xbc75621720000000, 0x3fd0000000000000,
  0x3fa4a03176acf82d, 0xbfee9f4156c62dda, 0xbc8760b1e0000000, 0x3fd0000000000000,
  0xbfbe087565455a75, 0xbfed906bcf328d46, 0xbc7457e620000000, 0x3fe0000000000000,
  0xbf9d4a2c7f909c4e, 0xbfec38b2f180bdb1, 0x3c76e0b180000000, 0x3fe0000000000000,
  0x3fac73b39ae68c87, 0xbfea9b66290ea1a3, 0xbc39f630e0000000, 0x3fe0000000000000,
  0x3fc133cc94247758, 0xbfe8bc806b151741, 0x3c82c5e120000000, 0x3fe0000000000000,
  0x3fca827999fcef32, 0xbfe6a09e667f3bcd, 0x3c8bdd3420000000, 0x3fe0000000000000,
  0xbfcd0dfe53aba2fd, 0xbfe44cf325091dd6, 0xbc68076a20000000, 0x3ff0000000000000,
  0xbfc592675bc57974, 0xbfe1c73b39ae68c8, 0xbc8b25dd20000000, 0x3ff0000000000000,
  0xbfbe3a6873fa1279, 0xbfde2b5d3806f63b, 0xbc5e0d8920000000, 0x3ff0000000000000,
  0xbfb37ca1866b95cf, 0xbfd87de2a6aea963, 0x3c672cede0000000, 0x3ff0000000000000,
  0xbfa60bea939d225a, 0xbfd294062ed59f06, 0x3c75d28da0000000, 0x3ff0000000000000,
  0xbf93ad06011469fb, 0xbfc8f8b83c69a60b, 0x3c626d19c0000000, 0x3ff0000000000000,
  0xbf73b92e176d6d31, 0xbfb917a6bc29b42c, 0x3c3e2718e0000000, 0x3ff0000000000000]

/-- An entry of `ctable` as a `double`. -/
def entry (m : ℕ) (i : ℕ) : Float := Float.ofBits (ctable.getD (4 * m + i) 0)

/-- `32 / pi`. -/
def pi32Inv : Float := Float.ofBits 0x40245f306dc9c883

/-- `pi / 32` in three parts, of which the first two have few bits. -/
def p1 : Float := Float.ofBits 0x3fb921fb54400000

@[inherit_doc p1]
def p2 : Float := Float.ofBits 0x3d90b4611a600000

@[inherit_doc p1]
def p3 : Float := Float.ofBits 0x3b63198a2e037073

/-- The main path of `generate_libmSin`, with the table read at `N + shift`: `sin x` for
`shift = 0` and `cos x` for `shift = 16`. The two lanes of the packed operations of the
routine are written as pairs `lo`, `hi`; `lo` belongs to the polynomial of `sin r - r` and
`hi` to that of `cos r - 1`. -/
def sinCos (x : Float) (shift : ℤ) : Float :=
  -- range reduction
  let y := pi32Inv * x + (if x.toBits >>> 63 == 1 then -0.5 else 0.5)
  let n : Float := if y < 0.0 then y.ceil else y.floor
  let m := ((n.toInt64.toInt + shift) % 64).toNat
  let cHl := entry m 0
  let sHi := entry m 1
  let sLo := entry m 2
  let sigma := entry m 3
  let r1 := x - p1 * n
  let m2 := p2 * n
  let r := r1 - m2
  let c2 := (r1 - r) - m2
  let negC := n * p3 - c2
  -- polynomials
  let r2 := r * r
  let r4 := r2 * r2
  let msc4Lo := Float.ofBits 0x3ec71de3a556c734 * r1 * r
  let msc4Hi := Float.ofBits 0x3efa01a01a01a01a * r1 * r
  let psc3Lo := msc4Lo + Float.ofBits 0xbf2a01a01a01a01a
  let psc3Hi := msc4Hi + Float.ofBits 0xbf56c16c16c16c17
  let psc1Lo := Float.ofBits 0x3f81111111111111 * r2 + Float.ofBits 0xbfc5555555555555
  let psc1Hi := Float.ofBits 0x3fa5555555555555 * r2 + Float.ofBits 0xbfe0000000000000
  let polsLo := (psc1Lo + psc3Lo * r4) * ((cHl + sigma) * r * r2)
  let polsHi := (psc1Hi + psc3Hi * r4) * (sHi * r2)
  -- correction term
  let negD := sHi * r - (cHl + sigma)
  let corr := negC * negD + sLo
  -- compensated summations
  let rs := sigma * r
  let resInt := rs + sHi
  let med := r * cHl
  let resHi := med + resInt
  let k2 := (sHi - resInt) + rs
  let k3 := (resInt - resHi) + med
  resHi + ((((corr + k2) + k3) + polsLo) + polsHi)

/-- `Math.sin(x)` on x86-64 HotSpot, for `x = 0` or `2^-252 <= |x| < 90112`. -/
def sin (x : Float) : Float := if x == 0.0 then x else sinCos x 0

/-- `Math.cos(x)` on x86-64 HotSpot, for `x = 0` or `2^-252 <= |x| < 90112`. -/
def cos (x : Float) : Float := if x == 0.0 then 1.0 else sinCos x 16

end Redstone.Entity.Tnt.JavaMath
