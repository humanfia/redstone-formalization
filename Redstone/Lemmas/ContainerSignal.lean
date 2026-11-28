import Redstone.Component.Container
import Redstone.Proof.Axioms

/-!
# The signal of a container, in closed form

`Container.redstoneSignal` follows the game: it adds up `count / maxStackSize` over the slots,
divides by the number of slots and scales to 1..15, rounding to a `float` after every
operation. This file proves that for the containers redstone is built with, the rounding
changes nothing:

* `Container.redstoneSignal_eq`: if the greatest size of every stack in the container divides
  one power of two `2 ^ j` (64 for ordinary items, 16 for ender pearls and the like, 1 for
  tools: all of them divide 64), no slot holds more than its greatest size, and
  `2 ^ j * slots ≤ 262144`, then

  `redstoneSignal = 14 * fill / (2 ^ j * slots) + (if fill > 0 then 1 else 0)`

  where `fill` counts every item with the weight `2 ^ j / maxStackSize` (`Container.fill`), and
  `/` rounds down.

The proof has three parts.

* Rounding a positive number to a `float` changes it by at most one part in `2 ^ 24`
  (`F32.roundFloat_bounds`).
* A number `a / 2 ^ j` with `a < 2 ^ 24` is a `float`, so rounding leaves it as it is
  (`F32.roundFloat_natCast_div_two_pow`). With stack sizes that divide `2 ^ j`, the sum over
  the slots is such a number at every step, so the sum is exact (`Container.foldl_addSlot`).
* What is left is two roundings: of `fill / capacity`, and of the product with 14. They move
  the result by less than `1 / capacity`, which is the least distance from `14 * fill /
  capacity` to the next whole number above; and when `14 * fill / capacity` is a whole number
  `k`, the two roundings of `k / 14` give `k` back, which is checked for the fourteen values of
  `k` by evaluation (`F32.fourteenths`). This is `F32.lerpDiscrete_div`.

## What is not proved

Nothing is claimed for a stack whose greatest size is not a power of two (a `max_stack_size`
component of 99, say): there the sum over the slots is rounded for real, and the signal has
to be computed (`decide +kernel` evaluates `redstoneSignal` on any concrete container).
-/

set_option Elab.async false

namespace Redstone.F32

theorem roundFloat_of_pos {q : ℚ} (h : 0 < q) : roundFloat q = roundPos q := by
  unfold roundFloat
  rw [ite_eq_right h.ne', ite_eq_right (not_lt.mpr h.le)]

theorem roundFloat_zero : roundFloat 0 = 0 := by
  unfold roundFloat
  rw [ite_eq_left rfl]

theorem floorLog2_def (q : ℚ) :
    floorLog2 q =
      if (2 : ℚ) ^ ((Nat.log2 q.num.toNat : ℤ) - (Nat.log2 q.den : ℤ)) ≤ q then
        (Nat.log2 q.num.toNat : ℤ) - (Nat.log2 q.den : ℤ)
      else (Nat.log2 q.num.toNat : ℤ) - (Nat.log2 q.den : ℤ) - 1 :=
  rfl

/-- The quotient of two natural numbers is at least two to the difference of their logarithms,
less one. -/
theorem two_zpow_log2_sub_le (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (2 : ℚ) ^ ((Nat.log2 a : ℤ) - (Nat.log2 b : ℤ) - 1) ≤ (a : ℚ) / b := by
  have h1 : ((2 ^ Nat.log2 a : ℕ) : ℚ) ≤ a := by exact_mod_cast Nat.log2_self_le ha
  have h2 : (b : ℚ) < ((2 ^ (Nat.log2 b + 1) : ℕ) : ℚ) := by exact_mod_cast Nat.lt_log2_self
  have hb' : (0 : ℚ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
  push_cast at h1 h2
  have e : (2 : ℚ) ^ ((Nat.log2 a : ℤ) - (Nat.log2 b : ℤ) - 1) =
      (2 : ℚ) ^ Nat.log2 a / (2 : ℚ) ^ (Nat.log2 b + 1) := by
    have : (Nat.log2 a : ℤ) - (Nat.log2 b : ℤ) - 1 =
        (Nat.log2 a : ℤ) - ((Nat.log2 b + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_sub₀ (two_ne_zero), zpow_natCast, zpow_natCast]
  have hp : (0 : ℚ) < (2 : ℚ) ^ (Nat.log2 b + 1) := by positivity
  rw [e, le_div_iff₀ hb', div_mul_eq_mul_div, div_le_iff₀ hp]
  calc (2 : ℚ) ^ Nat.log2 a * b ≤ a * b := mul_le_mul_of_nonneg_right h1 hb'.le
    _ ≤ a * (2 : ℚ) ^ (Nat.log2 b + 1) := mul_le_mul_of_nonneg_left h2.le (Nat.cast_nonneg a)

/-- `floorLog2` is not above the logarithm: `2 ^ floorLog2 q ≤ q`. -/
theorem two_zpow_floorLog2_le {q : ℚ} (h : 0 < q) : (2 : ℚ) ^ floorLog2 q ≤ q := by
  rw [floorLog2_def]
  split_ifs with h1
  · exact h1
  · have hnum : 0 < q.num := Rat.num_pos.mpr h
    have hc : (q.num.toNat : ℚ) = (q.num : ℚ) := by
      exact_mod_cast congrArg (Int.cast : ℤ → ℚ) (Int.toNat_of_nonneg hnum.le)
    have ha : q.num.toNat ≠ 0 := by omega
    calc (2 : ℚ) ^ ((Nat.log2 q.num.toNat : ℤ) - (Nat.log2 q.den : ℤ) - 1)
        ≤ (q.num.toNat : ℚ) / q.den := two_zpow_log2_sub_le _ _ ha q.den_nz
      _ = q := by rw [hc, Rat.num_div_den]

/-- The mantissa `roundPos` chooses for a number scaled to `2 ^ 23 ≤ x < 2 ^ 24`: the nearest
integer, the even one of two that are equally near. -/
def mantissa (x : ℚ) : ℤ :=
  if x - ⌊x⌋ < 1 / 2 then ⌊x⌋
  else if x - ⌊x⌋ > 1 / 2 then ⌊x⌋ + 1
  else if ⌊x⌋ % 2 = 0 then ⌊x⌋
  else ⌊x⌋ + 1

theorem roundPos_eq (q : ℚ) :
    roundPos q =
      (mantissa (q / (2 : ℚ) ^ (floorLog2 q - 23)) : ℚ) * (2 : ℚ) ^ (floorLog2 q - 23) :=
  rfl

theorem abs_mantissa_sub (x : ℚ) : |(mantissa x : ℚ) - x| ≤ 1 / 2 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  unfold mantissa
  split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

theorem mantissa_intCast (n : ℤ) : mantissa (n : ℚ) = n := by
  unfold mantissa
  rw [Int.floor_intCast, sub_self, ite_eq_left (by norm_num)]

theorem round_bounds_aux (q u m : ℚ) (hu : 0 < u) (hle : u * 8388608 ≤ q)
    (hm : |m - q / u| ≤ 1 / 2) :
    q * (1 - 1 / 16777216) ≤ m * u ∧ m * u ≤ q * (1 + 1 / 16777216) := by
  rw [abs_le] at hm
  have hq : q / u * u = q := div_mul_cancel₀ q hu.ne'
  have h1 : m * u - q = (m - q / u) * u := by rw [sub_mul, hq]
  have h2 : (m - q / u) * u ≤ 1 / 2 * u := mul_le_mul_of_nonneg_right hm.2 hu.le
  have h3 : -(1 / 2) * u ≤ (m - q / u) * u := mul_le_mul_of_nonneg_right hm.1 hu.le
  constructor <;> linarith

/-- Rounding a positive number to a `float` changes it by at most one part in `2 ^ 24`. -/
theorem roundFloat_bounds {q : ℚ} (h : 0 < q) :
    q * (1 - 1 / 16777216) ≤ roundFloat q ∧ roundFloat q ≤ q * (1 + 1 / 16777216) := by
  rw [roundFloat_of_pos h, roundPos_eq]
  have hu : (0 : ℚ) < (2 : ℚ) ^ (floorLog2 q - 23) := by positivity
  have hle : (2 : ℚ) ^ (floorLog2 q - 23) * 8388608 ≤ q := by
    have e : (2 : ℚ) ^ (floorLog2 q - 23) * 8388608 = (2 : ℚ) ^ floorLog2 q := by
      have h23 : (8388608 : ℚ) = (2 : ℚ) ^ ((23 : ℕ) : ℤ) := by rw [zpow_natCast]; norm_num
      rw [h23, ← zpow_add₀ (two_ne_zero)]
      congr 1
      push_cast
      ring
    rw [e]
    exact two_zpow_floorLog2_le h
  exact round_bounds_aux q _ _ hu hle (abs_mantissa_sub _)

/-- A number `a / 2 ^ j` with `a < 2 ^ 24` is a `float`: rounding leaves it as it is. -/
theorem roundFloat_natCast_div_two_pow (a j : ℕ) (ha : a < 16777216) :
    roundFloat ((a : ℚ) / (2 : ℚ) ^ j) = (a : ℚ) / (2 : ℚ) ^ j := by
  rcases Nat.eq_zero_or_pos a with rfl | hpos
  · rw [Nat.cast_zero, zero_div, roundFloat_zero]
  have ha' : (0 : ℚ) < a := by exact_mod_cast hpos
  have hj : (0 : ℚ) < (2 : ℚ) ^ j := by positivity
  obtain ⟨q, hqd⟩ : ∃ q : ℚ, q = (a : ℚ) / (2 : ℚ) ^ j := ⟨_, rfl⟩
  rw [← hqd]
  have hq : 0 < q := by rw [hqd]; exact div_pos ha' hj
  have he := two_zpow_floorLog2_le hq
  have h1 : (2 : ℚ) ^ (floorLog2 q + (j : ℤ)) < (2 : ℚ) ^ ((24 : ℕ) : ℤ) := by
    rw [zpow_add₀ (two_ne_zero), zpow_natCast, zpow_natCast]
    have h2 : (2 : ℚ) ^ floorLog2 q * (2 : ℚ) ^ j ≤ a := by
      have h := mul_le_mul_of_nonneg_right he hj.le
      have hqj : q * (2 : ℚ) ^ j = a := by rw [hqd, div_mul_cancel₀ _ hj.ne']
      rwa [hqj] at h
    have h3 : (a : ℚ) < (2 : ℚ) ^ 24 := by
      have : (a : ℚ) < ((16777216 : ℕ) : ℚ) := by exact_mod_cast ha
      calc (a : ℚ) < ((16777216 : ℕ) : ℚ) := this
        _ = (2 : ℚ) ^ 24 := by norm_num
    exact lt_of_le_of_lt h2 h3
  have h4 : floorLog2 q + (j : ℤ) < ((24 : ℕ) : ℤ) :=
    (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mp h1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (23 : ℤ) - floorLog2 q - j = k :=
    ⟨(23 - floorLog2 q - j).toNat, by push_cast at h4; omega⟩
  have hint : q / (2 : ℚ) ^ (floorLog2 q - 23) = (((a * 2 ^ k : ℕ) : ℤ) : ℚ) := by
    have hexp : floorLog2 q - 23 = -((k : ℤ) + (j : ℤ)) := by omega
    rw [hexp, zpow_neg, div_inv_eq_mul, zpow_add₀ (two_ne_zero), zpow_natCast, zpow_natCast, hqd,
      div_mul_eq_mul_div, div_eq_iff hj.ne']
    push_cast
    ring
  rw [roundFloat_of_pos hq, roundPos_eq, hint, mantissa_intCast, ← hint,
    div_mul_cancel₀ _ (by positivity)]

/-- Dividing `k` by 14 and multiplying by 14 again, in single precision, does not fall below
`k`. Checked by evaluation for each `k`. -/
theorem fourteenths :
    ∀ k ∈ List.range 15, ((k : ℕ) : ℚ) ≤ roundFloat (roundFloat ((k : ℚ) / 14) * 14) := by
  decide +kernel

assert_standard_axioms fourteenths

/-- `Mth.lerpDiscrete(s / d, 0, 15)` computed in single precision, for natural numbers
`s ≤ d ≤ 262144`: it is `14 * s / d`, rounded down, plus one unless `s` is zero. -/
theorem lerpDiscrete_div (s d : ℕ) (hd : 0 < d) (hd2 : d ≤ 262144) (hs : s ≤ d) :
    ⌊roundFloat (roundFloat ((s : ℚ) / d) * 14)⌋.toNat +
        (if roundFloat ((s : ℚ) / d) > 0 then 1 else 0) =
      14 * s / d + (if s > 0 then 1 else 0) := by
  rcases Nat.eq_zero_or_pos s with rfl | hspos
  · simp [roundFloat_zero]
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have hs' : (0 : ℚ) < s := by exact_mod_cast hspos
  have hq : (0 : ℚ) < (s : ℚ) / d := div_pos hs' hd'
  have hq1 : (s : ℚ) / d ≤ 1 := (div_le_one hd').mpr (by exact_mod_cast hs)
  obtain ⟨hb1, hb2⟩ := roundFloat_bounds hq
  obtain ⟨t, ht⟩ : ∃ t : ℚ, t = roundFloat ((s : ℚ) / d) := ⟨_, rfl⟩
  rw [← ht] at hb1 hb2 ⊢
  have ht0 : 0 < t := lt_of_lt_of_le (mul_pos hq (by norm_num)) hb1
  have ht14 : 0 < t * 14 := mul_pos ht0 (by norm_num)
  obtain ⟨hc1, hc2⟩ := roundFloat_bounds ht14
  rw [ite_eq_left ht0, ite_eq_left hspos]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = 14 * s / d := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = 14 * s % d := ⟨_, rfl⟩
  rw [← hk]
  have hdm : d * k + r = 14 * s := by rw [hk, hr]; exact Nat.div_add_mod _ _
  have hrlt : r + 1 ≤ d := by rw [hr]; exact Nat.mod_lt _ hd
  have hk14 : k ≤ 14 := by
    rw [hk]
    exact Nat.div_le_of_le_mul (by omega)
  have hdmQ : (d : ℚ) * k + r = 14 * s := by exact_mod_cast hdm
  have hrQ : (r : ℚ) + 1 ≤ d := by exact_mod_cast hrlt
  have hdQ : (d : ℚ) ≤ 262144 := by exact_mod_cast hd2
  -- `14 * s / d = k + r / d`, with `r / d ≤ 1 - 1 / d` and `1 / d ≥ 1 / 262144`.
  have hx : 14 * ((s : ℚ) / d) = k + r / d := by
    rw [← mul_div_assoc, ← hdmQ, add_div, mul_div_cancel_left₀ _ hd'.ne']
  have hp : (r : ℚ) / d + 1 / d ≤ 1 := by
    rw [← add_div]
    exact (div_le_one hd').mpr hrQ
  have hi : (1 : ℚ) / 262144 ≤ 1 / d := one_div_le_one_div_of_le hd' hdQ
  suffices h : (k : ℚ) ≤ roundFloat (t * 14) ∧ roundFloat (t * 14) < k + 1 by
    have hfloor : ⌊roundFloat (t * 14)⌋ = (k : ℤ) := Int.floor_eq_iff.mpr (by exact_mod_cast h)
    rw [hfloor, Int.toNat_natCast]
  constructor
  · rcases Nat.eq_zero_or_pos r with rfl | hrpos
    · -- `14 * s / d` is the whole number `k`: the fourteen cases checked by evaluation.
      have hqk : (s : ℚ) / d = (k : ℚ) / 14 := by
        rw [div_eq_div_iff hd'.ne' (by norm_num)]
        rw [Nat.cast_zero, add_zero] at hdmQ
        linarith
      rw [ht, hqk]
      exact fourteenths k (List.mem_range.mpr (by omega))
    · have hr1 : (1 : ℚ) / d ≤ r / d := by
        have : (1 : ℚ) ≤ r := by exact_mod_cast hrpos
        exact div_le_div_of_nonneg_right this hd'.le
      linarith
  · linarith

end Redstone.F32

namespace Redstone.Component.Container

open Redstone.F32

/-- What a slot adds to the sum, in units of `1 / M`: its count times `M / maxStackSize`. -/
def weight (M limit : ℕ) (s : ItemStack) : ℕ :=
  if s.isEmpty then 0 else s.count * (M / s.containerMaxStackSize limit)

/-- How full a container is, in units of `1 / M` of a slot: the sum of the weights of its
slots. With `M = 64` a full slot counts 64, whatever the item. -/
def fill (M limit : ℕ) (items : Inventory) : ℕ := (items.map (weight M limit)).sum

theorem redstoneSignal_def (items : Inventory) (limit : ℕ) :
    redstoneSignal items limit =
      ⌊F32.roundFloat
          (F32.roundFloat (items.foldl (addSlot limit) 0 / (items.length : ℚ)) * 14)⌋.toNat +
        (if F32.roundFloat (items.foldl (addSlot limit) 0 / (items.length : ℚ)) > 0 then 1
        else 0) :=
  rfl

theorem addSlot_def (limit : ℕ) (acc : ℚ) (s : ItemStack) :
    addSlot limit acc s =
      if s.isEmpty then acc
      else
        F32.roundFloat
          (acc + F32.roundFloat ((s.count : ℚ) / (s.containerMaxStackSize limit : ℚ))) :=
  rfl

/-- A slot whose greatest stack size is `M` weighs its count. -/
theorem weight_of_max_eq {M limit : ℕ} {s : ItemStack} (hM : 0 < M)
    (h : s.containerMaxStackSize limit = M) :
    weight M limit s = if s.isEmpty then 0 else s.count := by
  unfold weight
  rw [h, Nat.div_self hM, Nat.mul_one]

/-- While the greatest size of every stack divides `2 ^ j`, the sum over the slots is exact:
no rounding happens. -/
theorem foldl_addSlot (j limit : ℕ) :
    ∀ (items : Inventory) (a : ℕ),
      (∀ s ∈ items, s.isEmpty = false → s.containerMaxStackSize limit ∣ 2 ^ j) →
      a + fill (2 ^ j) limit items < 16777216 →
      items.foldl (addSlot limit) ((a : ℚ) / (2 : ℚ) ^ j) =
        ((a + fill (2 ^ j) limit items : ℕ) : ℚ) / (2 : ℚ) ^ j
  | [], a, _, _ => by
    rw [List.foldl_nil]
    rfl
  | s :: rest, a, hmax, hlt => by
    have hfill : fill (2 ^ j) limit (s :: rest) =
        weight (2 ^ j) limit s + fill (2 ^ j) limit rest := by
      unfold fill
      rw [List.map_cons, List.sum_cons]
    rw [hfill] at hlt ⊢
    have ih := foldl_addSlot j limit rest (a + weight (2 ^ j) limit s)
      (fun s' h => hmax s' (List.mem_cons_of_mem _ h)) (by omega)
    rw [List.foldl_cons, addSlot_def]
    cases hs : s.isEmpty with
    | true =>
      have hw : weight (2 ^ j) limit s = 0 := by
        unfold weight
        rw [hs, ite_eq_left rfl]
      rw [hw, Nat.add_zero] at ih
      rw [ite_eq_left rfl, hw, Nat.zero_add]
      exact ih
    | false =>
      obtain ⟨d, hd⟩ := hmax s List.mem_cons_self hs
      have hm0 : s.containerMaxStackSize limit ≠ 0 := by
        intro h
        rw [h, Nat.zero_mul] at hd
        exact (Nat.two_pow_pos j).ne' hd
      have hw : weight (2 ^ j) limit s = s.count * d := by
        unfold weight
        rw [hs, ite_eq_right (by decide), hd, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm0)]
      have hmQ : (s.containerMaxStackSize limit : ℚ) ≠ 0 := by exact_mod_cast hm0
      have hslot : (s.count : ℚ) / (s.containerMaxStackSize limit : ℚ) =
          ((weight (2 ^ j) limit s : ℕ) : ℚ) / (2 : ℚ) ^ j := by
        have hpow : (2 : ℚ) ^ j = (s.containerMaxStackSize limit : ℚ) * d := by
          exact_mod_cast hd
        have hdQ : (d : ℚ) ≠ 0 := by
          intro h
          rw [h, mul_zero] at hpow
          exact (by positivity : (2 : ℚ) ^ j ≠ 0) hpow
        rw [hw, hpow, Nat.cast_mul, mul_div_mul_right _ _ hdQ]
      rw [ite_eq_right (by decide), hslot, roundFloat_natCast_div_two_pow _ _ (by omega), ← add_div,
        ← Nat.cast_add, roundFloat_natCast_div_two_pow _ _ (by omega), ih, Nat.add_assoc]

/-- **The signal of a container in closed form.** If the greatest size of every stack divides
`2 ^ j`, the container holds no more than it can (`fill ≤ 2 ^ j * slots`) and
`2 ^ j * slots ≤ 262144`, then the signal a comparator reads is `14 * fill / (2 ^ j * slots)`,
rounded down, plus one if the container is not empty. Every container of the game with ordinary
items is such a container, with `j = 6`. -/
theorem redstoneSignal_eq (items : Inventory) (limit j : ℕ)
    (hmax : ∀ s ∈ items, s.isEmpty = false → s.containerMaxStackSize limit ∣ 2 ^ j)
    (hfill : fill (2 ^ j) limit items ≤ 2 ^ j * items.length)
    (hsize : 2 ^ j * items.length ≤ 262144) :
    redstoneSignal items limit =
      14 * fill (2 ^ j) limit items / (2 ^ j * items.length) +
        (if fill (2 ^ j) limit items > 0 then 1 else 0) := by
  rw [redstoneSignal_def]
  rcases Nat.eq_zero_or_pos items.length with h0 | hn
  · have hnil : items = [] := List.length_eq_zero_iff.mp h0
    subst hnil
    simp [fill, roundFloat_zero]
  · have hlt : 0 + fill (2 ^ j) limit items < 16777216 := by
      rw [Nat.zero_add]
      exact lt_of_le_of_lt (hfill.trans hsize) (by norm_num)
    have hfold := foldl_addSlot j limit items 0 hmax hlt
    rw [Nat.cast_zero, zero_div, Nat.zero_add] at hfold
    have hdiv : ((fill (2 ^ j) limit items : ℕ) : ℚ) / (2 : ℚ) ^ j / (items.length : ℚ) =
        ((fill (2 ^ j) limit items : ℕ) : ℚ) / ((2 ^ j * items.length : ℕ) : ℚ) := by
      rw [div_div]
      push_cast
      rfl
    rw [hfold, hdiv]
    exact lerpDiscrete_div _ _ (Nat.mul_pos (Nat.two_pow_pos j) hn) hsize hfill

assert_standard_axioms redstoneSignal_eq

/-- A hopper holding three full stacks of redstone and four ender pearls, which stack to
16: three and a quarter slots of five, signal `⌊14 * 13 / 20⌋ + 1 = 10`. The closed form and
the definition agree on it. -/
theorem redstoneSignal_example :
    redstoneSignal
        [.of "minecraft:redstone" 64, .of "minecraft:redstone" 64, .of "minecraft:redstone" 64,
          .of "minecraft:ender_pearl" 4, .empty] = 10 := by
  decide +kernel

assert_standard_axioms redstoneSignal_example

end Redstone.Component.Container
