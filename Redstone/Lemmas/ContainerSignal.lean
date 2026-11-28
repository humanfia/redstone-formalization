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

## The signal from the number of items

When every stack of the container has the same greatest size `m` (64, 16 or 1), the fill is
the number of items `T` (`itemTotal`) and the signal is a function of `T` alone:

* `Container.redstoneSignal_of_stackSize`, and `redstoneSignal_of_64`, `_of_16`, `_of_1`:
  `redstoneSignal items = signalOf slots m T = 14 * T / (m * slots) + (if T > 0 then 1 else 0)`;
* `Container.le_signalOf_iff`: the signal is `s` or more exactly when
  `T ≥ threshold slots m s`, where the threshold is 1 for `s = 1` and
  `(s - 1) * m * slots / 14`, rounded up, above; `signalOf_eq_iff` is the same for "exactly
  `s`";
* the tables of thresholds for `s = 0, ..., 15`: `hopper_thresholds` (5 slots: 1, 23, 46, 69,
  ...), `chest_thresholds` (27), `doubleChest_thresholds` (54), `dropper_thresholds` (9),
  `furnace_thresholds` (3), and the same for items that stack to 16 and for items that do not
  stack;
* `hopper_signal_one_two_three`: the numbers an item sorter is built on.

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

/-! ### Containers with one kind of stack: the signal from the number of items -/

/-- The number of items in an inventory: the counts of the slots that are not empty. -/
def itemTotal (items : Inventory) : ℕ := (items.map fun s => if s.isEmpty then 0 else s.count).sum

/-- The signal of a container of `slots` slots that holds `T` items, all of which stack to `m`:
`14 * T / (m * slots)`, rounded down, plus one unless the container is empty. -/
def signalOf (slots m T : ℕ) : ℕ := 14 * T / (m * slots) + (if T > 0 then 1 else 0)

/-- The least number of items, all stacking to `m`, with which a container of `slots` slots
gives the signal `s` or more: one item for the signal 1, and `(s - 1) * m * slots / 14`,
rounded up, for a signal `s` above 1. -/
def threshold (slots m s : ℕ) : ℕ := if s ≤ 1 then s else ((s - 1) * (m * slots) + 13) / 14

/-- An unpatched stack that is not empty has the greatest size of its item. -/
theorem maxStackSize_of_plain (s : ItemStack) (he : s.isEmpty = false) (hc : s.components = []) :
    s.maxStackSize = itemMaxStackSize s.id := by
  simp [ItemStack.maxStackSize, ItemStack.patched?, ItemStack.removes, he, hc]

/-- In a container with the usual limit of 99, an unpatched stack that is not empty has the
greatest size of its item (which is never above 99). -/
theorem containerMaxStackSize_of_plain (s : ItemStack) (he : s.isEmpty = false)
    (hc : s.components = []) : s.containerMaxStackSize = min 99 (itemMaxStackSize s.id) := by
  unfold ItemStack.containerMaxStackSize
  rw [maxStackSize_of_plain s he hc]

/-- If every stack has the greatest size `M`, the fill in units of `1 / M` of a slot is the
number of items. -/
theorem fill_of_stackSize {M limit : ℕ} (hM : 0 < M) (items : Inventory)
    (h : ∀ s ∈ items, s.isEmpty = false → s.containerMaxStackSize limit = M) :
    fill M limit items = itemTotal items := by
  unfold fill itemTotal
  congr 1
  apply List.map_congr_left
  intro s hs
  change weight M limit s = if s.isEmpty then 0 else s.count
  unfold weight
  cases he : s.isEmpty with
  | true => rfl
  | false =>
    rw [h s hs he, Nat.div_self hM, Nat.mul_one]

/-- A container whose stacks hold at most `M` items holds at most `M` items per slot. -/
theorem itemTotal_le {M : ℕ} (items : Inventory)
    (h : ∀ s ∈ items, s.isEmpty = false → s.count ≤ M) : itemTotal items ≤ M * items.length := by
  induction items with
  | nil => exact Nat.zero_le _
  | cons s rest ih =>
    have h1 := ih fun s' hs' => h s' (List.mem_cons_of_mem _ hs')
    have h2 : (if s.isEmpty then 0 else s.count) ≤ M := by
      cases he : s.isEmpty with
      | true => exact Nat.zero_le _
      | false => exact h s List.mem_cons_self he
    change (if s.isEmpty then 0 else s.count) + itemTotal rest ≤ M * (rest.length + 1)
    rw [Nat.mul_succ, Nat.add_comm (M * rest.length)]
    exact Nat.add_le_add h2 h1

/-- **The signal of a container whose stacks all have the same greatest size**, a power of two
`m = 2 ^ j`: it depends on the number of items only, and is `signalOf slots m total`. -/
theorem redstoneSignal_of_stackSize (items : Inventory) (limit j m : ℕ) (hm : m = 2 ^ j)
    (hmax : ∀ s ∈ items, s.isEmpty = false → s.containerMaxStackSize limit = m)
    (hcount : ∀ s ∈ items, s.isEmpty = false → s.count ≤ m)
    (hsize : m * items.length ≤ 262144) :
    redstoneSignal items limit = signalOf items.length m (itemTotal items) := by
  subst hm
  have hfill := fill_of_stackSize (Nat.two_pow_pos j) items hmax
  have h := redstoneSignal_eq items limit j
    (fun s hs he => Dvd.intro 1 (by rw [hmax s hs he, Nat.mul_one]))
    (by rw [hfill]; exact itemTotal_le items hcount) hsize
  rw [h, hfill]
  rfl

assert_standard_axioms redstoneSignal_of_stackSize

/-- A container of ordinary items (which stack to 64), with the usual limit of 99 per slot:
`14 * total / (64 * slots)`, rounded down, plus one unless it is empty. -/
theorem redstoneSignal_of_64 (items : Inventory)
    (hmax : ∀ s ∈ items, s.isEmpty = false → s.containerMaxStackSize = 64)
    (hcount : ∀ s ∈ items, s.isEmpty = false → s.count ≤ 64) (hsize : items.length ≤ 4096) :
    redstoneSignal items = signalOf items.length 64 (itemTotal items) :=
  redstoneSignal_of_stackSize items 99 6 64 (by norm_num) hmax hcount (by omega)

/-- A container of items that stack to 16 (ender pearls, snowballs, eggs, signs, ...). -/
theorem redstoneSignal_of_16 (items : Inventory)
    (hmax : ∀ s ∈ items, s.isEmpty = false → s.containerMaxStackSize = 16)
    (hcount : ∀ s ∈ items, s.isEmpty = false → s.count ≤ 16) (hsize : items.length ≤ 16384) :
    redstoneSignal items = signalOf items.length 16 (itemTotal items) :=
  redstoneSignal_of_stackSize items 99 4 16 (by norm_num) hmax hcount (by omega)

/-- A container of items that do not stack (tools, potions, minecarts, ...). -/
theorem redstoneSignal_of_1 (items : Inventory)
    (hmax : ∀ s ∈ items, s.isEmpty = false → s.containerMaxStackSize = 1)
    (hcount : ∀ s ∈ items, s.isEmpty = false → s.count ≤ 1) (hsize : items.length ≤ 262144) :
    redstoneSignal items = signalOf items.length 1 (itemTotal items) :=
  redstoneSignal_of_stackSize items 99 0 1 (by norm_num) hmax hcount (by omega)

/-- What a comparator reads from the block entity at `p` is the signal of its slots. -/
theorem redstoneSignalAt_eq {l : Level} {p : Pos} {be : BlockEntity} {items : Inventory}
    (hbe : l.blockEntities p = some be) (hitems : items? be = some items) :
    redstoneSignalAt l p = redstoneSignal items := by
  simp [redstoneSignalAt, hbe, hitems]

/-! ### Thresholds: how many items give which signal -/

/-- **The signal is `s` or more exactly from `threshold slots m s` items on.** -/
theorem le_signalOf_iff {slots m : ℕ} (hd : 0 < m * slots) (s T : ℕ) :
    s ≤ signalOf slots m T ↔ threshold slots m s ≤ T := by
  unfold signalOf threshold
  have key : s - 1 ≤ 14 * T / (m * slots) ↔ (s - 1) * (m * slots) ≤ 14 * T :=
    Nat.le_div_iff_mul_le hd
  have hp : s ≤ 1 ∨ 0 < (s - 1) * (m * slots) := by
    by_cases h : s ≤ 1
    · exact Or.inl h
    · exact Or.inr (Nat.mul_pos (by omega) hd)
  have hq0 : T = 0 → 14 * T / (m * slots) = 0 := by
    intro h
    rw [h, Nat.mul_zero, Nat.zero_div]
  generalize 14 * T / (m * slots) = q at key hq0 ⊢
  generalize (s - 1) * (m * slots) = X at key hp ⊢
  by_cases hT : T > 0
  · rw [ite_eq_left hT]
    by_cases hs : s ≤ 1
    · rw [ite_eq_left hs]
      constructor <;> intro _ <;> omega
    · rw [ite_eq_right hs]
      constructor
      · intro h
        have h2 := key.mp (by omega)
        omega
      · intro h
        have h2 := key.mpr (by omega)
        omega
  · rw [ite_eq_right hT]
    have hq := hq0 (by omega)
    by_cases hs : s ≤ 1
    · rw [ite_eq_left hs]
      constructor <;> intro _ <;> omega
    · rw [ite_eq_right hs]
      have h3 := hp.resolve_left hs
      constructor <;> intro _ <;> omega

assert_standard_axioms le_signalOf_iff

/-- The signal is exactly `s` for the numbers of items from the threshold of `s` up to, but not
including, the threshold of `s + 1`. -/
theorem signalOf_eq_iff {slots m : ℕ} (hd : 0 < m * slots) (s T : ℕ) :
    signalOf slots m T = s ↔ threshold slots m s ≤ T ∧ T < threshold slots m (s + 1) := by
  have h1 := le_signalOf_iff hd s T
  have h2 := le_signalOf_iff hd (s + 1) T
  constructor
  · intro h
    refine ⟨h1.mp (le_of_eq h.symm), ?_⟩
    by_contra hc
    have h3 := h2.mpr (by omega)
    omega
  · rintro ⟨ha, hb⟩
    have h3 := h1.mpr ha
    have h4 : ¬ s + 1 ≤ signalOf slots m T := fun h => by
      have h5 := h2.mp h
      omega
    omega

assert_standard_axioms signalOf_eq_iff

/-- More items never give a weaker signal. -/
theorem signalOf_mono (slots m : ℕ) {T T' : ℕ} (h : T ≤ T') :
    signalOf slots m T ≤ signalOf slots m T' := by
  unfold signalOf
  have h1 : 14 * T / (m * slots) ≤ 14 * T' / (m * slots) :=
    Nat.div_le_div_right (Nat.mul_le_mul_left 14 h)
  by_cases hT : T > 0
  · rw [ite_eq_left hT, ite_eq_left (show T' > 0 by omega)]
    exact Nat.add_le_add_right h1 1
  · rw [ite_eq_right hT]
    exact Nat.add_le_add h1 (Nat.zero_le _)

/-- A container that holds no more than it can gives at most 15. -/
theorem signalOf_le (slots m T : ℕ) (h : T ≤ m * slots) : signalOf slots m T ≤ 15 := by
  unfold signalOf
  have h1 : 14 * T / (m * slots) ≤ 14 :=
    Nat.div_le_of_le_mul (by
      rw [Nat.mul_comm (m * slots) 14]
      exact Nat.mul_le_mul_left 14 h)
  by_cases hT : T > 0
  · rw [ite_eq_left hT]
    exact Nat.add_le_add_right h1 1
  · rw [ite_eq_right hT]
    exact Nat.le_trans h1 (by decide)

/-- A full container gives 15. -/
theorem signalOf_full {slots m : ℕ} (hd : 0 < m * slots) : signalOf slots m (m * slots) = 15 := by
  unfold signalOf
  rw [ite_eq_left hd, Nat.mul_div_cancel _ hd]

/-! #### The tables

Entry `s` of each list (from 0 to 15) is the least number of items with which the container
gives the signal `s`. With `le_signalOf_iff` and `signalOf_eq_iff` the tables say for which
numbers of items a comparator reads which signal. -/

/-- **Hopper** (also brewing stand: 5 slots), items that stack to 64: 1 item gives 1, 23 give
2, 46 give 3, ..., 320 (full) give 15. -/
theorem hopper_thresholds :
    (List.range 16).map (threshold 5 64) =
      [0, 1, 23, 46, 69, 92, 115, 138, 160, 183, 206, 229, 252, 275, 298, 320] := by
  decide

/-- **Chest**, barrel, shulker box, trapped chest (27 slots), items that stack to 64. -/
theorem chest_thresholds :
    (List.range 16).map (threshold 27 64) =
      [0, 1, 124, 247, 371, 494, 618, 741, 864, 988, 1111, 1235, 1358, 1482, 1605, 1728] := by
  decide

/-- **Double chest** (54 slots), items that stack to 64. -/
theorem doubleChest_thresholds :
    (List.range 16).map (threshold 54 64) =
      [0, 1, 247, 494, 741, 988, 1235, 1482, 1728, 1975, 2222, 2469, 2716, 2963, 3210, 3456] := by
  decide

/-- **Dropper**, dispenser (9 slots), items that stack to 64. -/
theorem dropper_thresholds :
    (List.range 16).map (threshold 9 64) =
      [0, 1, 42, 83, 124, 165, 206, 247, 288, 330, 371, 412, 453, 494, 535, 576] := by
  decide

/-- **Furnace**, blast furnace, smoker (3 slots), items that stack to 64. -/
theorem furnace_thresholds :
    (List.range 16).map (threshold 3 64) =
      [0, 1, 14, 28, 42, 55, 69, 83, 96, 110, 124, 138, 151, 165, 179, 192] := by
  decide

/-- Hopper, items that stack to 16. -/
theorem hopper_thresholds_16 :
    (List.range 16).map (threshold 5 16) =
      [0, 1, 6, 12, 18, 23, 29, 35, 40, 46, 52, 58, 63, 69, 75, 80] := by
  decide

/-- Chest, items that stack to 16. -/
theorem chest_thresholds_16 :
    (List.range 16).map (threshold 27 16) =
      [0, 1, 31, 62, 93, 124, 155, 186, 216, 247, 278, 309, 340, 371, 402, 432] := by
  decide

/-- Double chest, items that stack to 16. -/
theorem doubleChest_thresholds_16 :
    (List.range 16).map (threshold 54 16) =
      [0, 1, 62, 124, 186, 247, 309, 371, 432, 494, 556, 618, 679, 741, 803, 864] := by
  decide

/-- Dropper, items that stack to 16. -/
theorem dropper_thresholds_16 :
    (List.range 16).map (threshold 9 16) =
      [0, 1, 11, 21, 31, 42, 52, 62, 72, 83, 93, 103, 114, 124, 134, 144] := by
  decide

/-- Hopper, items that do not stack: one item gives 3 already (a threshold repeated in the
list means that the signals before the last of them are skipped), five give 15. -/
theorem hopper_thresholds_1 :
    (List.range 16).map (threshold 5 1) = [0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5] := by
  decide

/-- Chest, items that do not stack. -/
theorem chest_thresholds_1 :
    (List.range 16).map (threshold 27 1) =
      [0, 1, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 27] := by
  decide

/-- Double chest, items that do not stack. -/
theorem doubleChest_thresholds_1 :
    (List.range 16).map (threshold 54 1) =
      [0, 1, 4, 8, 12, 16, 20, 24, 27, 31, 35, 39, 43, 47, 51, 54] := by
  decide

/-- Dropper, items that do not stack. -/
theorem dropper_thresholds_1 :
    (List.range 16).map (threshold 9 1) = [0, 1, 1, 2, 2, 3, 4, 4, 5, 6, 6, 7, 8, 8, 9, 9] := by
  decide

/-- **The item sorter's numbers.** A hopper of ordinary items reads 1 with 1 to 22 items, 2
with 23 to 45, and 3 with 46 to 68: a filter of 18 + 4 items is at 1 and one more item takes it
to 2; a filter of 41 + 4 is at 2 and one more item takes it to 3. -/
theorem hopper_signal_one_two_three (T : ℕ) :
    (signalOf 5 64 T = 1 ↔ 1 ≤ T ∧ T < 23) ∧ (signalOf 5 64 T = 2 ↔ 23 ≤ T ∧ T < 46) ∧
      (signalOf 5 64 T = 3 ↔ 46 ≤ T ∧ T < 69) :=
  ⟨signalOf_eq_iff (by decide) 1 T, signalOf_eq_iff (by decide) 2 T,
    signalOf_eq_iff (by decide) 3 T⟩

assert_standard_axioms hopper_signal_one_two_three

end Redstone.Component.Container
