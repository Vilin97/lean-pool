/-
Copyright (c) 2026 Arthur Champernowne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Champernowne
-/
module

public import LeanPool.Champernowne.Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Interval ↔ digit-string counting

Base-general (`1 < b`). Everything here feeds the lower comparison
`le_base_pow_countOccurrences_champBlocks` between the stream length and
`b^k ·` (occurrence count) over `[1, N]`; the upper direction is derived
downstream (`Positions.lean`) from the lower one via the `allWords`
pigeonhole. Two relaxations keep this file small:

* occurrences at the head position of a number are never counted — the
  interior positions already carry the main term, uniformly in `w` (so
  no `w.head? = some 0` case split anywhere), and
* every cohort, full or not, is handled by the partial-cohort lower
  bound, so only lower periodic-count bounds are ever needed.

The exact counterparts (exact periodic count, per-position cards, exact
cohort sums, `digitEquiv` and its round-trips) live in
`CountExtras.lean`.
-/

@[expose] public section

namespace Champernowne

/-! ### Generic counting and rounding lemmas (no base) -/

/-- Lower bound for periodic counting: over `[A, A + t)` with a left
endpoint divisible by `p * q`, the value `n / p % q` hits a fixed `d < q`
at least `t / (p·q) · p` times — `p` hits in each complete period `p·q`.
Proved directly by injecting `range (t/(p·q)) ×ˢ range p`; the main proof
never needs the exact count (`card_Ico_filter_div_mod`,
`CountExtras.lean`). -/
theorem le_card_Ico_filter_div_mod {A t p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hd : d < q) (hA : p * q ∣ A) :
    t / (p * q) * p
      ≤ ((Finset.Ico A (A + t)).filter (fun n => n / p % q = d)).card := by
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  have hdpr : ∀ r < p, d * p + r < p * q := by
    intro r hr
    calc d * p + r < (d + 1) * p := by rw [Nat.succ_mul]; omega
    _ ≤ q * p := Nat.mul_le_mul_right p (by omega)
    _ = p * q := Nat.mul_comm q p
  rw [show t / (p * q) * p
      = (Finset.range (t / (p * q)) ×ˢ Finset.range p).card by
    rw [Finset.card_product, Finset.card_range, Finset.card_range]]
  apply Finset.card_le_card_of_injOn
    (fun x => A + (x.1 * (p * q) + d * p + x.2))
  · -- the map lands in the filtered interval
    rintro ⟨h, r⟩ hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe,
      Finset.mem_range] at hx
    obtain ⟨hh, hr⟩ := hx
    have hlt : h * (p * q) + d * p + r < t :=
      calc h * (p * q) + d * p + r
          < h * (p * q) + p * q := by have := hdpr r hr; omega
      _ = (h + 1) * (p * q) := by ring
      _ ≤ t / (p * q) * (p * q) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ t := Nat.div_mul_le_self t (p * q)
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico]
    refine ⟨⟨Nat.le_add_right _ _, by omega⟩, ?_⟩
    obtain ⟨a, rfl⟩ := hA
    have hrew : p * q * a + (h * (p * q) + d * p + r)
        = r + p * (d + q * (a + h)) := by ring
    rw [hrew, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hr, Nat.zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
  · -- injectivity: extract `h` and `r` back out by div/mod
    have hext : ∀ h r, r < p →
        (h * (p * q) + d * p + r) / (p * q) = h
          ∧ (h * (p * q) + d * p + r) % p = r := by
      intro h r hr
      constructor
      · have hrew : h * (p * q) + d * p + r = d * p + r + (p * q) * h := by
          ring
        rw [hrew, Nat.add_mul_div_left _ _ hpq, Nat.div_eq_of_lt (hdpr r hr),
          Nat.zero_add]
      · have hrew : h * (p * q) + d * p + r = p * (h * q + d) + r := by ring
        rw [hrew, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    rintro ⟨h₁, r₁⟩ hx₁ ⟨h₂, r₂⟩ hx₂ heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe,
      Finset.mem_range] at hx₁ hx₂
    have hcancel : h₁ * (p * q) + d * p + r₁ = h₂ * (p * q) + d * p + r₂ :=
      Nat.add_left_cancel heq
    have hh : h₁ = h₂ := by
      rw [← (hext h₁ r₁ hx₁.2).1, ← (hext h₂ r₂ hx₂.2).1, hcancel]
    have hr : r₁ = r₂ := by
      rw [← (hext h₁ r₁ hx₁.2).2, ← (hext h₂ r₂ hx₂.2).2, hcancel]
    exact Prod.ext hh hr

/-- Rounding compatibility: `t/q ≤ t/(p·q)·p + p`. -/
theorem div_le_div_mul_add (t p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    t / q ≤ t / (p * q) * p + p := by
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  have e := Nat.div_add_mod t (p * q)
  have hm : t % (p * q) < p * q := Nat.mod_lt t hpq
  have key : t < (t / (p * q) * p + p) * q := by
    have h1 : t < p * q * (t / (p * q)) + p * q := by omega
    calc t < p * q * (t / (p * q)) + p * q := h1
    _ = (t / (p * q) * p + p) * q := by ring
  exact Nat.le_of_lt_succ (Nat.lt_succ_of_lt
    ((Nat.div_lt_iff_lt_mul hq).mpr key))

/-- `∑_{i<K} b^i < b^K` for `1 < b`. -/
theorem geomsum_lt {b : ℕ} (hb : 1 < b) (K : ℕ) :
    ∑ i ∈ Finset.range K, b ^ i < b ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h2 : b ^ K * 2 ≤ b ^ K * b := Nat.mul_le_mul_left _ hb
    omega

/-! ### `bigDigits` API -/

/-- A number in `[b^(m-1), b^m)` has exactly `m` digits. -/
theorem length_bigDigits_eq {b m n : ℕ} (hb : 1 < b)
    (h1 : b ^ (m - 1) ≤ n) (h2 : n < b ^ m) :
    (bigDigits b n).length = m := by
  have hle : (Nat.digits b n).length ≤ m :=
    (Nat.digits_length_le_iff hb n).mpr h2
  have hlt : m - 1 < (Nat.digits b n).length :=
    (Nat.lt_digits_length_iff hb n).mpr h1
  simp only [bigDigits, List.length_reverse]
  omega

/-! ### Cardinalities -/

/-- There are `(b-1) * b^(m-1)` numbers with exactly `m` digits. -/
theorem card_mDigit {b : ℕ} (hb : 1 < b) (m : ℕ) (hm : 0 < m) :
    (Finset.Ico (b ^ (m - 1)) (b ^ m)).card = (b - 1) * b ^ (m - 1) := by
  rw [Nat.card_Ico]
  have h : b ^ m = b * b ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ']
  have hd : (b - 1) * b ^ (m - 1) + b ^ (m - 1) = b * b ^ (m - 1) := by
    have hb1 : b - 1 + 1 = b := by omega
    calc (b - 1) * b ^ (m - 1) + b ^ (m - 1)
        = (b - 1 + 1) * b ^ (m - 1) := by ring
    _ = b * b ^ (m - 1) := by rw [hb1]
  omega

/-! ### Cohort decomposition -/

/-- Cohort decomposition of a sum over `[1, b^M)`. -/
theorem sum_Ico_one_pow {β : Type*} [AddCommMonoid β] {b : ℕ} (hb : 1 < b)
    (M : ℕ) (g : ℕ → β) :
    ∑ n ∈ Finset.Ico 1 (b ^ M), g n
      = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m), g n := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [← Finset.sum_Ico_consecutive g
        (Nat.one_le_pow M b (by omega))
        (Nat.pow_le_pow_right (by omega) (Nat.le_add_right M 1)),
      ih, Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]

/-! ### Stream and cohort length sums -/

/-- The stream-prefix length as a sum over the numbers `1..N`. -/
theorem length_champBlocks (b N : ℕ) :
    (champBlocks b N).length
      = ∑ n ∈ Finset.Ico 1 (N + 1), (bigDigits b n).length := by
  induction N with
  | zero => simp [champBlocks]
  | succ n ih =>
    rw [champBlocks_succ, List.length_append, ih]
    exact (Finset.sum_Ico_succ_top (show 1 ≤ n + 1 by omega) _).symm

/-- Total digit length of the `m`-digit cohort. -/
theorem sum_length_cohort {b : ℕ} (hb : 1 < b) (m : ℕ) (hm : 0 < m) :
    ∑ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m), (bigDigits b n).length
      = (b - 1) * b ^ (m - 1) * m := by
  have hc : ∀ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m),
      (bigDigits b n).length = m := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    exact length_bigDigits_eq hb hn.1 hn.2
  rw [Finset.sum_congr rfl hc, Finset.sum_const, card_mDigit hb m hm,
    smul_eq_mul]

/-- Total digit length of a partial cohort. -/
theorem sum_length_partial {b : ℕ} (hb : 1 < b) (K t : ℕ)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    ∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), (bigDigits b n).length
      = t * (K + 1) := by
  have hc : ∀ n ∈ Finset.Ico (b ^ K) (b ^ K + t),
      (bigDigits b n).length = K + 1 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    exact length_bigDigits_eq hb (by simpa using hn.1) (by omega)
  rw [Finset.sum_congr rfl hc, Finset.sum_const, Nat.card_Ico,
    Nat.add_sub_cancel_left, smul_eq_mul]

/-! ### Blocks at positions -/

/-- Substring ↔ arithmetic bridge: the block of `w.length` digits at
big-endian position `j` of an `m`-digit `n` equals `w` iff the
corresponding quotient-remainder is the value of `w`. -/
theorem block_eq_iff {b m n : ℕ} (hb : 1 < b)
    (hlen : (bigDigits b n).length = m) {w : List ℕ} (hw : ∀ d ∈ w, d < b)
    {j : ℕ} (hjk : j + w.length ≤ m) :
    ((bigDigits b n).drop j).take w.length = w
      ↔ n / b ^ (m - j - w.length) % b ^ w.length
          = Nat.ofDigits b w.reverse := by
  have hml : (Nat.digits b n).length = m := by simpa [bigDigits] using hlen
  have hsub : ((bigDigits b n).drop j).take w.length
      = (((Nat.digits b n).drop (m - j - w.length)).take w.length).reverse := by
    change (((Nat.digits b n).reverse.drop j).take w.length) = _
    rw [List.drop_reverse, hml, List.take_reverse, List.length_take, hml,
      Nat.min_eq_left (by omega)]
    congr 1
    rw [List.take_drop,
      show m - j - w.length + w.length = m - j by omega]
  have hA_lt : ∀ d ∈ ((Nat.digits b n).drop (m - j - w.length)).take w.length,
      d < b := fun d hd =>
    Nat.digits_lt_base hb (List.mem_of_mem_drop (List.mem_of_mem_take hd))
  have hA_len :
      ((((Nat.digits b n).drop (m - j - w.length)).take w.length)).length
      = w.length := by
    rw [List.length_take, List.length_drop, hml]
    omega
  have hofA : Nat.ofDigits b
      (((Nat.digits b n).drop (m - j - w.length)).take w.length)
      = n / b ^ (m - j - w.length) % b ^ w.length := by
    rw [← Nat.ofDigits_mod_pow_eq_ofDigits_take w.length (by omega) _
        (fun d hd => Nat.digits_lt_base hb (List.mem_of_mem_drop hd)),
      ← Nat.self_div_pow_eq_ofDigits_drop _ _ hb]
  rw [hsub, List.reverse_eq_iff]
  constructor
  · intro h
    rw [← hofA, h]
  · intro h
    refine Nat.ofDigits_inj_of_len_eq hb ?_ hA_lt
      (fun d hd => hw d (List.mem_reverse.mp hd)) ?_
    · rw [hA_len, List.length_reverse]
    · rw [hofA, h]

/-! ### Partial-cohort block occurrence sums

Every cohort is treated as a partial cohort `[b^K, b^K + t)` (a full one
has `t = b^(K+1) - b^K`), and only the interior positions `j ≥ 1` are
counted — occurrences at the head of a number are dropped, which is
sound for a lower bound and uniform in `w` (a leading-zero `w` simply
never occurs there). -/

/-- Convert the block predicate at interior position `j` to the arithmetic
predicate, on a partial cohort of `(K+1)`-digit numbers. -/
theorem filter_blockAt_partial_congr {b : ℕ} (hb : 1 < b) (K t j : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (_hj : 0 < j) (hjk : j + w.length ≤ K + 1)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    (Finset.Ico (b ^ K) (b ^ K + t)).filter
      (fun n => ((bigDigits b n).drop j).take w.length = w)
      = (Finset.Ico (b ^ K) (b ^ K + t)).filter
      (fun n => n / b ^ (K + 1 - j - w.length) % b ^ w.length
        = Nat.ofDigits b w.reverse) := by
  apply Finset.filter_congr
  intro n hn
  rw [Finset.mem_Ico] at hn
  exact block_eq_iff hb (length_bigDigits_eq (m := K + 1) hb hn.1 (by omega)) hw
    (by omega)

/-- Lower bound for one interior position over a partial cohort. -/
theorem le_card_blockAt_partial {b : ℕ} (hb : 1 < b) (K t j : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (hj : 0 < j) (hjk : j + w.length ≤ K + 1)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    t / b ^ w.length ≤ ((Finset.Ico (b ^ K) (b ^ K + t)).filter
      (fun n => ((bigDigits b n).drop j).take w.length = w)).card
      + b ^ (K + 1 - j - w.length) := by
  rw [filter_blockAt_partial_congr hb K t j hw hj hjk hAt]
  have hD : Nat.ofDigits b w.reverse < b ^ w.length := by
    have h := Nat.ofDigits_lt_base_pow_length hb
      (fun d hd => hw d (List.mem_reverse.mp hd))
    rwa [List.length_reverse] at h
  have hp : 0 < b ^ (K + 1 - j - w.length) := pow_pos (by omega) _
  have hq : 0 < b ^ w.length := pow_pos (by omega) _
  have hpq : b ^ (K + 1 - j - w.length) * b ^ w.length = b ^ (K + 1 - j) := by
    rw [← pow_add]; congr 1; omega
  have hdvd : b ^ (K + 1 - j - w.length) * b ^ w.length ∣ b ^ K :=
    hpq ▸ pow_dvd_pow b (by omega)
  calc t / b ^ w.length
      ≤ t / (b ^ (K + 1 - j - w.length) * b ^ w.length)
        * b ^ (K + 1 - j - w.length) + b ^ (K + 1 - j - w.length) :=
      div_le_div_mul_add t _ (b ^ w.length) hp hq
  _ ≤ _ := Nat.add_le_add_right
      (le_card_Ico_filter_div_mod hp hq hD hdvd) _

/-- Partial-cohort occurrence sum as a sum of per-position cards. -/
theorem sum_countOccurrences_Ico_eq {b : ℕ} (hb : 1 < b) (K t : ℕ) (w : List ℕ)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
      = ∑ j ∈ Finset.range (K + 2),
          ((Finset.Ico (b ^ K) (b ^ K + t)).filter
            (fun n => ((bigDigits b n).drop j).take w.length = w)).card := by
  have hstep : ∀ n ∈ Finset.Ico (b ^ K) (b ^ K + t),
      countOccurrences w (bigDigits b n)
        = ∑ j ∈ Finset.range (K + 2),
            if ((bigDigits b n).drop j).take w.length = w then 1 else 0 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hpred : ∀ j ∈ Finset.range (K + 2),
        (w.isPrefixOf ((bigDigits b n).drop j) = true)
          ↔ ((bigDigits b n).drop j).take w.length = w := fun j _ => by
      rw [List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take, eq_comm]
    rw [countOccurrences_eq_card_filter_range,
      length_bigDigits_eq (m := K + 1) hb hn.1 (by omega), Finset.filter_congr hpred,
      Finset.card_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => (Finset.card_filter _ _).symm

/-- Partial-cohort occurrence sum, lower bound (stated additively; drops the
head position, which is only ever a nonnegative contribution). -/
theorem le_sum_countOccurrences_partial_cohort {b : ℕ} (hb : 1 < b) (K t : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (hk : w.length ≤ K + 1)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    (K + 1 - w.length) * (t / b ^ w.length)
      ≤ (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
        + 2 * b ^ (K + 1 - w.length) := by
  rw [sum_countOccurrences_Ico_eq hb K t w hAt, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le (K + 1 - w.length + 1))
      (by omega : K + 1 - w.length + 1 ≤ K + 2),
    ← Finset.range_eq_Ico, Finset.sum_range_succ']
  have hint : (K + 1 - w.length) * (t / b ^ w.length)
      ≤ (∑ i ∈ Finset.range (K + 1 - w.length),
          ((Finset.Ico (b ^ K) (b ^ K + t)).filter
            (fun n => ((bigDigits b n).drop (i + 1)).take w.length = w)).card)
        + ∑ i ∈ Finset.range (K + 1 - w.length), b ^ (K - w.length - i) := by
    have h1 : ∑ _i ∈ Finset.range (K + 1 - w.length), t / b ^ w.length
        = (K + 1 - w.length) * (t / b ^ w.length) := by
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have h2 : (∑ _i ∈ Finset.range (K + 1 - w.length), t / b ^ w.length)
        ≤ ∑ i ∈ Finset.range (K + 1 - w.length),
            (((Finset.Ico (b ^ K) (b ^ K + t)).filter
              (fun n => ((bigDigits b n).drop (i + 1)).take w.length = w)).card
              + b ^ (K + 1 - (i + 1) - w.length)) :=
      Finset.sum_le_sum fun i hi =>
        le_card_blockAt_partial hb K t (i + 1) hw (Nat.succ_pos i)
          (by rw [Finset.mem_range] at hi; omega) hAt
    rw [Finset.sum_add_distrib] at h2
    rw [h1] at h2
    refine le_trans h2 (Nat.add_le_add_left (le_of_eq ?_) _)
    exact Finset.sum_congr rfl fun i _ => by congr 1; omega
  have hgl := geomsum_lt hb (K + 1 - w.length)
  have hrefl : ∑ i ∈ Finset.range (K + 1 - w.length), b ^ (K - w.length - i)
      = ∑ i ∈ Finset.range (K + 1 - w.length), b ^ i := by
    rw [← Finset.sum_range_reflect (fun i => b ^ i) (K + 1 - w.length)]
    exact Finset.sum_congr rfl fun i hi => by
      rw [Finset.mem_range] at hi; congr 1; omega
  rw [hrefl] at hint
  omega

/-! ### Partial-cohort comparison, boundary induction, and general `N` -/

/-- `c + j + 1 ≤ (c+1) * b^j` for `b ≥ 2` -- linear growth is dominated by
any base's exponential, uniformly from `j = 0`. -/
theorem linear_le_const_mul_pow {b : ℕ} (hb : 1 < b) (c j : ℕ) :
    c + j + 1 ≤ (c + 1) * b ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hpow : b ^ (j + 1) = b * b ^ j := by rw [pow_succ']
    rw [hpow]
    have h2 : (c + 1) * b ^ j * 2 ≤ (c + 1) * b ^ j * b := Nat.mul_le_mul_left _ hb
    nlinarith [ih]

/-- Partial-cohort comparison, lower. -/
theorem le_base_pow_countOccurrences_partial {b : ℕ} (hb : 1 < b) (K t : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hk : w.length ≤ K + 1)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), (bigDigits b n).length)
      ≤ b ^ w.length * (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
        + 3 * (w.length + 1) * b ^ (K + 1) := by
  have hwlen : 0 < w.length := List.length_pos_of_ne_nil hwne
  have hsum := le_sum_countOccurrences_partial_cohort hb K t hw hk hAt
  have hmul := Nat.mul_le_mul_left (b ^ w.length) hsum
  rw [Nat.mul_add] at hmul
  have hbpow : b ^ w.length * (2 * b ^ (K + 1 - w.length)) = 2 * b ^ (K + 1) := by
    rw [show b ^ w.length * (2 * b ^ (K + 1 - w.length))
        = 2 * (b ^ w.length * b ^ (K + 1 - w.length)) from by ring, ← pow_add]
    congr 2; omega
  have hlen := sum_length_partial hb K t hAt
  have hdm : b ^ w.length * (t / b ^ w.length) + t % b ^ w.length = t :=
    Nat.div_add_mod t (b ^ w.length)
  have hmod : t % b ^ w.length ≤ b ^ w.length := le_of_lt (Nat.mod_lt t (by positivity))
  have hlin := linear_le_const_mul_pow hb w.length (K + 1 - w.length)
  have hj : w.length + (K + 1 - w.length) + 1 = K + 2 := by omega
  rw [hj] at hlin
  have hpoweq : b ^ (K + 1 - w.length) * b ^ w.length = b ^ (K + 1) := by
    rw [← pow_add]; congr 1; omega
  have hrbound : (K + 1 - w.length) * (t % b ^ w.length) ≤ (w.length + 1) * b ^ (K + 1) := by
    calc (K + 1 - w.length) * (t % b ^ w.length)
        ≤ (K + 2) * b ^ w.length := Nat.mul_le_mul (by omega) hmod
    _ ≤ (w.length + 1) * b ^ (K + 1 - w.length) * b ^ w.length :=
        Nat.mul_le_mul_right _ hlin
    _ = (w.length + 1) * (b ^ (K + 1 - w.length) * b ^ w.length) := by ring
    _ = (w.length + 1) * b ^ (K + 1) := by rw [hpoweq]
  have htw : t * w.length ≤ (w.length + 1) * b ^ (K + 1) := by
    have ht1 : t ≤ b ^ (K + 1) := by omega
    calc t * w.length ≤ b ^ (K + 1) * w.length := Nat.mul_le_mul_right _ ht1
    _ ≤ b ^ (K + 1) * (w.length + 1) := Nat.mul_le_mul_left _ (by omega)
    _ = (w.length + 1) * b ^ (K + 1) := by ring
  have hkey : t * (K + 1) = (K + 1 - w.length) * (b ^ w.length * (t / b ^ w.length))
      + (K + 1 - w.length) * (t % b ^ w.length) + t * w.length := by
    have h2 : (K + 1 - w.length) * (b ^ w.length * (t / b ^ w.length))
        + (K + 1 - w.length) * (t % b ^ w.length) = (K + 1 - w.length) * t := by
      rw [← Nat.mul_add, hdm]
    have h3 : (K + 1 - w.length) * t + t * w.length = t * (K + 1) := by
      have hKw : (K + 1 - w.length) + w.length = K + 1 := by omega
      calc (K + 1 - w.length) * t + t * w.length
          = t * ((K + 1 - w.length) + w.length) := by ring
      _ = t * (K + 1) := by rw [hKw]
    omega
  have hcomm : b ^ w.length * ((K + 1 - w.length) * (t / b ^ w.length))
      = (K + 1 - w.length) * (b ^ w.length * (t / b ^ w.length)) := by ring
  have e1 : (K + 1 - w.length) * (b ^ w.length * (t / b ^ w.length))
      ≤ b ^ w.length * (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
        + b ^ w.length * (2 * b ^ (K + 1 - w.length)) := by
    rw [← hcomm]; exact hmul
  have hscale3 : 2 * b ^ (K + 1) ≤ (w.length + 1) * b ^ (K + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  calc (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), (bigDigits b n).length)
      = t * (K + 1) := hlen
  _ = (K + 1 - w.length) * (b ^ w.length * (t / b ^ w.length))
      + (K + 1 - w.length) * (t % b ^ w.length) + t * w.length := hkey
  _ ≤ (b ^ w.length * (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
      + b ^ w.length * (2 * b ^ (K + 1 - w.length)))
      + (w.length + 1) * b ^ (K + 1) + (w.length + 1) * b ^ (K + 1) :=
    Nat.add_le_add (Nat.add_le_add e1 hrbound) htw
  _ = b ^ w.length * (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
      + (b ^ w.length * (2 * b ^ (K + 1 - w.length))
        + (w.length + 1) * b ^ (K + 1) + (w.length + 1) * b ^ (K + 1)) := by ring
  _ = b ^ w.length * (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
      + (2 * b ^ (K + 1) + (w.length + 1) * b ^ (K + 1) + (w.length + 1) * b ^ (K + 1)) := by
    rw [hbpow]
  _ ≤ b ^ w.length * (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
      + 3 * (w.length + 1) * b ^ (K + 1) := by
    have hseq : 3 * (w.length + 1) * b ^ (K + 1)
        = (w.length + 1) * b ^ (K + 1) + (w.length + 1) * b ^ (K + 1)
          + (w.length + 1) * b ^ (K + 1) := by ring
    omega

/-- The accumulated cohort error is absorbed by the next power of the base. -/
theorem cohort_error_add_le {b : ℕ} (hb : 1 < b) (c K : ℕ) :
    6 * c * b ^ K + 3 * c * b ^ (K + 1) ≤ 6 * c * b ^ (K + 1) := by
  rw [pow_succ']
  have hstep : c * b ^ K * 2 ≤ c * b ^ K * b := Nat.mul_le_mul_left _ hb
  nlinarith only [hstep]

/-- Boundary comparison, lower: over the complete cohorts `[1, b^K)`, the
stream length exceeds `b^k` times the occurrence count by at most
`6·(k+1)·b^K`. Each full cohort `[b^K, b^(K+1))` is a partial cohort with
`t = b^(K+1) - b^K` (`le_base_pow_countOccurrences_partial`); the
geometric accumulation of the per-cohort errors `3(k+1)·b^(K+1)` stays
below `6(k+1)·b^K` because `2 ≤ b`. Cohorts too short to fit `w` only
need their length bounded (the occurrence count is dropped at `≥ 0`). -/
theorem le_base_pow_count_boundary {b : ℕ} (hb : 1 < b) (K : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) :
    (∑ n ∈ Finset.Ico 1 (b ^ K), (bigDigits b n).length)
      ≤ b ^ w.length * (∑ n ∈ Finset.Ico 1 (b ^ K), countOccurrences w (bigDigits b n))
        + 6 * (w.length + 1) * b ^ K := by
  have hwlen : 0 < w.length := List.length_pos_of_ne_nil hwne
  induction K with
  | zero => simp
  | succ K ih =>
    have h1 : b ^ K ≤ b ^ (K + 1) :=
      Nat.pow_le_pow_right (by omega) (Nat.le_add_right K 1)
    have hcov : b ^ K + (b ^ (K + 1) - b ^ K) = b ^ (K + 1) := by omega
    rw [← Finset.sum_Ico_consecutive (fun n => countOccurrences w (bigDigits b n))
        (Nat.one_le_pow K b (by omega)) h1,
      ← Finset.sum_Ico_consecutive (fun n => (bigDigits b n).length)
        (Nat.one_le_pow K b (by omega)) h1,
      Nat.mul_add]
    rcases Nat.lt_or_ge (K + 1) w.length with hshort | hlong
    · -- cohort shorter than `w`: drop the count, bound the length crudely
      have hlen := sum_length_partial hb K (b ^ (K + 1) - b ^ K) (by omega)
      rw [hcov] at hlen
      have hbnd : (b ^ (K + 1) - b ^ K) * (K + 1) ≤ (w.length + 1) * b ^ (K + 1) := by
        calc (b ^ (K + 1) - b ^ K) * (K + 1)
            ≤ b ^ (K + 1) * (K + 1) := Nat.mul_le_mul_right _ (by omega)
        _ ≤ b ^ (K + 1) * (w.length + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = (w.length + 1) * b ^ (K + 1) := Nat.mul_comm _ _
      have hscale : 6 * (w.length + 1) * b ^ K + (w.length + 1) * b ^ (K + 1)
          ≤ 6 * (w.length + 1) * b ^ (K + 1) := by
        have h := cohort_error_add_le hb (w.length + 1) K
        nlinarith only [h, Nat.zero_le ((w.length + 1) * b ^ (K + 1))]
      omega
    · have hpart := le_base_pow_countOccurrences_partial hb K (b ^ (K + 1) - b ^ K)
        hw hwne (by omega) (by omega)
      rw [hcov] at hpart
      have hscale := cohort_error_add_le hb (w.length + 1) K
      omega

/-- General-`N` comparison, lower. -/
theorem le_base_pow_countOccurrences_champBlocks {b : ℕ} (hb : 1 < b) (N M : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hM : 0 < M) (hwM : w.length ≤ M)
    (h1 : b ^ (M - 1) ≤ N + 1) (h2 : N + 1 ≤ b ^ M) :
    (∑ n ∈ Finset.Ico 1 (N + 1), (bigDigits b n).length)
      ≤ b ^ w.length * (∑ n ∈ Finset.Ico 1 (N + 1), countOccurrences w (bigDigits b n))
        + 6 * (w.length + 1) * b ^ M := by
  obtain ⟨K, rfl⟩ : ∃ K, M = K + 1 := ⟨M - 1, by omega⟩
  rw [show K + 1 - 1 = K from rfl] at h1
  obtain ⟨t, ht⟩ : ∃ t, N + 1 = b ^ K + t := ⟨N + 1 - b ^ K, by omega⟩
  have hAt : b ^ K + t ≤ b ^ (K + 1) := by omega
  rw [ht, ← Finset.sum_Ico_consecutive (fun n => countOccurrences w (bigDigits b n))
      (Nat.one_le_pow K b (by omega)) (Nat.le_add_right _ _),
    ← Finset.sum_Ico_consecutive (fun n => (bigDigits b n).length)
      (Nat.one_le_pow K b (by omega)) (Nat.le_add_right _ _),
    Nat.mul_add]
  have hbd := le_base_pow_count_boundary hb K hw hwne
  have hpart := le_base_pow_countOccurrences_partial hb K t hw hwne (by omega) hAt
  have hscale := cohort_error_add_le hb (w.length + 1) K
  omega

end Champernowne
