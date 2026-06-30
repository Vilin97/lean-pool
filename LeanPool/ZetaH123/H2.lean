/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

/-!
# H2 for Thakur's hypotheses on power sums
-/

namespace ZetaH123.H2

/-
# Problem Description

Throughout, fix a prime `q`. All "digit" and "carry" conditions below are taken in
base `q`.

## Definition 1 (Base-`q` digits).
Every nonnegative integer `x` has a unique base-`q` representation
`x = ∑_{e ≥ 0} x_e q ^ e`, with `0 ≤ x_e ≤ q-1` and `x_e = 0` for all sufficiently
large `e`. We call `x_e` the `e`-th base-`q` digit of `x`.

## Definition 2 (Carry-free addition).
A finite list of nonnegative integers `x_1, …, x_r` *adds without carries in base `q`*
if, at every digit position `e ≥ 0`, the digits sum to at most `q-1`:
`∑_{i=1} ^ r (x_i)_e ≤ q-1` for every `e ≥ 0`.

## Definition 3 (The set `T_{d,k-1}`).
For integers `d ≥ 1` and `k > 0`, `T_{d,k-1}` is the set of `d`-tuples
`(m_1, …, m_d)` of integers satisfying:
  1. `m_i > 0` for all `i`;
  2. `(q - 1) ∣ m_i` for all `i`;
  3. the list `(k-1, m_1, …, m_d)` adds without carries in base `q`.

## Definition 4 (The functions `s_d`).
For `d ≥ 1` and `k > 0`,
`s_d(k) = d*k + min_{(m_1,…,m_d) ∈ T_{d,k-1}} (m_1 + 2 m_2 + ⋯ + d m_d)`.
`T_{d,k-1}` is always nonempty so the minimum exists.

## Main Statement (Theorem).
Fix a prime `q` and integers `d > 1` and `k > 0`. Let `J` be the set of integers
`j ≥ 0` with `(q - 1) ∣ j` and `q ∤ C(s_1(k) + j - 1, k-1)`. For `j ∈ J` set
`F(j) = s_{d-1}(s_1(k) + j) + s_1(k) + j`. Then `F` attains its minimum over `J`
uniquely at `j = 0`: `F(0) < F(j)` for every `j ∈ J` with `j > 0`.

## Notes
- Here `n = s_1(k) + j - 1 ≥ k-1 ≥ 0` and `r = k-1 ≥ 0`, so all binomial
  coefficients are ordinary binomials of nonnegative integers.
- `0 ∈ J` (a nontrivial fact), so the uniqueness of the minimizer is meaningful;
  this admissibility is recorded as a separate statement `main_zero_mem`.
- We use `ℕ` and 1-indexing of digit positions via list indices starting at 0;
  the weight on `m_i` is `i`, encoded as `(i.val + 1)` for `i : Fin d`.
-/

/-- The `e`-th base-`q` digit of `x` (returns `0` for positions beyond the
representation, matching the convention `x_e = 0` for large `e`). -/
def qdigit (q x e : ℕ) : ℕ := (Nat.digits q x).getD e 0

/-- A finite list of nonnegative integers `xs` *adds without carries in base `q`*
if at every digit position `e` the base-`q` digits sum to at most `q - 1`. This is
exactly the carry-free condition of Definition 2. -/
def AddNoCarry (q : ℕ) (xs : List ℕ) : Prop :=
  ∀ e : ℕ, (xs.map (fun x => qdigit q x e)).sum ≤ q - 1

/-- The set `T_{d,k1}` of `d`-tuples (encoded as `m : Fin d → ℕ`) such that each
`m i` is positive, divisible by `q - 1`, and the list `(k1, m_0, …, m_{d-1})` adds
without carries in base `q`. Here `k1` plays the role of `k - 1`. -/
def TSet (q d k1 : ℕ) : Set (Fin d → ℕ) :=
  {m | (∀ i, 0 < m i) ∧ (∀ i, (q - 1) ∣ m i) ∧
        AddNoCarry q (k1 :: (List.ofFn m))}

/-- The function `s_d(k) = d*k + min over `T_{d,k-1}` of `∑ (i+1) * m i`.
The minimum over the nonempty set of objective values is realised as the infimum
(`sInf`) of that set of naturals. -/
noncomputable def s (q d k : ℕ) : ℕ :=
  d * k + sInf {v : ℕ | ∃ m ∈ TSet q d (k - 1), v = ∑ i : Fin d, (i.val + 1) * m i}

/-- The objective `F(j) = s_{d-1}(s_1(k) + j) + s_1(k) + j`. -/
noncomputable def F (q d k j : ℕ) : ℕ :=
  s q (d - 1) (s q 1 k + j) + s q 1 k + j

/-- The admissible set `J`: nonnegative integers `j` with `(q - 1) ∣ j` and
`q ∤ C(s_1(k) + j - 1, k - 1)`. -/
def Jset (q k : ℕ) : Set ℕ :=
  {j | (q - 1) ∣ j ∧ ¬ (q ∣ Nat.choose (s q 1 k + j - 1) (k - 1))}

-- Helper lemmas

/-- The `e`-th base-`q` digit equals `x / q ^ e % q`. -/
theorem qdigit_eq (q x e : ℕ) (hq : 2 ≤ q) : qdigit q x e = x / q ^ e % q := by
  unfold qdigit; exact Nat.getD_digits x e hq

/-- `a % q ^ i` is the base-`q` number formed by the first `i` digits. -/
theorem digit_mod (q a i : ℕ) :
    a % q ^ i = ∑ e ∈ Finset.range i, (a / q ^ e % q) * q ^ e := by
  induction i with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, Nat.mod_pow_succ]; ring

/-- `(q - 1) * ∑_{e<i} q ^ e = q ^ i - 1`. -/
theorem geom_pred (q i : ℕ) (hq : 1 ≤ q) :
    (q - 1) * ∑ e ∈ Finset.range i, q ^ e = q ^ i - 1 := by
  induction i with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih, pow_succ]
    have : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
    have h2 : (q - 1) * q ^ n = q ^ n * q - q ^ n := by rw [Nat.sub_mul, one_mul]; ring_nf
    have hle : q ^ n ≤ q ^ n * q := Nat.le_mul_of_pos_right _ (by omega)
    rw [h2]; omega

/-- If two numbers add without carry in the first `i` positions, then their
truncations to `i` digits sum to less than `q ^ i`. -/
theorem noCarry_mod (q a b i : ℕ) (hq : 1 < q)
    (h : ∀ e, e < i → (a / q ^ e % q) + (b / q ^ e % q) ≤ q - 1) :
    a % q ^ i + b % q ^ i < q ^ i := by
  rw [digit_mod q a i, digit_mod q b i, ← Finset.sum_add_distrib]
  have key : ∑ e ∈ Finset.range i, ((a / q ^ e % q) * q ^ e + (b / q ^ e % q) * q ^ e)
      ≤ q ^ i - 1 := by
    calc ∑ e ∈ Finset.range i, ((a / q ^ e % q) * q ^ e + (b / q ^ e % q) * q ^ e)
        = ∑ e ∈ Finset.range i, ((a / q ^ e % q) + (b / q ^ e % q)) * q ^ e := by
          apply Finset.sum_congr rfl; intro e _; ring
      _ ≤ ∑ e ∈ Finset.range i, (q - 1) * q ^ e := by
          apply Finset.sum_le_sum; intro e he
          exact Nat.mul_le_mul_right _ (h e (Finset.mem_range.mp he))
      _ = (q - 1) * ∑ e ∈ Finset.range i, q ^ e := by rw [Finset.mul_sum]
      _ = q ^ i - 1 := geom_pred q i (le_of_lt hq)
  have : 1 ≤ q ^ i := Nat.one_le_pow _ _ (by omega)
  omega

/-- Kummer's theorem (one direction): if adding `k` and `n-k` produces no carry in
any base-`q` position, then `q ∤ C(n,k)`. -/
theorem not_dvd_choose (q n k : ℕ) (hq : q.Prime) (hkn : k ≤ n)
    (hcarry : ∀ i, k % q ^ i + (n - k) % q ^ i < q ^ i) :
    ¬ q ∣ Nat.choose n k := by
  have hb : Nat.log q n < n + 1 := lt_of_le_of_lt (Nat.log_le_self q n) (Nat.lt_succ_self n)
  have hfac : (Nat.choose n k).factorization q = 0 := by
    rw [Nat.factorization_choose hq hkn hb, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
    intro i _
    simp only [not_le]
    exact hcarry i
  have hpos : 0 < Nat.choose n k := Nat.choose_pos hkn
  intro hdvd
  have := (Nat.Prime.dvd_iff_one_le_factorization hq (by omega)).mp hdvd
  omega

/-- The `e`-th digit of `(q - 1) * q ^ L`: equal to `q-1` at position `L`, else `0`. -/
theorem digit_special (q L e : ℕ) (hq : 2 ≤ q) :
    ((q - 1) * q ^ L) / q ^ e % q = if e = L then q - 1 else 0 := by
  rcases lt_trichotomy e L with h | h | h
  · rw [if_neg (by omega)]
    have hd : (q - 1) * q ^ L / q ^ e = (q - 1) * q ^ (L-e) := by
      rw [Nat.mul_div_assoc _ (pow_dvd_pow q (by omega))]
      congr 1
      rw [Nat.pow_div (by omega) (by omega)]
    rw [hd]
    have : q ∣ (q - 1) * q ^ (L-e) := Dvd.dvd.mul_left (dvd_pow_self q (by omega)) _
    omega
  · subst h
    rw [if_pos rfl, Nat.mul_div_cancel _ (Nat.pow_pos (by omega : 0 < q))]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [if_neg (by omega)]
    have hlt : (q - 1)*q ^ L < q ^ e := by
      calc (q - 1)*q ^ L < q * q ^ L := by
            apply Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl _) (Nat.pow_pos (by omega : 0 < q))
        _ = q ^ (L+1) := by rw [pow_succ]; ring
        _ ≤ q ^ e := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.div_eq_of_lt hlt]; simp

-- Main Statement(s)

/-- `0` is admissible: `0 ∈ J`. This nontrivial admissibility fact makes the
uniqueness-of-minimizer statement meaningful. -/
theorem main_zero_mem (q : ℕ) (hq : q.Prime) (d k : ℕ) (_hd : 1 < d) (hk : 0 < k) :
    (0 : ℕ) ∈ Jset q k := by
  have hq2 : 2 ≤ q := hq.two_le
  -- The objective value set for d = 1.
  set S : Set ℕ := {v : ℕ | ∃ m ∈ TSet q 1 (k - 1), v = ∑ i : Fin 1, (i.val + 1) * m i}
    with hS
  -- Choose L large so that k-1 < q ^ L.
  have hLlt : k - 1 < q ^ k := by
    calc k - 1 < k := by omega
      _ ≤ q ^ k := Nat.le_of_lt (Nat.lt_pow_self (by omega) )
  -- Construct a witness, proving nonemptiness of S.
  have hofn1 : ∀ (m : Fin 1 → ℕ), List.ofFn m = [m 0] := by
    intro m; simp [List.ofFn_succ, List.ofFn_zero]
  have hne : S.Nonempty := by
    refine ⟨(q - 1) * q ^ k, ?_⟩
    refine ⟨fun _ => (q - 1) * q ^ k, ?_, by simp⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i; have h1 : 0 < q ^ k := Nat.pow_pos (by omega)
      have h2 : 0 < q - 1 := by omega
      have : 0 < (q - 1) * q ^ k := Nat.mul_pos h2 h1
      simpa using this
    · intro i; exact ⟨q ^ k, rfl⟩
    · -- AddNoCarry q [k-1, (q - 1)*q ^ k]
      intro e
      rw [hofn1]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have h1 : qdigit q (k - 1) e ≤ q - 1 := by
        rw [qdigit_eq _ _ _ hq2]; have := Nat.mod_lt ((k - 1) / q ^ e) (by omega : 0 < q); omega
      have h2 : qdigit q ((q - 1) * q ^ k) e = if e = k then q - 1 else 0 := by
        rw [qdigit_eq _ _ _ hq2]; exact digit_special q k e hq2
      have h3 : qdigit q (k - 1) k = 0 := by
        rw [qdigit_eq _ _ _ hq2, Nat.div_eq_of_lt hLlt]; simp
      rcases eq_or_ne e k with he | he
      · subst he; rw [h2, if_pos rfl, h3]; omega
      · rw [h2, if_neg he]; omega
  -- The infimum is attained: extract a minimizer.
  have hmem : sInf S ∈ S := Nat.sInf_mem hne
  obtain ⟨m, hmT, hval⟩ := hmem
  obtain ⟨hpos, hdvd, hnc⟩ := hmT
  -- s q 1 k - 1 = (k - 1) + (m 0), with [k-1, m 0] carry-free.
  have hsval : s q 1 k = k + sInf S := by
    unfold s; simp [hS]
  -- objective for Fin 1 is m 0
  have hv0 : sInf S = m 0 := by
    rw [hval]; simp
  refine ⟨by simp, ?_⟩
  -- the binomial: n = s q 1 k - 1, r = k - 1, n - r = m 0
  have hn : s q 1 k + 0 - 1 = (k - 1) + m 0 := by
    rw [hsval, hv0]; omega
  rw [hn]
  -- apply Kummer
  apply not_dvd_choose q ((k - 1) + m 0) (k - 1) hq (by omega)
  intro i
  have hsub : ((k - 1) + m 0) - (k - 1) = m 0 := by omega
  rw [hsub]
  -- carry-free of [k-1, m 0] gives the per-position digit bound
  apply noCarry_mod q (k - 1) (m 0) i (by omega)
  intro e he
  have hh := hnc e
  rw [hofn1] at hh
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hh
  rw [qdigit_eq _ _ _ hq2, qdigit_eq _ _ _ hq2] at hh
  exact hh

/-- Carry-free addition is digit-additive (fact D2): if at every position the
base-`q` digits of `a` and `b` sum to `≤ q-1`, then the truncated sums agree. -/
theorem add_mod_eq (q a b i : ℕ) (hq : 1 < q)
    (h : ∀ e, e < i → (a / q ^ e % q) + (b / q ^ e % q) ≤ q - 1) :
    (a + b) % q ^ i = a % q ^ i + b % q ^ i := by
  have hlt := noCarry_mod q a b i hq h
  conv_lhs => rw [Nat.add_mod]
  rw [Nat.mod_eq_of_lt hlt]

/-- Digit additivity (fact D2): if `a` and `b` add without carry in every base-`q`
position, then each digit of `a + b` is the sum of the corresponding digits. -/
theorem qdigit_add (q a b e : ℕ) (hq : 2 ≤ q)
    (h : ∀ f, (a / q ^ f % q) + (b / q ^ f % q) ≤ q - 1) :
    (a + b) / q ^ e % q = a / q ^ e % q + b / q ^ e % q := by
  have hdig : ∀ x : ℕ, x / q ^ e % q = x % (q ^ e * q) / q ^ e := fun x =>
    (Nat.mod_mul_right_div_self x (q ^ e) q).symm
  have hpe1 : q ^ (e + 1) = q ^ e * q := by rw [pow_succ]
  rw [hdig (a+b), hdig a, hdig b, ← hpe1]
  have h1 : (a + b) % q ^ (e + 1) = a % q ^ (e + 1) + b % q ^ (e + 1) :=
    add_mod_eq q a b (e + 1) (by omega) (fun f _ => h f)
  rw [h1]
  have hsplit : ∀ x : ℕ, x % q ^ (e + 1) = x % q ^ e + q ^ e * (x / q ^ e % q) := by
    intro x; rw [hpe1]; exact Nat.mod_mul
  rw [hsplit a, hsplit b]
  have hpos : 0 < q ^ e := Nat.pow_pos (by omega)
  have hae : a % q ^ e < q ^ e := Nat.mod_lt _ hpos
  have hbe : b % q ^ e < q ^ e := Nat.mod_lt _ hpos
  have hlow : a % q ^ e + b % q ^ e < q ^ e :=
    noCarry_mod q a b e (by omega) (fun f _ => h f)
  set da := a / q ^ e % q
  set db := b / q ^ e % q
  have e1 : (a % q ^ e + q ^ e * da) / q ^ e = da := by
    rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hae]; ring_nf
  have e2 : (b % q ^ e + q ^ e * db) / q ^ e = db := by
    rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hbe]; ring_nf
  have e3 : (a % q ^ e + q ^ e * da + (b % q ^ e + q ^ e * db)) / q ^ e = da + db := by
    have : a % q ^ e + q ^ e * da + (b % q ^ e + q ^ e * db)
         = (a % q ^ e + b % q ^ e) + q ^ e * (da + db) := by ring
    rw [this, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlow]; ring_nf
  rw [e1, e2, e3]

/-- The objective value set for `TSet q d (k - 1)` is nonempty: an explicit witness
places each coordinate at a distinct high power `(q - 1)·q ^ (k+i)`, which is positive,
divisible by `q-1`, and carry-free with `k-1` (the powers are distinct and exceed
`log_q (k - 1)`). This generalises the `Fin 1` nonemptiness in `main_zero_mem`. -/
theorem tset_value_nonempty (q d k : ℕ) (hq : 2 ≤ q) (hk : 0 < k) :
    {v : ℕ | ∃ m ∈ TSet q d (k - 1), v = ∑ i : Fin d, (i.val + 1) * m i}.Nonempty := by
  classical
  set m : Fin d → ℕ := fun i => (q - 1) * q ^ (k + i.val) with hm
  refine ⟨∑ i : Fin d, (i.val + 1) * m i, m, ?_, rfl⟩
  have hLlt : k - 1 < q ^ k := by
    calc k - 1 < k := by omega
      _ ≤ q ^ k := Nat.le_of_lt (Nat.lt_pow_self (by omega))
  refine ⟨?_, ?_, ?_⟩
  · intro i; have h1 : 0 < q ^ (k + i.val) := Nat.pow_pos (by omega)
    have : 0 < (q - 1) * q ^ (k+i.val) := Nat.mul_pos (by omega) h1
    simpa [hm] using this
  · intro i; exact ⟨q ^ (k+i.val), by rw [hm]⟩
  · intro e
    rw [List.map_cons, List.sum_cons, List.map_ofFn, List.sum_ofFn]
    have hmd : ∀ i : Fin d,
        ((fun x => qdigit q x e) ∘ m) i = if e = k + i.val then q - 1 else 0 := by
      intro i; simp only [Function.comp_apply]; rw [hm]; simp only
      rw [qdigit_eq _ _ _ hq, digit_special q (k+i.val) e hq]
    rw [Finset.sum_congr rfl (fun i _ => hmd i)]
    have hsum : (∑ i : Fin d, (if e = k + i.val then q-1 else 0)) ≤ q - 1 := by
      rcases Nat.lt_or_ge e k with h | h
      · have : ∀ i : Fin d, (if e = k + i.val then (q - 1) else 0) = 0 := by
          intro i; rw [if_neg (by omega)]
        simp [this]
      · by_cases hd : e - k < d
        · rw [Finset.sum_eq_single (⟨e-k, hd⟩ : Fin d)]
          · rw [if_pos (by simp; omega)]
          · intro j _ hj; rw [if_neg]; intro hc; apply hj; ext; simp at hc ⊢; omega
          · intro hcon; exact absurd (Finset.mem_univ _) hcon
        · have : ∀ i : Fin d, (if e = k + i.val then (q - 1) else 0) = 0 := by
            intro i; rw [if_neg (by omega)]
          simp [this]
    have hk1 : qdigit q (k - 1) e ≤ q - 1 := by
      rw [qdigit_eq _ _ _ hq]; have := Nat.mod_lt ((k - 1)/q ^ e) (by omega : 0 < q); omega
    rcases Nat.lt_or_ge e k with h | h
    · have hz : (∑ i : Fin d, (if e = k + i.val then (q - 1) else 0)) = 0 := by
        have : ∀ i : Fin d, (if e = k + i.val then (q - 1) else 0) = 0 := by
          intro i; rw [if_neg (by omega)]
        simp [this]
      rw [hz]; omega
    · have hk1z : qdigit q (k - 1) e = 0 := by
        rw [qdigit_eq _ _ _ hq]
        have hlt : k - 1 < q ^ e := lt_of_lt_of_le hLlt (Nat.pow_le_pow_right (by omega) h)
        rw [Nat.div_eq_of_lt hlt]; simp
      rw [hk1z]; simpa using hsum

/-- Minimizer extraction: since the objective value set is nonempty, its `sInf`
is attained by some `m ∈ TSet q d (k - 1)`, giving the value identity for `s`. -/
theorem s_minimizer (q d k : ℕ) (hq : 2 ≤ q) (hk : 0 < k) :
    ∃ m ∈ TSet q d (k - 1), s q d k = d * k + ∑ i : Fin d, (i.val + 1) * m i := by
  have hne := tset_value_nonempty q d k hq hk
  obtain ⟨m, hmT, hval⟩ := Nat.sInf_mem hne
  exact ⟨m, hmT, by unfold s; rw [← hval]⟩

/-
The proof rests on two pillars, isolated as `composition_identity` and
`extraction_strict` below. Both follow from the reciprocal slot formula
(informal.tex Thm. thm:H2-slot-formula): letting `M` be the multiset of
available digit slots of `k-1` (value `q ^ e` with multiplicity `q-1-a_e`), with
block sums `β_r` over consecutive groups of `n = q-1` smallest slots,
  s_d(k) = d·k + Φ_d(M),   where Φ_d(M) := d·β₁ + (d-1)·β₂ + ⋯ + β_d.        (★)
Pillar 1 (`composition_identity`): F(0) = s_{d-1}(s_1(k)) + s_1(k) = s_d(k).
Pillar 2 (`extraction_strict`): for admissible j > 0, s_d(k) < F(j);
admissibility (via Kummer/Lucas) makes `u = β₁ + j` add to `k-1` carry-free,
and `u > β₁` gives strictness.
-/

/-- Easy direction of the composition identity:
`s_d(k) ≤ s_{d-1}(s_1(k)) + s_1(k)`. Constructive: combine a minimizer `μ₁` for
`s_1` (placed at top weight `d`) with a minimizer of `s_{d-1}` at argument
`s_1(k)`; the combined tuple lies in `TSet q d (k - 1)`. -/
theorem comp_id_le (q : ℕ) (hq : q.Prime) (d k : ℕ) (hd : 1 < d) (hk : 0 < k) :
    s q d k ≤ s q (d - 1) (s q 1 k) + s q 1 k := by
  have hq2 : 2 ≤ q := hq.two_le
  -- write d = d' + 1
  obtain ⟨d', rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hd' : 1 ≤ d' := by omega
  -- minimizer for s q 1 k : gives μ := m₁ 0 with [k-1, μ] carry-free and s₁ = k + μ
  obtain ⟨m₁, hm₁T, hm₁val⟩ := s_minimizer q 1 k hq2 hk
  obtain ⟨hpos₁, hdvd₁, hnc₁⟩ := hm₁T
  set μ := m₁ 0 with hμ
  have hofn1 : List.ofFn m₁ = [m₁ 0] := by simp [List.ofFn_succ, List.ofFn_zero]
  have hs1 : s q 1 k = k + μ := by rw [hm₁val]; simp [hμ]
  have hs1pos : 0 < s q 1 k := by rw [hs1]; omega
  have hsm1 : s q 1 k - 1 = (k - 1) + μ := by rw [hs1]; omega
  -- per-position carry-free of [k-1, μ]
  have hcf1 : ∀ e, qdigit q (k - 1) e + qdigit q μ e ≤ q - 1 := by
    intro e
    have := hnc₁ e
    rw [hofn1] at this
    simpa [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hμ] using this
  -- minimizer for s q d' (s q 1 k)
  obtain ⟨mν, hmνT, hmνval⟩ := s_minimizer q d' (s q 1 k) hq2 hs1pos
  obtain ⟨hposν, hdvdν, hncν⟩ := hmνT
  rw [hsm1] at hncν
  -- build the d-tuple by snoc'ing μ at the top weight
  set m : Fin (d'+1) → ℕ := Fin.snoc mν μ with hmdef
  have hmem : m ∈ TSet q (d'+1) (k - 1) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · rw [hmdef, Fin.snoc_last]; rw [hμ]; exact hpos₁ 0
      · intro j; rw [hmdef, Fin.snoc_castSucc]; exact hposν j
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · rw [hmdef, Fin.snoc_last]; rw [hμ]; exact hdvd₁ 0
      · intro j; rw [hmdef, Fin.snoc_castSucc]; exact hdvdν j
    · intro e
      rw [List.map_cons, List.sum_cons, List.map_ofFn, List.sum_ofFn,
          Fin.sum_univ_castSucc]
      simp only [hmdef, Fin.snoc_castSucc, Fin.snoc_last, Function.comp_apply]
      have hν := hncν e
      rw [List.map_cons, List.sum_cons, List.map_ofFn, List.sum_ofFn] at hν
      -- digit additivity: qdigit((k - 1)+μ, e) = qdigit(k-1,e) + qdigit(μ,e)
      have hadd : qdigit q ((k - 1)+μ) e = qdigit q (k - 1) e + qdigit q μ e := by
        rw [qdigit_eq _ _ _ hq2, qdigit_eq _ _ _ hq2, qdigit_eq _ _ _ hq2]
        exact qdigit_add q (k - 1) μ e hq2 (fun f => by
          have := hcf1 f; rw [qdigit_eq _ _ _ hq2, qdigit_eq _ _ _ hq2] at this; exact this)
      rw [hadd] at hν
      simp only [Function.comp_apply] at hν ⊢
      omega
  -- objective value of the constructed tuple
  have hobj : ∑ i : Fin (d'+1), (i.val + 1) * m i
      = (∑ i : Fin d', (i.val + 1) * mν i) + (d'+1) * μ := by
    rw [Fin.sum_univ_castSucc]
    congr 1
    · apply Finset.sum_congr rfl; intro i _
      rw [hmdef, Fin.snoc_castSucc, Fin.val_castSucc]
    · rw [hmdef, Fin.snoc_last, Fin.val_last]
  -- bound s q (d'+1) k by the constructed objective
  have hbound : s q (d'+1) k ≤ (d'+1) * k + ∑ i : Fin (d'+1), (i.val + 1) * m i := by
    unfold s
    refine Nat.add_le_add_left (Nat.sInf_le ?_) _
    exact ⟨m, hmem, rfl⟩
  -- final algebra
  rw [hmνval, hs1]
  rw [hobj] at hbound
  calc s q (d'+1) k
      ≤ (d'+1)*k + (∑ i : Fin d', (i.val+1)*mν i + (d'+1)*μ) := hbound
    _ = (d' * (k + μ) + ∑ i : Fin d', (i.val+1)*mν i) + (k + μ) := by ring

/-
Slot-list machinery for the slot formula. `M` is made concrete as `slotList q k1 L`:
in increasing order of value, position `e < L` contributes `(q - 1) - qdigit q k1 e`
copies of `q ^ e`. Since `q ^ e` increases with `e`, the list is sorted ascending, so
blocks of `n = q-1` smallest slots are consecutive windows, and the block
functional `Φ_d` is a weighted sum of block sums. The truncation `L` (via
`slotLen`) is chosen large enough to contain all slots used by relevant tuples.
-/

/-- The list of available base-`q` digit slots of `k1`, truncated to positions
`< L`, listed in INCREASING order of value: position `e` contributes
`(q - 1) - qdigit q k1 e` copies of `q ^ e`. Sorted ascending since `q ^ e` is
increasing in `e`. -/
def slotList (q k1 L : ℕ) : List ℕ :=
  (List.range L).flatMap (fun e => List.replicate ((q - 1) - qdigit q k1 e) (q ^ e))

/-- The sum of the `r`-th block of `n = q-1` smallest slots (1-indexed block `r`):
the slots at list positions `[(r-1)*n, r*n)`. -/
def blockSum (q k1 L r : ℕ) : ℕ :=
  ((slotList q k1 L).drop ((r - 1) * (q - 1))).take (q - 1) |>.sum

/-- The block functional `Φ_d(M) = d·β₁ + (d-1)·β₂ + ⋯ + 1·β_d`
(`β_r = blockSum … r`). -/
def Phi (q k1 d L : ℕ) : ℕ :=
  ∑ r ∈ Finset.range d, (d - r) * blockSum q k1 L (r + 1)

/-- A truncation length large enough to contain every slot used by any tuple in
`TSet q d (k - 1)` realizing the minimum. -/
def slotLen (q d k : ℕ) : ℕ :=
  if q = q then k + d * (k + 1) + 1 else k + d * (k + 1) + 1

/-- `slotList` is monotone in the truncation length: a larger `L` only appends
more slots. -/
theorem slotList_prefix (q k1 L₁ L₂ : ℕ) (h : L₁ ≤ L₂) :
    ∃ t, slotList q k1 L₂ = slotList q k1 L₁ ++ t := by
  unfold slotList
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.flatMap_append]; exact ⟨_, rfl⟩

/-- Digits of `k1` beyond position `k1` (in fact beyond `log_q k1`) vanish. -/
theorem qdigit_zero_of_ge (q k1 e : ℕ) (hq : 2 ≤ q) (he : k1 + 1 ≤ e) :
    qdigit q k1 e = 0 := by
  unfold qdigit
  apply List.getD_eq_default
  have : (Nat.digits q k1).length ≤ k1 + 1 := by
    rcases eq_or_ne k1 0 with rfl | hk0
    · simp
    · rw [Nat.length_digits q k1 hq hk0]; have := Nat.log_le_self q k1; omega
  omega

/-- Lower bound on the length of `slotList`: positions `e ∈ [k1+1, L)` each
contribute `q-1` slots (since the digits of `k1` vanish there). -/
theorem slotList_length_ge (q k1 L : ℕ) (hq : 2 ≤ q) :
    (q - 1) * (L - (k1 + 1)) ≤ (slotList q k1 L).length := by
  unfold slotList
  rw [List.length_flatMap]
  simp only [List.length_replicate]
  have hsub : Finset.Ico (k1 + 1) L ⊆ Finset.range L := by
    intro x hx; simp only [Finset.mem_Ico] at hx; simp only [Finset.mem_range]; omega
  calc (q - 1) * (L - (k1 + 1))
      = ∑ _e ∈ Finset.Ico (k1 + 1) L, (q - 1) := by
          rw [Finset.sum_const, Nat.card_Ico]; ring
    _ = ∑ e ∈ Finset.Ico (k1 + 1) L, ((q - 1) - qdigit q k1 e) := by
          apply Finset.sum_congr rfl; intro e he; simp only [Finset.mem_Ico] at he
          rw [qdigit_zero_of_ge q k1 e hq (by omega), Nat.sub_zero]
    _ ≤ ∑ e ∈ Finset.range L, ((q - 1) - qdigit q k1 e) :=
          Finset.sum_le_sum_of_subset hsub

/-- `blockSum` is independent of the truncation length once `L` is large enough
to contain the first `r` blocks. -/
theorem blockSum_Lindep (q k1 L₁ L₂ r : ℕ) (h : L₁ ≤ L₂) (hr : 1 ≤ r)
    (hlen : r * (q - 1) ≤ (slotList q k1 L₁).length) :
    blockSum q k1 L₂ r = blockSum q k1 L₁ r := by
  unfold blockSum
  obtain ⟨t, ht⟩ := slotList_prefix q k1 L₁ L₂ h
  rw [ht]
  have heq : (r - 1) * (q - 1) + (q - 1) = r * (q - 1) := by
    cases r with | zero => omega | succ m => simp; ring
  rw [List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by rw [List.length_drop]; omega)]

/-- (L3, pure reindexing) Split off the first block of `Φ_d`:
`Φ_d(M) = d·β₁ + ∑_{r<d-1} (d-1-r)·β_{r+2}`. -/
theorem Phi_split (q k1 d L : ℕ) (hd : 1 ≤ d) :
    Phi q k1 d L = d * blockSum q k1 L 1
      + ∑ r ∈ Finset.range (d - 1), (d - 1 - r) * blockSum q k1 L (r + 2) := by
  unfold Phi
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [Nat.add_sub_cancel, Nat.sub_zero]
  rw [Nat.add_comm]
  congr 1
  apply Finset.sum_congr rfl; intro r hr; simp only [Finset.mem_range] at hr
  have h1 : e + 1 - (r + 1) = e - r := by omega
  have h2 : r + 1 + 1 = r + 2 := by ring
  rw [h1, h2]

-- Recurrence for `slotList`: appending the slots at position `Lx`.
theorem slotList_succ (q k1 Lx : ℕ) :
    slotList q k1 (Lx+1)
      = slotList q k1 Lx ++ List.replicate ((q - 1) - qdigit q k1 Lx) (q ^ Lx) := by
  unfold slotList
  rw [List.range_succ, List.flatMap_append]; simp

-- Length of `slotList` as a sum of slot multiplicities.
theorem slotList_length (q k1 Lx : ℕ) :
    (slotList q k1 Lx).length = ∑ e ∈ Finset.range Lx, ((q - 1) - qdigit q k1 e) := by
  induction Lx with
  | zero => simp [slotList]
  | succ n ih =>
    rw [slotList_succ, List.length_append, List.length_replicate, Finset.sum_range_succ, ih]

-- `slotList` length is monotone in the truncation length.
theorem slotList_length_mono (q k1 : ℕ) {a b : ℕ} (h : a ≤ b) :
    (slotList q k1 a).length ≤ (slotList q k1 b).length := by
  rw [slotList_length, slotList_length]
  apply Finset.sum_le_sum_of_subset
  intro x hx; simp only [Finset.mem_range] at hx ⊢; omega

-- Sum of `slotList`: the base-`q` value contributed by all slots.
theorem slotList_sum (q k1 L : ℕ) :
    (slotList q k1 L).sum = ∑ e ∈ Finset.range L, ((q - 1) - qdigit q k1 e) * q ^ e := by
  induction L with
  | zero => simp [slotList]
  | succ L ih =>
    rw [slotList_succ, List.sum_append, ih, Finset.sum_range_succ, List.sum_replicate]
    simp [Nat.mul_comm]

-- Greedy structure of `take n`: the first `n` slots are all slots up to some
-- position `p`, plus a residual `r` slots at position `p`.
theorem slotList_take (q k1 L : ℕ) :
    ∀ n, n ≤ (slotList q k1 L).length →
      ∃ p, p ≤ L ∧ ∃ r, (slotList q k1 L).take n = slotList q k1 p ++ List.replicate r (q ^ p)
        ∧ (slotList q k1 p).length + r = n ∧ r ≤ (q - 1) - qdigit q k1 p := by
  induction L with
  | zero =>
    intro n hn
    simp only [slotList, List.range_zero, List.flatMap_nil, List.length_nil, Nat.le_zero] at hn
    subst hn
    refine ⟨0, le_refl _, 0, ?_, ?_, by omega⟩ <;> simp [slotList]
  | succ L ih =>
    intro n hn
    rw [slotList_succ] at hn ⊢
    rw [List.length_append, List.length_replicate] at hn
    by_cases hcase : n ≤ (slotList q k1 L).length
    · obtain ⟨p, hpL, r, htake, hlen, hr⟩ := ih n hcase
      refine ⟨p, by omega, r, ?_, hlen, hr⟩
      rw [List.take_append_of_le_length hcase]; exact htake
    · push Not at hcase
      refine ⟨L, by omega, n - (slotList q k1 L).length, ?_, by omega, by omega⟩
      rw [List.take_append]
      rw [List.take_of_length_le (by omega)]
      congr 1
      rw [List.take_replicate]
      congr 1
      omega

-- `take` of `c·n` slots equals the sum of the first `c` blocks.
theorem take_blocks (q k1 L c : ℕ) :
    ((slotList q k1 L).take (c * (q - 1))).sum
      = ∑ r ∈ Finset.range c, blockSum q k1 L (r+1) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold blockSum
    simp only [Nat.add_sub_cancel]
    have hn : (c + 1)*(q - 1) = c*(q - 1) + (q - 1) := by ring
    rw [hn, List.take_add, List.sum_append]

-- Abel-summation swap identity for the block functional.
theorem abel_swap (d : ℕ) (b : ℕ → ℕ) :
    ∑ r ∈ Finset.range d, (d - r) * b (r + 1)
      = ∑ c ∈ Finset.range d, ∑ r ∈ Finset.range (c + 1), b (r+1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ (f := fun c => ∑ r ∈ Finset.range (c + 1), b (r+1)), ← ih]
    rw [Finset.sum_range_succ (f := fun r => (d+1-r) * b (r+1))]
    have hcong : ∀ r ∈ Finset.range d, (d+1-r) * b (r+1) = (d-r) * b (r+1) + b (r+1) := by
      intro r hr; simp only [Finset.mem_range] at hr
      have : d + 1 - r = (d-r) + 1 := by omega
      rw [this]; ring
    rw [Finset.sum_congr rfl hcong, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ (f := fun r => b (r+1))]
    have h1 : d + 1 - d = 1 := by omega
    rw [h1, Nat.one_mul]
    ring

/-- Abel reformulation of `Φ_d(M)`: the layer-cake identity
`Φ_d(M) = ∑_{c<d} (sum of the smallest (c + 1)·n slots)`. -/
theorem Phi_eq_take_sum (q k1 d L : ℕ) :
    Phi q k1 d L = ∑ c ∈ Finset.range d, ((slotList q k1 L).take ((c + 1) * (q - 1))).sum := by
  unfold Phi
  rw [abel_swap d (fun r => blockSum q k1 L r)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [take_blocks]

-- Pure arithmetic greedy core: the smallest `m = ∑_{e<p} s_e + r` slots
-- (values `q ^ e`) have the least value among any selection `b` with `b e ≤ s e`
-- and total count `≥ m`.
theorem greedy_core (q p L : ℕ) (hq : 2 ≤ q) (hpL : p ≤ L)
    (b s : ℕ → ℕ) (r : ℕ)
    (hbs : ∀ e, e < L → b e ≤ s e)
    (hcount : (∑ e ∈ Finset.range p, s e) + r ≤ ∑ e ∈ Finset.range L, b e) :
    (∑ e ∈ Finset.range p, s e * q ^ e) + r * q ^ p ≤ ∑ e ∈ Finset.range L, b e * q ^ e := by
  have hsplit : Finset.range L = Finset.range p ∪ Finset.Ico p L := by
    ext e
    simp
    omega
  have hdisj : Disjoint (Finset.range p) (Finset.Ico p L) := by
    rw [Finset.range_eq_Ico]; exact Finset.Ico_disjoint_Ico_consecutive 0 p L
  set A := ∑ e ∈ Finset.range p, b e * q ^ e with hA
  have hRHS : ∑ e ∈ Finset.range L, b e * q ^ e
      = A + ∑ e ∈ Finset.Ico p L, b e * q ^ e := by
    rw [hsplit, Finset.sum_union hdisj]
  have hIco : (∑ e ∈ Finset.Ico p L, b e) * q ^ p ≤ ∑ e ∈ Finset.Ico p L, b e * q ^ e := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro e he; simp only [Finset.mem_Ico] at he
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_right (by omega) he.1
  have hLHSsplit : ∑ e ∈ Finset.range p, s e * q ^ e
      = A + ∑ e ∈ Finset.range p, (s e - b e) * q ^ e := by
    rw [hA, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro e he; simp only [Finset.mem_range] at he
    have := hbs e (by omega)
    rw [← Nat.add_mul]; congr 1; omega
  have hupper : ∑ e ∈ Finset.range p, (s e - b e) * q ^ e
      ≤ (∑ e ∈ Finset.range p, (s e - b e)) * q ^ p := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro e he; simp only [Finset.mem_range] at he
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hcountIco : (∑ e ∈ Finset.range p, (s e - b e)) + r ≤ ∑ e ∈ Finset.Ico p L, b e := by
    have hb_le_s : ∑ e ∈ Finset.range p, b e ≤ ∑ e ∈ Finset.range p, s e := by
      apply Finset.sum_le_sum
      intro e he
      simp only [Finset.mem_range] at he
      exact hbs e (by omega)
    have hsubsum : ∑ e ∈ Finset.range p, (s e - b e)
        = (∑ e ∈ Finset.range p, s e) - ∑ e ∈ Finset.range p, b e := by
      rw [← Finset.sum_tsub_distrib]
      intro e he
      simp only [Finset.mem_range] at he
      exact hbs e (by omega)
    have hLsplit2 : ∑ e ∈ Finset.range L, b e
        = (∑ e ∈ Finset.range p, b e) + ∑ e ∈ Finset.Ico p L, b e := by
      rw [hsplit, Finset.sum_union hdisj]
    rw [hsubsum]
    omega
  rw [hRHS, hLHSsplit]
  have hpp : 1 ≤ q ^ p := Nat.one_le_pow _ _ (by omega)
  calc A + ∑ e ∈ Finset.range p, (s e - b e) * q ^ e + r * q ^ p
      ≤ A + (∑ e ∈ Finset.range p, (s e - b e)) * q ^ p + r * q ^ p := by
        have := hupper; omega
    _ = A + ((∑ e ∈ Finset.range p, (s e - b e)) + r) * q ^ p := by ring
    _ ≤ A + (∑ e ∈ Finset.Ico p L, b e) * q ^ p := by
        apply Nat.add_le_add_left
        exact Nat.mul_le_mul_right _ hcountIco
    _ ≤ A + ∑ e ∈ Finset.Ico p L, b e * q ^ e := by
        apply Nat.add_le_add_left hIco

/-- Bridge: the value of the smallest `m` slots of `M(k - 1)` is at most any `N`
that adds to `k-1` without carry and whose total slot count (digit sum) is `≥ m`.
The greedy/exchange argument in closed arithmetic form. -/
theorem slot_value_le (q d k : ℕ) (hq : 2 ≤ q) (N m : ℕ)
    (hcarry : ∀ e, qdigit q (k - 1) e + qdigit q N e ≤ q - 1)
    (hm_len : m ≤ (slotList q (k - 1) (slotLen q d k)).length)
    (hcount : m ≤ ∑ e ∈ Finset.range (slotLen q d k + N + 1), qdigit q N e) :
    ((slotList q (k - 1) (slotLen q d k)).take m).sum ≤ N := by
  set k1 := k - 1 with hk1
  set Ls := slotLen q d k with hLs
  set L' := slotLen q d k + N + 1 with hL'
  obtain ⟨p, hpL, r, htake, hlen, hr⟩ := slotList_take q k1 Ls m hm_len
  -- value of the smallest m slots
  have hval : ((slotList q k1 Ls).take m).sum
      = (∑ e ∈ Finset.range p, ((q - 1) - qdigit q k1 e) * q ^ e) + r * q ^ p := by
    rw [htake, List.sum_append, List.sum_replicate, slotList_sum]
    simp [Nat.mul_comm]
  rw [hval]
  -- N as a truncated base-q expansion
  have hNlt : N < q ^ L' := by
    calc N < q ^ N := Nat.lt_pow_self (by omega)
      _ ≤ q ^ L' := Nat.pow_le_pow_right (by omega) (by omega)
  have hNexp : ∑ e ∈ Finset.range L', qdigit q N e * q ^ e = N := by
    have h1 : N % q ^ L' = ∑ e ∈ Finset.range L', (N / q ^ e % q) * q ^ e := digit_mod q N L'
    rw [Nat.mod_eq_of_lt hNlt] at h1
    rw [show (∑ e ∈ Finset.range L', qdigit q N e * q ^ e)
          = ∑ e ∈ Finset.range L', (N / q ^ e % q) * q ^ e from
        Finset.sum_congr rfl (fun e _ => by rw [qdigit_eq _ _ _ hq])]
    exact h1.symm
  rw [← hNexp]
  -- apply greedy_core
  apply greedy_core q p L' hq (by omega)
    (fun e => qdigit q N e) (fun e => (q - 1) - qdigit q k1 e) r
  · intro e _; have := hcarry e; omega
  · -- ∑_{e<p} s_e + r ≤ ∑_{e<L'} qdigit N e
    have hpcount : (∑ e ∈ Finset.range p, ((q - 1) - qdigit q k1 e)) + r = m := by
      rw [← slotList_length q k1 p]; omega
    rw [hpcount]; exact hcount

-- Finite-family digit additivity: if a family adds without carry then each digit
-- of the sum is the sum of the digits.
theorem qdigit_sum {ι : Type*} (q : ℕ) (hq : 2 ≤ q) (I : Finset ι) (f : ι → ℕ)
    (h : ∀ e, ∑ i ∈ I, qdigit q (f i) e ≤ q - 1) :
    ∀ e, qdigit q (∑ i ∈ I, f i) e = ∑ i ∈ I, qdigit q (f i) e := by
  classical
  induction I using Finset.induction with
  | empty => intro e; simp [qdigit, Nat.digits_zero]
  | insert a s ha ih =>
    have hsub : ∀ g, ∑ i ∈ s, qdigit q (f i) g ≤ q - 1 := by
      intro g; have := h g; rw [Finset.sum_insert ha] at this; omega
    have iheq := ih hsub
    intro e
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hcf : ∀ g, (f a / q ^ g % q) + ((∑ i ∈ s, f i) / q ^ g % q) ≤ q - 1 := by
      intro g
      have hsg := h g; rw [Finset.sum_insert ha] at hsg
      rw [← qdigit_eq _ _ _ hq, ← qdigit_eq _ _ _ hq, iheq g]
      exact hsg
    rw [qdigit_eq _ _ _ hq, qdigit_add q (f a) (∑ i ∈ s, f i) e hq hcf]
    rw [← qdigit_eq _ _ _ hq, ← qdigit_eq _ _ _ hq, iheq e]

-- `∑ d_e q ^ e ≡ ∑ d_e  (mod q-1)`, since `q ≡ 1 (mod q-1)`.
theorem sum_pow_modEq (q L : ℕ) (hq : 2 ≤ q) (d : ℕ → ℕ) :
    ∑ e ∈ Finset.range L, d e * q ^ e ≡ ∑ e ∈ Finset.range L, d e [MOD (q - 1)] := by
  have hpow : ∀ e, q ^ e ≡ 1 [MOD (q - 1)] := by
    intro e
    have h0 : (q - 1) ≡ 0 [MOD (q - 1)] := (Nat.modEq_zero_iff_dvd).mpr dvd_rfl
    have h1 : q ≡ 1 [MOD (q - 1)] := by
      calc q = (q - 1) + 1 := by omega
        _ ≡ 0 + 1 [MOD (q - 1)] := Nat.ModEq.add_right 1 h0
        _ = 1 := by ring
    calc q ^ e ≡ 1 ^ e [MOD (q - 1)] := h1.pow e
      _ = 1 := one_pow e
  induction L with
  | zero => simp [Nat.ModEq.refl]
  | succ L ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hh : d L * q ^ L ≡ d L * 1 [MOD (q - 1)] := Nat.ModEq.mul_left _ (hpow L)
    rw [Nat.mul_one] at hh
    exact Nat.ModEq.add ih hh

-- The digit sum (slot count) of a positive multiple of `q-1` is at least `q-1`.
theorem digitsum_ge (q x L : ℕ) (hq : 2 ≤ q) (hdvd : (q - 1) ∣ x) (hpos : 0 < x)
    (hxL : x < q ^ L) :
    q - 1 ≤ ∑ e ∈ Finset.range L, qdigit q x e := by
  have hexp : x = ∑ e ∈ Finset.range L, qdigit q x e * q ^ e := by
    have h1 : x % q ^ L = ∑ e ∈ Finset.range L, (x / q ^ e % q) * q ^ e := digit_mod q x L
    rw [Nat.mod_eq_of_lt hxL] at h1
    rw [show (∑ e ∈ Finset.range L, qdigit q x e * q ^ e)
          = ∑ e ∈ Finset.range L, (x / q ^ e % q) * q ^ e from
        Finset.sum_congr rfl (fun e _ => by rw [qdigit_eq _ _ _ hq])]
    exact h1
  have hmod : x ≡ ∑ e ∈ Finset.range L, qdigit q x e [MOD (q - 1)] := by
    conv_lhs => rw [hexp]
    exact sum_pow_modEq q L hq (fun e => qdigit q x e)
  have hSdvd : (q - 1) ∣ ∑ e ∈ Finset.range L, qdigit q x e :=
    (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).mpr hdvd))
  have hSpos : 0 < ∑ e ∈ Finset.range L, qdigit q x e := by
    by_contra hc
    push Not at hc
    have hz : ∑ e ∈ Finset.range L, qdigit q x e = 0 := by omega
    have hx0 : x = 0 := by
      rw [hexp]
      apply Finset.sum_eq_zero
      intro e he
      have : qdigit q x e = 0 := Finset.sum_eq_zero_iff.mp hz e he
      rw [this]; ring
    omega
  exact Nat.le_of_dvd hSpos hSdvd

-- Reindexing the objective `∑ (i+1)·m_i` as a sum over weight levels: the `c`-th
-- level groups the top `c+1` coordinates `{i : d-1-c ≤ i}`.
theorem rhs_reindex (d : ℕ) (m : Fin d → ℕ) :
    ∑ i : Fin d, (i.val + 1) * m i
      = ∑ c ∈ Finset.range d,
          ∑ i ∈ Finset.univ.filter (fun i : Fin d => d - 1 - c ≤ i.val), m i := by
  have hinner : ∀ c ∈ Finset.range d,
      ∑ i ∈ Finset.univ.filter (fun i : Fin d => d - 1 - c ≤ i.val), m i
        = ∑ i : Fin d, (if d - 1 - c ≤ i.val then m i else 0) := by
    intro c _; rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter, Finset.sum_const]
  have hcard : (Finset.range d |>.filter (fun c => d - 1 - c ≤ i.val)).card = i.val + 1 := by
    have hsub : (Finset.range d).filter (fun c => d - 1 - c ≤ i.val)
        = Finset.Ico (d - 1 - i.val) d := by
      ext c; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      have hi : i.val < d := i.isLt
      omega
    rw [hsub, Nat.card_Ico]
    have hi : i.val < d := i.isLt
    omega
  rw [hcard, smul_eq_mul, Nat.mul_comm]

/-- Optimality lower bound (the `≥` half of the slot formula): every tuple in
`TSet q d (k - 1)` has objective at least `Φ_d(M)` (informal.tex Lem. H2-block-min).
Proof idea: reindex the objective by weight levels and bound each level by the
greedy bound `slot_value_le`. -/
theorem slot_lower_bound (q d k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    (m : Fin d → ℕ) (hm : m ∈ TSet q d (k - 1)) :
    Phi q (k - 1) d (slotLen q d k) ≤ ∑ i : Fin d, (i.val + 1) * m i := by
  classical
  obtain ⟨hmpos, hmdvd, hnc⟩ := hm
  set k1 := k - 1 with hk1
  set Ls := slotLen q d k with hLs
  -- carry-free, per position: qdigit k1 e + ∑_i qdigit (m i) e ≤ q-1
  have hcf : ∀ e, qdigit q k1 e + ∑ i : Fin d, qdigit q (m i) e ≤ q - 1 := by
    intro e
    have := hnc e
    rw [List.map_cons, List.sum_cons, List.map_ofFn, List.sum_ofFn] at this
    simpa [Function.comp] using this
  -- rewrite both sides
  rw [Phi_eq_take_sum, rhs_reindex]
  apply Finset.sum_le_sum
  intro c hc
  simp only [Finset.mem_range] at hc
  -- the subset of top (c + 1) coordinates and its sum
  set I : Finset (Fin d) := Finset.univ.filter (fun i : Fin d => d - 1 - c ≤ i.val) with hI
  set N : ℕ := ∑ i ∈ I, m i with hN
  -- carry-free for the subfamily
  have hsubcf : ∀ e, ∑ i ∈ I, qdigit q (m i) e ≤ q - 1 := by
    intro e
    refine le_trans (Finset.sum_le_sum_of_subset (Finset.subset_univ I)) ?_
    have := hcf e; omega
  -- digit of N
  have hNdig : ∀ e, qdigit q N e = ∑ i ∈ I, qdigit q (m i) e :=
    qdigit_sum q hq I m hsubcf
  -- |I| = c+1
  have hIcard : I.card = c + 1 := by
    rw [hI, Finset.card_filter]
    rw [Fin.sum_univ_eq_sum_range (fun j => if d - 1 - c ≤ j then 1 else 0) d]
    rw [← Finset.card_filter]
    have heq : (Finset.range d).filter (fun j => d - 1 - c ≤ j) = Finset.Ico (d - 1 - c) d := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [heq, Nat.card_Ico]; omega
  -- apply the bridge
  refine slot_value_le q d k hq N ((c + 1) * (q - 1)) ?_ ?_ ?_
  · -- hcarry
    intro e
    rw [hNdig e]
    have hthis := hcf e
    have hmono : ∑ i ∈ I, qdigit q (m i) e ≤ ∑ i : Fin d, qdigit q (m i) e :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ I)
    calc qdigit q k1 e + ∑ i ∈ I, qdigit q (m i) e
        ≤ qdigit q k1 e + ∑ i : Fin d, qdigit q (m i) e := by
          exact Nat.add_le_add_left hmono _
      _ ≤ q - 1 := hthis
  · -- hm_len
    have hb := slotList_length_ge q k1 Ls hq
    have hk1k : k1 + 1 = k := by omega
    rw [hk1k] at hb
    have hLval : Ls = k + d * (k + 1) + 1 := by simp [hLs, slotLen]
    have hdd : d ≤ d * (k + 1) := Nat.le_mul_of_pos_right d (by omega)
    have hcd : c + 1 ≤ d := by omega
    calc (c + 1) * (q - 1) = (q - 1) * (c + 1) := by ring
      _ ≤ (q - 1) * (Ls - k) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ (slotList q k1 Ls).length := hb
  · -- hcount
    have hNexpand : ∑ e ∈ Finset.range (Ls + N + 1), qdigit q N e
        = ∑ i ∈ I, ∑ e ∈ Finset.range (Ls + N + 1), qdigit q (m i) e := by
      rw [show (∑ e ∈ Finset.range (Ls + N + 1), qdigit q N e)
            = ∑ e ∈ Finset.range (Ls + N + 1), ∑ i ∈ I, qdigit q (m i) e from
          Finset.sum_congr rfl (fun e _ => hNdig e)]
      rw [Finset.sum_comm]
    rw [hNexpand]
    -- each coordinate contributes ≥ q-1
    have hterm : ∀ i ∈ I, q - 1 ≤ ∑ e ∈ Finset.range (Ls + N + 1), qdigit q (m i) e := by
      intro i hiI
      have hmiN : m i ≤ N := by
        rw [hN]; exact Finset.single_le_sum (fun j _ => Nat.zero_le _) hiI
      have hmilt : m i < q ^ (Ls + N + 1) := by
        calc m i ≤ N := hmiN
          _ < q ^ N := Nat.lt_pow_self (by omega)
          _ ≤ q ^ (Ls + N + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      exact digitsum_ge q (m i) (Ls + N + 1) hq (hmdvd i) (hmpos i) hmilt
    calc (c + 1) * (q - 1) = I.card * (q - 1) := by rw [hIcard]
      _ = ∑ _i ∈ I, (q - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ I, ∑ e ∈ Finset.range (Ls + N + 1), qdigit q (m i) e :=
          Finset.sum_le_sum hterm


/-- The `f`-th base-`q` digit of a bounded expansion `∑_{e<m} coeff e · q ^ e`
is `coeff f`. -/
theorem digit_of_sum_aux (q : ℕ) (hq : 2 ≤ q) (m : ℕ) (coeff : ℕ → ℕ)
    (hc : ∀ e, e < m → coeff e < q) (f : ℕ) (hf : f < m) :
    (∑ e ∈ Finset.range m, coeff e * q ^ e) / q ^ f % q = coeff f := by
  have hqpos : 0 < q := by omega
  have hsplit : ∑ e ∈ Finset.range m, coeff e * q ^ e
      = (∑ e ∈ Finset.range f, coeff e * q ^ e) + coeff f * q ^ f
        + (∑ e ∈ Finset.Ico (f + 1) m, coeff e * q ^ e) := by
    have h1 : Finset.range m = Finset.range (f + 1) ∪ Finset.Ico (f + 1) m := by
      ext e
      simp
      omega
    rw [h1, Finset.sum_union (by
      rw [Finset.range_eq_Ico]; apply Finset.Ico_disjoint_Ico_consecutive)]
    rw [Finset.sum_range_succ]
  rw [hsplit]
  have hlow : ∑ e ∈ Finset.range f, coeff e * q ^ e < q ^ f := by
    have hb : ∑ e ∈ Finset.range f, coeff e * q ^ e ≤ q ^ f - 1 := by
      calc ∑ e ∈ Finset.range f, coeff e * q ^ e
          ≤ ∑ e ∈ Finset.range f, (q - 1) * q ^ e := by
            apply Finset.sum_le_sum; intro e he
            apply Nat.mul_le_mul_right; have := hc e (by simp at he; omega); omega
        _ = (q - 1) * ∑ e ∈ Finset.range f, q ^ e := by rw [Finset.mul_sum]
        _ = q ^ f - 1 := geom_pred q f (by omega)
    have : 1 ≤ q ^ f := Nat.one_le_pow _ _ hqpos
    omega
  have hhigh : q ^ (f + 1) ∣ ∑ e ∈ Finset.Ico (f + 1) m, coeff e * q ^ e := by
    apply Finset.dvd_sum; intro e he; simp only [Finset.mem_Ico] at he
    exact Dvd.dvd.mul_left (pow_dvd_pow q (by omega)) _
  obtain ⟨t, ht⟩ := hhigh
  rw [ht]
  have hpf : 0 < q ^ f := Nat.pow_pos hqpos
  rw [show (∑ e ∈ Finset.range f, coeff e * q ^ e) + coeff f * q ^ f + q ^ (f + 1)*t
        = (∑ e ∈ Finset.range f, coeff e * q ^ e) + q ^ f * (coeff f + q*t) by rw [pow_succ]; ring]
  rw [Nat.add_mul_div_left _ _ hpf, Nat.div_eq_of_lt hlow, Nat.zero_add]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (hc f hf)

theorem sum_lt_pow_aux (q : ℕ) (hq : 2 ≤ q) (m : ℕ) (coeff : ℕ → ℕ)
    (hc : ∀ e, e < m → coeff e < q) :
    (∑ e ∈ Finset.range m, coeff e * q ^ e) < q ^ m := by
  have hb : ∑ e ∈ Finset.range m, coeff e * q ^ e ≤ q ^ m - 1 := by
    calc ∑ e ∈ Finset.range m, coeff e * q ^ e
        ≤ ∑ e ∈ Finset.range m, (q - 1) * q ^ e := by
          apply Finset.sum_le_sum; intro e he
          apply Nat.mul_le_mul_right; have := hc e (by simp at he; omega); omega
      _ = (q - 1) * ∑ e ∈ Finset.range m, q ^ e := by rw [Finset.mul_sum]
      _ = q ^ m - 1 := geom_pred q m (by omega)
  have : 1 ≤ q ^ m := Nat.one_le_pow _ _ (by omega)
  omega

theorem qdigit_le_aux (q k1 e : ℕ) (hq : 2 ≤ q) : qdigit q k1 e ≤ q - 1 := by
  rw [qdigit_eq _ _ _ hq]; have := Nat.mod_lt (k1 / q ^ e) (by omega : 0 < q); omega

theorem list_map_range_sum (n : ℕ) (g : ℕ → ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem wsum_eq (q L : ℕ) (hq : 2 ≤ q) (w : List ℕ)
    (hpow : ∀ x ∈ w, ∃ e, e < L ∧ x = q ^ e) :
    w.sum = ∑ e ∈ Finset.range L, (w.count (q ^ e)) * q ^ e := by
  induction w with
  | nil => simp
  | cons a t ih =>
    have hpowt : ∀ x ∈ t, ∃ e, e < L ∧ x = q ^ e := fun x hx => hpow x (by simp [hx])
    obtain ⟨ea, heaL, haeq⟩ := hpow a (by simp)
    rw [List.sum_cons, ih hpowt]
    have hcount : ∀ e, (a :: t).count (q ^ e) = (if e = ea then 1 else 0) + t.count (q ^ e) := by
      intro e
      rw [List.count_cons]
      have heq : (if a = q ^ e then 1 else 0) = (if e = ea then 1 else 0) := by
        by_cases h : e = ea
        · subst h; rw [haeq]; simp
        · rw [if_neg h, if_neg]
          rw [haeq]
          intro hcontra
          exact h (Nat.pow_right_injective hq hcontra.symm)
      have hbeq : (if (a == q ^ e) = true then 1 else 0) = (if a = q ^ e then 1 else 0) := by
        simp [beq_iff_eq]
      omega
    have hrw : ∑ e ∈ Finset.range L, (a :: t).count (q ^ e) * q ^ e
        = (∑ e ∈ Finset.range L, (if e = ea then 1 else 0) * q ^ e)
          + ∑ e ∈ Finset.range L, t.count (q ^ e) * q ^ e := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      rw [hcount e, Nat.add_mul]
    have hfirst : ∑ e ∈ Finset.range L, (if e = ea then 1 else 0) * q ^ e = a := by
      rw [Finset.sum_eq_single ea]
      · simp [haeq]
      · intro b _ hb; rw [if_neg hb]; ring
      · intro hcontra; exact absurd (Finset.mem_range.mpr heaL) hcontra
    rw [hrw, hfirst]

theorem qdigit_window (q L : ℕ) (hq : 2 ≤ q) (w : List ℕ)
    (hpow : ∀ x ∈ w, ∃ e, e < L ∧ x = q ^ e)
    (hlt : ∀ e, w.count (q ^ e) < q) (f : ℕ) :
    qdigit q w.sum f = if f < L then w.count (q ^ f) else 0 := by
  rw [qdigit_eq _ _ _ hq, wsum_eq q L hq w hpow]
  by_cases hf : f < L
  · rw [if_pos hf]
    exact digit_of_sum_aux q hq L (fun e => w.count (q ^ e)) (fun e _ => hlt e) f hf
  · rw [if_neg hf]
    have hbound : (∑ e ∈ Finset.range L, (w.count (q ^ e)) * q ^ e) < q ^ L :=
      sum_lt_pow_aux q hq L (fun e => w.count (q ^ e)) (fun e _ => hlt e)
    have hle : q ^ L ≤ q ^ f := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.div_eq_of_lt (by omega), Nat.zero_mod]

theorem slotList_pow (q k1 L : ℕ) : ∀ x ∈ slotList q k1 L, ∃ e, e < L ∧ x = q ^ e := by
  intro x hx
  unfold slotList at hx
  rw [List.mem_flatMap] at hx
  obtain ⟨e, he, hx2⟩ := hx
  rw [List.mem_replicate] at hx2
  rw [List.mem_range] at he
  exact ⟨e, he, hx2.2⟩

theorem slotList_count (q k1 L : ℕ) (hq : 2 ≤ q) (e : ℕ) (he : e < L) :
    (slotList q k1 L).count (q ^ e) = (q - 1) - qdigit q k1 e := by
  unfold slotList
  rw [List.count_flatMap]
  change ((List.range L).map
      (List.count (q ^ e) ∘
        (fun e' => List.replicate ((q - 1) - qdigit q k1 e') (q ^ e')))).sum = _
  rw [list_map_range_sum]
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb
    simp only [Function.comp_apply, List.count_replicate]
    rw [if_neg]
    simp only [beq_iff_eq]
    intro hcontra
    exact hb (Nat.pow_right_injective hq hcontra)
  · intro hcontra; exact absurd (Finset.mem_range.mpr he) hcontra

theorem take_blocks_count {α : Type*} [BEq α] (L : List α) (n c : ℕ) (x : α) :
    ∑ s ∈ Finset.range c, ((L.drop (s * n)).take n).count x = (L.take (c * n)).count x := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show (c + 1)*n = c*n + n from by ring, List.take_add, List.count_append]

theorem window_len {α : Type*} (L : List α) (a n : ℕ) (h : a + n ≤ L.length) :
    ((L.drop a).take n).length = n := by
  rw [List.length_take, List.length_drop]
  omega

theorem pow_sum_modEq (q : ℕ) (hq : 2 ≤ q) (w : List ℕ)
    (hpow : ∀ x ∈ w, ∃ e, x = q ^ e) :
    w.sum ≡ w.length [MOD (q - 1)] := by
  induction w with
  | nil => simp [Nat.ModEq.refl]
  | cons a t ih =>
    have hpowt : ∀ x ∈ t, ∃ e, x = q ^ e := fun x hx => hpow x (by simp [hx])
    obtain ⟨ea, haeq⟩ := hpow a (by simp)
    rw [List.sum_cons, List.length_cons]
    have hq1 : q ≡ 1 [MOD (q - 1)] := by
      have h0 : (q - 1) ≡ 0 [MOD (q - 1)] := (Nat.modEq_zero_iff_dvd).mpr dvd_rfl
      calc q = (q - 1) + 1 := by omega
        _ ≡ 0 + 1 [MOD (q - 1)] := Nat.ModEq.add_right 1 h0
        _ = 1 := by ring
    have ha1 : a ≡ 1 [MOD (q - 1)] := by
      rw [haeq]; calc q ^ ea ≡ 1 ^ ea [MOD (q - 1)] := hq1.pow ea
        _ = 1 := one_pow ea
    calc a + t.sum ≡ 1 + t.length [MOD (q - 1)] := Nat.ModEq.add ha1 (ih hpowt)
      _ = t.length + 1 := by ring

/-- Optimality upper bound (the `≤` half of the slot formula): the tuple sending
the `r`-th smallest block to the coordinate of weight `d-r+1` lies in
`TSet q d (k - 1)` and has objective exactly `Φ_d(M)`. -/
theorem slot_upper_bound (q d k : ℕ) (hq : 2 ≤ q) (hk : 0 < k) :
    sInf {v : ℕ | ∃ m ∈ TSet q d (k - 1), v = ∑ i : Fin d, (i.val + 1) * m i}
      ≤ Phi q (k - 1) d (slotLen q d k) := by
  classical
  set k1 := k - 1 with hk1
  set L := slotLen q d k with hLdef
  -- length lower bound
  have hlen : d * (q - 1) ≤ (slotList q k1 L).length := by
    have hb := slotList_length_ge q k1 L hq
    have hk1k : k1 + 1 = k := by omega
    rw [hk1k] at hb
    have hLval : L = k + d * (k + 1) + 1 := by simp [hLdef, slotLen]
    have hdd : d ≤ d * (k + 1) := Nat.le_mul_of_pos_right d (by omega)
    have hd1 : d ≤ L - k := by omega
    calc d * (q - 1) = (q - 1) * d := by ring
      _ ≤ (q - 1) * (L - k) := Nat.mul_le_mul_left _ hd1
      _ ≤ (slotList q k1 L).length := hb
  -- the witness
  set m : Fin d → ℕ := fun i => blockSum q k1 L (d - i.val) with hm
  -- window for coordinate i
  have hmwin : ∀ i : Fin d,
      m i =
        (((slotList q k1 L).drop ((d - 1 - i.val) * (q - 1))).take (q - 1)).sum := by
    intro i
    have hi : i.val < d := i.isLt
    have hoffeq : (d - i.val) - 1 = d - 1 - i.val := by omega
    simp only [hm, blockSum, hoffeq]
  -- offset bound: (d - 1 - i.val)*(q - 1) + (q - 1) ≤ length
  have hoff : ∀ i : Fin d, (d - 1 - i.val) * (q - 1) + (q - 1) ≤ (slotList q k1 L).length := by
    intro i
    have hi : i.val < d := i.isLt
    calc (d - 1 - i.val) * (q - 1) + (q - 1) = (d - i.val) * (q - 1) := by
          rw [← Nat.succ_mul]; congr 1; omega
      _ ≤ d * (q - 1) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (slotList q k1 L).length := hlen
  -- each window is a list of powers q ^ e with e < L
  have hWpow : ∀ i : Fin d,
      ∀ x ∈ (((slotList q k1 L).drop ((d - 1 - i.val) * (q - 1))).take (q - 1)),
        ∃ e, e < L ∧ x = q ^ e := by
    intro i x hx
    have hsub : x ∈ slotList q k1 L := by
      have h1 : x ∈ (slotList q k1 L).drop ((d - 1 - i.val) * (q - 1)) :=
        List.mem_of_mem_take hx
      exact List.mem_of_mem_drop h1
    exact slotList_pow q k1 L x hsub
  -- window count ≤ slotList count
  have hWcount : ∀ i : Fin d, ∀ x,
      (((slotList q k1 L).drop ((d - 1 - i.val) * (q - 1))).take (q - 1)).count x
        ≤ (slotList q k1 L).count x := by
    intro i x
    apply List.Sublist.count_le
    exact (List.take_sublist _ _).trans (List.drop_sublist _ _)
  -- window length is q-1
  have hWlen : ∀ i : Fin d,
      (((slotList q k1 L).drop ((d - 1 - i.val) * (q - 1))).take (q - 1)).length
        = q - 1 := by
    intro i; exact window_len _ _ _ (hoff i)
  -- carry-free per position e: total count over coordinates ≤ count in slotList
  have hcountsum : ∀ e,
      (∑ i : Fin d,
        (((slotList q k1 L).drop ((d - 1 - i.val) * (q - 1))).take (q - 1)).count
          (q ^ e))
      ≤ (slotList q k1 L).count (q ^ e) := by
    intro e
    -- reindex i ↦ s = d-1-i.val to range d, use take_blocks_count
    have hreindex :
        (∑ i : Fin d,
          (((slotList q k1 L).drop ((d - 1 - i.val) * (q - 1))).take (q - 1)).count
            (q ^ e))
          = ∑ s ∈ Finset.range d,
              (((slotList q k1 L).drop (s * (q - 1))).take (q - 1)).count (q ^ e) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun i =>
          (((slotList q k1 L).drop ((d - 1 - i) * (q - 1))).take (q - 1)).count
            (q ^ e)) d]
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro s hs; simp only [Finset.mem_range] at hs
      have hse : d - 1 - (d - 1 - s) = s := by omega
      rw [hse]
    rw [hreindex, take_blocks_count]
    apply List.Sublist.count_le
    exact List.take_sublist _ _
  -- count of any power in slotList is < q
  have hSltq : ∀ e', (slotList q k1 L).count (q ^ e') < q := by
    intro e'
    by_cases he' : e' < L
    · rw [slotList_count q k1 L hq e' he']; omega
    · have : (slotList q k1 L).count (q ^ e') = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        obtain ⟨e, heL, hxe⟩ := slotList_pow q k1 L _ hmem
        have : e' = e := Nat.pow_right_injective hq hxe
        omega
      omega
  -- digit of m i at position e
  have hmdig : ∀ (i : Fin d) (e : ℕ), qdigit q (m i) e
      = if e < L then
          (((slotList q k1 L).drop ((d - 1 - i.val) * (q - 1))).take (q - 1)).count
            (q ^ e)
        else 0 := by
    intro i e
    rw [hmwin i]
    refine qdigit_window q L hq _ (hWpow i) ?_ e
    intro e'
    exact lt_of_le_of_lt (hWcount i (q ^ e')) (hSltq e')
  -- membership in TSet
  have hmem : m ∈ TSet q d k1 := by
    refine ⟨?_, ?_, ?_⟩
    · -- 0 < m i
      intro i
      rw [hmwin i]
      have hne : ((slotList q k1 L).drop ((d - 1 - i.val) * (q - 1))).take (q - 1) ≠ [] := by
        rw [← List.length_pos_iff_ne_nil, hWlen i]; omega
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨e, _, hxe⟩ := hWpow i x hx
      have hxpos : 0 < x := by rw [hxe]; exact Nat.pow_pos (by omega)
      exact lt_of_lt_of_le hxpos (List.le_sum_of_mem hx)
    · -- (q - 1) ∣ m i
      intro i
      rw [hmwin i]
      have hmod := pow_sum_modEq q hq _ (fun x hx => by
        obtain ⟨e, _, hxe⟩ := hWpow i x hx; exact ⟨e, hxe⟩)
      rw [hWlen i] at hmod
      exact (Nat.modEq_zero_iff_dvd).mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))
    · -- AddNoCarry
      intro e
      rw [List.map_cons, List.sum_cons, List.map_ofFn, List.sum_ofFn]
      simp only [Function.comp]
      have hsum : ∑ i : Fin d, qdigit q (m i) e
          ≤ (q - 1) - qdigit q k1 e := by
        by_cases he : e < L
        · have heq : ∀ i : Fin d, qdigit q (m i) e
              =
                (((slotList q k1 L).drop ((d - 1 - i.val) * (q - 1))).take
                  (q - 1)).count (q ^ e) := by
            intro i; rw [hmdig i e, if_pos he]
          rw [Finset.sum_congr rfl (fun i _ => heq i)]
          rw [← slotList_count q k1 L hq e he]
          exact hcountsum e
        · have hz : ∀ i : Fin d, qdigit q (m i) e = 0 := by
            intro i; rw [hmdig i e, if_neg he]
          rw [Finset.sum_congr rfl (fun i _ => hz i), Finset.sum_const, smul_eq_mul, Nat.mul_zero]
          exact Nat.zero_le _
      have hk1le : qdigit q k1 e ≤ q - 1 := qdigit_le_aux q k1 e hq
      omega
  -- objective equals Phi
  have hobj : ∑ i : Fin d, (i.val + 1) * m i = Phi q k1 d L := by
    have hstep : ∑ i : Fin d, (i.val + 1) * m i
        = ∑ j ∈ Finset.range d, (j + 1) * blockSum q k1 L (d - j) := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => (j + 1) * blockSum q k1 L (d - j)) d]
    rw [hstep]
    unfold Phi
    rw [← Finset.sum_range_reflect (fun r => (d - r) * blockSum q k1 L (r + 1)) d]
    apply Finset.sum_congr rfl
    intro j hj; simp only [Finset.mem_range] at hj
    have h1 : d - 1 - j + 1 = d - j := by omega
    have h2 : d - (d - 1 - j) = j + 1 := by omega
    rw [h1, h2]
  exact Nat.sInf_le ⟨m, hmem, hobj.symm⟩

/-- **The reciprocal slot formula** `s_d(k) = d·k + Φ_d(M)`. Assembled by
antisymmetry from `slot_lower_bound` (every value `≥ Φ_d`, hence `sInf ≥ Φ_d`)
and `slot_upper_bound` (`sInf ≤ Φ_d`). -/
theorem slot_formula (q d k : ℕ) (hq : 2 ≤ q) (hk : 0 < k) :
    s q d k = d * k + Phi q (k - 1) d (slotLen q d k) := by
  unfold s
  refine congrArg (d * k + ·) (le_antisymm (slot_upper_bound q d k hq hk) ?_)
  -- sInf ≥ Φ: every element of the value set is ≥ Φ (slot_lower_bound), and the
  -- set is nonempty (tset_value_nonempty), so its sInf is ≥ Φ.
  apply le_csInf (tset_value_nonempty q d k hq hk)
  rintro v ⟨m, hm, rfl⟩
  exact slot_lower_bound q d k hq hk m hm

/-- (L1) The `d=1` corollary `s_1(k) = k + β₁`: the slot formula at `d=1` gives
`Φ_1(M) = β₁` (the smallest block sum). -/
theorem s_one_eq (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k) :
    s q 1 k = k + blockSum q (k - 1) (slotLen q 1 k) 1 := by
  rw [slot_formula q 1 k hq hk]
  simp [Phi]

/-- Dropping the first `(slotList q k1 p).length + r` slots: the result is a
flatMap with the slots at positions `< p` removed, `r` removed at position `p`,
and all positions `> p` intact. -/
theorem slotList_drop (q k1 p r : ℕ)
    (hr : r ≤ (q - 1) - qdigit q k1 p) :
    ∀ Lx, (slotList q k1 Lx).drop ((slotList q k1 p).length + r)
      = (List.range Lx).flatMap (fun e =>
          List.replicate (if e < p then 0 else if e = p then ((q - 1)-qdigit q k1 p) - r
            else (q - 1)-qdigit q k1 e) (q ^ e)) := by
  intro Lx
  by_cases hLx : Lx ≤ p
  · have hlen : (slotList q k1 Lx).length ≤ (slotList q k1 p).length :=
      slotList_length_mono q k1 hLx
    rw [List.drop_eq_nil_of_le (by omega)]
    symm
    rw [List.flatMap_eq_nil_iff]
    intro e he; simp only [List.mem_range] at he
    rw [if_pos (by omega)]; simp
  · push Not at hLx
    set g : ℕ → List ℕ := fun e =>
      List.replicate (if e < p then 0 else if e = p then ((q - 1)-qdigit q k1 p) - r
        else (q - 1)-qdigit q k1 e) (q ^ e) with hg
    have hrange :
        List.range Lx =
          List.range (p + 1) ++ (List.range (Lx - (p + 1))).map ((p + 1) + ·) := by
      conv_lhs => rw [show Lx = (p + 1) + (Lx - (p + 1)) by omega]
      rw [List.range_add]
    have htail : ((List.range (Lx-(p + 1))).map ((p + 1) + ·)).flatMap
          (fun e => List.replicate ((q - 1)-qdigit q k1 e) (q ^ e))
        = ((List.range (Lx-(p + 1))).map ((p + 1) + ·)).flatMap g := by
      apply List.flatMap_congr
      intro e he
      simp only [List.mem_map, List.mem_range] at he
      obtain ⟨a, _, rfl⟩ := he
      rw [hg]; simp only
      rw [if_neg (by omega), if_neg (by omega)]
    have hLHS :
        slotList q k1 Lx =
          (slotList q k1 p ++ List.replicate ((q - 1)-qdigit q k1 p) (q ^ p))
        ++ ((List.range (Lx-(p + 1))).map ((p + 1) + ·)).flatMap
            (fun e => List.replicate ((q - 1)-qdigit q k1 e) (q ^ e)) := by
      conv_lhs => unfold slotList
      rw [hrange, List.flatMap_append]
      congr 1
      rw [← slotList_succ]; rfl
    have hRHS : (List.range Lx).flatMap g
        = List.replicate (((q - 1)-qdigit q k1 p) - r) (q ^ p)
          ++ ((List.range (Lx-(p + 1))).map ((p + 1) + ·)).flatMap g := by
      rw [hrange, List.flatMap_append]
      congr 1
      rw [List.range_succ, List.flatMap_append]
      have hhead : (List.range p).flatMap g = [] := by
        rw [List.flatMap_eq_nil_iff]
        intro e he; simp only [List.mem_range] at he
        rw [hg]; simp only; rw [if_pos he]; simp
      rw [hhead, List.nil_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [hg]; simp
    rw [hLHS, hRHS, htail]
    rw [List.drop_append_of_le_length (by simp; omega)]
    rw [List.drop_append]
    rw [List.drop_eq_nil_of_le (by omega), List.nil_append]
    rw [List.drop_replicate]
    congr 2
    omega

-- Digit extraction from a base-`q` expansion with bounded coefficients.
theorem digit_of_sum (q : ℕ) (hq : 2 ≤ q) (m : ℕ) (coeff : ℕ → ℕ)
    (hc : ∀ e, e < m → coeff e < q) (f : ℕ) (hf : f < m) :
    (∑ e ∈ Finset.range m, coeff e * q ^ e) / q ^ f % q = coeff f := by
  have hqpos : 0 < q := by omega
  have hsplit : ∑ e ∈ Finset.range m, coeff e * q ^ e
      = (∑ e ∈ Finset.range f, coeff e * q ^ e) + coeff f * q ^ f
        + (∑ e ∈ Finset.Ico (f + 1) m, coeff e * q ^ e) := by
    have h1 : Finset.range m = Finset.range (f + 1) ∪ Finset.Ico (f + 1) m := by
      ext e
      simp
      omega
    rw [h1, Finset.sum_union (by
      rw [Finset.range_eq_Ico]; apply Finset.Ico_disjoint_Ico_consecutive)]
    rw [Finset.sum_range_succ]
  rw [hsplit]
  have hlow : ∑ e ∈ Finset.range f, coeff e * q ^ e < q ^ f := by
    have hb : ∑ e ∈ Finset.range f, coeff e * q ^ e ≤ q ^ f - 1 := by
      calc ∑ e ∈ Finset.range f, coeff e * q ^ e
          ≤ ∑ e ∈ Finset.range f, (q - 1) * q ^ e := by
            apply Finset.sum_le_sum; intro e he
            apply Nat.mul_le_mul_right; have := hc e (by simp at he; omega); omega
        _ = (q - 1) * ∑ e ∈ Finset.range f, q ^ e := by rw [Finset.mul_sum]
        _ = q ^ f - 1 := geom_pred q f (by omega)
    have : 1 ≤ q ^ f := Nat.one_le_pow _ _ hqpos
    omega
  have hhigh : q ^ (f + 1) ∣ ∑ e ∈ Finset.Ico (f + 1) m, coeff e * q ^ e := by
    apply Finset.dvd_sum; intro e he; simp only [Finset.mem_Ico] at he
    exact Dvd.dvd.mul_left (pow_dvd_pow q (by omega)) _
  obtain ⟨t, ht⟩ := hhigh
  rw [ht]
  have hpf : 0 < q ^ f := Nat.pow_pos hqpos
  rw [show (∑ e ∈ Finset.range f, coeff e * q ^ e) + coeff f * q ^ f + q ^ (f + 1)*t
        = (∑ e ∈ Finset.range f, coeff e * q ^ e) + q ^ f * (coeff f + q*t) by rw [pow_succ]; ring]
  rw [Nat.add_mul_div_left _ _ hpf, Nat.div_eq_of_lt hlow, Nat.zero_add]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (hc f hf)

-- A bounded base-`q` expansion of length `m` is `< q ^ m`.
theorem sum_lt_pow (q : ℕ) (hq : 2 ≤ q) (m : ℕ) (coeff : ℕ → ℕ)
    (hc : ∀ e, e < m → coeff e < q) :
    (∑ e ∈ Finset.range m, coeff e * q ^ e) < q ^ m := by
  have hb : ∑ e ∈ Finset.range m, coeff e * q ^ e ≤ q ^ m - 1 := by
    calc ∑ e ∈ Finset.range m, coeff e * q ^ e
        ≤ ∑ e ∈ Finset.range m, (q - 1) * q ^ e := by
          apply Finset.sum_le_sum; intro e he
          apply Nat.mul_le_mul_right; have := hc e (by simp at he; omega); omega
      _ = (q - 1) * ∑ e ∈ Finset.range m, q ^ e := by rw [Finset.mul_sum]
      _ = q ^ m - 1 := geom_pred q m (by omega)
  have : 1 ≤ q ^ m := Nat.one_le_pow _ _ (by omega)
  omega

-- A base-`q` digit is at most `q - 1`.
theorem qdigit_le (q k1 e : ℕ) (hq : 2 ≤ q) : qdigit q k1 e ≤ q - 1 := by
  rw [qdigit_eq _ _ _ hq]; have := Nat.mod_lt (k1 / q ^ e) (by omega : 0 < q); omega

-- The digits of `β = (slotList q k1 p).sum + r·q ^ p`: slot multiplicities below
-- `p`, the residual `r` at `p`, and `0` above `p`.
theorem beta_digit (q k1 p r : ℕ) (hq : 2 ≤ q)
    (hr : r ≤ (q - 1) - qdigit q k1 p) (f : ℕ) :
    qdigit q ((slotList q k1 p).sum + r * q ^ p) f
      = if f < p then (q - 1) - qdigit q k1 f else if f = p then r else 0 := by
  set β := (slotList q k1 p).sum + r * q ^ p with hβ
  set bcoeff : ℕ → ℕ := fun e => if e = p then r else (q - 1)-qdigit q k1 e with hbc
  have hβsum : β = ∑ e ∈ Finset.range (p + 1), bcoeff e * q ^ e := by
    rw [hβ, slotList_sum, Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl; intro e he; simp only [Finset.mem_range] at he
      rw [hbc]; simp only; rw [if_neg (by omega)]
    · rw [hbc]; simp
  have hcbound : ∀ e, e < p+1 → bcoeff e < q := by
    intro e he; rw [hbc]; simp only
    by_cases h : e = p
    · rw [if_pos h]; subst h; omega
    · rw [if_neg h]; omega
  rw [qdigit_eq _ _ _ hq, hβsum]
  by_cases hf : f < p+1
  · rw [digit_of_sum q hq (p + 1) bcoeff hcbound f hf]
    rw [hbc]; simp only
    by_cases h : f = p
    · rw [if_pos h]; subst h; rw [if_neg (by omega), if_pos rfl]
    · rw [if_neg h]; rw [if_pos (by omega)]
  · have hlt : (∑ e ∈ Finset.range (p + 1), bcoeff e * q ^ e) < q ^ (p + 1) :=
      sum_lt_pow q hq (p + 1) bcoeff hcbound
    have : (∑ e ∈ Finset.range (p + 1), bcoeff e * q ^ e) / q ^ f = 0 := by
      apply Nat.div_eq_of_lt
      calc (∑ e ∈ Finset.range (p + 1), bcoeff e * q ^ e) < q ^ (p + 1) := hlt
        _ ≤ q ^ f := Nat.pow_le_pow_right (by omega) (by omega)
    rw [this, Nat.zero_mod]
    rw [if_neg (by omega), if_neg (by omega)]

-- The new slot multiplicity of `k1 + β` at each position: positions `< p` are
-- spent (multiplicity `0`), position `p` loses `r`, positions `> p` are intact.
theorem newmult_eq (q k1 p r : ℕ) (hq : 2 ≤ q)
    (hr : r ≤ (q - 1) - qdigit q k1 p) (e : ℕ) :
    (q - 1) - qdigit q (k1 + ((slotList q k1 p).sum + r * q ^ p)) e
      = if e < p then 0
        else if e = p then ((q - 1)-qdigit q k1 p) - r
        else (q - 1)-qdigit q k1 e := by
  set β := (slotList q k1 p).sum + r * q ^ p with hβ
  have hcf : ∀ f, (k1 / q ^ f % q) + (β / q ^ f % q) ≤ q - 1 := by
    intro f
    rw [← qdigit_eq _ _ _ hq, ← qdigit_eq _ _ _ hq]
    rw [beta_digit q k1 p r hq hr f]
    have hk := qdigit_le q k1 f hq
    by_cases h1 : f < p
    · rw [if_pos h1]; omega
    · rw [if_neg h1]
      by_cases h2 : f = p
      · rw [if_pos h2]; subst h2; omega
      · rw [if_neg h2]; omega
  have hadd : qdigit q (k1 + β) e = qdigit q k1 e + qdigit q β e := by
    rw [qdigit_eq _ _ _ hq, qdigit_eq _ _ _ hq, qdigit_eq _ _ _ hq]
    exact qdigit_add q k1 β e hq hcf
  rw [hadd, beta_digit q k1 p r hq hr e]
  have hk := qdigit_le q k1 e hq
  by_cases h1 : e < p
  · rw [if_pos h1, if_pos h1]; omega
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : e = p
    · rw [if_pos h2, if_pos h2]; subst h2; omega
    · rw [if_neg h2, if_neg h2]; omega

/-- (L2, slot subtraction) The slot list of `k1 + β₁`, where `β₁` is the sum of
the `q-1` smallest slots of `k1`, equals the slot list of `k1` with its first
block removed: `M(k1 + β₁) = M(k1) \ B₁`. Adding `β₁` is carry-free and "spends"
exactly the digit positions occupied by the `q-1` smallest slots. -/
theorem slot_subtraction (q k1 L₀ : ℕ) (hq : 2 ≤ q)
    (hβ : (q - 1) ≤ (slotList q k1 L₀).length) :
    ∀ Lx : ℕ, slotList q (k1 + blockSum q k1 L₀ 1) Lx
      = (slotList q k1 Lx).drop (q - 1) := by
  obtain ⟨p, hpL, r, htake, hlen, hr⟩ := slotList_take q k1 L₀ (q - 1) hβ
  have hβval : blockSum q k1 L₀ 1 = (slotList q k1 p).sum + r * q ^ p := by
    unfold blockSum
    simp only [Nat.sub_self, Nat.zero_mul, List.drop_zero]
    rw [htake, List.sum_append, List.sum_replicate]
    simp
  intro Lx
  rw [hβval]
  have hnew : slotList q (k1 + ((slotList q k1 p).sum + r * q ^ p)) Lx
      = (List.range Lx).flatMap (fun e =>
          List.replicate (if e < p then 0 else if e = p then ((q - 1)-qdigit q k1 p) - r
            else (q - 1)-qdigit q k1 e) (q ^ e)) := by
    rw [show slotList q (k1 + ((slotList q k1 p).sum + r * q ^ p)) Lx
          = (List.range Lx).flatMap (fun e =>
              List.replicate
                ((q - 1)-qdigit q (k1 + ((slotList q k1 p).sum + r * q ^ p)) e)
                (q ^ e)) from rfl]
    apply List.flatMap_congr
    intro e _
    rw [newmult_eq q k1 p r hq hr e]
  rw [hnew]
  have hgoal : (slotList q k1 Lx).drop (q - 1)
      = (slotList q k1 Lx).drop ((slotList q k1 p).length + r) := by rw [hlen]
  rw [hgoal, slotList_drop q k1 p r hr Lx]

/-- (L2)+(L3) Layer-cake identity linking `Φ_d(M)` at argument `k` to
`Φ_{d-1}` at argument `s_1(k)` (whose slot set is `M \ B₁`):
`d·k + Φ_d(M(k - 1)) = (d-1)·s_1(k) + Φ_{d-1}(M(s_1(k)-1)) + s_1(k)`.
Combines (L1) `s_1(k)=k+β₁`, (L2) slot subtraction `M(s_1(k)-1)=M\B₁`, and
(L3) `Φ_d(M)=d·β₁+Φ_{d-1}(M\B₁)`; pure block-reindexing algebra. -/
theorem layer_cake (q d k : ℕ) (hq : 2 ≤ q) (hd : 1 < d) (hk : 0 < k) :
    d * k + Phi q (k - 1) d (slotLen q d k)
      = (d - 1) * s q 1 k + Phi q (s q 1 k - 1) (d - 1) (slotLen q (d - 1) (s q 1 k))
        + s q 1 k := by
  set k1 := k - 1 with hk1
  set s1 := s q 1 k with hs1def
  set L := slotLen q d k with hLdef
  set L' := slotLen q (d - 1) s1 with hL'def
  -- A common large truncation length dominating all three.
  set Lbig := slotLen q d k + slotLen q (d - 1) s1 + slotLen q 1 k + s1 with hLbigdef
  have hpos : 0 < q - 1 := by omega
  have hk1k : k1 + 1 = k := by omega
  -- length lower bounds at the relevant lengths
  have hlenL : d * (q - 1) ≤ (slotList q k1 L).length := by
    have hb := slotList_length_ge q k1 L hq
    rw [hk1k] at hb
    have hLval : L = k + d * (k + 1) + 1 := by simp [hLdef, slotLen]
    have hdd : d ≤ d * (k + 1) := Nat.le_mul_of_pos_right d (by omega)
    have hd1 : d ≤ L - k := by omega
    calc d * (q - 1) = (q - 1) * d := by ring
      _ ≤ (q - 1) * (L - k) := Nat.mul_le_mul_left _ hd1
      _ ≤ (slotList q k1 L).length := hb
  -- (L1) s1 = k + β, with β = blockSum at length L
  have hβ_one : blockSum q k1 (slotLen q 1 k) 1 = blockSum q k1 L 1 := by
    refine (blockSum_Lindep q k1 (slotLen q 1 k) L 1 ?_ ?_ ?_).symm
    · rw [hLdef]; simp [slotLen]; nlinarith [hk]
    · omega
    · have hb := slotList_length_ge q k1 (slotLen q 1 k) hq
      rw [hk1k] at hb
      have hge : 1 ≤ slotLen q 1 k - k := by simp [slotLen]; omega
      calc 1 * (q - 1) = (q - 1) := by ring
        _ ≤ (q - 1) * (slotLen q 1 k - k) := by nlinarith [hpos]
        _ ≤ (slotList q k1 (slotLen q 1 k)).length := hb
  set β := blockSum q k1 L 1 with hβdef
  have hL1 : s1 = k + β := by
    rw [hs1def]; rw [s_one_eq q k hq hk, hβ_one]
  have hsm1 : s1 - 1 = k1 + β := by rw [hL1]; omega
  -- (L2) slot subtraction: the slot list of (k1+β) is M with its first block dropped.
  have hL2 : ∀ Lx : ℕ, slotList q (s1 - 1) Lx = (slotList q k1 Lx).drop (q - 1) := by
    rw [hsm1]
    refine slot_subtraction q k1 L hq ?_
    have hd1 : 1 ≤ d := by omega
    calc q - 1 = 1 * (q - 1) := by ring
      _ ≤ d * (q - 1) := Nat.mul_le_mul_right _ hd1
      _ ≤ (slotList q k1 L).length := hlenL
  -- block-shift: block (r+1) of M(s1-1) = block (r+2) of M(k1)
  have hshift : ∀ r Lx : ℕ,
      blockSum q (s1 - 1) Lx (r + 1) = blockSum q k1 Lx (r + 2) := by
    intro r Lx
    unfold blockSum
    rw [hL2 Lx, List.drop_drop]
    have hidx : q - 1 + (r + 1 - 1) * (q - 1) = (r + 2 - 1) * (q - 1) := by
      have e1 : r + 1 - 1 = r := by omega
      have e2 : r + 2 - 1 = r + 1 := by omega
      rw [e1, e2]; ring
    rw [hidx]
  -- length bound for the s1-1 slot list at L'
  have hlenL' : (d - 1) * (q - 1) ≤ (slotList q (s1 - 1) L').length := by
    have hb := slotList_length_ge q (s1 - 1) L' hq
    have hLk : (s1 - 1) + 1 = s1 := by omega
    rw [hLk] at hb
    have hL'val : L' = s1 + (d - 1) * (s1 + 1) + 1 := by simp [hL'def, slotLen]
    have hge : (d - 1) ≤ L' - s1 := by
      have hdd : (d - 1) ≤ (d - 1) * (s1 + 1) := Nat.le_mul_of_pos_right (d - 1) (by omega)
      omega
    calc (d - 1) * (q - 1) = (q - 1) * (d - 1) := by ring
      _ ≤ (q - 1) * (L' - s1) := Nat.mul_le_mul_left _ hge
      _ ≤ (slotList q (s1 - 1) L').length := hb
  have hLLbig : L ≤ Lbig := by rw [hLbigdef, hLdef]; omega
  have hL'Lbig : L' ≤ Lbig := by rw [hLbigdef, hL'def]; omega
  -- Phi on the RHS rewritten via block-shift, then L-reconciled to use M(k1) at L
  have hRHSphi : Phi q (s1 - 1) (d - 1) L'
      = ∑ r ∈ Finset.range (d - 1), (d - 1 - r) * blockSum q k1 L (r + 2) := by
    unfold Phi
    apply Finset.sum_congr rfl
    intro r hr; simp only [Finset.mem_range] at hr
    congr 1
    -- blockSum q (s1-1) L' (r+1) = blockSum q k1 L (r+2)
    have step1 : blockSum q (s1 - 1) L' (r + 1) = blockSum q (s1 - 1) Lbig (r + 1) := by
      rw [blockSum_Lindep q (s1 - 1) L' Lbig (r + 1) hL'Lbig (by omega)]
      calc (r + 1) * (q - 1) ≤ (d - 1) * (q - 1) := by
            apply Nat.mul_le_mul_right; omega
        _ ≤ (slotList q (s1 - 1) L').length := hlenL'
    have step2 : blockSum q (s1 - 1) Lbig (r + 1) = blockSum q k1 Lbig (r + 2) :=
      hshift r Lbig
    have step3 : blockSum q k1 Lbig (r + 2) = blockSum q k1 L (r + 2) := by
      rw [blockSum_Lindep q k1 L Lbig (r + 2) hLLbig (by omega)]
      calc (r + 2) * (q - 1) ≤ d * (q - 1) := by
            apply Nat.mul_le_mul_right; omega
        _ ≤ (slotList q k1 L).length := hlenL
    rw [step1, step2, step3]
  -- (L3) split the LHS Phi
  have hL3 : Phi q k1 d L = d * β
      + ∑ r ∈ Finset.range (d - 1), (d - 1 - r) * blockSum q k1 L (r + 2) :=
    Phi_split q k1 d L (by omega)
  -- assemble
  rw [hsm1] at hRHSphi ⊢
  rw [hRHSphi, hL3]
  -- goal: d*k + (d*β + S) = (d-1)*s1 + S + s1, with s1 = k+β
  have hkey : d * k + d * β = (d - 1) * s1 + s1 := by
    have hd1 : d - 1 + 1 = d := by omega
    calc d * k + d * β = d * (k + β) := by ring
      _ = d * s1 := by rw [hL1]
      _ = (d - 1 + 1) * s1 := by rw [hd1]
      _ = (d - 1) * s1 + s1 := by ring
  omega


/-- Hard direction of the composition identity:
`s_{d-1}(s_1(k)) + s_1(k) ≤ s_d(k)`. Assembled from the slot formula on `s_d`
and `s_{d-1}` plus the `layer_cake` reindexing. -/
theorem comp_id_ge (q : ℕ) (hq : q.Prime) (d k : ℕ) (hd : 1 < d) (hk : 0 < k) :
    s q (d - 1) (s q 1 k) + s q 1 k ≤ s q d k := by
  have hq2 : 2 ≤ q := hq.two_le
  have hs1pos : 0 < s q 1 k := by
    -- s q 1 k = k + (something), and k > 0
    have := s_one_eq q k hq2 hk; omega
  -- slot formula on s_d(k) and on s_{d-1}(s_1(k))
  have hsd : s q d k = d * k + Phi q (k - 1) d (slotLen q d k) := slot_formula q d k hq2 hk
  have hsd1 : s q (d - 1) (s q 1 k)
      = (d - 1) * s q 1 k + Phi q (s q 1 k - 1) (d - 1) (slotLen q (d - 1) (s q 1 k)) :=
    slot_formula q (d - 1) (s q 1 k) hq2 hs1pos
  -- assemble via layer-cake
  rw [hsd, hsd1, layer_cake q d k hq2 hd hk]

/-- Pillar 1, the composition identity: `s_{d-1}(s_1(k)) + s_1(k) = s_d(k)`,
i.e. `F(0) = s_d(k)`. Antisymmetry of `comp_id_le` and `comp_id_ge`. -/
theorem composition_identity (q : ℕ) (hq : q.Prime) (d k : ℕ) (hd : 1 < d)
    (hk : 0 < k) :
    s q (d - 1) (s q 1 k) + s q 1 k = s q d k := by
  exact Nat.le_antisymm (comp_id_ge q hq d k hd hk) (comp_id_le q hq d k hd hk)

/-
Pillar 2 (extraction inequality): put `s1 = k + β` (`s_one_eq`) and `u = β + j`,
so `s1 + j = k + u` and `(q - 1) ∣ u`. Admissibility `j ∈ J` forces `u` to add to
`k-1` carry-free (converse Kummer, `dvd_choose_of_carry`). Applying
`slot_formula` to `s_d(k)` and `s_{d-1}(k+u)`, the goal `s_d(k) < F(j)` reduces
to the core inequality `Φ_d(M) < d·u + Φ_{d-1}(M\U)` (`extraction_core`),
strict because `u > β` when `j > 0`.
-/

-- Helper lemmas for `extraction_core` (the layer-cake / removal-bound argument).

/-- Length of a list of powers `q ^ e` (`e < L`) is the sum of its value-counts. -/
theorem wlen_eq (q L : ℕ) (hq : 2 ≤ q) (w : List ℕ)
    (hpow : ∀ x ∈ w, ∃ e, e < L ∧ x = q ^ e) :
    w.length = ∑ e ∈ Finset.range L, (w.count (q ^ e)) := by
  induction w with
  | nil => simp
  | cons a t ih =>
    have hpowt : ∀ x ∈ t, ∃ e, e < L ∧ x = q ^ e := fun x hx => hpow x (by simp [hx])
    obtain ⟨ea, heaL, haeq⟩ := hpow a (by simp)
    rw [List.length_cons, ih hpowt]
    have hcount : ∀ e, (a :: t).count (q ^ e) = (if e = ea then 1 else 0) + t.count (q ^ e) := by
      intro e
      rw [List.count_cons]
      have heq : (if a = q ^ e then 1 else 0) = (if e = ea then 1 else 0) := by
        by_cases h : e = ea
        · subst h; rw [haeq]; simp
        · rw [if_neg h, if_neg]
          rw [haeq]; intro hcontra
          exact h (Nat.pow_right_injective hq hcontra.symm)
      have hbeq : (if (a == q ^ e) = true then 1 else 0) = (if a = q ^ e then 1 else 0) := by
        simp [beq_iff_eq]
      omega
    have hrw : ∑ e ∈ Finset.range L, (a :: t).count (q ^ e)
        = (∑ e ∈ Finset.range L, (if e = ea then 1 else 0))
          + ∑ e ∈ Finset.range L, t.count (q ^ e) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _; rw [hcount e]
    have hfirst : ∑ e ∈ Finset.range L, (if e = ea then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single ea]
      · simp
      · intro b _ hb; rw [if_neg hb]
      · intro hcontra; exact absurd (Finset.mem_range.mpr heaL) hcontra
    rw [hrw, hfirst]; omega

/-- Carry-free digit additivity for two numbers. -/
theorem qdigit_add2 (q k1 u e : ℕ) (hq : 2 ≤ q)
    (hcf : ∀ f, qdigit q k1 f + qdigit q u f ≤ q - 1) :
    qdigit q (k1 + u) e = qdigit q k1 e + qdigit q u e := by
  rw [qdigit_eq _ _ _ hq, qdigit_eq _ _ _ hq, qdigit_eq _ _ _ hq]
  apply qdigit_add q k1 u e hq
  intro f; have := hcf f
  rw [qdigit_eq _ _ _ hq, qdigit_eq _ _ _ hq] at this; exact this

/-- Slot multiplicity of `k1+u` (carry-free): smaller than `k1`'s by `qdigit u e`. -/
theorem newmult_gen (q k1 u e : ℕ) (hq : 2 ≤ q)
    (hcf : ∀ f, qdigit q k1 f + qdigit q u f ≤ q - 1) :
    (q - 1) - qdigit q (k1 + u) e + qdigit q u e = (q - 1) - qdigit q k1 e := by
  rw [qdigit_add2 q k1 u e hq hcf]
  have hk := qdigit_le q k1 e hq
  have := hcf e
  omega

/-- Digit sum of `u` over `range L` (with `u < q ^ L`) is the multiset size `m`. -/
theorem digitsum_eq (q u L : ℕ) (hq : 2 ≤ q) (huL : u < q ^ L) :
    u = ∑ e ∈ Finset.range L, qdigit q u e * q ^ e := by
  have h1 : u % q ^ L = ∑ e ∈ Finset.range L, (u / q ^ e % q) * q ^ e := digit_mod q u L
  rw [Nat.mod_eq_of_lt huL] at h1
  rw [show (∑ e ∈ Finset.range L, qdigit q u e * q ^ e)
        = ∑ e ∈ Finset.range L, (u / q ^ e % q) * q ^ e from
      Finset.sum_congr rfl (fun e _ => by rw [qdigit_eq _ _ _ hq])]
  exact h1

/-- Removal bound: with `u` adding to `k1` carry-free (so `M' = slotList q (k1+u)`
is `M = slotList q k1` with a size-`m` submultiset `U` of total value `u` removed),
the value of the smallest `t+m` slots of `M` is at most the value of the smallest
`t` slots of `M'` plus `u`. -/
theorem removal_bound (q k1 u Lbig : ℕ) (hq : 2 ≤ q)
    (hcf : ∀ f, qdigit q k1 f + qdigit q u f ≤ q - 1)
    (huL : u < q ^ Lbig)
    (m : ℕ) (hm : m = ∑ e ∈ Finset.range Lbig, qdigit q u e)
    (t : ℕ) (ht : t ≤ (slotList q (k1 + u) Lbig).length) :
    ((slotList q k1 Lbig).take (t + m)).sum
      ≤ ((slotList q (k1 + u) Lbig).take t).sum + u := by
  -- length of M ≥ t + m so the take is a genuine count
  have hMlen : t + m ≤ (slotList q k1 Lbig).length := by
    rw [slotList_length q k1 Lbig, hm]
    have hpt : (slotList q (k1 + u) Lbig).length =
        ∑ e ∈ Finset.range Lbig, ((q - 1) - qdigit q (k1 + u) e) :=
      slotList_length q (k1 + u) Lbig
    rw [hpt] at ht
    have hkey : ∀ e ∈ Finset.range Lbig,
        ((q - 1) - qdigit q (k1+u) e) + qdigit q u e = (q - 1) - qdigit q k1 e := by
      intro e _; exact newmult_gen q k1 u e hq hcf
    calc t + ∑ e ∈ Finset.range Lbig, qdigit q u e
        ≤ (∑ e ∈ Finset.range Lbig, ((q - 1) - qdigit q (k1+u) e))
            + ∑ e ∈ Finset.range Lbig, qdigit q u e := by
          apply Nat.add_le_add_right ht
      _ = ∑ e ∈ Finset.range Lbig, (((q - 1) - qdigit q (k1+u) e) + qdigit q u e) := by
          rw [Finset.sum_add_distrib]
      _ = ∑ e ∈ Finset.range Lbig, ((q - 1) - qdigit q k1 e) := by
          exact Finset.sum_congr rfl hkey
  -- prefix structure of the smallest t+m slots of M
  obtain ⟨p, hpL, r, htake, hlen, hr⟩ := slotList_take q k1 Lbig (t + m) hMlen
  have hval : ((slotList q k1 Lbig).take (t + m)).sum
      = (∑ e ∈ Finset.range p, ((q - 1) - qdigit q k1 e) * q ^ e) + r * q ^ p := by
    rw [htake, List.sum_append, List.sum_replicate, slotList_sum]
    simp [Nat.mul_comm]
  rw [hval]
  -- T' := the t smallest slots of M'
  set Tp := (slotList q (k1 + u) Lbig).take t with hTp
  -- candidate selection b e := count of T' at q ^ e plus qdigit u e
  set bcoef : ℕ → ℕ := fun e => Tp.count (q ^ e) + qdigit q u e with hbcoef
  -- value of candidate = Tp.sum + u
  have hTppow : ∀ x ∈ Tp, ∃ e, e < Lbig ∧ x = q ^ e := by
    intro x hx
    exact slotList_pow q (k1+u) Lbig x (List.mem_of_mem_take hx)
  have hcandval : ∑ e ∈ Finset.range Lbig, bcoef e * q ^ e = Tp.sum + u := by
    have h1 : ∑ e ∈ Finset.range Lbig, Tp.count (q ^ e) * q ^ e = Tp.sum :=
      (wsum_eq q Lbig hq Tp hTppow).symm
    have h2 : ∑ e ∈ Finset.range Lbig, qdigit q u e * q ^ e = u :=
      (digitsum_eq q u Lbig hq huL).symm
    rw [hbcoef]
    simp only []
    rw [show (∑ e ∈ Finset.range Lbig, (Tp.count (q ^ e) + qdigit q u e) * q ^ e)
          = (∑ e ∈ Finset.range Lbig, Tp.count (q ^ e) * q ^ e)
            + ∑ e ∈ Finset.range Lbig, qdigit q u e * q ^ e from by
        rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro e _; ring]
    rw [h1, h2]
  -- count of candidate = t + m
  have hTplen : Tp.length = t := by
    rw [hTp, List.length_take]; omega
  have hcandcount : ∑ e ∈ Finset.range Lbig, bcoef e = t + m := by
    rw [hbcoef]; simp only []
    rw [Finset.sum_add_distrib]
    rw [← wlen_eq q Lbig hq Tp hTppow, hTplen, ← hm]
  -- b e ≤ s e := (q - 1) - qdigit q k1 e
  have hbs : ∀ e, e < Lbig → bcoef e ≤ (q - 1) - qdigit q k1 e := by
    intro e _
    rw [hbcoef]; simp only []
    have hc1 : Tp.count (q ^ e) ≤ (slotList q (k1+u) Lbig).count (q ^ e) :=
      (List.take_sublist t _).count_le _
    have hc2 : (slotList q (k1+u) Lbig).count (q ^ e) = (q - 1) - qdigit q (k1+u) e := by
      by_cases he : e < Lbig
      · exact slotList_count q (k1+u) Lbig hq e he
      · rw [List.count_eq_zero.mpr]
        · have hkk := qdigit_le q (k1+u) e hq; omega
        · intro hmem
          obtain ⟨e', he'L, hxe⟩ := slotList_pow q (k1+u) Lbig _ hmem
          exact absurd (Nat.pow_right_injective hq hxe) (by omega)
    have hmg := newmult_gen q k1 u e hq hcf
    omega
  -- count condition: ∑_{e<p} s_e + r = t + m = ∑_{e<Lbig} b_e
  have hcountcond : (∑ e ∈ Finset.range p, ((q - 1) - qdigit q k1 e)) + r
      ≤ ∑ e ∈ Finset.range Lbig, bcoef e := by
    have hps : ∑ e ∈ Finset.range p, ((q - 1) - qdigit q k1 e) = (slotList q k1 p).length :=
      (slotList_length q k1 p).symm
    rw [hps, hcandcount]; omega
  -- apply greedy_core
  have hgc := greedy_core q p Lbig hq hpL bcoef (fun e => (q - 1) - qdigit q k1 e) r hbs
    hcountcond
  rw [hcandval] at hgc
  simpa using hgc

/-- Converse Kummer/Lucas: if `k`+`(n - k)` has a carry in base `q` at some
position (`q ^ i ≤ k%q ^ i + (n - k)%q ^ i`), then `q ∣ C(n,k)`. Proved via
`Nat.factorization_choose`. -/
theorem dvd_choose_of_carry (q n k : ℕ) (hq : q.Prime) (hkn : k ≤ n)
    (hcarry : ∃ i, q ^ i ≤ k % q ^ i + (n - k) % q ^ i) :
    q ∣ Nat.choose n k := by
  obtain ⟨i, hi⟩ := hcarry
  set b := Nat.log q n + 1 with hb
  have hlogb : Nat.log q n < b := by omega
  have hpos : 0 < Nat.choose n k := Nat.choose_pos hkn
  rw [Nat.Prime.dvd_iff_one_le_factorization hq hpos.ne']
  rw [Nat.factorization_choose hq hkn hlogb]
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro hcon
  have hi1 : 1 ≤ i := by
    by_contra h
    have hi0 : i = 0 := by omega
    subst hi0
    simp only [pow_zero, Nat.mod_one] at hi
    omega
  have hib : i < b := by
    by_contra h
    have hlt : Nat.log q n < i := by omega
    have hnq : n < q ^ i := Nat.lt_pow_of_log_lt hq.two_le hlt
    have hk : k % q ^ i = k := Nat.mod_eq_of_lt (by omega)
    have hnk : (n - k) % q ^ i = n - k := Nat.mod_eq_of_lt (by omega)
    rw [hk, hnk] at hi
    omega
  have hmem : i ∈ Finset.Ico 1 b := Finset.mem_Ico.mpr ⟨hi1, hib⟩
  exact hcon hmem hi

/-- Carry-free correspondence from admissibility. For `j ∈ Jset q k` set
`β = blockSum q (k - 1) (slotLen q 1 k) 1` and `u = β + j`. Then `u` adds to `k-1`
carry-free in base `q`, i.e. per position the digit sum is `≤ q-1`. Uses
`s_one_eq` (so `s q 1 k - 1 = (k - 1) + β`, hence `s q 1 k + j - 1 = (k - 1) + u`),
the admissibility `¬ q ∣ C((k - 1)+u, k-1)`, and `dvd_choose_of_carry`. -/
theorem admissible_carryfree (q : ℕ) (hq : q.Prime) (k : ℕ) (hk : 0 < k)
    (j : ℕ) (hj : j ∈ Jset q k) :
    ∀ e, qdigit q (k - 1) e
        + qdigit q (blockSum q (k - 1) (slotLen q 1 k) 1 + j) e ≤ q - 1 := by
  have hq2 : 2 ≤ q := hq.two_le
  obtain ⟨hjdvd, hjnd⟩ := hj
  set β := blockSum q (k - 1) (slotLen q 1 k) 1 with hβ
  set k1 := k - 1 with hk1
  set u := β + j with hu
  -- Step 2: s q 1 k + j - 1 = k1 + u
  have hseq : s q 1 k + j - 1 = k1 + u := by
    rw [s_one_eq q k hq2 hk, ← hβ, hu, hk1]; omega
  rw [hseq] at hjnd
  -- Step 3: no carry at any position
  have hnocarry : ∀ i, k1 % q ^ i + u % q ^ i < q ^ i := by
    intro i
    by_contra hc
    push Not at hc
    apply hjnd
    apply dvd_choose_of_carry q (k1 + u) k1 hq (by omega)
    exact ⟨i, by rw [Nat.add_sub_cancel_left]; exact hc⟩
  -- Step 4 & 5: bridge to digit-sum bound
  intro e
  rw [qdigit_eq _ _ _ hq2, qdigit_eq _ _ _ hq2]
  -- mod-pow-succ identities
  have hke : k1 % q ^ (e + 1) = k1 % q ^ e + q ^ e * (k1 / q ^ e % q) := Nat.mod_pow_succ
  have hue : u % q ^ (e + 1) = u % q ^ e + q ^ e * (u / q ^ e % q) := Nat.mod_pow_succ
  have hpe : q ^ (e + 1) = q ^ e * q := pow_succ q e
  have h1 := hnocarry (e + 1)
  have h0 := hnocarry e
  have hpos : 0 < q ^ e := pow_pos (by omega : 0 < q) e
  set da := k1 / q ^ e % q with hda
  set db := u / q ^ e % q with hdb
  -- da + db ≤ q - 1
  by_contra hcon
  push Not at hcon
  -- hcon : q - 1 < da + db, so da + db ≥ q
  have hge : q ≤ da + db := by omega
  -- (da + db) * q ^ e ≤ k1 % q ^ (e + 1) + u % q ^ (e + 1)
  have hbound : (da + db) * q ^ e ≤ k1 % q ^ (e + 1) + u % q ^ (e + 1) := by
    rw [hke, hue]; nlinarith [Nat.zero_le (k1 % q ^ e), Nat.zero_le (u % q ^ e)]
  have hmul : q * q ^ e ≤ (da + db) * q ^ e := Nat.mul_le_mul_right _ hge
  have h1' : k1 % q ^ (e + 1) + u % q ^ (e + 1) < q ^ e * q := by rw [← hpe]; exact h1
  nlinarith [hbound, hmul, h1']

/-- Prefix-sum monotonicity: taking more (nonneg ℕ) elements never decreases the sum. -/
theorem take_sum_mono (w : List ℕ) {a b : ℕ} (h : a ≤ b) :
    (w.take a).sum ≤ (w.take b).sum := by
  have hsplit : w.take b = w.take a ++ (w.take b).drop a := by
    conv_lhs => rw [← List.take_append_drop a (w.take b)]
    rw [List.take_take, Nat.min_eq_left h]
  calc (w.take a).sum ≤ (w.take a).sum + ((w.take b).drop a).sum := Nat.le_add_right _ _
    _ = (w.take b).sum := by
        conv_rhs => rw [hsplit]
        rw [List.sum_append]

/-- `Phi` is independent of the truncation length once it contains the first `d` blocks. -/
theorem Phi_Lindep (q k1 d L₁ Lbig : ℕ) (h : L₁ ≤ Lbig)
    (hlen : d * (q - 1) ≤ (slotList q k1 L₁).length) :
    Phi q k1 d Lbig = Phi q k1 d L₁ := by
  unfold Phi
  apply Finset.sum_congr rfl
  intro r hr; simp only [Finset.mem_range] at hr
  congr 1
  apply blockSum_Lindep q k1 L₁ Lbig (r + 1) h (by omega)
  calc (r + 1) * (q - 1) ≤ d * (q - 1) := Nat.mul_le_mul_right _ (by omega)
    _ ≤ (slotList q k1 L₁).length := hlen

/-- The core extraction inequality. Let `u` add to `k1 = k-1` carry-free with
`(q - 1) ∣ u` and `u > β₁` where `β₁ = blockSum q k1 L₀ 1`. Then for truncations
`L₁`, `L₂` large enough to contain the relevant blocks,
`Φ_d(M) < d·u + Φ_{d-1}(M\U)`, i.e. `Phi q k1 d L₁ < d*u + Phi q (k1+u) (d-1) L₂`.
Proof idea: expand both `Phi`s into prefix sums, bound each prefix sum of `M\U`
below via `removal_bound`, and use `u > β₁` for strictness. -/
theorem extraction_core (q : ℕ) (hq : 2 ≤ q) (k1 : ℕ) (d : ℕ) (hd : 1 < d)
    (u : ℕ) (hudvd : (q - 1) ∣ u)
    (hcf : ∀ e, qdigit q k1 e + qdigit q u e ≤ q - 1)
    (L₀ L₁ L₂ : ℕ)
    (hL₀ : (q - 1) ≤ (slotList q k1 L₀).length)
    (hugt : blockSum q k1 L₀ 1 < u)
    (hL₁ : d * (q - 1) ≤ (slotList q k1 L₁).length)
    (hL₂ : (d - 1) * (q - 1) ≤ (slotList q (k1 + u) L₂).length) :
    Phi q k1 d L₁ < d * u + Phi q (k1 + u) (d - 1) L₂ := by
  set n := q - 1 with hn
  -- A common large truncation length dominating everything.
  set Lbig := L₀ + L₁ + L₂ + u + 1 with hLbig
  have hL₀big : L₀ ≤ Lbig := by omega
  have hL₁big : L₁ ≤ Lbig := by omega
  have hL₂big : L₂ ≤ Lbig := by omega
  have huLbig : u < q ^ Lbig := by
    calc u < q ^ u := Nat.lt_pow_self (by omega)
      _ ≤ q ^ Lbig := Nat.pow_le_pow_right (by omega) (by omega)
  -- the removed multiset size m = digit sum of u
  set m := ∑ e ∈ Finset.range Lbig, qdigit q u e with hmdef
  -- m is a positive multiple of n, write m = ℓ * n
  have hupos : 0 < u := by omega
  have hmpos : 0 < m := by
    rw [hmdef]
    by_contra hc
    push Not at hc
    have hz : ∑ e ∈ Finset.range Lbig, qdigit q u e = 0 := by omega
    have hu0 : u = 0 := by
      rw [digitsum_eq q u Lbig hq huLbig]
      apply Finset.sum_eq_zero
      intro e he
      have : qdigit q u e = 0 := Finset.sum_eq_zero_iff.mp hz e he
      rw [this]; ring
    omega
  have hmdvd : n ∣ m := by
    have hmod : u ≡ m [MOD n] := by
      rw [hmdef]; conv_lhs => rw [digitsum_eq q u Lbig hq huLbig]
      exact sum_pow_modEq q Lbig hq (fun e => qdigit q u e)
    have : n ∣ u := hudvd
    exact (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).mpr this))
  obtain ⟨ℓ, hℓ⟩ := hmdvd
  have hnpos : 0 < n := by omega
  have hℓpos : 1 ≤ ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · rw [h, Nat.mul_zero] at hℓ; omega
    · exact h
  -- length lower bound for M' at Lbig
  have hM'len : (d - 1) * n ≤ (slotList q (k1 + u) Lbig).length :=
    le_trans hL₂ (slotList_length_mono q (k1+u) hL₂big)
  -- abbreviations for the prefix sums P j := σ_{j n}(M at Lbig)
  set P : ℕ → ℕ := fun j => ((slotList q k1 Lbig).take (j * n)).sum with hP
  set Q : ℕ → ℕ := fun j => ((slotList q (k1 + u) Lbig).take (j * n)).sum with hQ
  -- Φ_d(M) = ∑_{c<d} P (c + 1)
  have hPhiM : Phi q k1 d L₁ = ∑ c ∈ Finset.range d, P (c + 1) := by
    rw [← Phi_Lindep q k1 d L₁ Lbig hL₁big hL₁, Phi_eq_take_sum]
  -- Φ_{d-1}(M') = ∑_{c<d-1} Q (c + 1)
  have hPhiM' : Phi q (k1 + u) (d - 1) L₂ = ∑ c ∈ Finset.range (d-1), Q (c + 1) := by
    rw [← Phi_Lindep q (k1+u) (d-1) L₂ Lbig hL₂big hL₂, Phi_eq_take_sum]
  -- removal bound per layer: P (c+1+ℓ) ≤ Q (c + 1) + u   for c < d-1
  have hA1 : ∀ c, c < d - 1 → P (c + 1 + ℓ) ≤ Q (c + 1) + u := by
    intro c hc
    have htlen : (c + 1) * n ≤ (slotList q (k1 + u) Lbig).length := by
      calc (c + 1) * n ≤ (d - 1) * n := Nat.mul_le_mul_right _ (by omega)
        _ ≤ (slotList q (k1 + u) Lbig).length := hM'len
    have hrb := removal_bound q k1 u Lbig hq hcf huLbig m hmdef ((c + 1)*n) htlen
    have hidx : (c + 1) * n + m = (c + 1 + ℓ) * n := by
      rw [hℓ]; ring
    rw [hidx] at hrb
    exact hrb
  -- monotonicity: P (c+2) ≤ P (c+1+ℓ)  since c+2 ≤ c+1+ℓ (ℓ ≥ 1)
  have hmono : ∀ c, P (c + 2) ≤ P (c + 1 + ℓ) := by
    intro c
    apply take_sum_mono
    apply Nat.mul_le_mul_right
    omega
  -- P 1 = β₁ < u
  have hP1 : P 1 < u := by
    have hb1 : P 1 = blockSum q k1 Lbig 1 := by
      rw [hP]; simp only [Nat.one_mul]
      unfold blockSum
      simp only [Nat.sub_self, Nat.zero_mul, List.drop_zero, hn]
    have hbeq : blockSum q k1 Lbig 1 = blockSum q k1 L₀ 1 := by
      apply blockSum_Lindep q k1 L₀ Lbig 1 (by omega) (by omega)
      rw [Nat.one_mul]; exact hL₀
    rw [hb1, hbeq]; exact hugt
  -- Step (I): ∑_{c<d-1} P(c+1+ℓ) ≤ Φ'(L₂) + (d-1)*u
  have hStepI : ∑ c ∈ Finset.range (d-1), P (c + 1 + ℓ)
      ≤ Phi q (k1 + u) (d - 1) L₂ + (d - 1) * u := by
    rw [hPhiM']
    calc ∑ c ∈ Finset.range (d-1), P (c + 1 + ℓ)
        ≤ ∑ c ∈ Finset.range (d - 1), (Q (c + 1) + u) :=
          Finset.sum_le_sum (fun c hc => hA1 c (Finset.mem_range.mp hc))
      _ = (∑ c ∈ Finset.range (d-1), Q (c + 1)) + (d - 1) * u := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  -- Step (II): ∑_{c<d} P(c + 1) ≤ ∑_{c<d-1} P(c+1+ℓ) + P 1
  have hStepII :
      ∑ c ∈ Finset.range d, P (c + 1) ≤
        (∑ c ∈ Finset.range (d - 1), P (c + 1 + ℓ)) + P 1 := by
    -- ∑_{c<d} P(c + 1) = P 1 + ∑_{c<d-1} P(c+2)
    have hsplitL : ∑ c ∈ Finset.range d, P (c + 1)
        = P 1 + ∑ c ∈ Finset.range (d-1), P (c + 2) := by
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      rw [Finset.sum_range_succ']
      simp only [Nat.add_sub_cancel, Nat.zero_add]
      rw [Nat.add_comm]
    rw [hsplitL]
    have hmonosum :
        ∑ c ∈ Finset.range (d - 1), P (c + 2) ≤
          ∑ c ∈ Finset.range (d - 1), P (c + 1 + ℓ) :=
      Finset.sum_le_sum (fun c _ => hmono c)
    omega
  -- Assemble
  rw [hPhiM]
  -- d*u + Φ' ≥ u + (∑_{c<d-1} P(c+1+ℓ))  > ∑_{c<d} P(c + 1)
  have hda : d * u = u + (d - 1) * u := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega]
    ring
  -- combine StepI: Φ' + (d-1)*u ≥ ∑ P(c+1+ℓ)
  have hkey1 : (∑ c ∈ Finset.range (d - 1), P (c + 1 + ℓ))
      ≤ Phi q (k1 + u) (d - 1) L₂ + (d - 1) * u := hStepI
  -- and StepII + hP1
  have hkey2 : ∑ c ∈ Finset.range d, P (c + 1) < (∑ c ∈ Finset.range (d-1), P (c + 1 + ℓ)) + u := by
    have := hStepII; omega
  omega

/-- Pillar 2, the extraction inequality in strict form: for admissible `j > 0`,
`s_d(k) < F(j)` (informal.tex Lem. lem:H2-extraction). With `u = β₁ + j`,
admissibility makes `u` carry-free with `k-1`; the slot formula reduces the goal
to `extraction_core`, strict since `j > 0` gives `u > β₁`. -/
theorem extraction_strict (q : ℕ) (hq : q.Prime) (d k : ℕ) (hd : 1 < d)
    (hk : 0 < k) (j : ℕ) (hj : j ∈ Jset q k) (hjpos : 0 < j) :
    s q d k < F q d k j := by
  have hq2 : 2 ≤ q := hq.two_le
  -- abbreviations
  set s1 := s q 1 k with hs1def
  set β := blockSum q (k - 1) (slotLen q 1 k) 1 with hβdef
  -- s_one_eq:  s1 = k + β
  have hs1eq : s1 = k + β := by rw [hs1def, hβdef]; exact s_one_eq q k hq2 hk
  have hs1pos : 0 < s1 := by omega
  set u := β + j with hudef
  -- n_val = s1 + j = k + u
  have hnval : s1 + j = k + u := by rw [hs1eq, hudef]; ring
  have hnvalpos : 0 < s1 + j := by omega
  -- (q - 1) ∣ u :  (q - 1)∣β  (β is a block sum, divisible) and (q - 1)∣j (admissibility)
  have hjdvd : (q - 1) ∣ j := hj.1
  have hβdvd : (q - 1) ∣ β := by
    have hlen0 : (q - 1) ≤ (slotList q (k - 1) (slotLen q 1 k)).length := by
      have hb := slotList_length_ge q (k - 1) (slotLen q 1 k) hq2
      have hsl : slotLen q 1 k - ((k - 1) + 1) = k + 2 := by
        simp [slotLen]; omega
      rw [hsl] at hb
      have : (q - 1) * 1 ≤ (q - 1) * (k + 2) := by
        apply Nat.mul_le_mul_left; omega
      omega
    rw [hβdef, blockSum]
    set w := ((slotList q (k - 1) (slotLen q 1 k)).drop ((1 - 1) * (q - 1))).take (q - 1) with hwdef
    have hwlen : w.length = q - 1 := by
      rw [hwdef]
      apply window_len
      simp only [Nat.sub_self, Nat.zero_mul, Nat.zero_add]
      exact hlen0
    have hmod := pow_sum_modEq q hq2 w (fun x hx => by
      rw [hwdef] at hx
      have h1 : x ∈ (slotList q (k - 1) (slotLen q 1 k)).drop ((1 - 1) * (q - 1)) :=
        List.mem_of_mem_take hx
      obtain ⟨e, _, hxe⟩ := slotList_pow q (k - 1) (slotLen q 1 k) x (List.mem_of_mem_drop h1)
      exact ⟨e, hxe⟩)
    rw [hwlen] at hmod
    exact (Nat.modEq_zero_iff_dvd).mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))
  have hudvd : (q - 1) ∣ u := by rw [hudef]; exact Nat.dvd_add hβdvd hjdvd
  -- carry-free: `u` adds to `k-1` carry-free  (from admissibility, dvd_choose_of_carry)
  have hcf : ∀ e, qdigit q (k - 1) e + qdigit q u e ≤ q - 1 := by
    rw [hudef]; exact admissible_carryfree q hq k hk j hj
  -- u > β  (since j > 0)
  have hugt : β < u := by rw [hudef]; omega
  -- slot formula on both sides
  have hsd : s q d k = d * k + Phi q (k - 1) d (slotLen q d k) := slot_formula q d k hq2 hk
  have hFexp : F q d k j
      = d * (k + u) + Phi q ((k - 1) + u) (d - 1) (slotLen q (d - 1) (s1 + j)) := by
    have hsd1 : s q (d - 1) (s1 + j)
        = (d - 1) * (s1 + j)
          + Phi q (s1 + j - 1) (d - 1) (slotLen q (d - 1) (s1 + j)) :=
      slot_formula q (d - 1) (s1 + j) hq2 hnvalpos
    -- s1 + j - 1 = (k - 1) + u
    have hm1 : s1 + j - 1 = (k - 1) + u := by omega
    rw [hm1] at hsd1
    -- F q d k j unfolds to s q (d-1) (s1+j) + s1 + j  (s q 1 k = s1)
    have hFunf : F q d k j = s q (d - 1) (s1 + j) + s1 + j := by
      rw [F, ← hs1def]
    rw [hFunf, hsd1, hnval]
    -- (d-1)*(k+u) + P + (k+u) = d*(k+u) + P  needs 1 ≤ d
    have hd1 : (d - 1) * (k + u) + (k + u) = d * (k + u) := by
      cases d with
      | zero => omega
      | succ d' => simp only [Nat.succ_sub_one]; ring
    omega
  -- reduce to the core inequality
  have hβlen : (q - 1) ≤ (slotList q (k - 1) (slotLen q 1 k)).length := by
    have hb := slotList_length_ge q (k - 1) (slotLen q 1 k) hq2
    have hsl : slotLen q 1 k - ((k - 1) + 1) = k + 2 := by
      simp [slotLen]; omega
    rw [hsl] at hb
    have : (q - 1) * 1 ≤ (q - 1) * (k + 2) := by
      apply Nat.mul_le_mul_left; omega
    omega
  have hL₁ : d * (q - 1) ≤ (slotList q (k - 1) (slotLen q d k)).length := by
    have hb := slotList_length_ge q (k - 1) (slotLen q d k) hq2
    have hsl : slotLen q d k - ((k - 1) + 1) = d * (k + 1) + 1 := by
      simp [slotLen]; omega
    rw [hsl] at hb
    have hge : d ≤ d * (k + 1) + 1 := by
      have : d * 1 ≤ d * (k + 1) := by apply Nat.mul_le_mul_left; omega
      omega
    have : d * (q - 1) ≤ (q - 1) * (d * (k + 1) + 1) := by
      rw [Nat.mul_comm]
      apply Nat.mul_le_mul_left; exact hge
    omega
  have hL₂ : (d - 1) * (q - 1)
      ≤ (slotList q ((k - 1) + u) (slotLen q (d - 1) (s1 + j))).length := by
    have hb := slotList_length_ge q ((k - 1) + u) (slotLen q (d - 1) (s1 + j)) hq2
    have hsl : slotLen q (d - 1) (s1 + j) - (((k - 1) + u) + 1)
        = (d - 1) * ((k + u) + 1) + 1 := by
      simp only [slotLen, ↓reduceIte]
      rw [hnval]
      omega
    rw [hsl] at hb
    have hge : (d - 1) ≤ (d - 1) * ((k + u) + 1) + 1 := by
      have : (d - 1) * 1 ≤ (d - 1) * ((k + u) + 1) := by
        apply Nat.mul_le_mul_left; omega
      omega
    have : (d - 1) * (q - 1) ≤ (q - 1) * ((d - 1) * ((k + u) + 1) + 1) := by
      rw [Nat.mul_comm]
      apply Nat.mul_le_mul_left; exact hge
    omega
  have hcore : Phi q (k - 1) d (slotLen q d k)
      < d * u + Phi q ((k - 1) + u) (d - 1) (slotLen q (d - 1) (s1 + j)) :=
    extraction_core q hq2 (k - 1) d hd u hudvd hcf (slotLen q 1 k)
      (slotLen q d k) (slotLen q (d - 1) (s1 + j)) hβlen hugt hL₁ hL₂
  -- assemble
  rw [hsd, hFexp]
  -- goal: d*k + Phi(M) < d*(k+u) + Phi(M\U);  d*(k+u) = d*k + d*u
  have : d * (k + u) = d * k + d * u := by ring
  omega

/-- `F` attains its minimum over `J` uniquely at `j = 0`: for every admissible
`j ∈ J` with `j > 0` we have `F(0) < F(j)`.

Assembled from `composition_identity` (`F(0) = s_d(k)`) and `extraction_strict`
(`s_d(k) < F(j)` for admissible `j > 0`). -/
theorem main (q : ℕ) (hq : q.Prime) (d k : ℕ) (hd : 1 < d) (hk : 0 < k) :
    ∀ j ∈ Jset q k, 0 < j → F q d k 0 < F q d k j := by
  intro j hj hjpos
  -- F(0) = s_{d-1}(s_1(k) + 0) + s_1(k) + 0 = s_{d-1}(s_1(k)) + s_1(k) = s_d(k).
  have hF0 : F q d k 0 = s q d k := by
    simp only [F, add_zero]
    exact composition_identity q hq d k hd hk
  rw [hF0]
  exact extraction_strict q hq d k hd hk j hj hjpos

end ZetaH123.H2
