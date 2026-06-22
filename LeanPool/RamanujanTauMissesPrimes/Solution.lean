/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
/-!
# LeanPool.RamanujanTauMissesPrimes.Solution
-/

open Filter Asymptotics

/-- The *radical* of `n`: the product of its distinct prime factors (and `0` when `n = 0`). -/
noncomputable def Nat.radical (n : ℕ) : ℕ :=
  if n = 0 then 0 else ∏ p ∈ n.primeFactors, p

/-- An axiomatic Ramanujan tau function: a function `ℕ+ → ℤ` satisfying Hecke
multiplicativity, the Hecke recurrence at prime powers, the parity criterion,
Deligne's bound and the non-unit property. -/
structure RamanujanTau where
  /-- The underlying function `ℕ+ → ℤ`. -/
  τ : ℕ+ → ℤ
  hecke_mult : ∀ m n : ℕ+, Nat.Coprime (m : ℕ) (n : ℕ) → τ (m * n) = τ m * τ n
  hecke_rec : ∀ (p : ℕ+), (p : ℕ).Prime → ∀ (m : ℕ), 2 ≤ m →
    τ (p ^ m) = τ p * τ (p ^ (m - 1)) - (↑(p : ℕ) : ℤ) ^ 11 * τ (p ^ (m - 2))
  parity : ∀ n : ℕ+, ¬(2 ∣ τ n) ↔ (Odd (n : ℕ) ∧ IsSquare (n : ℕ))
  deligne_bound : ∀ (p : ℕ+), (p : ℕ).Prime →
    (|τ p| : ℝ) ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2)
  non_unit : ∀ (n : ℕ+), 2 ≤ (n : ℕ) → τ n ≠ 1 ∧ τ n ≠ -1

variable (R : RamanujanTau)

/-- The set of positive primes `ℓ ≤ X` such that `|τ n| = ℓ` for some `n ≥ 1`. -/
noncomputable def tauPrimeSet (X : ℝ) : Set ℕ :=
  {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧ ∃ n : ℕ+, (R.τ n).natAbs = ℓ}

/-- `S X` is the number of primes `ℓ ≤ X` taken (in absolute value) by `τ`. -/
noncomputable def S (X : ℝ) : ℕ := (tauPrimeSet R X).ncard

/-- The pairs `(x, y) ∈ ℕ+ × ℤ` with `x > X ^ (2/11)` and `1 ≤ |x ^ 11 - y ^ 2| ≤ X`. -/
noncomputable def E2Set (X : ℝ) : Set (ℕ+ × ℤ) :=
  {p : ℕ+ × ℤ | (p.1 : ℝ) > X ^ ((2 : ℝ) / 11) ∧
    1 ≤ |(↑p.1 : ℤ) ^ 11 - p.2 ^ 2| ∧
    (|(↑p.1 : ℤ) ^ 11 - p.2 ^ 2| : ℝ) ≤ X}

/-- `E2 X` is the cardinality of `E2Set X`. -/
noncomputable def E2 (X : ℝ) : ℕ := (E2Set X).ncard

/-- The pairs `(x, u) ∈ ℕ+ × ℤ` with `x > X ^ (1/11)` and `1 ≤ |u ^ 2 - 5 * x ^ 22| ≤ 4 * X`. -/
noncomputable def E4Set (X : ℝ) : Set (ℕ+ × ℤ) :=
  {p : ℕ+ × ℤ | (p.1 : ℝ) > X ^ ((1 : ℝ) / 11) ∧
    1 ≤ |p.2 ^ 2 - 5 * (↑p.1 : ℤ) ^ 22| ∧
    (|p.2 ^ 2 - 5 * (↑p.1 : ℤ) ^ 22| : ℝ) ≤ 4 * X}

/-- `E4 X` is the cardinality of `E4Set X`. -/
noncomputable def E4 (X : ℝ) : ℕ := (E4Set X).ncard

/-- The ABC conjecture: for every `ε > 0` there is `K > 0` with
`c ≤ K * rad (a * b * c) ^ (1 + ε)` for all coprime positive `a + b = c`. -/
def ABC : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ K : ℝ, 0 < K ∧
      ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → a + b = c →
          (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε)

/-- The set of signed odd primes `{±ℓ : ℓ an odd prime}`. -/
def oddPrimesSigned : Set ℤ :=
  {z : ℤ | ∃ p : ℕ, Nat.Prime p ∧ p ≠ 2 ∧ (z = ↑p ∨ z = -↑p)}

/-- `X2k R k = {τ (p ^ (2 * k)) : p a positive prime}`. -/
def X2k (k : ℕ) : Set ℤ :=
  {z : ℤ | ∃ p : ℕ+, (p : ℕ).Prime ∧ z = R.τ (p ^ (2 * k))}

/-- The (sharper, `N ^ (1/2)`) form of Xiong's Proposition 5.4 used as a hypothesis. -/
def Proposition54 : Prop :=
  (∃ c₄ C₄ : ℝ, 0 < c₄ ∧ 0 < C₄ ∧
    ∀ N : ℝ, c₄ < N →
      ∀ k : ℕ, 3 ≤ k → (k : ℝ) < Real.log N / (2 * Real.log 2) →
        ((oddPrimesSigned ∩ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ N}).ncard : ℝ) ≤
          C₄ * N ^ ((1 : ℝ) / 2)) ∧
  (∃ c₅ : ℝ, 0 < c₅ ∧
    ∀ N : ℝ, c₅ < N →
      ∀ k : ℕ, (k : ℝ) ≥ Real.log N / (2 * Real.log 2) →
        X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ N} = ∅)

open Classical in
/-- A choice of value `τ (p ^ (2 * k))` whose absolute value is `ℓ`, when such a prime `p`
exists; otherwise `0`. -/
noncomputable def tauWitness (R : RamanujanTau) (k : ℕ) (ℓ : ℕ) : ℤ :=
  if h : ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ (2 * k))).natAbs = ℓ
  then R.τ (h.choose ^ (2 * k))
  else 0

lemma tauWitness_natAbs (R : RamanujanTau) (k : ℕ) (ℓ : ℕ)
    (hw : ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ (2 * k))).natAbs = ℓ) :
    (tauWitness R k ℓ).natAbs = ℓ := by
  unfold tauWitness
  rw [dif_pos hw]
  exact hw.choose_spec.2

lemma tauWitness_mem_oddPrimesSigned (R : RamanujanTau) (k : ℕ) (ℓ : ℕ)
    (hprime : Nat.Prime ℓ) (hne2 : ℓ ≠ 2)
    (hw : ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ (2 * k))).natAbs = ℓ) :
    tauWitness R k ℓ ∈ oddPrimesSigned := by
  have habs := tauWitness_natAbs R k ℓ hw
  have hcases := Int.natAbs_eq (tauWitness R k ℓ)
  rw [habs] at hcases
  simp only [oddPrimesSigned, Set.mem_setOf_eq]
  exact ⟨ℓ, hprime, hne2, hcases⟩

lemma tauWitness_mem_X2k (R : RamanujanTau) (k : ℕ) (ℓ : ℕ)
    (hw : ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ (2 * k))).natAbs = ℓ) :
    tauWitness R k ℓ ∈ X2k R k := by
  have h₁ : tauWitness R k ℓ = R.τ (hw.choose ^ (2 * k)) := by
    simp only [tauWitness, dif_pos hw]
  rw [h₁]
  exact ⟨hw.choose, hw.choose_spec.1, rfl⟩

lemma tauWitness_abs_le (R : RamanujanTau) (k : ℕ) (ℓ : ℕ) (X : ℝ) (hle : (ℓ : ℝ) ≤ X)
    (hw : ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ (2 * k))).natAbs = ℓ) :
    (|tauWitness R k ℓ| : ℝ) ≤ X := by
  have h1 := tauWitness_natAbs R k ℓ hw
  have h2 : (|tauWitness R k ℓ| : ℝ) = ((tauWitness R k ℓ).natAbs : ℝ) := by
    exact_mod_cast (Nat.cast_natAbs (tauWitness R k ℓ)).symm
  rw [h2, h1]
  exact hle

lemma int_abs_le_subset_Icc (X : ℝ) :
    {z : ℤ | (|z| : ℝ) ≤ X} ⊆ Set.Icc (-⌈X⌉) ⌈X⌉ := by
  intro z (hz : (|z| : ℝ) ≤ X)
  constructor
  · exact_mod_cast show (-⌈X⌉ : ℝ) ≤ (z : ℝ) by
      linarith [neg_le_abs (z : ℝ), Int.le_ceil X]
  · exact_mod_cast show (z : ℝ) ≤ ⌈X⌉ by
      linarith [le_abs_self (z : ℝ), Int.le_ceil X]

lemma target_set_finite (R : RamanujanTau) (k : ℕ) (X : ℝ) (_hX : 0 < X) :
    (oddPrimesSigned ∩ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X}).Finite := by
  apply Set.Finite.subset (Set.finite_Icc (-⌈X⌉) ⌈X⌉)
  intro z hz
  exact int_abs_le_subset_Icc X (hz.2)

lemma tauWitness_injOn (R : RamanujanTau) (k : ℕ) (X : ℝ) :
    Set.InjOn (tauWitness R k) {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ (2 * k))).natAbs = ℓ} := by
  intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ heq
  have hw₁ := hℓ₁.2.2.2
  have hw₂ := hℓ₂.2.2.2
  have h₁ := tauWitness_natAbs R k ℓ₁ hw₁
  have h₂ := tauWitness_natAbs R k ℓ₂ hw₂
  calc ℓ₁ = (tauWitness R k ℓ₁).natAbs := h₁.symm
    _ = (tauWitness R k ℓ₂).natAbs := congrArg Int.natAbs heq
    _ = ℓ₂ := h₂

lemma per_k_odd_prime_ncard_le (R : RamanujanTau) (k : ℕ) (X : ℝ) (hX : 0 < X) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard ≤
    (oddPrimesSigned ∩ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X}).ncard := by
  have hfin := target_set_finite R k X hX
  exact Set.ncard_le_ncard_of_injOn (tauWitness R k)
    (fun ℓ hℓ => by
      simp only [Set.mem_setOf_eq] at hℓ
      obtain ⟨hprime, hne2, hle, hw⟩ := hℓ
      exact ⟨⟨tauWitness_mem_oddPrimesSigned R k ℓ hprime hne2 hw,
             tauWitness_mem_X2k R k ℓ hw⟩,
             tauWitness_abs_le R k ℓ X hle hw⟩)
    (tauWitness_injOn R k X)
    hfin

lemma even_prime_subset_singleton (R : RamanujanTau) (X : ℝ) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ = 2 ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
        (R.τ (p ^ (2 * k))).natAbs = ℓ} ⊆ {2} := by
  grind

lemma even_prime_ncard_le (R : RamanujanTau) (X : ℝ) (_hX : 0 < X) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ = 2 ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
        (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard ≤ 1 := by
  calc _ ≤ ({2} : Set ℕ).ncard := Set.ncard_le_ncard (even_prime_subset_singleton R X)
    _ = 1 := Set.ncard_singleton 2

lemma natAbs_ne_zero_of_eq_prime {n : ℤ} {ℓ : ℕ} (hprime : Nat.Prime ℓ)
    (heq : n.natAbs = ℓ) : n.natAbs ≠ 0 := by
  rw [heq]
  exact Nat.Prime.ne_zero hprime

lemma k_le_K_of_prime_witness (R : RamanujanTau) (X : ℝ) (K : ℕ)
    (hvanish : ∀ k : ℕ, K < k → ∀ p : ℕ+, (p : ℕ).Prime →
      (R.τ (p ^ (2 * k))).natAbs ≠ 0 → ¬((↑(R.τ (p ^ (2 * k))).natAbs : ℝ) ≤ X))
    (ℓ : ℕ) (hprime : Nat.Prime ℓ) (hle : (ℓ : ℝ) ≤ X)
    (p : ℕ+) (hp : (p : ℕ).Prime) (k : ℕ) (_hk3 : 3 ≤ k)
    (heq : (R.τ (p ^ (2 * k))).natAbs = ℓ) : k ≤ K := by
  by_contra hgt
  push Not at hgt
  have hne : (R.τ (p ^ (2 * k))).natAbs ≠ 0 := natAbs_ne_zero_of_eq_prime hprime heq
  have habs := hvanish k hgt p hp hne
  rw [heq] at habs
  exact habs (by exact_mod_cast hle)

lemma target_subset_finite_union (R : RamanujanTau) (X : ℝ) (_hX : 0 < X)
    (K : ℕ) (_hK : 3 ≤ K)
    (hvanish : ∀ k : ℕ, K < k → ∀ p : ℕ+, (p : ℕ).Prime →
      (R.τ (p ^ (2 * k))).natAbs ≠ 0 → ¬((↑(R.τ (p ^ (2 * k))).natAbs : ℝ) ≤ X)) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
        (R.τ (p ^ (2 * k))).natAbs = ℓ} ⊆
    ⋃ k ∈ Finset.Icc 3 K, {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ (2 * k))).natAbs = ℓ} := by
  intro ℓ hℓ
  simp only [Set.mem_setOf_eq] at hℓ
  obtain ⟨hprime, hne2, hle, p, hp, k, hk3, heq⟩ := hℓ
  have hkK : k ≤ K := k_le_K_of_prime_witness R X K hvanish ℓ hprime hle p hp k hk3 heq
  simp only [Set.mem_iUnion]
  exact ⟨k, ⟨Finset.mem_Icc.mpr ⟨hk3, hkK⟩, hprime, hne2, hle, p, hp, heq⟩⟩

lemma biUnion_per_k_finite (R : RamanujanTau) (X : ℝ) (K : ℕ) :
    (⋃ k ∈ Finset.Icc 3 K,
      {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ (2 * k))).natAbs = ℓ}).Finite := by
  refine Set.Finite.subset (Set.finite_le_nat ⌊X⌋₊) ?_
  intro ℓ hℓ
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hℓ
  obtain ⟨k, _, _, _, hle, _⟩ := hℓ
  exact Nat.le_floor hle

lemma target_ncard_le_sum_nat (R : RamanujanTau) (X : ℝ) (hX : 0 < X)
    (K : ℕ) (hK : 3 ≤ K)
    (hvanish : ∀ k : ℕ, K < k → ∀ p : ℕ+, (p : ℕ).Prime →
      (R.τ (p ^ (2 * k))).natAbs ≠ 0 → ¬((↑(R.τ (p ^ (2 * k))).natAbs : ℝ) ≤ X)) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
        (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard ≤
    ∑ k ∈ Finset.Icc 3 K,
      (oddPrimesSigned ∩ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X}).ncard := by
  have hsub := target_subset_finite_union R X hX K hK hvanish
  have hfin := biUnion_per_k_finite R X K
  have h1 : {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
        (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard ≤
    (⋃ k ∈ Finset.Icc 3 K,
      {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ (2 * k))).natAbs = ℓ}).ncard :=
    Set.ncard_le_ncard hsub hfin
  have h2 : (⋃ k ∈ Finset.Icc 3 K,
      {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ (2 * k))).natAbs = ℓ}).ncard ≤
    ∑ k ∈ Finset.Icc 3 K,
      {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard :=
    Finset.set_ncard_biUnion_le _ _
  have h3 : ∑ k ∈ Finset.Icc 3 K,
      {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard ≤
    ∑ k ∈ Finset.Icc 3 K,
      (oddPrimesSigned ∩ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X}).ncard :=
    Finset.sum_le_sum (fun k _ => per_k_odd_prime_ncard_le R k X hX)
  exact le_trans (le_trans h1 h2) h3

lemma odd_prime_ncard_le_sum (R : RamanujanTau) (X : ℝ) (hX : 0 < X)
    (K : ℕ) (hK : 3 ≤ K)
    (hvanish : ∀ k : ℕ, K < k → ∀ p : ℕ+, (p : ℕ).Prime →
      (R.τ (p ^ (2 * k))).natAbs ≠ 0 → ¬((↑(R.τ (p ^ (2 * k))).natAbs : ℝ) ≤ X)) :
    ({ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
        (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard : ℝ) ≤
    ∑ k ∈ Finset.Icc 3 K,
      ((oddPrimesSigned ∩ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X}).ncard : ℝ) := by
  exact_mod_cast target_ncard_le_sum_nat R X hX K hK hvanish

lemma target_eq_union (R : RamanujanTau) (X : ℝ) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
        (R.τ (p ^ (2 * k))).natAbs = ℓ} =
    {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ = 2 ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
        (R.τ (p ^ (2 * k))).natAbs = ℓ} ∪
    {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
        (R.τ (p ^ (2 * k))).natAbs = ℓ} := by
  apply Set.ext
  intro ℓ
  simp only [Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro h
    have h₁ : Nat.Prime ℓ := h.1
    have h₂ : (ℓ : ℝ) ≤ X := h.2.1
    have h₃ := h.2.2
    by_cases h₄ : ℓ = 2
    · exact Or.inl ⟨h₁, h₄, h₂, h₃⟩
    · exact Or.inr ⟨h₁, h₄, h₂, h₃⟩
  · intro h
    cases h with
    | inl h => exact ⟨h.1, h.2.2.1, h.2.2.2⟩
    | inr h => exact ⟨h.1, h.2.2.1, h.2.2.2⟩

lemma target_ncard_split (R : RamanujanTau) (X : ℝ) (_hX : 0 < X) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
        (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard ≤
    {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ = 2 ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
        (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard +
    {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
        (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard := by
  rw [target_eq_union R X]
  exact Set.ncard_union_le _ _

theorem target_ncard_le_sum (R : RamanujanTau) (X : ℝ) (hX : 0 < X)
    (K : ℕ) (hK : 3 ≤ K)
    (hvanish : ∀ k : ℕ, K < k → ∀ p : ℕ+, (p : ℕ).Prime →
      (R.τ (p ^ (2 * k))).natAbs ≠ 0 → ¬((↑(R.τ (p ^ (2 * k))).natAbs : ℝ) ≤ X)) :
    ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
        (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard : ℝ) ≤
    1 + ∑ k ∈ Finset.Icc 3 K,
      ((oddPrimesSigned ∩ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X}).ncard : ℝ) := by
  have hsplit := target_ncard_split R X hX
  have heven := even_prime_ncard_le R X hX
  have hodd := odd_prime_ncard_le_sum R X hX K hK hvanish
  calc ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
        (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard : ℝ) ≤
      ({ℓ : ℕ | Nat.Prime ℓ ∧ ℓ = 2 ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
          (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard : ℝ) +
      ({ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
          (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard : ℝ) := by
        exact_mod_cast hsplit
    _ ≤ 1 + ∑ k ∈ Finset.Icc 3 K,
        ((oddPrimesSigned ∩ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X}).ncard : ℝ) := by
        have h1 : ({ℓ : ℕ | Nat.Prime ℓ ∧ ℓ = 2 ∧ (ℓ : ℝ) ≤ X ∧
          ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
            (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard : ℝ) ≤ 1 := by exact_mod_cast heven
        linarith

lemma nat_gt_floor_imp_ge (a : ℝ) (k : ℕ) (hk : ⌊a⌋₊ < k) : (k : ℝ) ≥ a :=
  le_of_lt (Nat.lt_of_floor_lt hk)

lemma tau_mem_X2k (R : RamanujanTau) (k : ℕ) (p : ℕ+) (hp : (p : ℕ).Prime) :
    R.τ (p ^ (2 * k)) ∈ X2k R k := by
  refine ⟨p, hp, ?_⟩
  simp [mul_comm]

lemma not_abs_le_of_mem_empty_inter (R : RamanujanTau) (k : ℕ) (X : ℝ) (z : ℤ)
    (hmem : z ∈ X2k R k)
    (hempty : X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X} = ∅) :
    ¬((|z| : ℝ) ≤ X) := by
  intro h₃
  have := hempty ▸ Set.mem_inter hmem (by simpa using h₃ : z ∈ {z : ℤ | (|z| : ℝ) ≤ X})
  exact Set.notMem_empty _ this

lemma natAbs_cast_eq_abs_cast (n : ℤ) :
    (↑n.natAbs : ℝ) = (|↑n| : ℝ) := by
  norm_cast
  exact Nat.cast_natAbs n

lemma not_le_of_empty_inter (R : RamanujanTau) (k : ℕ) (X : ℝ)
    (hempty : X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X} = ∅)
    (p : ℕ+) (hp : (p : ℕ).Prime)
    (_hne : (R.τ (p ^ (2 * k))).natAbs ≠ 0) :
    ¬((↑(R.τ (p ^ (2 * k))).natAbs : ℝ) ≤ X) := by
  have hmem := tau_mem_X2k R k p hp
  have habs := not_abs_le_of_mem_empty_inter R k X _ hmem hempty
  rw [natAbs_cast_eq_abs_cast]
  exact habs

lemma vanishing_large_k (R : RamanujanTau) (h54_part2 : ∃ c₅ : ℝ, 0 < c₅ ∧
    ∀ N : ℝ, c₅ < N →
      ∀ k : ℕ, (k : ℝ) ≥ Real.log N / (2 * Real.log 2) →
        X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ N} = ∅) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ < X →
      ∀ k : ℕ, ⌊Real.log X / (2 * Real.log 2)⌋₊ < k →
        ∀ p : ℕ+, (p : ℕ).Prime →
          (R.τ (p ^ (2 * k))).natAbs ≠ 0 → ¬((↑(R.τ (p ^ (2 * k))).natAbs : ℝ) ≤ X) := by
  obtain ⟨c₅, hc₅_pos, hc₅⟩ := h54_part2
  exact ⟨c₅, hc₅_pos, fun X hX k hk p hp hne => by
    have hge : (k : ℝ) ≥ Real.log X / (2 * Real.log 2) :=
      nat_gt_floor_imp_ge _ _ hk
    exact not_le_of_empty_inter R k X (hc₅ X hX k hge) p hp hne⟩

lemma six_mul_log_two_le_log (X : ℝ) (hX : 64 < X) :
    6 * Real.log 2 ≤ Real.log X := by
  have h₁ : Real.log 64 = 6 * Real.log 2 := by
    have h₂ : Real.log 64 = Real.log (2 ^ 6) := by norm_num
    rw [h₂]
    have h₃ : Real.log (2 ^ 6 : ℝ) = 6 * Real.log 2 := by
      rw [Real.log_pow]; norm_num
    rw [h₃]
  have h₂ : Real.log 64 < Real.log X := by
    have h₃ : (64 : ℝ) < X := by exact_mod_cast hX
    exact Real.log_lt_log (by positivity) h₃
  linarith

lemma log_div_two_log_two_gt_three (X : ℝ) (hX : 64 < X) :
    (3 : ℝ) ≤ Real.log X / (2 * Real.log 2) := by
  have h2log2 : (0 : ℝ) < 2 * Real.log 2 := by positivity
  rw [le_div_iff₀ h2log2]
  linarith [six_mul_log_two_le_log X hX]

lemma rpow_half_nonneg {X : ℝ} (hX : 0 < X) :
    0 ≤ X ^ ((1 : ℝ) / 2) := by
  have h : 0 ≤ (X : ℝ) := by positivity
  exact Real.rpow_nonneg h _

lemma triple_inter_empty_of_X2k_inter_empty (R : RamanujanTau) (k : ℕ) (X : ℝ)
    (h : X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X} = ∅) :
    oddPrimesSigned ∩ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X} = ∅ := by
  rw [Set.inter_assoc]
  exact Set.subset_eq_empty Set.inter_subset_right h

lemma per_k_ncard_le_rpow_half (R : RamanujanTau) (h54 : Proposition54 R) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ < X →
      ∀ k ∈ Finset.Icc 3 ⌊Real.log X / (2 * Real.log 2)⌋₊,
        ((oddPrimesSigned ∩ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X}).ncard : ℝ) ≤
        C * X ^ ((1 : ℝ) / 2) := by
  obtain ⟨⟨c₄, C₄, hc₄_pos, hC₄_pos, hpart1⟩, ⟨c₅, _, hpart2⟩⟩ := h54
  refine ⟨C₄, hC₄_pos, max c₄ c₅, lt_max_of_lt_left hc₄_pos, ?_⟩
  intro X hX_gt k hk_mem
  rw [Finset.mem_Icc] at hk_mem
  obtain ⟨hk_lo, _⟩ := hk_mem
  by_cases hk_lt : (k : ℝ) < Real.log X / (2 * Real.log 2)
  · have hX_gt_c₄ : c₄ < X := lt_of_le_of_lt (le_max_left c₄ c₅) hX_gt
    exact hpart1 X hX_gt_c₄ k hk_lo hk_lt
  · have hX_gt_c₅ : c₅ < X := lt_of_le_of_lt (le_max_right c₄ c₅) hX_gt
    push Not at hk_lt
    have hempty := hpart2 X hX_gt_c₅ k hk_lt
    rw [triple_inter_empty_of_X2k_inter_empty R k X hempty,
      show ((∅ : Set ℤ).ncard : ℝ) = 0 by simp]
    exact mul_nonneg hC₄_pos.le (rpow_half_nonneg (lt_trans (lt_max_of_lt_left hc₄_pos) hX_gt))

lemma sum_const_le_floor_mul (a : ℝ) (ha : 0 ≤ a) (c : ℝ) (hc : 0 ≤ c) :
    ∑ _k ∈ Finset.Icc 3 ⌊a⌋₊, c ≤ a * c := by
  rw [Finset.sum_const, nsmul_eq_mul]
  have : ((Finset.Icc 3 ⌊a⌋₊).card : ℝ) ≤ ⌊a⌋₊ := by
    simp only [Nat.card_Icc]; exact_mod_cast show ⌊a⌋₊ + 1 - 3 ≤ ⌊a⌋₊ by omega
  exact mul_le_mul_of_nonneg_right (this.trans (Nat.floor_le ha)) hc

lemma sum_per_k_bound (R : RamanujanTau) (h54 : Proposition54 R) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ < X →
      ∑ k ∈ Finset.Icc 3 ⌊Real.log X / (2 * Real.log 2)⌋₊,
        ((oddPrimesSigned ∩ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X}).ncard : ℝ) ≤
      C * (Real.log X / (2 * Real.log 2) * X ^ ((1 : ℝ) / 2)) := by
  obtain ⟨C, hC_pos, X₀, hX₀_pos, hX₀⟩ := per_k_ncard_le_rpow_half R h54
  refine ⟨C, hC_pos, max X₀ 64, lt_max_of_lt_left hX₀_pos, fun X hX => ?_⟩
  have hX_gt : X₀ < X := lt_of_le_of_lt (le_max_left X₀ 64) hX
  have hX_64 : 64 < X := lt_of_le_of_lt (le_max_right X₀ 64) hX
  have hX_pos : 0 < X := by linarith
  have ha_nonneg : 0 ≤ Real.log X / (2 * Real.log 2) :=
    le_trans (by norm_num : (0 : ℝ) ≤ 3) (log_div_two_log_two_gt_three X hX_64)
  calc ∑ k ∈ Finset.Icc 3 ⌊Real.log X / (2 * Real.log 2)⌋₊,
        ((oddPrimesSigned ∩ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X}).ncard : ℝ)
      ≤ ∑ _ ∈ Finset.Icc 3 ⌊Real.log X / (2 * Real.log 2)⌋₊,
        C * X ^ ((1 : ℝ) / 2) :=
          Finset.sum_le_sum (fun k hk => hX₀ X hX_gt k hk)
    _ ≤ Real.log X / (2 * Real.log 2) * (C * X ^ ((1 : ℝ) / 2)) :=
          sum_const_le_floor_mul (Real.log X / (2 * Real.log 2))
            ha_nonneg (C * X ^ ((1 : ℝ) / 2))
            (mul_nonneg hC_pos.le (rpow_half_nonneg hX_pos))
    _ = C * (Real.log X / (2 * Real.log 2) * X ^ ((1 : ℝ) / 2)) := by ring

lemma floor_log_ge_three (X : ℝ) (hX : 64 < X) :
    3 ≤ ⌊Real.log X / (2 * Real.log 2)⌋₊ := Nat.le_floor (log_div_two_log_two_gt_three X hX)

lemma one_le_sqrt_mul_log (X : ℝ) (hX : Real.exp 1 < X) :
    1 ≤ X ^ ((1 : ℝ) / 2) * Real.log X := by
  have h₁ : 1 < Real.log X := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log X := Real.log_lt_log (by linarith [Real.add_one_le_exp 1]) hX
  have h₂ : 1 ≤ X ^ ((1 : ℝ) / 2) := by
    apply Real.one_le_rpow
    · linarith [Real.exp_one_gt_d9.le]
    · linarith
  nlinarith

lemma log_div_mul_eq (X : ℝ) (hX : 0 < X) :
    Real.log X / (2 * Real.log 2) * X ^ ((1 : ℝ) / 2) =
    1 / (2 * Real.log 2) * (X ^ ((1 : ℝ) / 2) * Real.log X) := by
  have h1 : Real.log 2 > 0 := Real.log_pos (by norm_num)
  have h2 : 2 * Real.log 2 ≠ 0 := by linarith
  calc
    Real.log X / (2 * Real.log 2) * X ^ ((1 : ℝ) / 2)
        = (Real.log X / (2 * Real.log 2)) * X ^ ((1 : ℝ) / 2) := by ring
    _ = (Real.log X * (1 / (2 * Real.log 2))) * X ^ ((1 : ℝ) / 2) := by
      field_simp [h2]
    _ = (1 / (2 * Real.log 2)) * (Real.log X * X ^ ((1 : ℝ) / 2)) := by
      ring_nf
    _ = (1 / (2 * Real.log 2)) * (X ^ ((1 : ℝ) / 2) * Real.log X) := by
      ring_nf
    _ = 1 / (2 * Real.log 2) * (X ^ ((1 : ℝ) / 2) * Real.log X) := by ring

lemma final_arithmetic_bound (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ < X →
      1 + A * (Real.log X / (2 * Real.log 2) * X ^ ((1 : ℝ) / 2)) ≤
      C * (X ^ ((1 : ℝ) / 2) * Real.log X) := by
  refine ⟨1 + A / (2 * Real.log 2),
    by have : 0 < A / (2 * Real.log 2) := div_pos hA (by positivity); linarith,
    Real.exp 1, Real.exp_pos 1, fun X hX => ?_⟩
  have h1 : 1 ≤ X ^ ((1 : ℝ) / 2) * Real.log X := one_le_sqrt_mul_log X hX
  have hXpos : 0 < X := lt_trans (Real.exp_pos 1) hX
  rw [log_div_mul_eq X hXpos]
  calc
    1 + A * (1 / (2 * Real.log 2) * (X ^ ((1 : ℝ) / 2) * Real.log X))
        = 1 + (A / (2 * Real.log 2)) * (X ^ ((1 : ℝ) / 2) * Real.log X) := by ring_nf
    _ ≤ (X ^ ((1 : ℝ) / 2) * Real.log X) +
        (A / (2 * Real.log 2)) * (X ^ ((1 : ℝ) / 2) * Real.log X) := by
          linarith
    _ = (1 + A / (2 * Real.log 2)) * (X ^ ((1 : ℝ) / 2) * Real.log X) := by ring

lemma k_ge3_contribution (R : RamanujanTau) (h54 : Proposition54 R) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
          ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
            (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard : ℝ) ≤
        C * (X ^ ((1 : ℝ) / 2) * Real.log X) := by
  obtain ⟨h54_1, h54_2⟩ := h54
  obtain ⟨X₁, hX₁_pos, hX₁_vanish⟩ := vanishing_large_k R h54_2
  obtain ⟨Csum, hCsum_pos, X₂, hX₂_pos, hX₂_sum⟩ := sum_per_k_bound R ⟨h54_1, h54_2⟩
  obtain ⟨C, hC_pos, X₃, hX₃_pos, hX₃_arith⟩ := final_arithmetic_bound Csum hCsum_pos
  refine ⟨C, hC_pos, max (max (max X₁ X₂) X₃) 64, by positivity, ?_⟩
  intro X hX
  have hX64 : 64 < X := lt_of_le_of_lt (le_max_right _ (64 : ℝ)) hX
  have hX_maxL : max (max X₁ X₂) X₃ < X :=
    lt_of_le_of_lt (le_max_left _ (64 : ℝ)) hX
  have hX_X1 : X₁ < X :=
    lt_of_le_of_lt (le_max_left X₁ X₂ |>.trans (le_max_left _ X₃)) hX_maxL
  have hX_X2 : X₂ < X :=
    lt_of_le_of_lt (le_max_right X₁ X₂ |>.trans (le_max_left _ X₃)) hX_maxL
  have hX_X3 : X₃ < X := lt_of_le_of_lt (le_max_right _ X₃) hX_maxL
  have hX_pos : (0 : ℝ) < X := by linarith
  set K := ⌊Real.log X / (2 * Real.log 2)⌋₊ with hK_def
  have hK3 : 3 ≤ K := floor_log_ge_three X hX64
  have hstep1 := target_ncard_le_sum R X hX_pos K hK3
    (hX₁_vanish X hX_X1)
  have hstep2 := hX₂_sum X hX_X2
  have hstep3 := hX₃_arith X hX_X3
  calc ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
          ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
            (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard : ℝ)
      ≤ 1 + ∑ k ∈ Finset.Icc 3 K,
          ((oddPrimesSigned ∩ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X}).ncard : ℝ) := hstep1
    _ ≤ 1 + Csum * (Real.log X / (2 * Real.log 2) * X ^ ((1 : ℝ) / 2)) := by linarith
    _ ≤ C * (X ^ ((1 : ℝ) / 2) * Real.log X) := hstep3

lemma tau_one_zero_or_one (R : RamanujanTau) : R.τ 1 = 0 ∨ R.τ 1 = 1 := by
  have h₁ : R.τ 1 = R.τ 1 * R.τ 1 := by
    have := R.hecke_mult 1 1 (by decide : Nat.Coprime 1 1)
    simpa using this
  have h₂ : R.τ 1 * (R.τ 1 - 1) = 0 := by linarith [h₁]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h₂ with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

lemma tau_one_ne_zero (R : RamanujanTau) : R.τ 1 ≠ 0 := by
  have h₁ : ¬(2 : ℤ) ∣ R.τ 1 :=
    (R.parity ⟨1, by norm_num⟩).mpr ⟨by decide, 1, by norm_num⟩
  intro h
  exact h₁ (h ▸ ⟨0, by ring⟩)

lemma tau_one_eq_one (R : RamanujanTau) : R.τ 1 = 1 := by
  rcases tau_one_zero_or_one R with h | h
  · exact absurd h (tau_one_ne_zero R)
  · exact h

lemma ordCompl_ge_two_of_not_isPrimePow (n : ℕ) (hn : 2 ≤ n) (hnp : ¬ IsPrimePow n)
    (p : ℕ) (hp : Nat.Prime p) (_hpn : p ∣ n) :
    2 ≤ n / p ^ n.factorization p := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hpos := Nat.ordCompl_pos p hn0
  have hne1 : n / p ^ n.factorization p ≠ 1 := by
    intro heq
    have := (exists_ordCompl_eq_one_iff_isPrimePow hn1).mpr ⟨p, hp, heq⟩
    exact hnp this
  omega

lemma ordProj_ge_two (n : ℕ) (p : ℕ) (hp : Nat.Prime p) (hn : n ≠ 0)
    (hpn : p ∣ n) : 2 ≤ p ^ n.factorization p := by
  have hfact : n.factorization p ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (hp.factorization_pos_of_dvd hn hpn)
  calc 2 ≤ p := hp.two_le
    _ ≤ p ^ n.factorization p := le_self_pow (Nat.one_le_iff_ne_zero.mpr hp.ne_zero) hfact

lemma ordProj_coprime_ordCompl (n : ℕ) (p : ℕ) (hp : Nat.Prime p) (hn : n ≠ 0)
    (hpn : p ∣ n) :
    Nat.Coprime (p ^ n.factorization p) (n / p ^ n.factorization p) :=
  (Nat.coprime_pow_left_iff (hp.factorization_pos_of_dvd hn hpn) p _).mpr
    (Nat.coprime_ordCompl hp hn)

lemma lift_to_pnat_factorization (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (hnp : ¬ IsPrimePow (n : ℕ))
    (p : ℕ) (hp : Nat.Prime p) (hpn : p ∣ (n : ℕ)) :
    ∃ (u v : ℕ+), (u : ℕ) * (v : ℕ) = (n : ℕ) ∧
      Nat.Coprime (u : ℕ) (v : ℕ) ∧ 2 ≤ (u : ℕ) ∧ 2 ≤ (v : ℕ) := by
  set pe := p ^ (n : ℕ).factorization p with hpe_def
  set nc := (n : ℕ) / pe with hnc_def
  have hn0 : (n : ℕ) ≠ 0 := by omega
  have hpe_ge : 2 ≤ pe := ordProj_ge_two (n : ℕ) p hp hn0 hpn
  have hnc_ge : 2 ≤ nc := ordCompl_ge_two_of_not_isPrimePow (n : ℕ) hn hnp p hp hpn
  have hcop : Nat.Coprime pe nc := ordProj_coprime_ordCompl (n : ℕ) p hp hn0 hpn
  have hprod : pe * nc = (n : ℕ) := Nat.ordProj_mul_ordCompl_eq_self (n : ℕ) p
  refine ⟨⟨pe, by omega⟩, ⟨nc, by omega⟩, ?_, ?_, ?_, ?_⟩
  · exact hprod
  · exact hcop
  · exact hpe_ge
  · exact hnc_ge

lemma exists_coprime_factorization_of_not_isPrimePow (n : ℕ+) (hn : 2 ≤ (n : ℕ))
    (hnp : ¬ IsPrimePow (n : ℕ)) :
    ∃ (u v : ℕ+), (u : ℕ) * (v : ℕ) = (n : ℕ) ∧
      Nat.Coprime (u : ℕ) (v : ℕ) ∧ 2 ≤ (u : ℕ) ∧ 2 ≤ (v : ℕ) := by
  have hn1 : (n : ℕ) ≠ 1 := by omega
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
  exact lift_to_pnat_factorization n hn hnp p hp hpn

lemma natAbs_tau_eq_one_of_coprime_factor (R : RamanujanTau) (u v : ℕ+)
    (hcop : Nat.Coprime (u : ℕ) (v : ℕ))
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hτ : (R.τ (u * v)).natAbs = ℓ) :
    (R.τ u).natAbs = 1 ∨ (R.τ v).natAbs = 1 := by
  have h1 : (R.τ u).natAbs * (R.τ v).natAbs = ℓ := by
    rw [← Int.natAbs_mul, ← R.hecke_mult u v hcop]
    exact hτ
  rcases hℓ.eq_one_or_self_of_dvd _ ⟨_, h1.symm⟩ with h | h
  · exact Or.inl h
  · exact Or.inr (by nlinarith [hℓ.pos])

lemma tau_prime_imp_prime_power (R : RamanujanTau) (n : ℕ+) (hn : 2 ≤ (n : ℕ))
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hτ : (R.τ n).natAbs = ℓ) :
    IsPrimePow (n : ℕ) := by
  by_contra hnp
  obtain ⟨u, v, huv_eq, hcop, hu2, hv2⟩ :=
    exists_coprime_factorization_of_not_isPrimePow n hn hnp
  have huv_pnat : u * v = n := PNat.eq (by simp only [PNat.mul_coe]; exact huv_eq)
  rw [← huv_pnat] at hτ
  have h := natAbs_tau_eq_one_of_coprime_factor R u v hcop ℓ hℓ hτ
  rcases h with hu1 | hv1
  · have hu_unit : IsUnit (R.τ u) := Int.isUnit_iff_natAbs_eq.mpr hu1
    have ⟨hne1, hne_neg1⟩ := R.non_unit u hu2
    rcases Int.isUnit_eq_one_or hu_unit with h1 | h1 <;> contradiction
  · have hv_unit : IsUnit (R.τ v) := Int.isUnit_iff_natAbs_eq.mpr hv1
    have ⟨hne1, hne_neg1⟩ := R.non_unit v hv2
    rcases Int.isUnit_eq_one_or hv_unit with h1 | h1 <;> contradiction

lemma tau_not_two_dvd_of_odd_prime (R : RamanujanTau) (n : ℕ+)
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hℓ_odd : ℓ ≠ 2)
    (hτ : (R.τ n).natAbs = ℓ) :
    ¬(2 ∣ R.τ n) := by
  intro h2
  have hodd : Odd ℓ := hℓ.eq_two_or_odd'.resolve_left hℓ_odd
  have hndvd : ¬(2 ∣ ℓ) := hodd.not_two_dvd_nat
  exact hndvd (hτ ▸ Int.natCast_dvd.mp h2)

lemma tau_odd_prime_imp_odd_square (R : RamanujanTau) (n : ℕ+)
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hℓ_odd : ℓ ≠ 2)
    (hτ : (R.τ n).natAbs = ℓ) :
    Odd (n : ℕ) ∧ IsSquare (n : ℕ) :=
  (R.parity n).mp (tau_not_two_dvd_of_odd_prime R n ℓ hℓ hℓ_odd hτ)

lemma prime_pow_sq_even_exp_via_factorization (p a m : ℕ) (hp : Nat.Prime p) (_ha : 0 < a)
    (hm : p ^ a = m ^ 2) : a = 2 * m.factorization p := by
  have key : (p ^ a).factorization p = (m ^ 2).factorization p := by rw [hm]
  simpa [Nat.factorization_pow, hp.factorization_self] using key

lemma prime_pow_sq_even_exp (p a : ℕ) (hp : Nat.Prime p) (ha : 0 < a)
    (hsq : IsSquare (p ^ a)) : ∃ k, a = 2 * k := by
  rw [isSquare_iff_exists_sq] at hsq
  obtain ⟨m, hm⟩ := hsq
  exact ⟨m.factorization p, prime_pow_sq_even_exp_via_factorization p a m hp ha hm⟩

lemma prime_power_odd_square_form (n : ℕ+) (hn : 2 ≤ (n : ℕ))
    (hpp : IsPrimePow (n : ℕ))
    (hodd : Odd (n : ℕ)) (hsq : IsSquare (n : ℕ)) :
    ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 1 ≤ k ∧ (n : ℕ) = (p : ℕ) ^ (2 * k) := by
  set p := (n : ℕ).minFac with hp_def
  have hn1 : (n : ℕ) ≠ 1 := by omega
  have hprime : p.Prime := Nat.minFac_prime hn1
  set a := (n : ℕ).factorization p with ha_def
  have hna : p ^ a = (n : ℕ) := hpp.minFac_pow_factorization_eq
  have ha_pos : 0 < a := by
    rw [ha_def]; exact (Nat.factorization_minFac_ne_zero (by omega : 1 < (n : ℕ))).bot_lt
  have hsq_pa : IsSquare (p ^ a) := hna ▸ hsq
  obtain ⟨k, hk⟩ := prime_pow_sq_even_exp p a hprime ha_pos hsq_pa
  have hk_pos : 1 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k
    simp at hk
    omega
  have hp_odd : Odd p := by
    rcases hprime.eq_two_or_odd' with hp2 | hodd_p
    · exfalso
      have : Odd (p ^ a) := hna ▸ hodd
      rw [Nat.odd_pow_iff (by omega : a ≠ 0)] at this
      rw [hp2] at this
      simp [Nat.odd_iff] at this
    · exact hodd_p
  have hp_pos : 0 < p := hprime.pos
  refine ⟨⟨p, hp_pos⟩, hprime, k, hk_pos, ?_⟩
  rw [hk] at hna
  exact hna.symm

lemma witness_ge_two (R : RamanujanTau) (n : ℕ+) (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (hτ : (R.τ n).natAbs = ℓ) : 2 ≤ (n : ℕ) := by
  by_contra h
  push Not at h
  have hn_pos := n.pos
  have hn1 : (n : ℕ) = 1 := by omega
  rw [show n = (1 : ℕ+) from PNat.eq (by exact hn1), tau_one_eq_one] at hτ
  simp at hτ
  linarith [hℓ.one_lt]

lemma tau_eq_of_pnat_eq_pow (R : RamanujanTau) (n : ℕ+) (p : ℕ+) (k : ℕ)
    (heq : (n : ℕ) = (p : ℕ) ^ (2 * k)) :
    R.τ n = R.τ (p ^ (2 * k)) := by
  congr 1
  apply PNat.coe_injective
  rw [PNat.pow_coe]
  exact heq

lemma S_set_subset_union (R : RamanujanTau) (X : ℝ) (_hX : 1 < X) :
    tauPrimeSet R X ⊆
      {2} ∪
      {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 2)).natAbs = ℓ} ∪
      {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 4)).natAbs = ℓ} ∪
      {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
          (R.τ (p ^ (2 * k))).natAbs = ℓ} := by
  intro ℓ hℓ_mem
  simp only [tauPrimeSet, Set.mem_setOf_eq] at hℓ_mem
  obtain ⟨hprime, hle, n, hτ⟩ := hℓ_mem
  rcases hprime.eq_two_or_odd' with rfl | hodd_ℓ
  · left; left; left
    exact Set.mem_singleton 2
  · have hℓ_ne2 : ℓ ≠ 2 := by intro h; subst h; simp [Nat.odd_iff] at hodd_ℓ
    have ⟨hodd_n, hsq_n⟩ := tau_odd_prime_imp_odd_square R n ℓ hprime hℓ_ne2 hτ
    have hn2 := witness_ge_two R n ℓ hprime hτ
    have hpp := tau_prime_imp_prime_power R n hn2 ℓ hprime hτ
    obtain ⟨p, hp_prime, k, hk1, heq⟩ := prime_power_odd_square_form n hn2 hpp hodd_n hsq_n
    have hτ_eq := tau_eq_of_pnat_eq_pow R n p k heq
    have hτ' : (R.τ (p ^ (2 * k))).natAbs = ℓ := by rw [← hτ_eq]; exact hτ
    rcases le_or_gt k 2 with hk_le | hk_ge
    · interval_cases k
      · left; left; right
        exact ⟨hprime, hle, p, hp_prime, hτ'⟩
      · left; right
        exact ⟨hprime, hle, p, hp_prime, hτ'⟩
    · right
      exact ⟨hprime, hle, p, hp_prime, k, hk_ge, hτ'⟩

lemma nat_bounded_by_real_finite (X : ℝ) : {n : ℕ | (n : ℝ) ≤ X}.Finite := by
  obtain ⟨k, hk⟩ := exists_nat_gt X
  exact (Set.finite_Iic k).subset fun n (hn : (n : ℝ) ≤ X) => by
    exact_mod_cast le_of_lt (lt_of_le_of_lt hn hk)

lemma A_sets_finite (X : ℝ) :
    ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 2)).natAbs = ℓ} ∪
     {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 4)).natAbs = ℓ} ∪
     {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
        (R.τ (p ^ (2 * k))).natAbs = ℓ}).Finite := by
  apply Set.Finite.subset (nat_bounded_by_real_finite X)
  intro ℓ hℓ
  simp only [Set.mem_union, Set.mem_setOf_eq] at hℓ ⊢
  obtain (⟨-, hle, -⟩ | ⟨-, hle, -⟩) | ⟨-, hle, -⟩ := hℓ <;> exact hle

lemma full_union_finite (R : RamanujanTau) (X : ℝ) :
    ({2} ∪
     {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
       ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 2)).natAbs = ℓ} ∪
     {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
       ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 4)).natAbs = ℓ} ∪
     {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
       ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
         (R.τ (p ^ (2 * k))).natAbs = ℓ}).Finite := by
  have hA := A_sets_finite R X
  have hA1 : ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
    ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 2)).natAbs = ℓ}).Finite :=
    hA.subset (Set.subset_union_left.trans Set.subset_union_left)
  have hA2 : ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
    ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 4)).natAbs = ℓ}).Finite :=
    hA.subset (Set.subset_union_right.trans Set.subset_union_left)
  have hA3 : ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
    ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
      (R.τ (p ^ (2 * k))).natAbs = ℓ}).Finite :=
    hA.subset Set.subset_union_right
  exact ((Set.finite_singleton 2).union hA1).union hA2 |>.union hA3

lemma ncard_four_union_le_nat (A B C D : Set ℕ) (a : ℕ) (hA : A = {a}) :
    (A ∪ B ∪ C ∪ D).ncard ≤ 1 + B.ncard + C.ncard + D.ncard := by
  have hA_card : A.ncard = 1 := by
    rw [hA]
    simp [Set.ncard_singleton]
  have h₁ : (A ∪ B).ncard ≤ 1 + B.ncard := by
    have h₂ : (A ∪ B).ncard ≤ A.ncard + B.ncard := by
      apply Set.ncard_union_le
    linarith
  have h₂ : (A ∪ B ∪ C).ncard ≤ 1 + B.ncard + C.ncard := by
    have h₃ : (A ∪ B ∪ C).ncard ≤ (A ∪ B).ncard + C.ncard := by
      calc
        (A ∪ B ∪ C).ncard = ((A ∪ B) ∪ C).ncard := by simp [Set.union_assoc]
        _ ≤ (A ∪ B).ncard + C.ncard := by
          apply Set.ncard_union_le
    linarith
  have h₃ : (A ∪ B ∪ C ∪ D).ncard ≤ 1 + B.ncard + C.ncard + D.ncard := by
    have h₄ : (A ∪ B ∪ C ∪ D).ncard ≤ (A ∪ B ∪ C).ncard + D.ncard := by
      calc
        (A ∪ B ∪ C ∪ D).ncard = ((A ∪ B ∪ C) ∪ D).ncard := by
          simp [Set.union_assoc]
        _ ≤ (A ∪ B ∪ C).ncard + D.ncard := by
          apply Set.ncard_union_le
    linarith
  exact h₃

lemma ncard_four_union_le (R : RamanujanTau) (X : ℝ) :
    (({2} ∪
     {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
       ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 2)).natAbs = ℓ} ∪
     {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
       ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 4)).natAbs = ℓ} ∪
     {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
       ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
         (R.τ (p ^ (2 * k))).natAbs = ℓ}).ncard : ℝ) ≤
    1 +
    ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 2)).natAbs = ℓ}.ncard : ℝ) +
    ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 4)).natAbs = ℓ}.ncard : ℝ) +
    ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
        (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard : ℝ) := by
  have h := ncard_four_union_le_nat
    ({2} : Set ℕ)
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧ ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 2)).natAbs = ℓ}
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧ ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 4)).natAbs = ℓ}
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧ (R.τ (p ^ (2 * k))).natAbs = ℓ}
    2 rfl
  exact_mod_cast h

lemma S_decomposition (R : RamanujanTau) (X : ℝ) (hX : 1 < X) :
    (S R X : ℝ) ≤ 1 +
      ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 2)).natAbs = ℓ}.ncard : ℝ) +
      ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 4)).natAbs = ℓ}.ncard : ℝ) +
      ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
          (R.τ (p ^ (2 * k))).natAbs = ℓ}.ncard : ℝ) := by
  have hsub := S_set_subset_union R X hX
  have hfin := full_union_finite R X
  have hcard := ncard_four_union_le R X
  unfold S tauPrimeSet
  calc (({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧ ∃ n : ℕ+, (R.τ n).natAbs = ℓ}.ncard : ℝ))
      ≤ (({2} ∪
          {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
            ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 2)).natAbs = ℓ} ∪
          {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
            ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 4)).natAbs = ℓ} ∪
          {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
            ∃ p : ℕ+, (p : ℕ).Prime ∧ ∃ k : ℕ, 3 ≤ k ∧
              (R.τ (p ^ (2 * k))).natAbs = ℓ}).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hfin
    _ ≤ _ := hcard

lemma L_subset_union (R : RamanujanTau) (X : ℝ) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ} ⊆
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ ∧
        (p : ℝ) > X ^ ((2 : ℝ) / 11)} ∪
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ ∧
        (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)} := by
  intro ℓ hℓ
  obtain ⟨hprime, hle, p, hp, htau⟩ := hℓ
  rcases le_or_gt (↑↑p : ℝ) (X ^ ((2 : ℝ) / 11)) with h | h
  · right
    exact ⟨hprime, hle, p, hp, htau, h⟩
  · left
    exact ⟨hprime, hle, p, hp, htau, h⟩

lemma bounded_nat_set_finite (X : ℝ) : {ℓ : ℕ | (ℓ : ℝ) ≤ X}.Finite := by
  apply Set.Finite.subset (Set.finite_Iio (⌊X⌋₊ + 1))
  intro ℓ hℓ
  simp only [Set.mem_setOf_eq] at hℓ
  simp only [Set.mem_Iio]
  exact Nat.lt_of_le_of_lt (Nat.le_floor hℓ) (Nat.lt_succ_iff.mpr le_rfl)

lemma L_union_finite (R : RamanujanTau) (X : ℝ) :
    ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ ∧
        (p : ℝ) > X ^ ((2 : ℝ) / 11)} ∪
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ ∧
        (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}).Finite := by
  apply Set.Finite.subset (bounded_nat_set_finite X)
  intro ℓ hℓ
  simp only [Set.mem_union, Set.mem_setOf_eq] at hℓ ⊢
  rcases hℓ with ⟨_, hle, _⟩ | ⟨_, hle, _⟩ <;> exact hle

lemma ell_split_large_small (R : RamanujanTau) (X : ℝ) :
    ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ}.ncard : ℝ) ≤
    ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ ∧
        (p : ℝ) > X ^ ((2 : ℝ) / 11)}.ncard : ℝ) +
    ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ ∧
        (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}.ncard : ℝ) := by
  have hsub := L_subset_union R X
  have hfin := L_union_finite R X
  have h1 : {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ}.ncard ≤
    ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ ∧
        (p : ℝ) > X ^ ((2 : ℝ) / 11)} ∪
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ ∧
        (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}).ncard :=
    Set.ncard_le_ncard hsub hfin
  have h2 := Set.ncard_union_le
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ ∧
        (p : ℝ) > X ^ ((2 : ℝ) / 11)}
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ ∧
        (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}
  exact_mod_cast le_trans h1 h2

lemma bounded_nat_set_finite_real (B : ℝ) :
    {n : ℕ | (n : ℝ) ≤ B}.Finite := by
  by_cases hB : B < 0
  · convert Set.finite_empty
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · push Not at hB
    exact Set.Finite.subset (Finset.finite_toSet (Finset.range (⌊B⌋₊ + 1)))
      fun n hn => Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hn)))

lemma pnat_bounded_finite (B : ℝ) :
    {p : ℕ+ | (p : ℝ) ≤ B}.Finite :=
  (bounded_nat_set_finite_real B).preimage PNat.coe_injective.injOn

lemma bounded_pnat_int_subset (S : Set (ℕ+ × ℤ)) (N : ℕ) (M : ℕ)
    (hS : ∀ p ∈ S, (p.1 : ℕ) ≤ N ∧ |p.2| ≤ (M : ℤ)) :
    S ⊆ {q : ℕ+ | (q : ℝ) ≤ (N : ℝ)} ×ˢ Set.Icc (-(M : ℤ)) (M : ℤ) := by
  intro p hp
  obtain ⟨h1, h2⟩ := hS p hp
  simp only [Set.mem_prod, Set.mem_setOf_eq, Set.mem_Icc]
  exact ⟨Nat.cast_le.mpr (Nat.cast_le.mpr h1), abs_le.mp h2⟩

lemma bounded_pnat_int_set_finite (S : Set (ℕ+ × ℤ)) (N : ℕ) (M : ℕ)
    (hS : ∀ p ∈ S, (p.1 : ℕ) ≤ N ∧ |p.2| ≤ (M : ℤ)) : S.Finite := by
  have hfin1 : {p : ℕ+ | (p : ℝ) ≤ (N : ℝ)}.Finite := pnat_bounded_finite N
  have hfin2 : (Set.Icc (-(M : ℤ)) (M : ℤ)).Finite := Set.finite_Icc _ _
  exact (hfin1.prod hfin2).subset (bounded_pnat_int_subset S N M hS)

lemma real_bound_to_nat_bound (p : ℕ+ × ℤ) (B : ℝ) (hB : (p.1 : ℝ) ≤ B) :
    (p.1 : ℕ) ≤ ⌈B⌉₊ := Nat.cast_le.mp (hB.trans (Nat.le_ceil B))

lemma abc_specialize_half (habc : ABC) :
    ∃ K : ℝ, 0 < K ∧
      ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → a + b = c →
          (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by
  obtain ⟨K, hK, hABC⟩ := habc (1 / 2) (by norm_num)
  exact ⟨K, hK, fun a b c ha hb hc hcop heq => by
    have := hABC a b c ha hb hc hcop heq
    rwa [show (1 : ℝ) + 1 / 2 = 3 / 2 from by norm_num] at this⟩

lemma E2_ysq_le_x11_add_X_int_step (X : ℝ) (p : ℕ+ × ℤ)
    (h3 : (|(↑p.1 : ℤ) ^ 11 - p.2 ^ 2| : ℝ) ≤ X) :
    (p.2 : ℝ) ^ 2 - ((p.1 : ℕ) : ℝ) ^ 11 ≤ X := by
  have h3' : |((↑↑p.1 : ℝ) ^ 11 - (↑p.2 : ℝ) ^ 2)| ≤ X := by
    convert h3 using 2
    push_cast
    ring
  linarith [neg_le_abs ((↑↑p.1 : ℝ) ^ 11 - (↑p.2 : ℝ) ^ 2)]

lemma E2_ysq_le_x11_add_X_helper (X : ℝ) (p : ℕ+ × ℤ)
    (h3 : (|(↑p.1 : ℤ) ^ 11 - p.2 ^ 2| : ℝ) ≤ X) :
    (p.2 : ℝ) ^ 2 ≤ ((p.1 : ℕ) : ℝ) ^ 11 + X := by
  linarith [E2_ysq_le_x11_add_X_int_step X p h3]

lemma E2_ysq_le_x11_add_X (X : ℝ) (p : ℕ+ × ℤ) (hp : p ∈ E2Set X) :
    (p.2 : ℝ) ^ 2 ≤ ((p.1 : ℕ) : ℝ) ^ 11 + X := E2_ysq_le_x11_add_X_helper X p hp.2.2

lemma int_diff_toNat_le_floor (z n : ℤ) (X : ℝ) (_hX : 0 ≤ X)
    (hnn : 0 ≤ z - n) (hle : (z : ℝ) - (n : ℝ) ≤ X) :
    (z - n).toNat ≤ ⌊X⌋₊ := by
  apply Nat.le_floor
  calc ((z - n).toNat : ℝ) = ((z - n).toNat : ℤ) := by push_cast; ring
    _ = (z - n : ℤ) := by rw [Int.toNat_of_nonneg hnn]
    _ = (z : ℝ) - (n : ℝ) := by push_cast; ring
    _ ≤ X := hle

lemma intLe_add_floor_of_toNat_le (z n : ℤ) (X : ℝ)
    (hnn : 0 ≤ z - n) (h : (z - n).toNat ≤ ⌊X⌋₊) :
    z ≤ n + ⌊X⌋₊ := by
  have key : (z - n : ℤ) ≤ ↑⌊X⌋₊ := by
    have h1 := Int.toNat_of_nonneg hnn
    rw [← h1]
    exact_mod_cast h
  omega

lemma intLe_int_add_floor_of_cast_le (z n : ℤ) (X : ℝ) (hX : 0 ≤ X)
    (h : (z : ℝ) ≤ (n : ℝ) + X) : z ≤ n + ⌊X⌋₊ := by
  by_cases hnn : 0 ≤ z - n
  · have hle : (z : ℝ) - (n : ℝ) ≤ X := by linarith
    exact intLe_add_floor_of_toNat_le z n X hnn
      (int_diff_toNat_le_floor z n X hX hnn hle)
  · have : z ≤ n := by omega
    have : (0 : ℤ) ≤ ⌊X⌋₊ := Int.natCast_nonneg _
    omega

lemma E2_X_nonneg (X : ℝ) (p : ℕ+ × ℤ) (hp : p ∈ E2Set X) : 0 ≤ X := by
  obtain ⟨_, h1, h2⟩ := hp
  have h3 : (1 : ℝ) ≤ (|(↑↑p.1 : ℤ) ^ 11 - p.2 ^ 2| : ℝ) := by exact_mod_cast h1
  linarith

lemma E2_ysq_le_x11_add_floor (X : ℝ) (p : ℕ+ × ℤ) (hp : p ∈ E2Set X) :
    p.2 ^ 2 ≤ (↑p.1 : ℤ) ^ 11 + ⌊X⌋₊ := intLe_int_add_floor_of_cast_le
    (p.2 ^ 2) ((↑p.1 : ℤ) ^ 11) X
    (E2_X_nonneg X p hp)
    (by exact_mod_cast E2_ysq_le_x11_add_X X p hp)

lemma E2_y_sq_le (X : ℝ) (N : ℕ) (p : ℕ+ × ℤ)
    (hp : p ∈ E2Set X) (hxN : (p.1 : ℕ) ≤ N) :
    p.2 ^ 2 ≤ (N ^ 11 + ⌊X⌋₊ : ℕ) := by
  have h1 := E2_ysq_le_x11_add_floor X p hp
  have h2 : (↑p.1 : ℤ) ^ 11 ≤ (N : ℤ) ^ 11 := by
    exact_mod_cast Nat.pow_le_pow_left hxN 11
  have h3 : (↑p.1 : ℤ) ^ 11 + (⌊X⌋₊ : ℤ) ≤ (N : ℤ) ^ 11 + ⌊X⌋₊ := by linarith
  calc p.2 ^ 2 ≤ (↑p.1 : ℤ) ^ 11 + ⌊X⌋₊ := h1
    _ ≤ (N : ℤ) ^ 11 + ⌊X⌋₊ := h3
    _ = ↑(N ^ 11 + ⌊X⌋₊) := by push_cast; ring

lemma int_abs_le_of_sq_le (y : ℤ) (M : ℕ) (h : y ^ 2 ≤ (M : ℤ)) :
    |y| ≤ (M : ℤ) := by
  rcases le_or_gt 2 |y| with h2 | h2
  · calc |y| ≤ |y| ^ 2 := by nlinarith [abs_nonneg y]
      _ = y ^ 2 := sq_abs y
      _ ≤ (M : ℤ) := h
  · have hy : -1 ≤ y ∧ y ≤ 1 := abs_le.mp (by omega)
    obtain ⟨hy1, hy2⟩ := hy
    interval_cases y
    · simpa using h
    · simp
    · simpa using h

lemma E2_y_bound (X : ℝ) (N : ℕ)
    (p : ℕ+ × ℤ) (hp : p ∈ E2Set X)
    (hxN : (p.1 : ℕ) ≤ N) :
    |p.2| ≤ (N ^ 11 + ⌊X⌋₊ + 1 : ℕ) := by
  have hsq := E2_y_sq_le X N p hp hxN
  have hab := int_abs_le_of_sq_le p.2 (N ^ 11 + ⌊X⌋₊) (by exact_mod_cast hsq)
  exact_mod_cast le_trans hab (by exact_mod_cast Nat.le_succ _)

lemma rpow_pow_eleven_eq_sq (X : ℝ) (hX : 0 ≤ X) :
    (X ^ ((2 : ℝ) / 11)) ^ (11 : ℕ) = X ^ (2 : ℕ) := by
  rw [← Real.rpow_natCast X 2, ← Real.rpow_mul_natCast hX]
  norm_num

lemma E2_x11_gt_Xsq (X : ℝ) (hX : 2 < X)
    (x : ℕ+) (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    (x : ℝ) ^ 11 > X ^ 2 := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hbase : (0 : ℝ) ≤ X ^ ((2 : ℝ) / 11) := by positivity
  have h11 : (X ^ ((2 : ℝ) / 11)) ^ (11 : ℕ) < (x : ℝ) ^ 11 :=
    pow_lt_pow_left₀ hx hbase (by norm_num)
  rw [rpow_pow_eleven_eq_sq X hX0] at h11
  exact h11

lemma E2_y_ne_zero (X : ℝ) (hX : 2 < X)
    (p : ℕ+ × ℤ) (hp : p ∈ E2Set X) :
    p.2 ≠ 0 := by
  intro hy
  obtain ⟨hx_gt, h_abs_ge, h_abs_le⟩ := hp
  rw [hy] at h_abs_ge h_abs_le
  simp only [zero_pow two_ne_zero, sub_zero] at h_abs_ge
  simp only [Int.cast_zero, zero_pow two_ne_zero, sub_zero] at h_abs_le
  have hx11 : (p.1 : ℝ) ^ 11 > X ^ 2 := E2_x11_gt_Xsq X hX p.1 hx_gt
  have hXsq_gt : X ^ 2 > X := by nlinarith
  have hx_pos_int : (0 : ℤ) < (↑↑p.1 : ℤ) ^ 11 := by positivity
  rw [show ((↑↑↑p.1 : ℤ) : ℝ) ^ 11 = ((↑↑p.1 : ℕ) : ℝ) ^ 11 from by push_cast; ring] at h_abs_le
  rw [abs_of_pos (by positivity : (0 : ℝ) < ((↑↑p.1 : ℕ) : ℝ) ^ 11)] at h_abs_le
  linarith

theorem E2_ysq_lt_2x11 (X : ℝ) (hX : 2 < X)
    (p : ℕ+ × ℤ) (hp : p ∈ E2Set X) :
    (p.2 : ℝ) ^ 2 < 2 * ((p.1 : ℕ) : ℝ) ^ 11 := by
  have h1 : (p.2 : ℝ) ^ 2 ≤ ((p.1 : ℕ) : ℝ) ^ 11 + X := E2_ysq_le_x11_add_X X p hp
  have hx_gt : (p.1 : ℝ) > X ^ ((2 : ℝ) / 11) := hp.1
  have h2 : ((p.1 : ℕ) : ℝ) ^ 11 > X ^ 2 := E2_x11_gt_Xsq X hX p.1 hx_gt
  have h3 : X < X ^ 2 := by nlinarith
  linarith

lemma prime_factor_dvd_of_dvd_pow (m n : ℕ) (k : ℕ) (_hk : 0 < k) (h : m ∣ n ^ k)
    (p : ℕ) (hp : p ∈ m.primeFactors) : p ∣ n := by
  have hp_prime := (Nat.mem_primeFactors.mp hp).1
  have hp_dvd_m := (Nat.mem_primeFactors.mp hp).2.1
  exact hp_prime.dvd_of_dvd_pow (dvd_trans hp_dvd_m h)

lemma radical_dvd_of_dvd_pow (m n : ℕ) (k : ℕ) (hk : 0 < k) (h : m ∣ n ^ k) :
    Nat.radical m ∣ n := by
  unfold Nat.radical
  by_cases hm : m = 0
  · simp only [hm, ↓reduceIte]
    have hnk : n ^ k = 0 := by rwa [hm, zero_dvd_iff] at h
    rw [show n = 0 by rwa [pow_eq_zero_iff hk.ne'] at hnk]
  · simp only [hm, ↓reduceIte]
    exact Finset.prod_primes_dvd n
      (fun p hp => (Nat.mem_primeFactors.mp hp).1.prime)
      (fun p hp => prime_factor_dvd_of_dvd_pow m n k hk h p hp)

lemma gcd_quotients_coprime (M N : ℕ) (hM : 0 < M) (_hN : 0 < N) :
    let g := Nat.gcd M N
    Nat.Coprime (M / g) (N / g) :=
  Nat.coprime_div_gcd_div_gcd (Nat.pos_of_ne_zero (by simp [Nat.gcd_eq_zero_iff]; omega))

lemma coprime_of_coprime_sub (a c : ℕ) (hac : Nat.Coprime a c) (hle : a ≤ c) :
    Nat.Coprime a (c - a) :=
  ((Nat.coprime_sub_self_left hle).mpr (hac.symm)).symm

lemma mul_div_cancel_of_dvd (g M : ℕ) (h : g ∣ M) : g * (M / g) = M := by
  rw [Nat.mul_div_cancel' h]

lemma mul_sub_div_eq (g M N : ℕ) (hgM : g ∣ M) (hgN : g ∣ N) (_hle : M ≤ N) :
    g * (N / g - M / g) = N - M := by
  rw [mul_tsub, mul_div_cancel_of_dvd g N hgN, mul_div_cancel_of_dvd g M hgM]

lemma sub_eq_gcd_mul_sub_div (M N : ℕ) (hM : 0 < M) (hle : M ≤ N) :
    N - M = Nat.gcd M N * (N / Nat.gcd M N - M / Nat.gcd M N) := by
  have _hg := Nat.gcd_pos_of_pos_left N hM
  exact (mul_sub_div_eq (Nat.gcd M N) M N (Nat.gcd_dvd_left M N) (Nat.gcd_dvd_right M N) hle).symm

lemma sub_div_gcd (M N : ℕ) (hM : 0 < M) (hle : M ≤ N) :
    (N - M) / Nat.gcd M N = N / Nat.gcd M N - M / Nat.gcd M N := by
  have hg : 0 < Nat.gcd M N := Nat.gcd_pos_of_pos_left N hM
  rw [sub_eq_gcd_mul_sub_div M N hM hle]
  exact Nat.mul_div_cancel_left _ hg

lemma gcd_coprime_setup (M N : ℕ) (hM : 0 < M) (hN : 0 < N) (hle : M ≤ N) (hd : 0 < N - M) :
    let g := Nat.gcd M N
    let a := M / g
    let c := N / g
    let b := c - a
    0 < g ∧ 0 < a ∧ 0 < c ∧ 0 < b ∧
    Nat.Coprime a b ∧ a + b = c ∧
    N = g * c ∧ M = g * a ∧ g ∣ (N - M) ∧ (N - M) / g = b := by
  intro g a c b
  have hg_pos : 0 < g := Nat.pos_of_ne_zero (by
    intro h; simp [g, Nat.gcd_eq_zero_iff] at h; omega)
  have hgM : g ∣ M := Nat.gcd_dvd_left M N
  have hgN : g ∣ N := Nat.gcd_dvd_right M N
  have hMga : M = g * a := (Nat.mul_div_cancel' hgM).symm
  have hNgc : N = g * c := (Nat.mul_div_cancel' hgN).symm
  have ha_pos : 0 < a := by
    by_contra h; push Not at h; interval_cases a; omega
  have hc_pos : 0 < c := by
    by_contra h; push Not at h; interval_cases c; omega
  have hac_le : a ≤ c := Nat.div_le_div_right hle
  have ha_lt_c : a < c := by
    rcases eq_or_lt_of_le hac_le with h | h
    · exfalso; have : M = N := by rw [hMga, hNgc, h]
      omega
    · exact h
  have hb_pos : 0 < b := Nat.sub_pos_of_lt ha_lt_c
  have hac_cop : Nat.Coprime a c := gcd_quotients_coprime M N hM hN
  have hab_cop : Nat.Coprime a b := coprime_of_coprime_sub a c hac_cop hac_le
  have hab_sum : a + b = c := Nat.add_sub_cancel' hac_le
  have hg_dvd_diff : g ∣ (N - M) := by
    rw [hNgc, hMga, ← mul_tsub]
    exact dvd_mul_right g (c - a)
  have hdiff_div : (N - M) / g = b := sub_div_gcd M N hM hle
  exact ⟨hg_pos, ha_pos, hc_pos, hb_pos, hab_cop, hab_sum, hNgc, hMga, hg_dvd_diff, hdiff_div⟩

lemma primeFactors_mem_one_le (n : ℕ) (p : ℕ) (hp : p ∈ n.primeFactors) : 1 ≤ p :=
  (Nat.mem_primeFactors.mp hp).1.one_le

lemma one_le_prod_primeFactors (n : ℕ) :
    1 ≤ ∏ p ∈ n.primeFactors, p := Finset.one_le_prod' (fun p hp => primeFactors_mem_one_le n p hp)

lemma radical_mul_le_aux (m n : ℕ) (_hm : 0 < m) (_hn : 0 < n) :
    (∏ p ∈ (m * n).primeFactors, p) ≤
    (∏ p ∈ m.primeFactors, p) * (∏ p ∈ n.primeFactors, p) := by
  have key := Nat.prod_primeFactors_gcd_mul_prod_primeFactors_mul m n id
  simp only [Function.id_def] at key
  have hgcd := one_le_prod_primeFactors (m.gcd n)
  calc ∏ p ∈ (m * n).primeFactors, p
      ≤ (∏ p ∈ (m.gcd n).primeFactors, p) * (∏ p ∈ (m * n).primeFactors, p) :=
        le_mul_of_one_le_left' hgcd
    _ = (∏ p ∈ m.primeFactors, p) * (∏ p ∈ n.primeFactors, p) := key

lemma radical_mul_le_pos (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Nat.radical (m * n) ≤ Nat.radical m * Nat.radical n := by
  have hm' : m ≠ 0 := ne_of_gt hm
  have hn' : n ≠ 0 := ne_of_gt hn
  have hmn' : m * n ≠ 0 := Nat.mul_ne_zero hm' hn'
  simp only [Nat.radical, hmn', ↓reduceIte, hm', hn']
  exact radical_mul_le_aux m n hm hn

lemma radical_mul_le (a b : ℕ) :
    Nat.radical (a * b) ≤ Nat.radical a * Nat.radical b := by
  by_cases ha : a = 0
  · simp [ha, Nat.radical]
  · by_cases hb : b = 0
    · simp [hb, Nat.radical]
    · exact radical_mul_le_pos a b (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)

lemma rpow_three_halves_mono
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    a ^ ((3 : ℝ) / 2) ≤ b ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow ha hab (by positivity)

lemma mul_K_t_mono_left
    (K : ℝ) (hK : 0 < K)
    (g d : ℕ) (h_g_le_d : g ≤ d)
    (t : ℝ) (ht : 0 ≤ t) :
    (g : ℝ) * (K * t) ≤ (d : ℝ) * (K * t) := by
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast h_g_le_d

lemma radical_le_self (n : ℕ) (hn : 0 < n) : Nat.radical n ≤ n := by
  have h : n ≠ 0 := ne_of_gt hn
  rw [show Nat.radical n = ∏ p ∈ n.primeFactors, p by simp [h, Nat.radical]]
  exact Nat.le_of_dvd (by positivity) n.prod_primeFactors_dvd

lemma radical_abc_bound
    (x : ℕ) (hx : 0 < x)
    (y_abs : ℕ) (hy : 0 < y_abs)
    (d : ℕ) (hd : 0 < d)
    (hsum : y_abs ^ 2 + d = x ^ 11) :
    let g := Nat.gcd (y_abs ^ 2) (x ^ 11)
    let a := y_abs ^ 2 / g
    let c := x ^ 11 / g
    let b := c - a
    (Nat.radical (a * b * c) : ℝ) ≤ (y_abs : ℝ) * (d : ℝ) * (x : ℝ) := by
  intro g a c b
  have hle : y_abs ^ 2 ≤ x ^ 11 := Nat.le_of_lt_succ (by omega)
  have hd_pos : 0 < x ^ 11 - y_abs ^ 2 := by omega
  obtain ⟨_, _, _, hb_pos, _, _, hNgc, hMga, _, hdgb_eq⟩ :=
    gcd_coprime_setup (y_abs ^ 2) (x ^ 11) (by positivity) (by positivity) hle hd_pos
  have ha_dvd : a ∣ y_abs ^ 2 := ⟨g, by rw [mul_comm]; exact hMga⟩
  have hc_dvd : c ∣ x ^ 11 := ⟨g, by rw [mul_comm]; exact hNgc⟩
  have hrad_a := radical_dvd_of_dvd_pow a y_abs 2 (by norm_num) ha_dvd
  have hrad_c := radical_dvd_of_dvd_pow c x 11 (by norm_num) hc_dvd
  have hdeq : d = x ^ 11 - y_abs ^ 2 := by omega
  have hb_dvd_d : b ∣ d := by
    rw [hdeq]
    refine ⟨g, ?_⟩
    rw [mul_comm]
    exact (mul_sub_div_eq g (y_abs ^ 2) (x ^ 11)
      (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) hle).symm
  have hrad_b := radical_dvd_of_dvd_pow b d 1 (by norm_num) (by rwa [pow_one])
  have hrad_a_le : Nat.radical a ≤ y_abs := Nat.le_of_dvd hy hrad_a
  have hrad_b_le : Nat.radical b ≤ d := Nat.le_of_dvd hd hrad_b
  have hrad_c_le : Nat.radical c ≤ x := Nat.le_of_dvd hx hrad_c
  have h1 := radical_mul_le (a * b) c
  have h2 := radical_mul_le a b
  have h_nat : Nat.radical (a * b * c) ≤ y_abs * d * x := by
    calc Nat.radical (a * b * c)
        ≤ Nat.radical (a * b) * Nat.radical c := h1
      _ ≤ Nat.radical a * Nat.radical b * Nat.radical c := Nat.mul_le_mul_right _ h2
      _ ≤ y_abs * d * x := Nat.mul_le_mul (Nat.mul_le_mul hrad_a_le hrad_b_le) hrad_c_le
  exact_mod_cast h_nat

lemma assemble_abc_bound_chain
    (K : ℝ) (hK : 0 < K)
    (x : ℕ) (_hx : 0 < x)
    (y_abs : ℕ) (_hy : 0 < y_abs)
    (d : ℕ) (_hd : 0 < d)
    (g : ℕ) (_hg : 0 < g)
    (c : ℕ) (_hc : 0 < c)
    (a : ℕ) (_ha : 0 < a)
    (b : ℕ) (_hb : 0 < b)
    (h_x11_eq : (x : ℝ) ^ 11 = (g : ℝ) * (c : ℝ))
    (h_abc : (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (h_rad_mono : ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ ((3 : ℝ) / 2)
      ≤ ((y_abs : ℝ) * (d : ℝ) * (x : ℝ)) ^ ((3 : ℝ) / 2))
    (h_gd_mono : (g : ℝ) * (K * ((d : ℝ) * (x : ℝ) * (y_abs : ℝ)) ^ ((3 : ℝ) / 2))
      ≤ (d : ℝ) * (K * ((d : ℝ) * (x : ℝ) * (y_abs : ℝ)) ^ ((3 : ℝ) / 2))) :
    (x : ℝ) ^ 11 ≤ (d : ℝ) * K * ((d : ℝ) * (x : ℝ) * (y_abs : ℝ)) ^ ((3 : ℝ) / 2) := by
  calc (x : ℝ) ^ 11
      ≤ (g : ℝ) * (K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) := by
        rw [h_x11_eq]; exact mul_le_mul_of_nonneg_left h_abc (Nat.cast_nonneg g)
    _ ≤ (g : ℝ) * (K * ((y_abs : ℝ) * (d : ℝ) * (x : ℝ)) ^ ((3 : ℝ) / 2)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h_rad_mono (le_of_lt hK)) (Nat.cast_nonneg g)
    _ = (g : ℝ) * (K * ((d : ℝ) * (x : ℝ) * (y_abs : ℝ)) ^ ((3 : ℝ) / 2)) := by
        grind
    _ ≤ (d : ℝ) * (K * ((d : ℝ) * (x : ℝ) * (y_abs : ℝ)) ^ ((3 : ℝ) / 2)) := h_gd_mono
    _ = (d : ℝ) * K * ((d : ℝ) * (x : ℝ) * (y_abs : ℝ)) ^ ((3 : ℝ) / 2) := by ring

lemma assemble_abc_bound
    (K : ℝ) (hK : 0 < K)
    (x : ℕ) (hx : 0 < x)
    (y_abs : ℕ) (hy : 0 < y_abs)
    (d : ℕ) (hd : 0 < d)
    (_hsum : y_abs ^ 2 + d = x ^ 11)
    (g : ℕ) (hg : 0 < g)
    (c : ℕ) (hc : 0 < c)
    (a : ℕ) (ha : 0 < a)
    (b : ℕ) (hb : 0 < b)
    (hcop : Nat.Coprime a b)
    (hab : a + b = c)
    (hNgc : x ^ 11 = g * c)
    (_hMga : y_abs ^ 2 = g * a)
    (hdgb : d = g * b)
    (hK_abc : ∀ a' b' c' : ℕ, 0 < a' → 0 < b' → 0 < c' →
        Nat.Coprime a' b' → a' + b' = c' →
          (c' : ℝ) ≤ K * ((Nat.radical (a' * b' * c') : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (hrad : (Nat.radical (a * b * c) : ℝ) ≤ (y_abs : ℝ) * (d : ℝ) * (x : ℝ)) :
    (x : ℝ) ^ 11 ≤ (d : ℝ) * K * ((d : ℝ) * (x : ℝ) * (y_abs : ℝ)) ^ ((3 : ℝ) / 2) := by
  have h_abc := hK_abc a b c ha hb hc hcop hab
  have h_x11_eq : (x : ℝ) ^ 11 = (g : ℝ) * (c : ℝ) := by
    exact_mod_cast hNgc
  have h_rad_mono := rpow_three_halves_mono
    ((Nat.radical (a * b * c) : ℕ) : ℝ) ((y_abs : ℝ) * (d : ℝ) * (x : ℝ))
    (by positivity) hrad
  have h_g_le_d : g ≤ d := by
    rw [hdgb]; exact Nat.le_mul_of_pos_right g hb
  have h_gd_mono := mul_K_t_mono_left K hK g d h_g_le_d
    (((d : ℝ) * (x : ℝ) * (y_abs : ℝ)) ^ ((3 : ℝ) / 2)) (by positivity)
  exact assemble_abc_bound_chain K hK x hx y_abs hy d hd g hg c hc a ha b hb
    h_x11_eq h_abc h_rad_mono h_gd_mono

lemma abc_gcd_bound_nat
    (K : ℝ) (hK : 0 < K)
    (hK_abc : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → a + b = c →
          (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (x : ℕ) (hx : 0 < x)
    (y_abs : ℕ) (hy : 0 < y_abs)
    (d : ℕ) (hd : 0 < d)
    (hsum : y_abs ^ 2 + d = x ^ 11) :
    (x : ℝ) ^ 11 ≤
      (d : ℝ) * K * ((d : ℝ) * (x : ℝ) * (y_abs : ℝ)) ^ ((3 : ℝ) / 2) := by
  have hle : y_abs ^ 2 ≤ x ^ 11 := Nat.le_of_lt_succ (by omega)
  have hd_pos : 0 < x ^ 11 - y_abs ^ 2 := by omega
  obtain ⟨hg, ha, hc, hb, hcop, hab, hNgc, hMga, hgdvd, hdgb_eq⟩ :=
    gcd_coprime_setup (y_abs ^ 2) (x ^ 11) (by positivity) (by positivity) hle hd_pos
  have hdeq : d = x ^ 11 - y_abs ^ 2 := by omega
  have hdgb : d = Nat.gcd (y_abs ^ 2) (x ^ 11) *
      (x ^ 11 / Nat.gcd (y_abs ^ 2) (x ^ 11) - y_abs ^ 2 / Nat.gcd (y_abs ^ 2) (x ^ 11)) := by
    rw [hdeq, ← hdgb_eq]
    rw [mul_comm]
    exact (Nat.div_mul_cancel hgdvd).symm
  have hrad := radical_abc_bound x hx y_abs hy d hd hsum
  exact assemble_abc_bound K hK x hx y_abs hy d hd hsum
    (Nat.gcd (y_abs ^ 2) (x ^ 11)) hg
    (x ^ 11 / Nat.gcd (y_abs ^ 2) (x ^ 11)) hc
    (y_abs ^ 2 / Nat.gcd (y_abs ^ 2) (x ^ 11)) ha
    (x ^ 11 / Nat.gcd (y_abs ^ 2) (x ^ 11) - y_abs ^ 2 / Nat.gcd (y_abs ^ 2) (x ^ 11)) hb
    hcop hab hNgc hMga hdgb hK_abc hrad

lemma int_eq_from_diff
    (x : ℕ) (y : ℤ) (d : ℕ)
    (hd_eq : (d : ℤ) = (x : ℤ) ^ 11 - y ^ 2) :
    y ^ 2 + (d : ℤ) = (x : ℤ) ^ 11 := by
  grind

lemma nat_eq_from_int_eq
    (x : ℕ) (y : ℤ) (d : ℕ)
    (hint : y ^ 2 + (d : ℤ) = (x : ℤ) ^ 11) :
    y.natAbs ^ 2 + d = x ^ 11 := by
  have h1 : (↑(y.natAbs ^ 2 + d) : ℤ) = ↑(x ^ 11) := by
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Int.natAbs_sq]
    exact hint
  exact_mod_cast h1

lemma cast_to_nat_setup
    (x : ℕ) (_hx : 0 < x)
    (y : ℤ) (hy : y ≠ 0)
    (d : ℕ) (_hd : 0 < d)
    (hd_eq : (d : ℤ) = (x : ℤ) ^ 11 - y ^ 2)
    (_hge : y ^ 2 ≤ (x : ℤ) ^ 11) :
    y.natAbs ^ 2 + d = x ^ 11 ∧ 0 < y.natAbs := by
  constructor
  · exact nat_eq_from_int_eq x y d (int_eq_from_diff x y d hd_eq)
  · exact Int.natAbs_pos.mpr hy

lemma E2_abc_applied_case1 (K : ℝ) (hK : 0 < K)
    (hK_abc : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → a + b = c →
          (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (x : ℕ) (hx : 0 < x)
    (y : ℤ) (hy : y ≠ 0)
    (d : ℕ) (hd : 0 < d)
    (hd_eq : (d : ℤ) = (x : ℤ) ^ 11 - y ^ 2)
    (hge : y ^ 2 ≤ (x : ℤ) ^ 11) :
    (x : ℝ) ^ 11 ≤
      (d : ℝ) * K * ((d : ℝ) * (x : ℝ) * (|y| : ℝ)) ^ ((3 : ℝ) / 2) := by
  obtain ⟨hsum, hy_pos⟩ := cast_to_nat_setup x hx y hy d hd hd_eq hge
  have habs_eq : (|y| : ℝ) = ((y.natAbs : ℕ) : ℝ) := by
    rw [Nat.cast_natAbs, ← Int.cast_abs]
  rw [habs_eq]
  exact abc_gcd_bound_nat K hK hK_abc x hx y.natAbs hy_pos d hd hsum

lemma x11_le_natAbs_sq (x : ℕ) (y : ℤ) (hlt : (x : ℤ) ^ 11 < y ^ 2) :
    x ^ 11 ≤ y.natAbs ^ 2 := by
  have h : x ^ 11 < y.natAbs ^ 2 := by
    rwa [show (x : ℤ) ^ 11 = ↑(x ^ 11) from (Nat.cast_pow x 11).symm,
         show y ^ 2 = ↑(y.natAbs ^ 2) from (Int.natAbs_sq y).symm,
         Nat.cast_lt] at hlt
  exact le_of_lt h

lemma d_eq_natAbs_diff (x : ℕ) (y : ℤ) (d : ℕ)
    (hd_eq : (d : ℤ) = y ^ 2 - (x : ℤ) ^ 11)
    (hlt : (x : ℤ) ^ 11 < y ^ 2) :
    d = y.natAbs ^ 2 - x ^ 11 := by
  have hle : x ^ 11 ≤ y.natAbs ^ 2 := x11_le_natAbs_sq x y hlt
  have key : (d : ℤ) = ↑(y.natAbs ^ 2 - x ^ 11) := by
    rw [Nat.cast_sub hle]
    rw [← Int.natAbs_sq y] at hd_eq
    push_cast at hd_eq ⊢
    linarith
  exact Nat.cast_injective key

lemma a_dvd_x11 (x : ℕ) (y : ℤ) :
    let g := Nat.gcd (y.natAbs ^ 2) (x ^ 11)
    let a := x ^ 11 / g
    a ∣ x ^ 11 := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right (y.natAbs ^ 2) (x ^ 11))

lemma c_dvd_yabs2 (x : ℕ) (y : ℤ) :
    let g := Nat.gcd (y.natAbs ^ 2) (x ^ 11)
    let c := y.natAbs ^ 2 / g
    c ∣ y.natAbs ^ 2 := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

lemma radical_triple_le (a b c : ℕ) :
    Nat.radical (a * b * c) ≤ Nat.radical a * Nat.radical b * Nat.radical c := by
  calc Nat.radical (a * b * c)
      ≤ Nat.radical (a * b) * Nat.radical c := radical_mul_le (a * b) c
    _ ≤ Nat.radical a * Nat.radical b * Nat.radical c := by
        apply Nat.mul_le_mul_right
        exact radical_mul_le a b

lemma mul_radical_bounds (a b c x d yabs : ℕ)
    (ha : Nat.radical a ≤ x)
    (hb : Nat.radical b ≤ d)
    (hc : Nat.radical c ≤ yabs) :
    Nat.radical a * Nat.radical b * Nat.radical c ≤ x * d * yabs :=
  mul_le_mul' (mul_le_mul' ha hb) hc

lemma radical_abc_le_dxy (a b c x d yabs : ℕ)
    (ha : Nat.radical a ≤ x)
    (hb : Nat.radical b ≤ d)
    (hc : Nat.radical c ≤ yabs) :
    (Nat.radical (a * b * c) : ℝ) ≤ (d : ℝ) * (x : ℝ) * (yabs : ℝ) := by
  have h1 : Nat.radical (a * b * c) ≤ Nat.radical a * Nat.radical b * Nat.radical c :=
    radical_triple_le a b c
  have h2 : Nat.radical a * Nat.radical b * Nat.radical c ≤ x * d * yabs :=
    mul_radical_bounds a b c x d yabs ha hb hc
  have h3 : Nat.radical (a * b * c) ≤ x * d * yabs := le_trans h1 h2
  have h4 : (Nat.radical (a * b * c) : ℝ) ≤ (x * d * yabs : ℝ) := by exact_mod_cast h3
  calc (Nat.radical (a * b * c) : ℝ)
      ≤ (x * d * yabs : ℝ) := h4
    _ = (d : ℝ) * (x : ℝ) * (yabs : ℝ) := by ring

lemma radical_dvd_implies_le (m n : ℕ) (hn : 0 < n) (h : Nat.radical m ∣ n) :
    Nat.radical m ≤ n := Nat.le_of_dvd hn h

lemma radical_bound_case2 (x : ℕ) (hx : 0 < x) (y : ℤ) (hy : y ≠ 0)
    (d : ℕ) (hd : 0 < d) (hd_nat : d = y.natAbs ^ 2 - x ^ 11)
    (_hlt : (x : ℤ) ^ 11 < y ^ 2) :
    let g := Nat.gcd (y.natAbs ^ 2) (x ^ 11)
    let a := x ^ 11 / g
    let b := d / g
    let c := y.natAbs ^ 2 / g
    (Nat.radical (a * b * c) : ℝ) ≤ (d : ℝ) * (x : ℝ) * (y.natAbs : ℝ) := by
  intro g a b c
  have hg_dvd_d : g ∣ d := by
    have h1 : g ∣ y.natAbs ^ 2 := Nat.gcd_dvd_left _ _
    have h2 : g ∣ x ^ 11 := Nat.gcd_dvd_right _ _
    obtain ⟨k1, hk1⟩ := h1
    obtain ⟨k2, hk2⟩ := h2
    rw [hd_nat, hk1, hk2]
    exact ⟨k1 - k2, by rw [mul_tsub]⟩
  have hg_pos : 0 < g := Nat.pos_of_ne_zero (by
    intro hg0
    have : g ∣ y.natAbs ^ 2 := Nat.gcd_dvd_left _ _
    rw [hg0] at this
    simp at this
    have : 0 < y.natAbs := Int.natAbs_pos.mpr hy
    omega)
  have hb_pos : 0 < b := Nat.div_pos (Nat.le_of_dvd hd hg_dvd_d) hg_pos
  have ha_dvd : a ∣ x ^ 11 := a_dvd_x11 x y
  have hrad_a_dvd_x : Nat.radical a ∣ x :=
    radical_dvd_of_dvd_pow a x 11 (by norm_num) ha_dvd
  have hrad_a_le : Nat.radical a ≤ x := radical_dvd_implies_le a x hx hrad_a_dvd_x
  have hc_dvd : c ∣ y.natAbs ^ 2 := c_dvd_yabs2 x y
  have hyabs_pos : 0 < y.natAbs := Int.natAbs_pos.mpr hy
  have hrad_c_dvd_y : Nat.radical c ∣ y.natAbs :=
    radical_dvd_of_dvd_pow c y.natAbs 2 (by norm_num) hc_dvd
  have hrad_c_le : Nat.radical c ≤ y.natAbs :=
    radical_dvd_implies_le c y.natAbs hyabs_pos hrad_c_dvd_y
  have hrad_b_le : Nat.radical b ≤ d :=
    le_trans (radical_le_self b hb_pos) (Nat.div_le_self d g)
  exact radical_abc_le_dxy a b c x d y.natAbs hrad_a_le hrad_b_le hrad_c_le

lemma yabs_sq_le_g_mul_K_rad
    (K : ℝ) (_hK : 0 < K)
    (g c yabs : ℕ) (_hg : 0 < g) (_hc : 0 < c) (_hyabs : 0 < yabs)
    (h_gc : yabs ^ 2 = g * c)
    (rad : ℕ)
    (h_abc_bound : (c : ℝ) ≤ K * (rad : ℝ) ^ ((3 : ℝ) / 2)) :
    (yabs : ℝ) ^ 2 ≤ (g : ℝ) * (K * (rad : ℝ) ^ ((3 : ℝ) / 2)) := by
  rw [show (yabs : ℝ) ^ 2 = (g : ℝ) * (c : ℝ) from by exact_mod_cast h_gc]
  exact mul_le_mul_of_nonneg_left h_abc_bound (Nat.cast_nonneg g)

lemma assemble_case2_bound
    (K : ℝ) (hK : 0 < K)
    (g c d x yabs : ℕ) (hg : 0 < g) (hc : 0 < c) (_hd : 0 < d)
    (_hx : 0 < x) (hyabs : 0 < yabs)
    (h_gc : yabs ^ 2 = g * c)
    (h_abc_bound : (c : ℝ) ≤ K * ((Nat.radical (x ^ 11 / g * (d / g) * c) : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (h_rad : (Nat.radical (x ^ 11 / g * (d / g) * c) : ℝ) ≤ (d : ℝ) * (x : ℝ) * (yabs : ℝ))
    (h_g_le_d : g ≤ d) :
    (yabs : ℝ) ^ 2 ≤ (d : ℝ) * K * ((d : ℝ) * (x : ℝ) * (yabs : ℝ)) ^ ((3 : ℝ) / 2) := by
  set rad := Nat.radical (x ^ 11 / g * (d / g) * c) with hrad_def
  have step1 := yabs_sq_le_g_mul_K_rad K hK g c yabs hg hc hyabs h_gc rad h_abc_bound
  have hrad_nn : (0 : ℝ) ≤ (rad : ℝ) := Nat.cast_nonneg _
  have step2 := rpow_three_halves_mono (rad : ℝ) ((d : ℝ) * (x : ℝ) * (yabs : ℝ)) hrad_nn h_rad
  have step3 : (g : ℝ) * (K * (rad : ℝ) ^ ((3 : ℝ) / 2)) ≤
      (g : ℝ) * (K * ((d : ℝ) * (x : ℝ) * (yabs : ℝ)) ^ ((3 : ℝ) / 2)) := by
    apply mul_le_mul_of_nonneg_left
    · exact mul_le_mul_of_nonneg_left step2 (le_of_lt hK)
    · exact Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ ((d : ℝ) * (x : ℝ) * (yabs : ℝ)) ^ ((3 : ℝ) / 2) := by positivity
  have step4 := mul_K_t_mono_left K hK g d h_g_le_d
      (((d : ℝ) * (x : ℝ) * (yabs : ℝ)) ^ ((3 : ℝ) / 2)) ht
  calc (yabs : ℝ) ^ 2
      ≤ (g : ℝ) * (K * (rad : ℝ) ^ ((3 : ℝ) / 2)) := step1
    _ ≤ (g : ℝ) * (K * ((d : ℝ) * (x : ℝ) * (yabs : ℝ)) ^ ((3 : ℝ) / 2)) := step3
    _ ≤ (d : ℝ) * (K * ((d : ℝ) * (x : ℝ) * (yabs : ℝ)) ^ ((3 : ℝ) / 2)) := step4
    _ = (d : ℝ) * K * ((d : ℝ) * (x : ℝ) * (yabs : ℝ)) ^ ((3 : ℝ) / 2) := by ring

lemma E2_abc_applied_case2 (K : ℝ) (hK : 0 < K)
    (hK_abc : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → a + b = c →
          (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (x : ℕ) (hx : 0 < x)
    (y : ℤ) (hy : y ≠ 0)
    (d : ℕ) (hd : 0 < d)
    (hd_eq : (d : ℤ) = y ^ 2 - (x : ℤ) ^ 11)
    (hlt : (x : ℤ) ^ 11 < y ^ 2) :
    (y : ℝ) ^ 2 ≤
      (d : ℝ) * K * ((d : ℝ) * (x : ℝ) * (|y| : ℝ)) ^ ((3 : ℝ) / 2) := by
  set g := Nat.gcd (y.natAbs ^ 2) (x ^ 11) with hg_def
  set yabs := y.natAbs with hyabs_def
  have hd_nat : d = yabs ^ 2 - x ^ 11 := d_eq_natAbs_diff x y d hd_eq hlt
  have hx11_pos : 0 < x ^ 11 := Nat.pos_of_ne_zero (by positivity)
  have hyabs_pos : 0 < yabs := by rw [hyabs_def]; exact Int.natAbs_pos.mpr hy
  have hyabs2_pos : 0 < yabs ^ 2 := by positivity
  have hle_nat : x ^ 11 ≤ yabs ^ 2 := by
    rw [← Nat.cast_le (α := ℤ)]
    have : (↑(yabs ^ 2) : ℤ) = y ^ 2 := by
      rw [hyabs_def]; push_cast; exact sq_abs y
    rw [this]; push_cast; exact le_of_lt hlt
  have hd_pos_nat : 0 < yabs ^ 2 - x ^ 11 := by omega
  have hg_comm : Nat.gcd (x ^ 11) (yabs ^ 2) = g := by
    rw [hg_def]; exact Nat.gcd_comm (x ^ 11) (yabs ^ 2)
  have hsetup := gcd_coprime_setup (x ^ 11) (yabs ^ 2) hx11_pos hyabs2_pos hle_nat hd_pos_nat
  obtain ⟨hg_pos', ha_pos', hc_pos', hb_pos', hcop',
    hsum', hN_eq', hM_eq', hdvd_diff', hdiff_div'⟩ := hsetup
  rw [hg_comm] at hg_pos' ha_pos' hc_pos' hb_pos' hcop' hsum' hN_eq' hM_eq' hdvd_diff' hdiff_div'
  have hg_pos : 0 < g := hg_pos'
  have hg_dvd_d : g ∣ d := hd_nat ▸ hdvd_diff'
  have hd_div_eq : d / g = yabs ^ 2 / g - x ^ 11 / g := by
    rw [hd_nat]; exact hdiff_div'
  have hcop : Nat.Coprime (x ^ 11 / g) (d / g) := by
    rw [hd_div_eq]; exact hcop'
  have hsum : x ^ 11 / g + d / g = yabs ^ 2 / g := by
    rw [hd_div_eq]; exact hsum'
  have hb_pos : 0 < d / g := by rw [hd_div_eq]; exact hb_pos'
  have hg_le_d : g ≤ d := Nat.le_of_dvd hd hg_dvd_d
  have h_gc : yabs ^ 2 = g * (yabs ^ 2 / g) := hN_eq'
  have habc := hK_abc _ _ _ ha_pos' hb_pos hc_pos' hcop hsum
  have hrad := radical_bound_case2 x hx y hy d hd hd_nat hlt
  have h := assemble_case2_bound K hK g (yabs ^ 2 / g) d x yabs
    hg_pos hc_pos' hd hx hyabs_pos h_gc habc hrad hg_le_d
  have h1 : (y : ℝ) ^ 2 = (yabs : ℝ) ^ 2 := by
    rw [hyabs_def]
    have h' : (y : ℝ) ^ 2 = ((y ^ 2 : ℤ) : ℝ) := by push_cast; ring
    have h'' : ((y.natAbs : ℕ) : ℝ) ^ 2 = ((y.natAbs ^ 2 : ℕ) : ℝ) := by push_cast; ring
    rw [h', h'']; exact congr_arg _ (Int.natAbs_sq y).symm
  have h2 : |(y : ℝ)| = (yabs : ℝ) := by
    rw [hyabs_def, Nat.cast_natAbs y, Int.cast_abs]
  rw [h1, h2]; exact h

lemma E2_abc_case_A_d_eq
    (x : ℕ) (y : ℤ)
    (d : ℕ) (hd_eq : (d : ℤ) = |((x : ℤ) ^ 11 - y ^ 2)|)
    (hge : y ^ 2 ≤ (x : ℤ) ^ 11) :
    (d : ℤ) = (x : ℤ) ^ 11 - y ^ 2 := by
  rw [hd_eq, abs_of_nonneg (sub_nonneg.mpr hge)]

lemma E2_abc_case_A_cast_le
    (x : ℕ) (y : ℤ)
    (hge : y ^ 2 ≤ (x : ℤ) ^ 11) :
    (y : ℝ) ^ 2 ≤ (x : ℝ) ^ 11 := by
  exact_mod_cast hge

lemma E2_abc_case_A (K : ℝ) (_hK : 0 < K)
    (x : ℕ) (_hx : 0 < x)
    (y : ℤ) (_hy : y ≠ 0)
    (d : ℕ) (_hd : 0 < d)
    (hd_eq : (d : ℤ) = |((x : ℤ) ^ 11 - y ^ 2)|)
    (h1 : ∀ (_hge : y ^ 2 ≤ (x : ℤ) ^ 11)
            (_hd1 : (d : ℤ) = (x : ℤ) ^ 11 - y ^ 2),
          (x : ℝ) ^ 11 ≤ (d : ℝ) * K * ((d : ℝ) * (x : ℝ) * (|y| : ℝ)) ^ ((3 : ℝ) / 2))
    (hge : y ^ 2 ≤ (x : ℤ) ^ 11) :
    max ((x : ℝ) ^ 11) ((y : ℝ) ^ 2) ≤
      (d : ℝ) * K * ((d : ℝ) * (x : ℝ) * (|y| : ℝ)) ^ ((3 : ℝ) / 2) := by
  have hd1 := E2_abc_case_A_d_eq x y d hd_eq hge
  have hx11_le := h1 hge hd1
  have hy2_le := E2_abc_case_A_cast_le x y hge
  exact max_le hx11_le (le_trans hy2_le hx11_le)

lemma d_eq_ysq_sub_x11 (x : ℕ) (y : ℤ) (d : ℕ)
    (hd_eq : (d : ℤ) = |((x : ℤ) ^ 11 - y ^ 2)|)
    (hlt : (x : ℤ) ^ 11 < y ^ 2) :
    (d : ℤ) = y ^ 2 - (x : ℤ) ^ 11 := by
  rw [hd_eq, abs_of_neg (sub_neg_of_lt hlt)]
  ring

lemma x11_le_y2_real (x : ℕ) (y : ℤ)
    (hlt : (x : ℤ) ^ 11 < y ^ 2) :
    ((x : ℤ) : ℝ) ^ 11 ≤ ((y : ℤ) : ℝ) ^ 2 := by
  exact_mod_cast hlt.le

lemma E2_abc_case_B (K : ℝ) (_hK : 0 < K)
    (x : ℕ) (_hx : 0 < x)
    (y : ℤ) (_hy : y ≠ 0)
    (d : ℕ) (_hd : 0 < d)
    (hd_eq : (d : ℤ) = |((x : ℤ) ^ 11 - y ^ 2)|)
    (h2 : ∀ (_hlt : (x : ℤ) ^ 11 < y ^ 2)
            (_hd2 : (d : ℤ) = y ^ 2 - (x : ℤ) ^ 11),
          (y : ℝ) ^ 2 ≤ (d : ℝ) * K * ((d : ℝ) * (x : ℝ) * (|y| : ℝ)) ^ ((3 : ℝ) / 2))
    (hlt : (x : ℤ) ^ 11 < y ^ 2) :
    max ((x : ℝ) ^ 11) ((y : ℝ) ^ 2) ≤
      (d : ℝ) * K * ((d : ℝ) * (x : ℝ) * (|y| : ℝ)) ^ ((3 : ℝ) / 2) := by
  have hd2 : (d : ℤ) = y ^ 2 - (x : ℤ) ^ 11 := d_eq_ysq_sub_x11 x y d hd_eq hlt
  have hy2_bound := h2 hlt hd2
  have hx11_le_y2 : ((x : ℤ) : ℝ) ^ 11 ≤ ((y : ℤ) : ℝ) ^ 2 := x11_le_y2_real x y hlt
  exact max_le (le_trans hx11_le_y2 hy2_bound) hy2_bound

lemma E2_abc_applied_from_cases (K : ℝ) (hK : 0 < K)
    (_hK_abc : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → a + b = c →
          (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (x : ℕ) (hx : 0 < x)
    (y : ℤ) (hy : y ≠ 0)
    (d : ℕ) (hd : 0 < d)
    (hd_eq : (d : ℤ) = |((x : ℤ) ^ 11 - y ^ 2)|)
    (h1 : ∀ (_hge : y ^ 2 ≤ (x : ℤ) ^ 11)
            (_hd1 : (d : ℤ) = (x : ℤ) ^ 11 - y ^ 2),
          (x : ℝ) ^ 11 ≤ (d : ℝ) * K * ((d : ℝ) * (x : ℝ) * (|y| : ℝ)) ^ ((3 : ℝ) / 2))
    (h2 : ∀ (_hlt : (x : ℤ) ^ 11 < y ^ 2)
            (_hd2 : (d : ℤ) = y ^ 2 - (x : ℤ) ^ 11),
          (y : ℝ) ^ 2 ≤ (d : ℝ) * K * ((d : ℝ) * (x : ℝ) * (|y| : ℝ)) ^ ((3 : ℝ) / 2)) :
    max ((x : ℝ) ^ 11) ((y : ℝ) ^ 2) ≤
      (d : ℝ) * K * ((d : ℝ) * (x : ℝ) * (|y| : ℝ)) ^ ((3 : ℝ) / 2) := by
  rcases le_or_gt (y ^ 2) ((x : ℤ) ^ 11) with hge | hlt
  · exact E2_abc_case_A K hK x hx y hy d hd hd_eq h1 hge
  · exact E2_abc_case_B K hK x hx y hy d hd hd_eq h2 hlt

lemma E2_abc_applied (K : ℝ) (hK : 0 < K)
    (hK_abc : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → a + b = c →
          (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (x : ℕ) (hx : 0 < x)
    (y : ℤ) (hy : y ≠ 0)
    (d : ℕ) (hd : 0 < d)
    (hd_eq : (d : ℤ) = |((x : ℤ) ^ 11 - y ^ 2)|) :
    max ((x : ℝ) ^ 11) ((y : ℝ) ^ 2) ≤
      (d : ℝ) * K * ((d : ℝ) * (x : ℝ) * (|y| : ℝ)) ^ ((3 : ℝ) / 2) :=
    E2_abc_applied_from_cases K hK hK_abc x hx y hy d hd hd_eq
    (fun hge hd1 => E2_abc_applied_case1 K hK hK_abc x hx y hy d hd hd1 hge)
    (fun hlt hd2 => E2_abc_applied_case2 K hK hK_abc x hx y hy d hd hd2 hlt)

lemma rpow_mul_distrib (d x y_abs : ℝ) (hd : 0 < d) (hx : 1 ≤ x) (hy : 0 < y_abs) :
    (d * x * y_abs) ^ ((3 : ℝ) / 2) =
    d ^ ((3 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) * y_abs ^ ((3 : ℝ) / 2) := by
  rw [Real.mul_rpow (mul_nonneg hd.le (by linarith)) hy.le]
  rw [Real.mul_rpow hd.le (by linarith)]

lemma d_mul_d_rpow (d : ℝ) (hd : 0 < d) :
    d * d ^ ((3 : ℝ) / 2) = d ^ ((5 : ℝ) / 2) := by
  have h : (1 : ℝ) + 3 / 2 = 5 / 2 := by norm_num
  rw [← h, Real.rpow_add hd, Real.rpow_one]

lemma expand_abc_rhs_eq (K : ℝ) (_hK : 0 < K)
    (x : ℝ) (hx : 1 ≤ x)
    (y_abs : ℝ) (hy : 0 < y_abs)
    (d : ℝ) (hd_pos : 0 < d) :
    d * K * (d * x * y_abs) ^ ((3 : ℝ) / 2) =
    K * d ^ ((5 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) * y_abs ^ ((3 : ℝ) / 2) := by
  rw [rpow_mul_distrib d x y_abs hd_pos hx hy]
  rw [show d * K * (d ^ ((3 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) * y_abs ^ ((3 : ℝ) / 2)) =
      K * (d * d ^ ((3 : ℝ) / 2)) * x ^ ((3 : ℝ) / 2) * y_abs ^ ((3 : ℝ) / 2) by ring]
  rw [d_mul_d_rpow d hd_pos]

lemma expand_abc_rhs (K : ℝ) (hK : 0 < K)
    (x : ℝ) (hx : 1 ≤ x)
    (y_abs : ℝ) (hy : 0 < y_abs)
    (d : ℝ) (hd_pos : 0 < d)
    (habc : x ^ 11 ≤ d * K * (d * x * y_abs) ^ ((3 : ℝ) / 2)) :
    x ^ (11 : ℝ) ≤ K * d ^ ((5 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) * y_abs ^ ((3 : ℝ) / 2) := by
  have heq := expand_abc_rhs_eq K hK x hx y_abs hy d hd_pos
  calc x ^ (11 : ℝ)
      = x ^ 11 := by norm_cast
    _ ≤ d * K * (d * x * y_abs) ^ ((3 : ℝ) / 2) := habc
    _ = K * d ^ ((5 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) * y_abs ^ ((3 : ℝ) / 2) := heq

lemma rpow_three_fourths_strict_mono (x : ℝ) (_hx : 1 ≤ x)
    (y_abs : ℝ) (_hy : 0 < y_abs)
    (hysq : y_abs ^ 2 < 2 * x ^ 11) :
    (y_abs ^ 2) ^ ((3 : ℝ) / 4) < (2 * x ^ 11) ^ ((3 : ℝ) / 4) := by
  apply Real.rpow_lt_rpow (sq_nonneg y_abs) hysq
  positivity

lemma lhs_simplify (y_abs : ℝ) (hy : 0 < y_abs) :
    (y_abs ^ 2) ^ ((3 : ℝ) / 4) = y_abs ^ ((3 : ℝ) / 2) := by
  rw [← Real.rpow_natCast_mul (le_of_lt hy) 2 ((3 : ℝ) / 4)]
  norm_num

lemma rhs_simplify (x : ℝ) (hx : 1 ≤ x) :
    (2 * x ^ 11) ^ ((3 : ℝ) / 4) = 2 ^ ((3 : ℝ) / 4) * x ^ ((33 : ℝ) / 4) := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hx11 : (0 : ℝ) ≤ x ^ 11 := pow_nonneg hx0 11
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx11]
  congr 1
  rw [← Real.rpow_natCast_mul hx0 11 ((3 : ℝ) / 4)]
  norm_num

lemma bound_y_three_halves (x : ℝ) (hx : 1 ≤ x)
    (y_abs : ℝ) (hy : 0 < y_abs)
    (hysq : y_abs ^ 2 < 2 * x ^ 11) :
    y_abs ^ ((3 : ℝ) / 2) < 2 ^ ((3 : ℝ) / 4) * x ^ ((33 : ℝ) / 4) := by
  have h1 := rpow_three_fourths_strict_mono x hx y_abs hy hysq
  rw [lhs_simplify y_abs hy] at h1
  rw [rhs_simplify x hx] at h1
  exact h1

lemma coeff_pos (K : ℝ) (hK : 0 < K)
    (x : ℝ) (hx : 1 ≤ x)
    (d : ℝ) (hd_pos : 0 < d) :
    0 < K * d ^ ((5 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) := by
  apply mul_pos
  · apply mul_pos hK
    exact Real.rpow_pos_of_pos hd_pos _
  · exact Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hx) _

lemma rpow_combine_x (x : ℝ) (hx : 0 < x) :
    x ^ ((3 : ℝ) / 2) * x ^ ((33 : ℝ) / 4) = x ^ ((39 : ℝ) / 4) := by
  rw [← Real.rpow_add hx]
  norm_num

lemma rearrange_rhs (K : ℝ) (_hK : 0 < K)
    (x : ℝ) (hx : 1 ≤ x)
    (d : ℝ) (_hd_pos : 0 < d) :
    K * d ^ ((5 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) * (2 ^ ((3 : ℝ) / 4) * x ^ ((33 : ℝ) / 4)) =
    2 ^ ((3 : ℝ) / 4) * K * d ^ ((5 : ℝ) / 2) * x ^ ((39 : ℝ) / 4) := by
  have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  rw [show K * d ^ ((5 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) * (2 ^ ((3 : ℝ) / 4) * x ^ ((33 : ℝ) / 4))
    = 2 ^ ((3 : ℝ) / 4) * K * d ^ ((5 : ℝ) / 2) * (x ^ ((3 : ℝ) / 2) * x ^ ((33 : ℝ) / 4))
    from by ring]
  rw [rpow_combine_x x hx_pos]

lemma substitute_y_combine_x (K : ℝ) (hK : 0 < K)
    (x : ℝ) (hx : 1 ≤ x)
    (y_abs : ℝ) (_hy : 0 < y_abs)
    (d : ℝ) (hd_pos : 0 < d)
    (h_expanded : x ^ (11 : ℝ) ≤ K * d ^ ((5 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) * y_abs ^ ((3 : ℝ) / 2))
    (h_ybound : y_abs ^ ((3 : ℝ) / 2) < 2 ^ ((3 : ℝ) / 4) * x ^ ((33 : ℝ) / 4)) :
    x ^ (11 : ℝ) ≤ 2 ^ ((3 : ℝ) / 4) * K * d ^ ((5 : ℝ) / 2) * x ^ ((39 : ℝ) / 4) := by
  have hcoeff := coeff_pos K hK x hx d hd_pos
  have hstep : K * d ^ ((5 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) * y_abs ^ ((3 : ℝ) / 2) <
      K * d ^ ((5 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) * (2 ^ ((3 : ℝ) / 4) * x ^ ((33 : ℝ) / 4)) :=
    mul_lt_mul_of_pos_left h_ybound hcoeff
  have hlt : x ^ (11 : ℝ) <
      K * d ^ ((5 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) * (2 ^ ((3 : ℝ) / 4) * x ^ ((33 : ℝ) / 4)) :=
    lt_of_le_of_lt h_expanded hstep
  rw [rearrange_rhs K hK x hx d hd_pos] at hlt
  exact le_of_lt hlt

lemma rpow_div_le_of_rpow_le (x : ℝ) (hx_pos : 0 < x)
    (a b : ℝ) (B : ℝ)
    (h : x ^ a ≤ B * x ^ b) :
    x ^ a / x ^ b ≤ B := by
  rwa [div_le_iff₀ (Real.rpow_pos_of_pos hx_pos b)]

lemma rpow_sub_eq_div (x : ℝ) (hx_pos : 0 < x) (a b : ℝ) :
    x ^ (a - b) = x ^ a / x ^ b := Real.rpow_sub hx_pos a b

lemma rpow_cancel_general (x : ℝ) (hx : 1 ≤ x)
    (a b : ℝ) (B : ℝ) (_hB : 0 < B)
    (h : x ^ a ≤ B * x ^ b) :
    x ^ (a - b) ≤ B := by
  have hx_pos : 0 < x := lt_of_lt_of_le one_pos hx
  rw [rpow_sub_eq_div x hx_pos a b]
  exact rpow_div_le_of_rpow_le x hx_pos a b B h

lemma divide_x_power (C : ℝ) (hC : 0 < C)
    (x : ℝ) (hx : 1 ≤ x)
    (h : x ^ (11 : ℝ) ≤ C * x ^ ((39 : ℝ) / 4)) :
    x ^ ((5 : ℝ) / 4) ≤ C := by
  have key := rpow_cancel_general x hx 11 (39 / 4) C hC h
  rwa [show (11 : ℝ) - 39 / 4 = 5 / 4 from by norm_num] at key

lemma cancel_x_powers (K : ℝ) (hK : 0 < K)
    (x : ℝ) (hx : 1 ≤ x)
    (y_abs : ℝ) (hy : 0 < y_abs)
    (d : ℝ) (hd_pos : 0 < d)
    (h_expanded : x ^ (11 : ℝ) ≤ K * d ^ ((5 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) * y_abs ^ ((3 : ℝ) / 2))
    (h_ybound : y_abs ^ ((3 : ℝ) / 2) < 2 ^ ((3 : ℝ) / 4) * x ^ ((33 : ℝ) / 4)) :
    x ^ ((5 : ℝ) / 4) ≤ 2 ^ ((3 : ℝ) / 4) * K * d ^ ((5 : ℝ) / 2) := by
  have hstep := substitute_y_combine_x K hK x hx y_abs hy d hd_pos h_expanded h_ybound
  exact divide_x_power (2 ^ ((3 : ℝ) / 4) * K * d ^ ((5 : ℝ) / 2))
    (by positivity) x hx hstep

lemma x_fifth_fourth_le (K : ℝ) (hK : 0 < K)
    (x : ℝ) (hx : 1 ≤ x)
    (y_abs : ℝ) (hy : 0 < y_abs)
    (d : ℝ) (hd_pos : 0 < d)
    (hysq : y_abs ^ 2 < 2 * x ^ 11)
    (habc : x ^ 11 ≤ d * K * (d * x * y_abs) ^ ((3 : ℝ) / 2)) :
    x ^ ((5 : ℝ) / 4) ≤ 2 ^ ((3 : ℝ) / 4) * K * d ^ ((5 : ℝ) / 2) := by
  have h1 := expand_abc_rhs K hK x hx y_abs hy d hd_pos habc
  have h2 := bound_y_three_halves x hx y_abs hy hysq
  exact cancel_x_powers K hK x hx y_abs hy d hd_pos h1 h2

lemma rpow_five_fourths_pow_four (x : ℝ) (hx : 0 ≤ x) :
    (x ^ ((5 : ℝ) / 4)) ^ 4 = x ^ 5 := by
  rw [← Real.rpow_natCast (x ^ ((5 : ℝ) / 4)) 4]
  rw [← Real.rpow_mul hx]
  norm_num

lemma two_rpow_three_fourths_pow_four :
    ((2 : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 = 8 := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ ((3 : ℝ) / 4)) 4]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma rpow_five_halves_pow_four (d : ℝ) (hd : 0 ≤ d) :
    (d ^ ((5 : ℝ) / 2)) ^ 4 = d ^ 10 := by
  rw [← Real.rpow_natCast (d ^ ((5 : ℝ) / 2)) 4]
  rw [← Real.rpow_mul hd]
  norm_num

lemma rhs_fourth_power (K : ℝ) (_hK : 0 < K) (d : ℝ) (hd : 0 < d) :
    (2 ^ ((3 : ℝ) / 4) * K * d ^ ((5 : ℝ) / 2)) ^ 4 = 8 * K ^ 4 * d ^ 10 := by
  have h1 : ((2 : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 = 8 := two_rpow_three_fourths_pow_four
  have h2 : (d ^ ((5 : ℝ) / 2)) ^ 4 = d ^ 10 := rpow_five_halves_pow_four d hd.le
  rw [show (2 : ℝ) ^ ((3 : ℝ) / 4) * K * d ^ ((5 : ℝ) / 2)
      = (2 : ℝ) ^ ((3 : ℝ) / 4) * (K * d ^ ((5 : ℝ) / 2)) from by ring]
  rw [mul_pow, mul_pow, h1, h2]
  ring

lemma pow_four_mono (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 4 ≤ b ^ 4 :=
  pow_le_pow_left₀ ha hab 4

lemma rpow_five_fourths_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x ^ ((5 : ℝ) / 4) :=
  Real.rpow_nonneg hx _

lemma raise_to_fourth (K : ℝ) (hK : 0 < K)
    (x : ℝ) (hx : 1 ≤ x)
    (d : ℝ) (hd_pos : 0 < d)
    (h : x ^ ((5 : ℝ) / 4) ≤ 2 ^ ((3 : ℝ) / 4) * K * d ^ ((5 : ℝ) / 2)) :
    x ^ 5 ≤ 8 * K ^ 4 * d ^ 10 := by
  have hx0 : (0 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hlhs : (x ^ ((5 : ℝ) / 4)) ^ 4 = x ^ 5 := rpow_five_fourths_pow_four x hx0
  have hrhs : (2 ^ ((3 : ℝ) / 4) * K * d ^ ((5 : ℝ) / 2)) ^ 4 = 8 * K ^ 4 * d ^ 10 :=
    rhs_fourth_power K hK d hd_pos
  have ha : 0 ≤ x ^ ((5 : ℝ) / 4) := rpow_five_fourths_nonneg x hx0
  have h4 : (x ^ ((5 : ℝ) / 4)) ^ 4 ≤ (2 ^ ((3 : ℝ) / 4) * K * d ^ ((5 : ℝ) / 2)) ^ 4 :=
    pow_four_mono _ _ ha h
  linarith

lemma d_pow_le_X_pow (K : ℝ) (hK : 0 < K)
    (X : ℝ) (_hX : 0 < X)
    (d : ℝ) (hd_pos : 0 < d) (hd_le : d ≤ X) :
    8 * K ^ 4 * d ^ 10 ≤ 8 * K ^ 4 * X ^ 10 := by
  gcongr

lemma E2_case1_bound (K : ℝ) (hK : 0 < K)
    (X : ℝ) (hX : 0 < X)
    (x : ℝ) (hx : 1 ≤ x)
    (y_abs : ℝ) (hy : 0 < y_abs)
    (d : ℝ) (hd_pos : 0 < d) (hd_le : d ≤ X)
    (hysq : y_abs ^ 2 < 2 * x ^ 11)
    (habc : x ^ 11 ≤ d * K * (d * x * y_abs) ^ ((3 : ℝ) / 2)) :
    x ^ 5 ≤ 8 * K ^ 4 * X ^ 10 := by
  have step1 := x_fifth_fourth_le K hK x hx y_abs hy d hd_pos hysq habc
  have step2 := raise_to_fourth K hK x hx d hd_pos step1
  have step3 := d_pow_le_X_pow K hK X hX d hd_pos hd_le
  linarith

lemma expand_case2_rhs (K : ℝ) (hK : 0 < K)
    (x : ℝ) (hx : 1 ≤ x)
    (y_abs : ℝ) (hy : 0 < y_abs)
    (d : ℝ) (hd_pos : 0 < d)
    (habc : y_abs ^ 2 ≤ d * K * (d * x * y_abs) ^ ((3 : ℝ) / 2)) :
    y_abs ^ (2 : ℝ) ≤ K * d ^ ((5 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) * y_abs ^ ((3 : ℝ) / 2) := by
  rw [Real.rpow_ofNat]
  rw [expand_abc_rhs_eq K hK x hx y_abs hy d hd_pos] at habc
  exact habc

lemma rpow_half_le_of_sq_le_mul_three_halves
    (y : ℝ) (hy : 0 < y) (A : ℝ)
    (h : y ^ (2 : ℝ) ≤ A * y ^ ((3 : ℝ) / 2)) :
    y ^ ((1 : ℝ) / 2) ≤ A := by
  have hy_pos : (0 : ℝ) < y ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hy _
  have key : y ^ ((1 : ℝ) / 2) * y ^ ((3 : ℝ) / 2) ≤ A * y ^ ((3 : ℝ) / 2) := by
    rwa [← Real.rpow_add hy, show (1 : ℝ) / 2 + 3 / 2 = 2 from by norm_num]
  exact le_of_mul_le_mul_right key hy_pos

lemma div_y_three_halves (K : ℝ) (_hK : 0 < K)
    (x : ℝ) (_hx : 1 ≤ x)
    (y_abs : ℝ) (hy : 0 < y_abs)
    (d : ℝ) (_hd_pos : 0 < d)
    (h : y_abs ^ (2 : ℝ) ≤ K * d ^ ((5 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) * y_abs ^ ((3 : ℝ) / 2)) :
    y_abs ^ ((1 : ℝ) / 2) ≤ K * d ^ ((5 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) := by
  apply rpow_half_le_of_sq_le_mul_three_halves y_abs hy
  linarith

lemma rpow_quarter_preserves_lt (x : ℝ) (hx : 1 ≤ x)
    (y_abs : ℝ) (_hy : 0 < y_abs)
    (hx11_lt_y2 : x ^ (11 : ℕ) < y_abs ^ (2 : ℕ)) :
    (x ^ (11 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) < (y_abs ^ (2 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
  apply Real.rpow_lt_rpow (pow_nonneg (le_trans zero_le_one hx) 11) hx11_lt_y2
  norm_num

lemma rpow_nat_pow_quarter_lhs (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (11 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) = x ^ ((11 : ℝ) / 4) := by
  rw [← Real.rpow_natCast_mul hx]
  norm_num

lemma rpow_nat_pow_quarter_rhs (y : ℝ) (hy : 0 ≤ y) :
    (y ^ (2 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) = y ^ ((1 : ℝ) / 2) := by
  rw [← Real.rpow_natCast y 2, ← Real.rpow_mul hy]
  norm_num

lemma x_pow_lt_y_half (x : ℝ) (hx : 1 ≤ x)
    (y_abs : ℝ) (hy : 0 < y_abs)
    (hx11_lt_y2 : x ^ 11 < y_abs ^ 2) :
    x ^ ((11 : ℝ) / 4) < y_abs ^ ((1 : ℝ) / 2) := by
  have hx0 : 0 ≤ x := le_trans (by norm_num : (0 : ℝ) ≤ 1) hx
  have hy0 : 0 ≤ y_abs := le_of_lt hy
  have h1 := rpow_quarter_preserves_lt x hx y_abs hy hx11_lt_y2
  rw [rpow_nat_pow_quarter_lhs x hx0, rpow_nat_pow_quarter_rhs y_abs hy0] at h1
  exact h1

lemma combine_and_cancel_x (K : ℝ) (hK : 0 < K)
    (x : ℝ) (hx : 1 ≤ x)
    (d : ℝ) (hd_pos : 0 < d)
    (h : x ^ ((11 : ℝ) / 4) ≤ K * d ^ ((5 : ℝ) / 2) * x ^ ((3 : ℝ) / 2)) :
    x ^ ((5 : ℝ) / 4) ≤ K * d ^ ((5 : ℝ) / 2) := by
  have hKd : 0 < K * d ^ ((5 : ℝ) / 2) :=
    mul_pos hK (Real.rpow_pos_of_pos hd_pos _)
  have h_eq : (11 : ℝ) / 4 - 3 / 2 = 5 / 4 := by norm_num
  rw [← h_eq]
  exact rpow_cancel_general x hx ((11 : ℝ) / 4) ((3 : ℝ) / 2) (K * d ^ ((5 : ℝ) / 2)) hKd h

lemma scale_up_by_two_pow (K : ℝ) (hK : 0 < K)
    (x : ℝ) (_hx : 1 ≤ x)
    (d : ℝ) (hd_pos : 0 < d)
    (h : x ^ ((5 : ℝ) / 4) ≤ K * d ^ ((5 : ℝ) / 2)) :
    x ^ ((5 : ℝ) / 4) ≤ 2 ^ ((3 : ℝ) / 4) * K * d ^ ((5 : ℝ) / 2) := by
  calc x ^ ((5 : ℝ) / 4)
      ≤ K * d ^ ((5 : ℝ) / 2) := h
    _ ≤ 2 ^ ((3 : ℝ) / 4) * (K * d ^ ((5 : ℝ) / 2)) :=
        le_mul_of_one_le_left (by positivity)
          (Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 3 / 4))
    _ = 2 ^ ((3 : ℝ) / 4) * K * d ^ ((5 : ℝ) / 2) := by ring

lemma case2_x_fifth_fourth_le (K : ℝ) (hK : 0 < K)
    (x : ℝ) (hx : 1 ≤ x)
    (y_abs : ℝ) (hy : 0 < y_abs)
    (d : ℝ) (hd_pos : 0 < d)
    (hx11_lt_y2 : x ^ 11 < y_abs ^ 2)
    (habc : y_abs ^ 2 ≤ d * K * (d * x * y_abs) ^ ((3 : ℝ) / 2)) :
    x ^ ((5 : ℝ) / 4) ≤ 2 ^ ((3 : ℝ) / 4) * K * d ^ ((5 : ℝ) / 2) := by
  have h1 := expand_case2_rhs K hK x hx y_abs hy d hd_pos habc
  have h2 := div_y_three_halves K hK x hx y_abs hy d hd_pos h1
  have h3 := x_pow_lt_y_half x hx y_abs hy hx11_lt_y2
  have h4 : x ^ ((11 : ℝ) / 4) ≤ K * d ^ ((5 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) :=
    le_trans (le_of_lt h3) h2
  have h5 := combine_and_cancel_x K hK x hx d hd_pos h4
  exact scale_up_by_two_pow K hK x hx d hd_pos h5

lemma E2_case2_bound (K : ℝ) (hK : 0 < K)
    (X : ℝ) (hX : 0 < X)
    (x : ℝ) (hx : 1 ≤ x)
    (y_abs : ℝ) (hy : 0 < y_abs)
    (d : ℝ) (hd_pos : 0 < d) (hd_le : d ≤ X)
    (hx11_lt_y2 : x ^ 11 < y_abs ^ 2)
    (_hysq_le : y_abs ^ 2 ≤ x ^ 11 + d)
    (habc : y_abs ^ 2 ≤ d * K * (d * x * y_abs) ^ ((3 : ℝ) / 2)) :
    x ^ 5 ≤ 8 * K ^ 4 * X ^ 10 := by
  have h1 := case2_x_fifth_fourth_le K hK x hx y_abs hy d hd_pos hx11_lt_y2 habc
  have h2 := raise_to_fourth K hK x hx d hd_pos h1
  have h3 := d_pow_le_X_pow K hK X hX d hd_pos hd_le
  linarith

lemma E2_x_fifth_le_of_max_bound (K : ℝ) (hK : 0 < K)
    (X : ℝ) (hX : 0 < X)
    (x : ℝ) (hx : 1 ≤ x)
    (y_abs : ℝ) (hy : 0 < y_abs)
    (d : ℝ) (hd_pos : 0 < d) (hd_le : d ≤ X)
    (hysq_lt : y_abs ^ 2 < 2 * x ^ 11)
    (hysq_le_d : y_abs ^ 2 ≤ x ^ 11 + d)
    (hmax : max (x ^ 11) (y_abs ^ 2) ≤ d * K * (d * x * y_abs) ^ ((3 : ℝ) / 2)) :
    x ^ 5 ≤ 8 * K ^ 4 * X ^ 10 := by
  rcases le_or_gt (y_abs ^ 2) (x ^ 11) with h | h
  · have hx11_le : x ^ 11 ≤ d * K * (d * x * y_abs) ^ ((3 : ℝ) / 2) :=
      le_trans (le_max_left _ _) hmax
    exact E2_case1_bound K hK X hX x hx y_abs hy d hd_pos hd_le hysq_lt hx11_le
  · have hy2_le : y_abs ^ 2 ≤ d * K * (d * x * y_abs) ^ ((3 : ℝ) / 2) :=
      le_trans (le_max_right _ _) hmax
    exact E2_case2_bound K hK X hX x hx y_abs hy d hd_pos hd_le (gt_iff_lt.mp h) hysq_le_d hy2_le

lemma E2_x_fifth_le (K : ℝ) (hK : 0 < K)
    (hK_abc : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → a + b = c →
          (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (X : ℝ) (hX : 2 < X)
    (p : ℕ+ × ℤ) (hp : p ∈ E2Set X) :
    ((p.1 : ℕ) : ℝ) ^ 5 ≤ 8 * K ^ 4 * X ^ 10 := by
  have hysq_int := E2_y_sq_le X (p.1 : ℕ) p hp le_rfl
  have hy_abs_int := int_abs_le_of_sq_le p.2 ((p.1 : ℕ) ^ 11 + ⌊X⌋₊) (by exact_mod_cast hysq_int)
  have hy_ne : p.2 ≠ 0 := E2_y_ne_zero X hX p hp
  have hysq_lt : (p.2 : ℝ) ^ 2 < 2 * ((p.1 : ℕ) : ℝ) ^ 11 := E2_ysq_lt_2x11 X hX p hp
  obtain ⟨hx_gt, hd_lb, hd_ub⟩ := hp
  set d := (|(↑↑p.1 : ℤ) ^ 11 - p.2 ^ 2|).natAbs with hd_def
  have hd_pos : 0 < d := by
    rw [hd_def, Nat.pos_iff_ne_zero, ne_eq, Int.natAbs_eq_zero]
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℤ) < 1) hd_lb)
  have hd_eq : (d : ℤ) = |(↑↑p.1 : ℤ) ^ 11 - p.2 ^ 2| := by
    simp [hd_def]
  have hd_le_X : (d : ℝ) ≤ X := by
    have h1 : (d : ℝ) = (|(↑↑p.1 : ℤ) ^ 11 - p.2 ^ 2| : ℤ) := by exact_mod_cast hd_eq
    rw [h1]; push_cast; exact hd_ub
  have hx_pos : 0 < (p.1 : ℕ) := p.1.pos
  have hmax := E2_abc_applied K hK hK_abc (p.1 : ℕ) hx_pos p.2 hy_ne d hd_pos hd_eq
  have hysq_le_d : (p.2 : ℝ) ^ 2 ≤ ((p.1 : ℕ) : ℝ) ^ 11 + (d : ℝ) := by
    suffices h : (p.2 : ℝ) ^ 2 - ((p.1 : ℕ) : ℝ) ^ 11 ≤ (d : ℝ) by linarith
    rw [show (d : ℝ) = ((|(↑↑p.1 : ℤ) ^ 11 - p.2 ^ 2| : ℤ) : ℝ) by exact_mod_cast hd_eq]; push_cast
    linarith [abs_nonneg (((p.1 : ℕ) : ℝ) ^ 11 - (p.2 : ℝ) ^ 2),
              abs_sub_comm (((p.1 : ℕ) : ℝ) ^ 11) ((p.2 : ℝ) ^ 2),
              le_abs_self ((p.2 : ℝ) ^ 2 - ((p.1 : ℕ) : ℝ) ^ 11)]
  have hy_abs_pos : 0 < |(p.2 : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hy_ne)
  have hx_ge1 : (1 : ℝ) ≤ ((p.1 : ℕ) : ℝ) := by exact_mod_cast hx_pos
  have hd_pos_real : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos
  have hX_pos : (0 : ℝ) < X := by linarith
  exact E2_x_fifth_le_of_max_bound K hK X hX_pos ((p.1 : ℕ) : ℝ) hx_ge1
    |(p.2 : ℝ)| hy_abs_pos (d : ℝ) hd_pos_real hd_le_X
    (by rw [sq_abs]; exact hysq_lt) (by rw [sq_abs]; exact hysq_le_d)
    (by rw [sq_abs]; exact hmax)

lemma fifth_root_bound (x C : ℝ) (hx : 0 ≤ x) (hC : 0 ≤ C)
    (h : x ^ 5 ≤ C) :
    x ≤ C ^ ((1 : ℝ) / 5) := by
  rw [← Real.rpow_natCast x 5] at h
  have hC' := Real.rpow_nonneg hC ((1 : ℝ) / 5)
  rw [← Real.rpow_le_rpow_iff hx hC' (by positivity : (0 : ℝ) < 5)]
  have key : (C ^ ((1 : ℝ) / 5)) ^ ((5 : ℝ)) = C := by
    rw [← Real.rpow_mul hC]
    norm_num
  rw [key]
  exact h

lemma E2_x_bound_real (K : ℝ) (hK : 0 < K)
    (hK_abc : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → a + b = c →
          (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (X : ℝ) (hX : 2 < X)
    (p : ℕ+ × ℤ) (hp : p ∈ E2Set X) :
    (p.1 : ℝ) ≤ (8 * K ^ 4 * X ^ 10) ^ ((1 : ℝ) / 5) := by
  have h5 := E2_x_fifth_le K hK hK_abc X hX p hp
  exact fifth_root_bound (↑↑p.1) (8 * K ^ 4 * X ^ 10) (by positivity) (by positivity) h5

lemma E2_set_bounded_of_abc (habc : ABC) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ < X →
      ∃ (N : ℕ) (M : ℕ),
        ∀ p : ℕ+ × ℤ, p ∈ E2Set X → (p.1 : ℕ) ≤ N ∧ |p.2| ≤ (M : ℤ) := by
  obtain ⟨K, hK, hK_abc⟩ := abc_specialize_half habc
  refine ⟨2, by norm_num, fun X hX => ?_⟩
  set N := ⌈(8 * K ^ 4 * X ^ 10) ^ ((1 : ℝ) / 5)⌉₊ with hN_def
  refine ⟨N, N ^ 11 + ⌊X⌋₊ + 1, fun p hp => ?_⟩
  constructor
  · exact real_bound_to_nat_bound p _ (E2_x_bound_real K hK hK_abc X hX p hp)
  · exact E2_y_bound X N p hp (real_bound_to_nat_bound p _ (E2_x_bound_real K hK hK_abc X hX p hp))

lemma E2_set_finite_of_abc (habc : ABC) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ < X → (E2Set X).Finite := by
  obtain ⟨X₀, hX₀pos, hbounded⟩ := E2_set_bounded_of_abc habc
  exact ⟨X₀, hX₀pos, fun X hX => by
    obtain ⟨N, M, hNM⟩ := hbounded X hX
    exact bounded_pnat_int_set_finite _ N M hNM⟩

lemma tau_sq_formula (R : RamanujanTau) (p : ℕ+) (hp : (p : ℕ).Prime) :
    R.τ (p ^ 2) = R.τ p ^ 2 - (↑(p : ℕ) : ℤ) ^ 11 := by
  have h := R.hecke_rec p hp 2 (le_refl 2)
  simp only [show (2 : ℕ) - 1 = 1 from rfl, show (2 : ℕ) - 2 = 0 from rfl] at h
  rw [pow_one, pow_zero, tau_one_eq_one] at h
  linarith [sq (R.τ p)]

lemma p11_minus_tau_sq (R : RamanujanTau) (p : ℕ+) (hp : (p : ℕ).Prime) :
    (↑(p : ℕ) : ℤ) ^ 11 - R.τ p ^ 2 = -R.τ (p ^ 2) := by
  have h := tau_sq_formula R p hp
  linarith

lemma E2_cond2 (R : RamanujanTau) (p : ℕ+) (hp : (p : ℕ).Prime)
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hτ : (R.τ (p ^ 2)).natAbs = ℓ) :
    1 ≤ |(↑(p : ℕ) : ℤ) ^ 11 - R.τ p ^ 2| := by
  have h1 := p11_minus_tau_sq R p hp
  rw [h1, abs_neg]
  rw [Int.abs_eq_natAbs]
  rw [hτ]
  exact_mod_cast hℓ.one_le

lemma E2_cond3 (R : RamanujanTau) (X : ℝ) (p : ℕ+) (hp : (p : ℕ).Prime)
    (ℓ : ℕ) (hℓX : (ℓ : ℝ) ≤ X) (hτ : (R.τ (p ^ 2)).natAbs = ℓ) :
    (|(↑(p : ℕ) : ℤ) ^ 11 - R.τ p ^ 2| : ℝ) ≤ X := by
  have h_eq : (|(↑(p : ℕ) : ℤ) ^ 11 - R.τ p ^ 2| : ℝ) = (|R.τ (p ^ 2)| : ℝ) := by
    have h := p11_minus_tau_sq R p hp
    have h_cast : (|(↑(p : ℕ) : ℤ) ^ 11 - R.τ p ^ 2| : ℤ) = (|R.τ (p ^ 2)| : ℤ) := by
      rw [h, abs_neg]
    exact_mod_cast h_cast
  rw [h_eq]
  have : (|R.τ (p ^ 2)| : ℝ) = ((R.τ (p ^ 2)).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [this, hτ]
  exact hℓX

lemma witness_in_E2_set (R : RamanujanTau) (X : ℝ) (p : ℕ+)
    (hp : (p : ℕ).Prime) (hpX : (p : ℝ) > X ^ ((2 : ℝ) / 11))
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hℓX : (ℓ : ℝ) ≤ X)
    (hτ : (R.τ (p ^ 2)).natAbs = ℓ) :
    (p, R.τ p) ∈ E2Set X := by
  refine ⟨hpX, E2_cond2 R p hp ℓ hℓ hτ, E2_cond3 R X p hp ℓ hℓX hτ⟩

open Classical in
/-- A choice of prime `p` exhibiting `ℓ` as `|τ (p ^ 2)|` with `p > X ^ (2/11)`, when one
exists; otherwise `1`. -/
noncomputable def witnessPE2 (R : RamanujanTau) (X : ℝ) (ℓ : ℕ) : ℕ+ :=
  if h : ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 2)).natAbs = ℓ ∧
    (p : ℝ) > X ^ ((2 : ℝ) / 11) then h.choose else 1

lemma witnessP_E2_spec (R : RamanujanTau) (X : ℝ) (ℓ : ℕ)
    (h : ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 2)).natAbs = ℓ ∧
      (p : ℝ) > X ^ ((2 : ℝ) / 11)) :
    (witnessPE2 R X ℓ : ℕ).Prime ∧
    (R.τ ((witnessPE2 R X ℓ) ^ 2)).natAbs = ℓ ∧
    (witnessPE2 R X ℓ : ℝ) > X ^ ((2 : ℝ) / 11) := by
  unfold witnessPE2
  rw [dif_pos h]
  exact h.choose_spec

/-- The map sending `ℓ` to `(witnessPE2 R X ℓ, τ (witnessPE2 R X ℓ ^ 2))`. -/
noncomputable def witnessMapE2 (R : RamanujanTau) (X : ℝ) (ℓ : ℕ) : ℕ+ × ℤ :=
  (witnessPE2 R X ℓ, R.τ (witnessPE2 R X ℓ))

lemma witnessMap_E2_mapsTo (R : RamanujanTau) (X : ℝ) :
    ∀ ℓ ∈ {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ ∧
        (p : ℝ) > X ^ ((2 : ℝ) / 11)},
    witnessMapE2 R X ℓ ∈ E2Set X := by
  intro ℓ hℓ
  simp only [Set.mem_setOf_eq] at hℓ
  obtain ⟨hℓ_prime, hℓX, p, hp_prime, hτ, hpX⟩ := hℓ
  have h_ex : ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 2)).natAbs = ℓ ∧
      (p : ℝ) > X ^ ((2 : ℝ) / 11) := ⟨p, hp_prime, hτ, hpX⟩
  obtain ⟨hw_prime, hw_τ, hw_large⟩ := witnessP_E2_spec R X ℓ h_ex
  exact witness_in_E2_set R X (witnessPE2 R X ℓ) hw_prime hw_large ℓ hℓ_prime hℓX hw_τ

lemma witnessMap_E2_injOn (R : RamanujanTau) (X : ℝ) :
    Set.InjOn (witnessMapE2 R X)
      {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧
          (R.τ (p ^ 2)).natAbs = ℓ ∧
          (p : ℝ) > X ^ ((2 : ℝ) / 11)} := by
  intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ heq
  obtain ⟨_, _, hexists₁⟩ := hℓ₁
  obtain ⟨_, _, hexists₂⟩ := hℓ₂
  have spec₁ := witnessP_E2_spec R X ℓ₁ hexists₁
  have spec₂ := witnessP_E2_spec R X ℓ₂ hexists₂
  simp only [witnessMapE2, Prod.mk.injEq] at heq
  obtain ⟨hp_eq, _⟩ := heq
  rw [← spec₁.2.1, ← spec₂.2.1, hp_eq]

lemma L_large_ncard_le_E2 (R : RamanujanTau) (X : ℝ) (hfin : (E2Set X).Finite) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ ∧
        (p : ℝ) > X ^ ((2 : ℝ) / 11)}.ncard ≤ E2 X :=
    Set.ncard_le_ncard_of_injOn (witnessMapE2 R X)
    (witnessMap_E2_mapsTo R X) (witnessMap_E2_injOn R X) hfin

theorem large_ell_bound (R : RamanujanTau) (habc : ABC) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
          ∃ p : ℕ+, (p : ℕ).Prime ∧
            (R.τ (p ^ 2)).natAbs = ℓ ∧
            (p : ℝ) > X ^ ((2 : ℝ) / 11)}.ncard : ℝ) ≤ (E2 X : ℝ) := by
  obtain ⟨X₀, hX₀pos, hX₀fin⟩ := E2_set_finite_of_abc habc
  exact ⟨X₀, hX₀pos, fun X hX => by
    have hfin := hX₀fin X hX
    exact Nat.cast_le.mpr (L_large_ncard_le_E2 R X hfin)⟩

lemma target_subset_image_k1 (R : RamanujanTau) (X : ℝ) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ ∧
        (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)} ⊆
    (fun p : ℕ+ => (R.τ (p ^ 2)).natAbs) ''
      {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)} := by
  intro ℓ hℓ
  simp only [Set.mem_setOf_eq] at hℓ
  obtain ⟨_, _, p, hp_prime, hp_eq, hp_bd⟩ := hℓ
  exact ⟨p, ⟨hp_prime, hp_bd⟩, hp_eq⟩

lemma natLe_floor_of_cast_le (B : ℝ) (x : ℕ) (hx : (x : ℝ) ≤ B) : x ≤ ⌊B⌋₊ := by
  by_contra h
  push Not at h
  have hlt : B < ↑(⌊B⌋₊ + 1) := by exact_mod_cast Nat.lt_floor_add_one B
  have hxge : (x : ℝ) ≥ ↑(⌊B⌋₊ + 1) := by exact_mod_cast h
  linarith

lemma pnat_bounded_finite_k1 (B : ℝ) :
    {p : ℕ+ | (p : ℝ) ≤ B}.Finite :=
  pnat_bounded_finite B

lemma pnat_bounded_finite_nat (M : ℕ) :
    {p : ℕ+ | (p : ℕ) ≤ M}.Finite := by
  apply Set.Finite.subset (pnat_bounded_finite_k1 (M : ℝ))
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  exact_mod_cast hp

lemma witness_set_subset_bounded (X : ℝ) :
    {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)} ⊆
    {p : ℕ+ | (p : ℕ) ≤ ⌊X ^ ((2 : ℝ) / 11)⌋₊} := by
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  exact natLe_floor_of_cast_le _ _ hp.2

lemma witness_set_finite_k1 (X : ℝ) :
    {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}.Finite := by
  apply Set.Finite.subset (pnat_bounded_finite_nat ⌊X ^ ((2 : ℝ) / 11)⌋₊)
  exact witness_set_subset_bounded X

lemma ncard_Icc_one_M (M : ℕ) :
    (↑(Finset.Icc 1 M) : Set ℕ).ncard = M := by
  rw [Set.ncard_coe_finset, Nat.card_Icc]
  omega

lemma pnat_val_mapsTo_Icc (M : ℕ) :
    ∀ a ∈ {p : ℕ+ | (p : ℕ) ≤ M}, (a : ℕ) ∈ (↑(Finset.Icc 1 M) : Set ℕ) := by
  intro a ha
  simp only [Set.mem_setOf_eq] at ha
  simp only [Finset.coe_Icc, Set.mem_Icc]
  exact ⟨a.pos, ha⟩

lemma pnat_bounded_ncard_le (M : ℕ) :
    {p : ℕ+ | (p : ℕ) ≤ M}.ncard ≤ M := by
  calc {p : ℕ+ | (p : ℕ) ≤ M}.ncard
      ≤ (↑(Finset.Icc 1 M) : Set ℕ).ncard := Set.ncard_le_ncard_of_injOn
          (fun p => (p : ℕ))
          (pnat_val_mapsTo_Icc M)
          (fun _ _ _ _ h => PNat.coe_injective h)
          (Set.toFinite _)
    _ = M := ncard_Icc_one_M M

lemma witness_set_ncard_le_k1 (X : ℝ) (_hX : 1 ≤ X) :
    {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}.ncard ≤ ⌊X ^ ((2 : ℝ) / 11)⌋₊ := by
  calc {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}.ncard
      ≤ {p : ℕ+ | (p : ℕ) ≤ ⌊X ^ ((2 : ℝ) / 11)⌋₊}.ncard := by
        apply Set.ncard_le_ncard (witness_set_subset_bounded X)
          (pnat_bounded_finite_nat _)
    _ ≤ ⌊X ^ ((2 : ℝ) / 11)⌋₊ := pnat_bounded_ncard_le _

lemma floor_rpow_le_k1 (X : ℝ) (hX : 1 ≤ X) :
    (⌊X ^ ((2 : ℝ) / 11)⌋₊ : ℝ) ≤ X ^ ((2 : ℝ) / 11) := Nat.floor_le (by positivity)

lemma small_ell_bound (R : RamanujanTau) :
    ∀ X : ℝ, 1 ≤ X →
      ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧
          (R.τ (p ^ 2)).natAbs = ℓ ∧
          (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}.ncard : ℝ) ≤ X ^ ((2 : ℝ) / 11) := by
  intro X hX
  have h_sub := target_subset_image_k1 R X
  have h_wfin := witness_set_finite_k1 X
  have h_img_fin := h_wfin.image (fun p : ℕ+ => (R.τ (p ^ 2)).natAbs)
  have h_ncard_sub : {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ ∧
        (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}.ncard ≤
    ((fun p : ℕ+ => (R.τ (p ^ 2)).natAbs) ''
        {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}).ncard :=
    Set.ncard_le_ncard h_sub h_img_fin
  have h_img_le : ((fun p : ℕ+ => (R.τ (p ^ 2)).natAbs) ''
      {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}).ncard ≤
    {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}.ncard :=
    Set.ncard_image_le h_wfin
  have h_ncard_floor := witness_set_ncard_le_k1 X hX
  have h_floor_le := floor_rpow_le_k1 X hX
  have h_ncard_le : {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ ∧
        (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}.ncard ≤ ⌊X ^ ((2 : ℝ) / 11)⌋₊ :=
    le_trans h_ncard_sub (le_trans h_img_le h_ncard_floor)
  calc ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 2)).natAbs = ℓ ∧
        (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}.ncard : ℝ)
      ≤ (⌊X ^ ((2 : ℝ) / 11)⌋₊ : ℝ) := by exact_mod_cast h_ncard_le
    _ ≤ X ^ ((2 : ℝ) / 11) := h_floor_le

lemma rpow_le_rpow_of_le_exp {X a b : ℝ} (hX : 1 ≤ X) (hab : a ≤ b) :
    X ^ a ≤ X ^ b := Real.rpow_le_rpow_of_exponent_le hX hab

lemma k1_contribution_abc (R : RamanujanTau) (habc : ABC) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
          ∃ p : ℕ+, (p : ℕ).Prime ∧
            (R.τ (p ^ 2)).natAbs = ℓ}.ncard : ℝ) ≤
        (E2 X : ℝ) + X ^ ((13 : ℝ) / 22) := by
  obtain ⟨X₀, hX₀pos, hX₀⟩ := large_ell_bound R habc
  refine ⟨max X₀ 1, by positivity, ?_⟩
  intro X hX
  have hX₀lt : X₀ < X := lt_of_le_of_lt (le_max_left _ _) hX
  have hX1 : 1 ≤ X := le_of_lt (lt_of_le_of_lt (le_max_right X₀ 1) hX)
  calc ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
          ∃ p : ℕ+, (p : ℕ).Prime ∧
            (R.τ (p ^ 2)).natAbs = ℓ}.ncard : ℝ)
      ≤ ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
            ∃ p : ℕ+, (p : ℕ).Prime ∧
              (R.τ (p ^ 2)).natAbs = ℓ ∧
              (p : ℝ) > X ^ ((2 : ℝ) / 11)}.ncard : ℝ) +
          ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
            ∃ p : ℕ+, (p : ℕ).Prime ∧
              (R.τ (p ^ 2)).natAbs = ℓ ∧
              (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}.ncard : ℝ) := ell_split_large_small R X
    _ ≤ (E2 X : ℝ) + X ^ ((2 : ℝ) / 11) := by
        have h1 := hX₀ X hX₀lt
        have h2 := small_ell_bound R X hX1
        linarith
    _ ≤ (E2 X : ℝ) + X ^ ((13 : ℝ) / 22) := by
        have := rpow_le_rpow_of_le_exp hX1 (show (2 : ℝ) / 11 ≤ 13 / 22 by norm_num)
        linarith

lemma target_subset_image (R : RamanujanTau) (X : ℝ) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11) ∧
        (R.τ (p ^ 4)).natAbs = ℓ} ⊆
    (fun p : ℕ+ => (R.τ (p ^ 4)).natAbs) ''
      {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11)} := by
  intro ℓ hℓ
  simp only [Set.mem_setOf_eq] at hℓ
  obtain ⟨_, _, p, hp_prime, hp_bound, hp_eq⟩ := hℓ
  exact ⟨p, ⟨hp_prime, hp_bound⟩, hp_eq⟩

lemma witness_set_finite (X : ℝ) :
    {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11)}.Finite := by
  apply Set.Finite.subset (pnat_bounded_finite (X ^ ((1 : ℝ) / 11)))
  intro p hp
  exact hp.2

private lemma prime_set_subset_bounded (X : ℝ) :
    {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11)} ⊆
    {p : ℕ+ | (p : ℕ) ≤ ⌊X ^ ((1 : ℝ) / 11)⌋₊} := by
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  exact Nat.le_floor hp.2

lemma witness_set_ncard_le (X : ℝ) (_hX : 1 < X) :
    {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11)}.ncard ≤ ⌊X ^ ((1 : ℝ) / 11)⌋₊ := by
  calc {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11)}.ncard
      ≤ {p : ℕ+ | (p : ℕ) ≤ ⌊X ^ ((1 : ℝ) / 11)⌋₊}.ncard := by
        apply Set.ncard_le_ncard (prime_set_subset_bounded X) (pnat_bounded_finite_nat _)
    _ ≤ ⌊X ^ ((1 : ℝ) / 11)⌋₊ := pnat_bounded_ncard_le _

lemma floor_rpow_le (X : ℝ) (hX : 0 < X) :
    (⌊X ^ ((1 : ℝ) / 11)⌋₊ : ℝ) ≤ X ^ ((1 : ℝ) / 11) :=
  Nat.floor_le (Real.rpow_nonneg (le_of_lt hX) _)

lemma small_primes_k2_bound (R : RamanujanTau) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ < X →
      ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11) ∧
          (R.τ (p ^ 4)).natAbs = ℓ}.ncard : ℝ) ≤
      X ^ ((1 : ℝ) / 11) := by
  refine ⟨1, one_pos, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have h_sub := target_subset_image R X
  have h_wfin := witness_set_finite X
  have h_ifin := h_wfin.image (fun p : ℕ+ => (R.τ (p ^ 4)).natAbs)
  have h1 : {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11) ∧
        (R.τ (p ^ 4)).natAbs = ℓ}.ncard ≤
    ((fun p : ℕ+ => (R.τ (p ^ 4)).natAbs) ''
        {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11)}).ncard :=
    Set.ncard_le_ncard h_sub h_ifin
  have h2 : ((fun p : ℕ+ => (R.τ (p ^ 4)).natAbs) ''
      {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11)}).ncard ≤
    {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11)}.ncard :=
    Set.ncard_image_le h_wfin
  have h3 := witness_set_ncard_le X hX
  have h4 := floor_rpow_le X hX0
  calc ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11) ∧
        (R.τ (p ^ 4)).natAbs = ℓ}.ncard : ℝ)
      ≤ (⌊X ^ ((1 : ℝ) / 11)⌋₊ : ℝ) := by
        exact_mod_cast le_trans h1 (le_trans h2 h3)
    _ ≤ X ^ ((1 : ℝ) / 11) := h4

private theorem tau_cube_formula (R : RamanujanTau) (p : ℕ+) (hp : (p : ℕ).Prime) :
    R.τ (p ^ 3) = R.τ p ^ 3 - 2 * (↑(p : ℕ) : ℤ) ^ 11 * R.τ p := by
  have h3 := R.hecke_rec p hp 3 (by omega)
  simp only [show 3 - 1 = 2 from rfl, show 3 - 2 = 1 from rfl, pow_one] at h3
  have hsq := tau_sq_formula R p hp
  rw [hsq] at h3
  linarith [h3]

private lemma tau_fourth_formula (R : RamanujanTau) (p : ℕ+) (hp : (p : ℕ).Prime) :
    R.τ (p ^ 4) = R.τ p ^ 4 - 3 * (↑(p : ℕ) : ℤ) ^ 11 * R.τ p ^ 2 +
      (↑(p : ℕ) : ℤ) ^ 22 := by
  have hrec := R.hecke_rec p hp 4 (by omega)
  have h3 := tau_cube_formula R p hp
  have h2 := tau_sq_formula R p hp
  simp only [show 4 - 1 = 3 from rfl, show 4 - 2 = 2 from rfl] at hrec
  rw [h3, h2] at hrec
  rw [hrec]
  ring

lemma hecke_u_identity (R : RamanujanTau) (p : ℕ+) (hp : (p : ℕ).Prime) :
    let u := 2 * (R.τ p) ^ 2 - 3 * (↑(p : ℕ) : ℤ) ^ 11
    u ^ 2 - 5 * (↑(p : ℕ) : ℤ) ^ 22 = 4 * R.τ (p ^ 4) := by
  simp only
  rw [tau_fourth_formula R p hp]
  ring

lemma E4_set_D_bounds (X : ℝ) (p : ℕ+ × ℤ) (hp : p ∈ E4Set X) :
    (1 : ℝ) ≤ (|p.2 ^ 2 - 5 * (↑p.1 : ℤ) ^ 22| : ℝ) ∧
    (|p.2 ^ 2 - 5 * (↑p.1 : ℤ) ^ 22| : ℝ) ≤ 4 * X := by
  obtain ⟨_, h1, h2⟩ := hp
  exact ⟨by exact_mod_cast h1, h2⟩

lemma rpow_11_strict_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    a ^ (11 : ℕ) < b ^ (11 : ℕ) := pow_lt_pow_left₀ hab ha (by norm_num)

lemma rpow_one_div_11_pow_11 (X : ℝ) (hX : 0 ≤ X) :
    (X ^ ((1 : ℝ) / 11)) ^ (11 : ℕ) = X := by
  have h11 : (11 : ℕ) ≠ 0 := by norm_num
  rw [show (1 : ℝ) / 11 = (↑(11 : ℕ))⁻¹ by norm_num]
  exact Real.rpow_inv_natCast_pow hX h11

lemma x11_gt_X_of_x_gt (X : ℝ) (hX : 1 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    (x : ℝ) ^ 11 > X := by
  have hX_pos : 0 < X := by linarith
  have hX_nonneg : 0 ≤ X := le_of_lt hX_pos
  have h1 : (X ^ ((1 : ℝ) / 11)) ^ (11 : ℕ) = X := rpow_one_div_11_pow_11 X hX_nonneg
  have hXr_nonneg : 0 ≤ X ^ ((1 : ℝ) / 11) := le_of_lt (Real.rpow_pos_of_pos hX_pos _)
  have h2 : (X ^ ((1 : ℝ) / 11)) ^ (11 : ℕ) < (x : ℝ) ^ (11 : ℕ) :=
    rpow_11_strict_mono hXr_nonneg hx
  linarith

lemma E4_x11_pow_gt_X (X : ℝ) (hX : 4 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    (↑↑x : ℝ) ^ 11 > X := x11_gt_X_of_x_gt X (by linarith) x hx

lemma sq_lt_sq_of_pos_lt (a b : ℝ) (ha : 0 < a) (hab : a < b) : a ^ 2 < b ^ 2 :=
  (sq_lt_sq₀ (le_of_lt ha) (le_of_lt (lt_trans ha hab))).mpr hab

lemma x22_gt_X2_of_x11_gt (X : ℝ) (hX : 0 < X) (x : ℕ+)
    (h : (x : ℝ) ^ 11 > X) :
    (x : ℝ) ^ 22 > X ^ 2 := by
  rw [show (x : ℝ) ^ 22 = ((x : ℝ) ^ 11) ^ 2 by ring]
  exact sq_lt_sq_of_pos_lt X ((x : ℝ) ^ 11) hX h

lemma x22_gt_X_sq (X : ℝ) (hX : 4 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    (↑↑x : ℝ) ^ 22 > X ^ 2 := by
  have h11 := E4_x11_pow_gt_X X hX x hx
  exact x22_gt_X2_of_x11_gt X (by linarith) x h11

lemma x22_gt_four_mul_X (X : ℝ) (hX : 4 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    (↑↑x : ℝ) ^ 22 > 4 * X :=
  lt_trans (by nlinarith [sq_nonneg (X - 4), sq_nonneg (X - 2)]) (x22_gt_X_sq X hX x hx)

lemma five_x22_sub_4X_pos (X : ℝ) (hX : 4 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    5 * (↑↑x : ℝ) ^ 22 - 4 * X > 0 := by
  have h1 := x22_gt_four_mul_X X hX x hx
  linarith

lemma sqrt_sub_eq_div (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (_hab : b < a) :
    Real.sqrt a - Real.sqrt b = (a - b) / (Real.sqrt a + Real.sqrt b) := by
  have h1 : 0 < Real.sqrt a + Real.sqrt b := by
    linarith [Real.sqrt_pos.mpr ha, Real.sqrt_nonneg b]
  have h2 : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
    rw [show (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) =
        (Real.sqrt a) ^ 2 - (Real.sqrt b) ^ 2 from by ring,
      Real.sq_sqrt ha.le, Real.sq_sqrt hb]
  field_simp [h1.ne'] at h2 ⊢
  nlinarith

lemma five_x22_sub_4X_ge_four_x22 (X : ℝ) (hX : 4 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    5 * (↑↑x : ℝ) ^ 22 - 4 * X > 4 * (↑↑x : ℝ) ^ 22 := by
  have h := x22_gt_four_mul_X X hX x hx
  linarith

lemma sqrt_five_x22_sub_gt_two_x11 (X : ℝ) (hX : 4 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    Real.sqrt (5 * (↑↑x : ℝ) ^ 22 - 4 * X) > 2 * (↑↑x : ℝ) ^ 11 := by
  have h_ge := five_x22_sub_4X_ge_four_x22 X hX x hx
  have hx_pos : (0 : ℝ) < (↑↑x : ℝ) := Nat.cast_pos.mpr x.pos
  have h2x11_nonneg : (0 : ℝ) ≤ 2 * (↑↑x : ℝ) ^ 11 := by positivity
  rw [show (4 : ℝ) * (↑↑x : ℝ) ^ 22 = (2 * (↑↑x : ℝ) ^ 11) ^ 2 from by ring] at h_ge
  rw [gt_iff_lt, ← Real.sqrt_sq h2x11_nonneg]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) h_ge

lemma sqrt_five_x22_add_gt_two_x11 (X : ℝ) (hX : 4 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    Real.sqrt (5 * (↑↑x : ℝ) ^ 22 + 4 * X) > 2 * (↑↑x : ℝ) ^ 11 := by
  have hsub_pos := five_x22_sub_4X_pos X hX x hx
  have hsub_gt := sqrt_five_x22_sub_gt_two_x11 X hX x hx
  have h_lt : 5 * (↑↑x : ℝ) ^ 22 - 4 * X < 5 * (↑↑x : ℝ) ^ 22 + 4 * X := by linarith
  have h_sqrt_lt := Real.sqrt_lt_sqrt (le_of_lt hsub_pos) h_lt
  linarith

lemma denom_gt_four_x11 (X : ℝ) (hX : 4 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    Real.sqrt (5 * (↑↑x : ℝ) ^ 22 + 4 * X) + Real.sqrt (5 * (↑↑x : ℝ) ^ 22 - 4 * X) >
    4 * (↑↑x : ℝ) ^ 11 := by
  have h1 := sqrt_five_x22_add_gt_two_x11 X hX x hx
  have h2 := sqrt_five_x22_sub_gt_two_x11 X hX x hx
  linarith

lemma E4_interval_length_lt_two (X : ℝ) (hX : 4 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    Real.sqrt (5 * (↑↑x : ℝ) ^ 22 + 4 * X) - Real.sqrt (5 * (↑↑x : ℝ) ^ 22 - 4 * X) < 2 := by
  set a := 5 * (↑↑x : ℝ) ^ 22 + 4 * X with ha_def
  set b := 5 * (↑↑x : ℝ) ^ 22 - 4 * X with hb_def
  have hb_pos : 0 < b := five_x22_sub_4X_pos X hX x hx
  have ha_pos : 0 < a := by linarith
  have hba : b < a := by simp [ha_def, hb_def]; linarith
  rw [sqrt_sub_eq_div a b ha_pos (le_of_lt hb_pos) hba]
  rw [show a - b = 8 * X by simp [ha_def, hb_def]; ring]
  have hdenom_pos : Real.sqrt a + Real.sqrt b > 0 := by
    have := Real.sqrt_pos_of_pos ha_pos
    have := Real.sqrt_nonneg b
    linarith
  have hdenom_bound : Real.sqrt a + Real.sqrt b > 4 * (↑↑x : ℝ) ^ 11 := denom_gt_four_x11 X hX x hx
  have hx11_gt := E4_x11_pow_gt_X X hX x hx
  rw [div_lt_iff₀ hdenom_pos]
  calc 8 * X < 8 * ((↑↑x : ℝ) ^ 11) := by linarith
    _ = 2 * (4 * (↑↑x : ℝ) ^ 11) := by ring
    _ < 2 * (Real.sqrt a + Real.sqrt b) := by
        apply mul_lt_mul_of_pos_left hdenom_bound (by norm_num : (0 : ℝ) < 2)

lemma pos_int_subset_Icc (a b : ℝ) :
    {u : ℤ | 0 < u ∧ a ≤ (↑u : ℝ) ∧ (↑u : ℝ) ≤ b} ⊆ Set.Icc ⌈a⌉ ⌊b⌋ := by
  intro u ⟨_, ha, hb⟩
  exact ⟨Int.ceil_le.mpr ha, Int.le_floor.mpr hb⟩

lemma pos_int_in_interval_finite (a b : ℝ) :
    {u : ℤ | 0 < u ∧ a ≤ (↑u : ℝ) ∧ (↑u : ℝ) ≤ b}.Finite :=
  Set.Finite.subset (Set.finite_Icc ⌈a⌉ ⌊b⌋) (pos_int_subset_Icc a b)

lemma no_three_pos_ints_in_short_interval (a b : ℝ) (hlen : b - a < 2)
    (u₁ u₂ u₃ : ℤ)
    (_h1pos : 0 < u₁) (_h2pos : 0 < u₂) (_h3pos : 0 < u₃)
    (h1a : a ≤ ↑u₁) (_h1b : (↑u₁ : ℝ) ≤ b)
    (_h2a : a ≤ ↑u₂) (_h2b : (↑u₂ : ℝ) ≤ b)
    (_h3a : a ≤ ↑u₃) (h3b : (↑u₃ : ℝ) ≤ b)
    (h12 : u₁ < u₂) (h23 : u₂ < u₃) : False := by
  have hreal : (↑(u₃ - u₁) : ℝ) ≤ b - a := by push_cast; linarith
  have h2le : (2 : ℝ) ≤ ↑(u₃ - u₁) := by
    have : u₃ - u₁ ≥ 2 := by omega
    exact_mod_cast this
  linarith

lemma exists_three_mem_of_three_le_ncard {S : Set ℤ} (_hfin : S.Finite)
    (hcard : 3 ≤ S.ncard) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨T, hTS, hTcard⟩ := Set.exists_subset_card_eq hcard
  rw [Set.ncard_eq_three] at hTcard
  obtain ⟨x, y, z, hxy, hxz, hyz, hTeq⟩ := hTcard
  exact ⟨x, hTS (hTeq ▸ Set.mem_insert x _),
         y, hTS (hTeq ▸ Set.mem_insert_of_mem _ (Set.mem_insert y _)),
         z, hTS (hTeq ▸ Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton z))),
         hxy, hxz, hyz⟩

lemma exists_strict_order_of_three_distinct_case_lt
    (a b c : ℤ) (hab : a < b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ u₁ u₂ u₃, ({u₁, u₂, u₃} : Set ℤ) ⊆ {a, b, c} ∧ u₁ < u₂ ∧ u₂ < u₃ := by
  rcases lt_or_gt_of_ne hac.symm with hca | hac'
  · refine ⟨c, a, b, ?_, hca, hab⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  · rcases lt_or_gt_of_ne hbc.symm with hcb | hbc'
    · refine ⟨a, c, b, ?_, hac', hcb⟩
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
    · refine ⟨a, b, c, ?_, hab, hbc'⟩
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto

lemma exists_strict_order_of_three_distinct (a b c : ℤ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ u₁ u₂ u₃, ({u₁, u₂, u₃} : Set ℤ) ⊆ {a, b, c} ∧ u₁ < u₂ ∧ u₂ < u₃ := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact exists_strict_order_of_three_distinct_case_lt a b c h hac hbc
  · obtain ⟨u₁, u₂, u₃, hsub, h1, h2⟩ :=
      exists_strict_order_of_three_distinct_case_lt b a c h hbc hac
    have hsub' : ({b, a, c} : Set ℤ) ⊆ {a, b, c} := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    exact ⟨u₁, u₂, u₃, hsub.trans hsub', h1, h2⟩

lemma ncard_le_two_of_no_three_ordered {S : Set ℤ} (hfin : S.Finite)
    (h : ∀ u₁ ∈ S, ∀ u₂ ∈ S, ∀ u₃ ∈ S, u₁ < u₂ → u₂ < u₃ → False) :
    S.ncard ≤ 2 := by
  by_contra hle
  push Not at hle
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := exists_three_mem_of_three_le_ncard hfin hle
  obtain ⟨u₁, u₂, u₃, hsub, h12, h23⟩ := exists_strict_order_of_three_distinct a b c hab hac hbc
  have hu₁ : u₁ ∈ S := by
    have : u₁ ∈ ({u₁, u₂, u₃} : Set ℤ) := Set.mem_insert u₁ _
    have := hsub this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with rfl | rfl | rfl <;> assumption
  have hu₂ : u₂ ∈ S := by
    have : u₂ ∈ ({u₁, u₂, u₃} : Set ℤ) := by simp
    have := hsub this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with rfl | rfl | rfl <;> assumption
  have hu₃ : u₃ ∈ S := by
    have : u₃ ∈ ({u₁, u₂, u₃} : Set ℤ) := by simp
    have := hsub this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with rfl | rfl | rfl <;> assumption
  exact h u₁ hu₁ u₂ hu₂ u₃ hu₃ h12 h23

lemma ncard_pos_int_in_interval_lt_two (a b : ℝ) (hlen : b - a < 2) :
    {u : ℤ | 0 < u ∧ a ≤ (↑u : ℝ) ∧ (↑u : ℝ) ≤ b}.ncard ≤ 2 := by
  apply ncard_le_two_of_no_three_ordered (pos_int_in_interval_finite a b)
  intro u₁ hu₁ u₂ hu₂ u₃ hu₃ h12 h23
  exact no_three_pos_ints_in_short_interval a b hlen u₁ u₂ u₃
    hu₁.1 hu₂.1 hu₃.1 hu₁.2.1 hu₁.2.2 hu₂.2.1 hu₂.2.2 hu₃.2.1 hu₃.2.2 h12 h23

lemma E4_pos_fiber_subset_sqrt (X : ℝ) (_hX : 4 < X) (x : ℕ+)
    (_hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    {u : ℤ | 0 < u ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
              (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X} ⊆
    {u : ℤ | 0 < u ∧ Real.sqrt (5 * (↑↑x : ℝ) ^ 22 - 4 * X) ≤ (↑u : ℝ) ∧
              (↑u : ℝ) ≤ Real.sqrt (5 * (↑↑x : ℝ) ^ 22 + 4 * X)} := by
  intro u hu
  refine ⟨hu.1, ?_, ?_⟩
  · exact (Real.sqrt_le_left (le_of_lt (Int.cast_pos.mpr hu.1))).mpr hu.2.1
  · exact Real.le_sqrt_of_sq_le hu.2.2

lemma E4_pos_sqrt_fiber_finite (X : ℝ) (_hX : 4 < X) (x : ℕ+)
    (_hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    {u : ℤ | 0 < u ∧ Real.sqrt (5 * (↑↑x : ℝ) ^ 22 - 4 * X) ≤ (↑u : ℝ) ∧
              (↑u : ℝ) ≤ Real.sqrt (5 * (↑↑x : ℝ) ^ 22 + 4 * X)}.Finite :=
    pos_int_in_interval_finite _ _

lemma E4_pos_fiber_ncard_via_sqrt (X : ℝ) (hX : 4 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    {u : ℤ | 0 < u ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
              (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X}.ncard ≤
    {u : ℤ | 0 < u ∧ Real.sqrt (5 * (↑↑x : ℝ) ^ 22 - 4 * X) ≤ (↑u : ℝ) ∧
              (↑u : ℝ) ≤ Real.sqrt (5 * (↑↑x : ℝ) ^ 22 + 4 * X)}.ncard :=
    Set.ncard_le_ncard (E4_pos_fiber_subset_sqrt X hX x hx) (E4_pos_sqrt_fiber_finite X hX x hx)

lemma E4_pos_fiber_ncard_le_two (X : ℝ) (hX : 4 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    {u : ℤ | 0 < u ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
              (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X}.ncard ≤ 2 := by
  have hlen := E4_interval_length_lt_two X hX x hx
  have hvia := E4_pos_fiber_ncard_via_sqrt X hX x hx
  calc {u : ℤ | 0 < u ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
              (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X}.ncard
      ≤ {u : ℤ | 0 < u ∧ Real.sqrt (5 * (↑↑x : ℝ) ^ 22 - 4 * X) ≤ (↑u : ℝ) ∧
              (↑u : ℝ) ≤ Real.sqrt (5 * (↑↑x : ℝ) ^ 22 + 4 * X)}.ncard := hvia
      _ ≤ 2 := ncard_pos_int_in_interval_lt_two _ _ hlen

private def pos_fiber (X : ℝ) (x : ℕ+) : Set ℤ :=
  {u : ℤ | 0 < u ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
            (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X}

private def neg_fiber (X : ℝ) (x : ℕ+) : Set ℤ :=
  {u : ℤ | u < 0 ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
            (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X}

lemma neg_maps_to_pos (X : ℝ) (x : ℕ+) :
    ∀ u ∈ neg_fiber X x, -u ∈ pos_fiber X x := by
  intro u hu
  simp only [neg_fiber, Set.mem_setOf_eq] at hu
  simp only [pos_fiber, Set.mem_setOf_eq]
  obtain ⟨hu_neg, hu_lb, hu_ub⟩ := hu
  refine ⟨neg_pos.mpr hu_neg, ?_, ?_⟩
  · rwa [Int.cast_neg, neg_sq]
  · rwa [Int.cast_neg, neg_sq]

private lemma int_abs_le_ceil_sqrt (y : ℤ) (M : ℝ) (_hM : 0 ≤ M)
    (hy : (y : ℝ) ^ 2 ≤ M) :
    |y| ≤ ⌈Real.sqrt M⌉ := by
  rw [← @Int.cast_le ℝ]
  calc (↑|y| : ℝ) = |(↑y : ℝ)| := by rw [Int.cast_abs]
    _ ≤ Real.sqrt M := Real.abs_le_sqrt hy
    _ ≤ ↑⌈Real.sqrt M⌉ := Int.le_ceil _

lemma pos_fiber_subset_Icc (X : ℝ) (x : ℕ+) :
    pos_fiber X x ⊆ Set.Icc 1 ⌈Real.sqrt (5 * (↑↑x : ℝ) ^ 22 + 4 * X)⌉ := by
  intro u hu
  simp only [pos_fiber, Set.mem_setOf_eq] at hu
  obtain ⟨hu_pos, _, hu_sq_le⟩ := hu
  constructor
  · omega
  · have hM : (0 : ℝ) ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X := by
      calc (0 : ℝ) ≤ (↑u : ℝ) ^ 2 := sq_nonneg _
        _ ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X := hu_sq_le
    have h_abs : |u| ≤ ⌈Real.sqrt (5 * (↑↑x : ℝ) ^ 22 + 4 * X)⌉ :=
      int_abs_le_ceil_sqrt u _ hM hu_sq_le
    rwa [abs_of_pos hu_pos] at h_abs

lemma pos_fiber_finite (X : ℝ) (x : ℕ+) :
    (pos_fiber X x).Finite := (Set.finite_Icc 1 ⌈Real.sqrt (5 * (↑↑x : ℝ) ^ 22 + 4 * X)⌉).subset
    (pos_fiber_subset_Icc X x)

lemma E4_neg_fiber_ncard_le_pos_fiber (X : ℝ) (x : ℕ+) :
    {u : ℤ | u < 0 ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
              (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X}.ncard ≤
    {u : ℤ | 0 < u ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
              (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X}.ncard := by
  have h1 := neg_maps_to_pos X x
  have h2 := pos_fiber_finite X x
  change (neg_fiber X x).ncard ≤ (pos_fiber X x).ncard
  exact Set.ncard_le_ncard_of_injOn Neg.neg
    (fun u hu => h1 u hu)
    (neg_injective.injOn)
    h2

lemma E4_neg_fiber_ncard_le_two (X : ℝ) (hX : 4 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    {u : ℤ | u < 0 ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
              (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X}.ncard ≤ 2 := by
  calc {u : ℤ | u < 0 ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
              (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X}.ncard
      ≤ {u : ℤ | 0 < u ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
              (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X}.ncard :=
        E4_neg_fiber_ncard_le_pos_fiber X x
    _ ≤ 2 := E4_pos_fiber_ncard_le_two X hX x hx

lemma u_sq_le_of_abs_le (x : ℕ+) (u : ℤ) (X : ℝ)
    (habs_le : (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) ≤ 4 * X) :
    (u : ℝ) ^ 2 ≤ 5 * (x : ℝ) ^ 22 + 4 * X := by
  have h₁ : ((u : ℝ) ^ 2 - 5 * (x : ℝ) ^ 22 : ℝ) ≤ 4 * X := by
    have h₂ : ((u : ℝ) ^ 2 - 5 * (x : ℝ) ^ 22 : ℝ) = (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 : ℝ) := by
      norm_cast
    rw [h₂]
    have h₄ : ((u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 : ℝ) : ℝ) ≤ 4 * X := by
      have h₅ : ((u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 : ℝ) : ℝ)
          ≤ |(u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 : ℝ)| := le_abs_self _
      linarith
    exact h₄
  linarith

lemma u_sq_ge_of_abs_le (x : ℕ+) (u : ℤ) (X : ℝ)
    (habs_le : (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) ≤ 4 * X) :
    5 * (↑↑x : ℝ) ^ 22 - 4 * X ≤ (↑u : ℝ) ^ 2 := by
  have h₁ : -(4 * X) ≤ ((u : ℝ) ^ 2 - 5 * (x : ℝ) ^ 22 : ℝ) := by
    have h₂ : ((u : ℝ) ^ 2 - 5 * (x : ℝ) ^ 22 : ℝ) = (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 : ℝ) := by
      norm_cast
    rw [h₂]
    have h₃ : -(4 * X) ≤ (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 : ℝ) := by
      have h₄ : -|(u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 : ℝ)|
          ≤ (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 : ℝ) := neg_abs_le _
      linarith
    exact h₃
  linarith

lemma u_sq_in_interval (X : ℝ) (x : ℕ+) (u : ℤ)
    (h : (|u ^ 2 - 5 * (↑x : ℤ) ^ 22| : ℝ) ≤ 4 * X) :
    5 * (↑↑x : ℝ) ^ 22 - 4 * X ≤ (↑u : ℝ) ^ 2 ∧
    (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X :=
  ⟨u_sq_ge_of_abs_le x u X h, u_sq_le_of_abs_le x u X h⟩

lemma u_ne_zero_of_fiber (X : ℝ) (_hX : 4 < X) (_x : ℕ+)
    (_hx : (_x : ℝ) > X ^ ((1 : ℝ) / 11)) (u : ℤ)
    (hu_lb : 5 * (↑↑_x : ℝ) ^ 22 - 4 * X ≤ (↑u : ℝ) ^ 2)
    (h5pos : 5 * (↑↑_x : ℝ) ^ 22 - 4 * X > 0) :
    u ≠ 0 := by
  by_contra h_u_zero
  have h_u_sq_zero : (↑u : ℝ) ^ 2 = 0 := by
    norm_cast
    simp [h_u_zero]
  linarith

lemma E4_fiber_subset_pos_neg (X : ℝ) (hX : 4 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    {u : ℤ | (x, u) ∈ E4Set X} ⊆
    {u : ℤ | 0 < u ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
              (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X} ∪
    {u : ℤ | u < 0 ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
              (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X} := by
  intro u hu
  have hbounds := E4_set_D_bounds X (x, u) hu
  have h5pos := five_x22_sub_4X_pos X hX x hx
  have hinterval := u_sq_in_interval X x u hbounds.2
  have hne : u ≠ 0 := u_ne_zero_of_fiber X hX x hx u hinterval.1 h5pos
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · right
    exact ⟨hneg, hinterval.1, hinterval.2⟩
  · left
    exact ⟨hpos, hinterval.1, hinterval.2⟩

lemma int_mem_Icc_ceil_sqrt_of_sq_le (y : ℤ) (M : ℝ) (hM : 0 ≤ M)
    (hy : (y : ℝ) ^ 2 ≤ M) :
    y ∈ Set.Icc (-⌈Real.sqrt M⌉) (⌈Real.sqrt M⌉) := by
  rw [Set.mem_Icc]
  constructor
  · linarith [neg_abs_le y, int_abs_le_ceil_sqrt y M hM hy]
  · exact le_trans (le_abs_self y) (int_abs_le_ceil_sqrt y M hM hy)

lemma E4_pos_neg_fiber_finite (X : ℝ) (hX : 4 < X) (x : ℕ+)
    (_hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    ({u : ℤ | 0 < u ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
              (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X} ∪
    {u : ℤ | u < 0 ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
              (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X}).Finite := by
  set M : ℝ := 5 * (↑↑x : ℝ) ^ 22 + 4 * X with hM
  have hM0 : 0 ≤ M := by positivity
  refine Set.Finite.subset (Set.finite_Icc (-⌈Real.sqrt M⌉) ⌈Real.sqrt M⌉) ?_
  rintro u (h | h) <;> exact int_mem_Icc_ceil_sqrt_of_sq_le u M hM0 h.2.2

lemma E4_fiber_ncard_le_four (X : ℝ) (hX : 4 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    {u : ℤ | (x, u) ∈ E4Set X}.ncard ≤ 4 := by
  have hsub := E4_fiber_subset_pos_neg X hX x hx
  have hfin := E4_pos_neg_fiber_finite X hX x hx
  have hle := Set.ncard_le_ncard hsub hfin
  have hunion := Set.ncard_union_le
    {u : ℤ | 0 < u ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
              (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X}
    {u : ℤ | u < 0 ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
              (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X}
  have hpos := E4_pos_fiber_ncard_le_two X hX x hx
  have hneg := E4_neg_fiber_ncard_le_two X hX x hx
  omega

lemma E4_fiber_empty_of_le (X : ℝ) (x : ℕ+)
    (hx : ¬((x : ℝ) > X ^ ((1 : ℝ) / 11))) :
    {u : ℤ | (x, u) ∈ E4Set X} = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro u hu
  exact hx hu.1

lemma denom_pos_E4 (ε : ℝ) (hε : 0 < ε) (hε_bound : ε ≤ 1 / 24) :
    0 < 10 - 12 * ε := by
  linarith

private lemma cleared_ineq_E4 (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε)
    (hε_η : ε ≤ η) (hε_bound : ε ≤ 1 / 24) :
    ε * (17 / 5 + 12 * η) ≤ 10 * η := by
  by_cases h : η ≤ 11 / 20
  · nlinarith [sq_nonneg (η - 11 / 20)]
  · nlinarith

lemma exponent_bound_E4 (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε)
    (hε_η : ε ≤ η) (hε_bound : ε ≤ 1 / 24) :
    (2 + ε) / (10 - 12 * ε) ≤ 1 / 5 + η := by
  have h_denom := denom_pos_E4 ε hε hε_bound
  rw [div_le_iff₀ h_denom]
  have h_cleared := cleared_ineq_E4 η ε hη hε hε_η hε_bound
  nlinarith

lemma five_x22_gt_four_X_of_x_gt (X : ℝ) (hX : 1 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    5 * (x : ℝ) ^ 22 > 4 * X := by
  have h22 := x22_gt_X2_of_x11_gt X (by linarith) x (x11_gt_X_of_x_gt X hX x hx)
  nlinarith [sq_nonneg (X - 1)]

lemma product_upper_bound (x : ℕ+) (X : ℝ) (hX : 1 < X) (Y : ℝ) (_hY : 0 ≤ Y)
    (h_Y : Y ≤ Real.sqrt 2 * (x : ℝ) ^ ((11 : ℝ) / 2)) :
    (x : ℝ) * Y * X ≤ Real.sqrt 2 * (x : ℝ) ^ ((13 : ℝ) / 2) * X := by
  have hx_pos : (0 : ℝ) < (x : ℝ) := by positivity
  have hx_mul : (x : ℝ) * (x : ℝ) ^ ((11 : ℝ) / 2) = (x : ℝ) ^ ((13 : ℝ) / 2) := by
    have h₁ : (x : ℝ) ^ (1 : ℝ) * (x : ℝ) ^ ((11 : ℝ) / 2) = (x : ℝ) ^ ((13 : ℝ) / 2) := by
      rw [← Real.rpow_add hx_pos, show (1 : ℝ) + 11 / 2 = 13 / 2 from by norm_num]
    rwa [Real.rpow_one] at h₁
  have hX_nn : (0 : ℝ) ≤ X := by linarith
  have hx_nn : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hx_pos
  calc (x : ℝ) * Y * X
      ≤ (x : ℝ) * (Real.sqrt 2 * (x : ℝ) ^ ((11 : ℝ) / 2)) * X := by
        have : (x : ℝ) * Y ≤ (x : ℝ) * (Real.sqrt 2 * (x : ℝ) ^ ((11 : ℝ) / 2)) := by
          exact mul_le_mul_of_nonneg_left h_Y hx_nn
        nlinarith
    _ = Real.sqrt 2 * ((x : ℝ) * (x : ℝ) ^ ((11 : ℝ) / 2)) * X := by ring
    _ = Real.sqrt 2 * (x : ℝ) ^ ((13 : ℝ) / 2) * X := by rw [hx_mul]

lemma rpow_triple_mul_distrib (a b c e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a * b * c) ^ e = a ^ e * b ^ e * c ^ e := by
  rw [Real.mul_rpow (mul_nonneg ha hb) hc, Real.mul_rpow ha hb]

lemma pnat_rpow_mul (x : ℕ+) (p q : ℝ) :
    (x : ℝ) ^ (p * q) = ((x : ℝ) ^ p) ^ q := Real.rpow_mul (Nat.cast_nonneg' x) p q

lemma rpow_product_expand (x : ℕ+) (X : ℝ) (hX : 1 < X) (ε : ℝ) (_hε : 0 < ε) :
    (Real.sqrt 2 * (x : ℝ) ^ ((13 : ℝ) / 2) * X) ^ (1 + ε) =
    Real.sqrt 2 ^ (1 + ε) * (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) * X ^ (1 + ε) := by
  rw [rpow_triple_mul_distrib _ _ _ _ (Real.sqrt_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg' _) _) (le_of_lt (lt_trans one_pos hX))]
  rw [pnat_rpow_mul x (13 / 2) (1 + ε)]

lemma combine_X_powers (K : ℝ) (x : ℕ+) (X : ℝ) (hX : 1 < X) (ε : ℝ) (_hε : 0 < ε) :
    K * X * (Real.sqrt 2 ^ (1 + ε) * (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) * X ^ (1 + ε)) =
    K * Real.sqrt 2 ^ (1 + ε) * (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) * X ^ (2 + ε) := by
  calc
    K * X * (Real.sqrt 2 ^ (1 + ε) * (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) * X ^ (1 + ε))
      = K * Real.sqrt 2 ^ (1 + ε) * (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) * (X * X ^ (1 + ε)) := by
      ring_nf
    _ = K * Real.sqrt 2 ^ (1 + ε) * (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) * (X ^ (2 + ε)) := by
      have h₄ : (X : ℝ) * X ^ (1 + ε) = X ^ (2 + ε) := by
        calc
          (X : ℝ) * X ^ (1 + ε) = X ^ (1 : ℝ) * X ^ (1 + ε) := by
            simp
          _ = X ^ ((1 : ℝ) + (1 + ε)) := by
            rw [← Real.rpow_add (by positivity : (0 : ℝ) < X)]
          _ = X ^ (2 + ε) := by
            ring_nf
      rw [h₄]

theorem substitute_Y_bound (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε)
    (x : ℕ+) (X : ℝ) (hX : 1 < X) (Y : ℝ) (hY : 0 ≤ Y)
    (h_x11 : (x : ℝ) ^ 11 ≤ K * X * ((x : ℝ) * Y * X) ^ (1 + ε))
    (h_Y : Y ≤ Real.sqrt 2 * (x : ℝ) ^ ((11 : ℝ) / 2)) :
    (x : ℝ) ^ 11 ≤ K * Real.sqrt 2 ^ (1 + ε) *
      (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) * X ^ (2 + ε) := by
  have h_prod := product_upper_bound x X hX Y hY h_Y
  have hxYX_nn : 0 ≤ (x : ℝ) * Y * X := by positivity
  have h_rpow := Real.rpow_le_rpow hxYX_nn h_prod (by linarith : 0 ≤ 1 + ε)
  have h_expand := rpow_product_expand x X hX ε hε
  rw [h_expand] at h_rpow
  have h_chain : K * X * ((x : ℝ) * Y * X) ^ (1 + ε) ≤
      K * X * (Real.sqrt 2 ^ (1 + ε) * (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) * X ^ (1 + ε)) := by
    apply mul_le_mul_of_nonneg_left h_rpow
    exact mul_nonneg (le_of_lt hK) (le_of_lt (by linarith : 0 < X))
  rw [combine_X_powers K x X hX ε hε] at h_chain
  exact le_trans h_x11 h_chain

lemma cancel_common_rpow_factor (K : ℝ) (_hK : 0 < K)
    (ε : ℝ) (_hε : 0 < ε) (_hε' : ε < 9 / 13)
    (x : ℕ+) (X : ℝ) (_hX : 1 < X)
    (h : (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) * (x : ℝ) ^ ((9 - 13 * ε) / 2) ≤
      (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) * (K * Real.sqrt 2 ^ (1 + ε) * X ^ (2 + ε))) :
    (x : ℝ) ^ ((9 - 13 * ε) / 2) ≤
      K * Real.sqrt 2 ^ (1 + ε) * X ^ (2 + ε) := by
  have h₂ : 0 < (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) := by positivity
  exact le_of_mul_le_mul_left h h₂

lemma exponent_sum_eq_11 (ε : ℝ) :
    (13 / 2 : ℝ) * (1 + ε) + (9 - 13 * ε) / 2 = 11 := by grind

lemma lhs_eq_x_pow_11 (ε : ℝ) (_hε : 0 < ε) (_hε' : ε < 9 / 13)
    (x : ℕ+) (hx : (0 : ℝ) < (x : ℝ)) :
    (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) * (x : ℝ) ^ ((9 - 13 * ε) / 2) =
    (x : ℝ) ^ (11 : ℝ) := by
  rw [← Real.rpow_add hx]
  congr 1
  linarith [exponent_sum_eq_11 ε]

lemma nat_pow_eq_rpow (x : ℕ+) :
    (x : ℝ) ^ (11 : ℕ) = (x : ℝ) ^ (11 : ℝ) := (Real.rpow_natCast (x : ℝ) 11).symm

lemma rhs_rearrange (K : ℝ) (ε : ℝ) (x : ℕ+) (X : ℝ) :
    K * Real.sqrt 2 ^ (1 + ε) *
      (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) * X ^ (2 + ε) =
    (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) * (K * Real.sqrt 2 ^ (1 + ε) * X ^ (2 + ε)) := by
  ring

lemma rewrite_hypothesis (K : ℝ) (_hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 9 / 13)
    (x : ℕ+) (X : ℝ) (_hX : 1 < X)
    (h : (x : ℝ) ^ 11 ≤ K * Real.sqrt 2 ^ (1 + ε) *
      (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) * X ^ (2 + ε)) :
    (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) * (x : ℝ) ^ ((9 - 13 * ε) / 2) ≤
      (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) * (K * Real.sqrt 2 ^ (1 + ε) * X ^ (2 + ε)) := by
  have hx : (0 : ℝ) < (x : ℝ) := Nat.cast_pos.mpr x.pos
  rw [lhs_eq_x_pow_11 ε hε hε' x hx, ← nat_pow_eq_rpow x]
  rw [← rhs_rearrange K ε x X]
  exact h

theorem isolate_x_power (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 9 / 13)
    (x : ℕ+) (X : ℝ) (hX : 1 < X)
    (h : (x : ℝ) ^ 11 ≤ K * Real.sqrt 2 ^ (1 + ε) *
      (x : ℝ) ^ ((13 / 2 : ℝ) * (1 + ε)) * X ^ (2 + ε)) :
    (x : ℝ) ^ ((9 - 13 * ε) / 2) ≤
      K * Real.sqrt 2 ^ (1 + ε) * X ^ (2 + ε) :=
  cancel_common_rpow_factor K hK ε hε hε' x X hX
    (rewrite_hypothesis K hK ε hε hε' x X hX h)

lemma denom_pos_general (ε : ℝ) (_hε : 0 < ε) (hε' : ε < 9 / 13) :
    0 < 9 - 13 * ε := by grind

lemma exponent_cancel (ε : ℝ) (_hε : 0 < ε) (hε' : ε < 9 / 13) :
    (9 - 13 * ε) / 2 * (2 / (9 - 13 * ε)) = 1 := by grind

lemma X_exponent_eq (ε : ℝ) (_hε : 0 < ε) (_hε' : ε < 9 / 13) :
    (2 + ε) * (2 / (9 - 13 * ε)) = (4 + 2 * ε) / (9 - 13 * ε) := by grind

lemma raise_to_reciprocal_power (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 9 / 13)
    (x : ℕ+) (X : ℝ) (hX : 1 < X)
    (h : (x : ℝ) ^ ((9 - 13 * ε) / 2) ≤
      K * Real.sqrt 2 ^ (1 + ε) * X ^ (2 + ε)) :
    (x : ℝ) ≤ (K * Real.sqrt 2 ^ (1 + ε)) ^ ((2 : ℝ) / (9 - 13 * ε)) *
      X ^ (((4 : ℝ) + 2 * ε) / (9 - 13 * ε)) := by
  have hdenom : 0 < 9 - 13 * ε := denom_pos_general ε hε hε'
  have hexp_pos : 0 < 2 / (9 - 13 * ε) := div_pos two_pos hdenom
  have hx_pos : (0 : ℝ) < (x : ℝ) := Nat.cast_pos.mpr x.pos
  have hx_nn : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hx_pos
  have hX_pos : 0 < X := lt_trans one_pos hX
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos two_pos
  have hKs_pos : 0 < K * Real.sqrt 2 ^ (1 + ε) :=
    mul_pos hK (Real.rpow_pos_of_pos hsqrt2_pos _)
  have hstep := Real.rpow_le_rpow (Real.rpow_nonneg hx_nn _) h (le_of_lt hexp_pos)
  rw [← Real.rpow_mul hx_nn] at hstep
  rw [exponent_cancel ε hε hε'] at hstep
  rw [Real.rpow_one] at hstep
  rw [Real.mul_rpow (le_of_lt hKs_pos) (le_of_lt (Real.rpow_pos_of_pos hX_pos _))] at hstep
  rw [← Real.rpow_mul (le_of_lt hX_pos)] at hstep
  rw [X_exponent_eq ε hε hε'] at hstep
  exact hstep

lemma u_ne_zero_of_E4 (X : ℝ) (hX : 1 < X)
    (p : ℕ+ × ℤ) (hp : p ∈ E4Set X) : p.2 ≠ 0 := by
  have ⟨_, hD_upper⟩ := E4_set_D_bounds X p hp
  have hx_lower := hp.1
  intro hu
  have hD_eq : (|p.2 ^ 2 - 5 * (↑p.1 : ℤ) ^ 22| : ℝ) = 5 * (↑↑p.1 : ℝ) ^ 22 := by
    rw [hu]; push_cast; simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_sub, abs_neg, abs_mul, abs_pow]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have h5 := five_x22_gt_four_X_of_x_gt X hX p.1 hx_lower
  linarith

lemma x_pow11_gt_X (x : ℕ+) (X : ℝ) (hX : 1 < X)
    (hx_lower : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    (x : ℝ) ^ 11 > X := by
  have hX0 : (0 : ℝ) ≤ X := le_of_lt (lt_trans zero_lt_one hX)
  have hrpow_nonneg : (0 : ℝ) ≤ X ^ ((1 : ℝ) / 11) := Real.rpow_nonneg hX0 _
  calc (x : ℝ) ^ 11
      > (X ^ ((1 : ℝ) / 11)) ^ 11 := pow_lt_pow_left₀ hx_lower hrpow_nonneg (by norm_num)
    _ = X := rpow_one_div_11_pow_11 X hX0

lemma x11_gt_one (x : ℕ+) (X : ℝ) (hX : 1 < X)
    (hx11_gt : (x : ℝ) ^ 11 > X) :
    (x : ℝ) ^ 11 > 1 :=
  lt_trans hX hx11_gt

lemma x22_gt_X (x : ℕ+) (X : ℝ) (hX : 1 < X)
    (hx11_gt : (x : ℝ) ^ 11 > X) :
    (x : ℝ) ^ 22 > X := by
  have h1 : (x : ℝ) ^ 11 > 1 := x11_gt_one x X hX hx11_gt
  nlinarith [sq_nonneg ((x : ℝ) ^ 11 - 1), show (x : ℝ) ^ 22 = ((x : ℝ) ^ 11) ^ 2 by ring]

lemma four_X_le_four_x22 (x : ℕ+) (X : ℝ) (hX : 1 < X)
    (hx11_gt : (x : ℝ) ^ 11 > X) :
    4 * X < 4 * (x : ℝ) ^ 22 := by
  have h := x22_gt_X x X hX hx11_gt
  linarith

lemma u_sq_lt_nine_x22 (x : ℕ+) (u : ℤ) (X : ℝ)
    (hu_sq : (u : ℝ) ^ 2 ≤ 5 * (x : ℝ) ^ 22 + 4 * X)
    (h4X : 4 * X < 4 * (x : ℝ) ^ 22) :
    (u : ℝ) ^ 2 < 9 * (x : ℝ) ^ 22 := by
  linarith

lemma natAbs_le_of_sq_lt (x : ℕ+) (u : ℤ)
    (hu_sq : (u : ℝ) ^ 2 < 9 * (x : ℝ) ^ 22) :
    (Int.natAbs u : ℝ) ≤ 3 * (x : ℝ) ^ 11 := by
  have h₁ : (u : ℝ) ^ 2 ≤ (3 * (x : ℝ) ^ 11) ^ 2 := by
    linarith
  have h₂ : (0 : ℝ) ≤ 3 * (x : ℝ) ^ 11 := by
    have h₂₂ : (0 : ℝ) < (x : ℝ) ^ 11 := by positivity
    linarith
  have h₃ : |(u : ℝ)| ≤ 3 * (x : ℝ) ^ 11 := abs_le_of_sq_le_sq h₁ h₂
  have h₄ : (Int.natAbs u : ℝ) = |(u : ℝ)| := by
    simp [Nat.cast_natAbs]
  rw [h₄]
  exact h₃

lemma u_bound_from_E4 (x : ℕ+) (u : ℤ) (X : ℝ) (hX : 1 < X)
    (hx_lower : (x : ℝ) > X ^ ((1 : ℝ) / 11))
    (habs_le : (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) ≤ 4 * X) :
    (Int.natAbs u : ℝ) ≤ 3 * (x : ℝ) ^ 11 := by
  have h1 := u_sq_le_of_abs_le x u X habs_le
  have h2 := x_pow11_gt_X x X hX hx_lower
  have h3 := four_X_le_four_x22 x X hX h2
  have h4 := u_sq_lt_nine_x22 x u X h1 h3
  exact natAbs_le_of_sq_lt x u h4

lemma radical_pow (n : ℕ) (k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    Nat.radical (n ^ k) = Nat.radical n := by
  have h₁ : (n ^ k).primeFactors = n.primeFactors := by
    rw [Nat.primeFactors_pow]; omega
  by_cases h : n = 0
  · exfalso
    linarith
  · by_cases h₂ : n ^ k = 0
    · exfalso
      simp_all [Nat.pow_eq_zero]
    · simp_all [Nat.radical]

lemma radical_prime (p : ℕ) (hp : p.Prime) : Nat.radical p = p := by
  simp [Nat.radical, hp.ne_zero, hp.primeFactors]

lemma radical_factors_le (U x D : ℕ) (hU : 0 < U) (hx : 0 < x) (hD : 0 < D) :
    Nat.radical U * Nat.radical D * (Nat.radical 5 * Nat.radical x) ≤ U * D * (5 * x) := by
  have hU' := radical_le_self U hU
  have hD' := radical_le_self D hD
  have hx' := radical_le_self x hx
  have h5 := radical_prime 5 (by decide)
  rw [h5]
  calc Nat.radical U * Nat.radical D * (5 * Nat.radical x)
      ≤ U * D * (5 * x) := by
        apply Nat.mul_le_mul
        · exact Nat.mul_le_mul hU' hD'
        · exact Nat.mul_le_mul_left 5 hx'

lemma radical_chain_bound (U x D : ℕ) (hU : 0 < U) (hx : 0 < x) (_hD : 0 < D) :
    Nat.radical (U ^ 2 * D * (5 * x ^ 22)) ≤
    Nat.radical U * Nat.radical D * (Nat.radical 5 * Nat.radical x) := by
  calc Nat.radical (U ^ 2 * D * (5 * x ^ 22))
      _ ≤ Nat.radical (U ^ 2 * D) * Nat.radical (5 * x ^ 22) :=
          radical_mul_le _ _
      _ ≤ (Nat.radical U * Nat.radical D) * (Nat.radical 5 * Nat.radical x) := by
          apply Nat.mul_le_mul
          · calc Nat.radical (U ^ 2 * D) ≤ Nat.radical (U ^ 2) * Nat.radical D :=
                  radical_mul_le _ _
              _ = Nat.radical U * Nat.radical D := by rw [radical_pow U 2 hU (by norm_num)]
          · calc Nat.radical (5 * x ^ 22) ≤ Nat.radical 5 * Nat.radical (x ^ 22) :=
                  radical_mul_le _ _
              _ = Nat.radical 5 * Nat.radical x := by rw [radical_pow x 22 hx (by norm_num)]
      _ = Nat.radical U * Nat.radical D * (Nat.radical 5 * Nat.radical x) := by ring

lemma radical_E4_bound_nat (U x D : ℕ) (hU : 0 < U) (hx : 0 < x) (hD : 0 < D) :
    Nat.radical (U ^ 2 * D * (5 * x ^ 22)) ≤ U * D * (5 * x) := by
  calc Nat.radical (U ^ 2 * D * (5 * x ^ 22))
      ≤ Nat.radical U * Nat.radical D * (Nat.radical 5 * Nat.radical x) :=
        radical_chain_bound U x D hU hx hD
    _ ≤ U * D * (5 * x) :=
        radical_factors_le U x D hU hx hD

lemma radical_E4_bound (U x D : ℕ) (hU : 0 < U) (hx : 0 < x) (hD : 0 < D) :
    (Nat.radical (U ^ 2 * D * (5 * x ^ 22)) : ℝ) ≤ (U : ℝ) * (D : ℝ) * (5 * (x : ℝ)) := by
  have h := radical_E4_bound_nat U x D hU hx hD
  exact_mod_cast h

lemma radical_E4_bound' (U x D : ℕ) (hU : 0 < U) (hx : 0 < x) (hD : 0 < D) :
    (Nat.radical (5 * x ^ 22 * D * (U ^ 2)) : ℝ) ≤ (5 * (x : ℝ)) * (D : ℝ) * (U : ℝ) := by
  rw [show 5 * x ^ 22 * D * U ^ 2 = U ^ 2 * D * (5 * x ^ 22) by ring]
  have h_nat := radical_E4_bound_nat U x D hU hx hD
  have h_rhs_eq : (↑(U * D * (5 * x)) : ℝ) = 5 * (x : ℝ) * (D : ℝ) * (U : ℝ) := by push_cast; ring
  exact_mod_cast h_rhs_eq ▸ Nat.cast_le.mpr h_nat


lemma radical_dvd_le (d n : ℕ) (hd : 0 < d) (hn : 0 < n) (hdvd : d ∣ n) :
    Nat.radical d ≤ Nat.radical n := by
  unfold Nat.radical
  simp only [Nat.pos_iff_ne_zero.mp hd, Nat.pos_iff_ne_zero.mp hn, ↓reduceIte]
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · exact Nat.primeFactors_mono hdvd (Nat.pos_iff_ne_zero.mp hn)
  · intro p hp _
    exact Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hp)

lemma coprime_of_div_gcd (a b : ℕ) (h : 0 < Nat.gcd a b) :
    Nat.Coprime (a / Nat.gcd a b) (b / Nat.gcd a b) := Nat.coprime_div_gcd_div_gcd h

lemma gcd_reduction_coprime (a b : ℕ) (ha : 0 < a) :
    Nat.Coprime (a / Nat.gcd a b) (b / Nat.gcd a b) :=
  coprime_of_div_gcd a b (Nat.gcd_pos_of_pos_left b ha)

lemma gcd_reduction_pos_a_div (a b : ℕ) (ha : 0 < a) :
    0 < a / Nat.gcd a b :=
  Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) (Nat.gcd_pos_of_pos_left b ha)

lemma gcd_reduction_pos_b_div (a b : ℕ) (hb : 0 < b) :
    0 < b / Nat.gcd a b :=
  Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)) (Nat.gcd_pos_of_pos_right a hb)

lemma gcd_dvd_add (a b : ℕ) : Nat.gcd a b ∣ a + b :=
  dvd_add (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)

lemma gcd_pos_of_sum_pos (a b c : ℕ) (hc : 0 < c) (hsum : a + b = c) :
    0 < Nat.gcd a b := by
  rw [Nat.pos_iff_ne_zero]
  intro h
  rw [Nat.gcd_eq_zero_iff] at h
  omega

lemma gcd_reduction_pos_c_div (a b c : ℕ) (hc : 0 < c) (hsum : a + b = c) :
    0 < c / Nat.gcd a b := Nat.div_pos
    (Nat.le_of_dvd hc (hsum ▸ dvd_add (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)))
    (gcd_pos_of_sum_pos a b c hc hsum)

lemma gcd_reduction_dvd_c (a b c : ℕ) (hsum : a + b = c) :
    Nat.gcd a b ∣ c := by
  rw [← hsum]
  exact gcd_dvd_add a b

lemma gcd_reduction_mul_div_cancel (a b c : ℕ) (hsum : a + b = c) :
    Nat.gcd a b * (c / Nat.gcd a b) = c := Nat.mul_div_cancel' (gcd_reduction_dvd_c a b c hsum)

lemma abc_eq_gcd_cubed_mul (a b c : ℕ) (_ha : 0 < a) (_hb : 0 < b)
    (_hc : 0 < c) (hsum : a + b = c) :
    a * b * c = Nat.gcd a b ^ 3 *
      ((a / Nat.gcd a b) * (b / Nat.gcd a b) * (c / Nat.gcd a b)) := by
  set g := Nat.gcd a b with hg_def
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hgb : g ∣ b := Nat.gcd_dvd_right a b
  have hgc : g ∣ c := gcd_reduction_dvd_c a b c hsum
  have ha' : a / g * g = a := Nat.div_mul_cancel hga
  have hb' : b / g * g = b := Nat.div_mul_cancel hgb
  have hc' : c / g * g = c := Nat.div_mul_cancel hgc
  calc a * b * c
      = (a / g * g) * (b / g * g) * (c / g * g) := by rw [ha', hb', hc']
    _ = g ^ 3 * (a / g * (b / g) * (c / g)) := by ring

lemma gcd_reduction_product_dvd (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hsum : a + b = c) :
    (a / Nat.gcd a b) * (b / Nat.gcd a b) * (c / Nat.gcd a b) ∣ a * b * c := by
  rw [abc_eq_gcd_cubed_mul a b c ha hb hc hsum]
  exact dvd_mul_left _ _

lemma gcd_reduction (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b = c) :
    let g := Nat.gcd a b
    Nat.Coprime (a / g) (b / g) ∧
    a / g + b / g = c / g ∧
    0 < a / g ∧ 0 < b / g ∧ 0 < c / g ∧
    g ∣ c ∧
    g * (c / g) = c ∧
    (a / g) * (b / g) * (c / g) ∣ a * b * c := by
  refine ⟨gcd_reduction_coprime a b ha,
         (by rw [← hsum, Nat.add_div_of_dvd_right (Nat.gcd_dvd_left a b)]),
         gcd_reduction_pos_a_div a b ha,
         gcd_reduction_pos_b_div a b hb,
         gcd_reduction_pos_c_div a b c hc hsum,
         gcd_reduction_dvd_c a b c hsum,
         gcd_reduction_mul_div_cancel a b c hsum,
         gcd_reduction_product_dvd a b c ha hb hc hsum⟩

lemma abc_triple_to_bound (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε)
    (habc_ineq : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b = c)
    (g_bound : ℝ) (hg_bound : (Nat.gcd a b : ℝ) ≤ g_bound)
    (rad_bound : ℝ) (hrad : (Nat.radical (a * b * c) : ℝ) ≤ rad_bound)
    (hrad_nn : 0 ≤ rad_bound) :
    (c : ℝ) ≤ g_bound * K * rad_bound ^ (1 + ε) := by
  set g := Nat.gcd a b
  obtain ⟨hcop, hsum', ha', hb', hc', hg_dvd_c, hg_mul, hprod_dvd⟩ :=
    gcd_reduction a b c ha hb hc hsum
  set c' := c / g with hc'_def
  have habc' := habc_ineq (a / g) (b / g) c' ha' hb' hc' hcop hsum'
  have hrad_red : (Nat.radical ((a / g) * (b / g) * c') : ℝ) ≤ rad_bound := by
    calc (Nat.radical ((a / g) * (b / g) * c') : ℝ)
        ≤ (Nat.radical (a * b * c) : ℝ) := by
          exact_mod_cast radical_dvd_le _ _ (by positivity) (by positivity) hprod_dvd
      _ ≤ rad_bound := hrad
  have hc'_bound : (c' : ℝ) ≤ K * rad_bound ^ (1 + ε) := by
    calc (c' : ℝ)
        ≤ K * (Nat.radical ((a / g) * (b / g) * c') : ℝ) ^ (1 + ε) := habc'
      _ ≤ K * rad_bound ^ (1 + ε) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hK)
          exact Real.rpow_le_rpow (by positivity) hrad_red (by linarith)
  have hc_eq : (c : ℝ) = (g : ℝ) * (c' : ℝ) := by
    exact_mod_cast hg_mul.symm
  rw [hc_eq]
  have hg_bound_nn : 0 ≤ g_bound := le_trans (Nat.cast_nonneg g) hg_bound
  have hK_rad_nn : 0 ≤ K * rad_bound ^ (1 + ε) :=
    mul_nonneg (le_of_lt hK) (Real.rpow_nonneg hrad_nn _)
  calc (g : ℝ) * (c' : ℝ)
      ≤ g_bound * (K * rad_bound ^ (1 + ε)) :=
        mul_le_mul hg_bound hc'_bound (by positivity) hg_bound_nn
    _ = g_bound * K * rad_bound ^ (1 + ε) := by ring

lemma abc_E4_sum_eq (x : ℕ+) (u : ℤ)
    (hD_pos : u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 > 0) :
    5 * (x : ℕ) ^ 22 + (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22).natAbs = u.natAbs ^ 2 := by
  apply_fun (↑· : ℕ → ℤ)
  · push_cast
    rw [abs_of_pos hD_pos, sq_abs]
    ring
  · exact Nat.cast_injective

lemma D_pos_of_hD_pos (x : ℕ+) (u : ℤ)
    (hD_pos : u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 > 0) :
    0 < (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22).natAbs := Int.natAbs_pos.mpr (ne_of_gt hD_pos)

lemma gcd_le_D (x : ℕ+) (u : ℤ)
    (hD_pos : u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 > 0) :
    (Nat.gcd (5 * (x : ℕ) ^ 22) (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22).natAbs : ℝ) ≤
      ((u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22).natAbs : ℝ) := by
  exact_mod_cast Nat.gcd_le_right _ (D_pos_of_hD_pos x u hD_pos)

lemma int_ineq_from_sub_pos (x : ℕ+) (u : ℤ)
    (hD_pos : u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 > 0) :
    5 * (↑(x : ℕ) : ℤ) ^ 22 < u ^ 2 := by
  linarith

lemma cast_int_ineq_to_real (x : ℕ+) (u : ℤ)
    (h : 5 * (↑(x : ℕ) : ℤ) ^ 22 < u ^ 2) :
    5 * (x : ℝ) ^ 22 < (u : ℝ) ^ 2 := by
  exact_mod_cast h

lemma natAbs_sq_real (u : ℤ) :
    (u.natAbs : ℝ) ^ 2 = (u : ℝ) ^ 2 := by
  have h := Int.natAbs_sq u
  rw [show (u.natAbs : ℝ) ^ 2 = ((u.natAbs : ℤ) : ℝ) ^ 2 from by rw [Int.cast_natCast]]
  rw [show (u : ℝ) ^ 2 = ((u : ℤ) : ℝ) ^ 2 from rfl]
  exact_mod_cast h

lemma five_x22_lt_U_sq (x : ℕ+) (u : ℤ)
    (hD_pos : u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 > 0) :
    5 * (x : ℝ) ^ 22 < (u.natAbs : ℝ) ^ 2 := by
  rw [natAbs_sq_real]
  exact cast_int_ineq_to_real x u (int_ineq_from_sub_pos x u hD_pos)

lemma radical_E4_bound_reorder (U x D : ℕ) (hU : 0 < U) (hx : 0 < x) (hD : 0 < D) :
    (Nat.radical (5 * x ^ 22 * D * (U ^ 2)) : ℝ) ≤ (U : ℝ) * (D : ℝ) * (5 * (x : ℝ)) := by
  have h := radical_E4_bound' U x D hU hx hD
  linarith [mul_comm (5 * (x : ℝ)) ((D : ℝ) * (U : ℝ)), mul_comm (D : ℝ) (U : ℝ),
            mul_assoc (5 * (x : ℝ)) (D : ℝ) (U : ℝ),
            mul_assoc (U : ℝ) (D : ℝ) (5 * (x : ℝ))]

lemma abc_E4_case_pos (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε)
    (habc_ineq : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    (x : ℕ+) (u : ℤ)
    (hu_ne : u ≠ 0)
    (hD_pos : u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 > 0) :
    let D := (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22).natAbs
    5 * (x : ℝ) ^ 22 ≤
      (D : ℝ) * K * ((Int.natAbs u : ℝ) * (D : ℝ) * (5 * (x : ℝ))) ^ (1 + ε) := by
  intro D
  set Dnat := (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22).natAbs with hDnat_def
  have hsum := abc_E4_sum_eq x u hD_pos
  have h5x22 : 0 < 5 * (x : ℕ) ^ 22 := by positivity
  have hDnat_pos := D_pos_of_hD_pos x u hD_pos
  have hU_pos : 0 < u.natAbs := Int.natAbs_pos.mpr hu_ne
  have hU2_pos : 0 < u.natAbs ^ 2 := Nat.pos_of_ne_zero (by positivity)
  have hgcd := gcd_le_D x u hD_pos
  have hrad := radical_E4_bound_reorder u.natAbs (x : ℕ) Dnat hU_pos x.pos hDnat_pos
  have hrad_nn : (0 : ℝ) ≤ ↑u.natAbs * ↑Dnat * (5 * ↑↑x) := by positivity
  have hU2_bound := abc_triple_to_bound K hK ε hε habc_ineq
    (5 * (x : ℕ) ^ 22) Dnat (u.natAbs ^ 2) h5x22 hDnat_pos hU2_pos hsum
    (Dnat : ℝ) hgcd
    ((u.natAbs : ℝ) * (Dnat : ℝ) * (5 * (x : ℝ))) hrad hrad_nn
  have h5x22_lt := five_x22_lt_U_sq x u hD_pos
  rw [Nat.cast_pow] at hU2_bound
  exact le_trans (le_of_lt h5x22_lt) hU2_bound

lemma E4_neg_abc_sum_int (x : ℕ+) (u : ℤ)
    (habs_pos : 1 ≤ |u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|)
    (hD_neg : u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 ≤ 0) :
    (u.natAbs ^ 2 + (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22).natAbs : ℤ) =
    (5 * (x : ℕ) ^ 22 : ℤ) := by grind

lemma E4_neg_abc_sum (x : ℕ+) (u : ℤ)
    (habs_pos : 1 ≤ |u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|)
    (hD_neg : u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 ≤ 0) :
    u.natAbs ^ 2 + (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22).natAbs = 5 * (x : ℕ) ^ 22 := by
  exact_mod_cast E4_neg_abc_sum_int x u habs_pos hD_neg

lemma E4_neg_D_natAbs_pos (u : ℤ) (x : ℕ+)
    (habs_pos : 1 ≤ |u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|)
    (hD_neg : u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 ≤ 0) :
    0 < (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22).natAbs := by
  rw [Int.natAbs_pos]
  intro h
  linarith [abs_of_nonpos hD_neg]

lemma natAbs_pos_of_ne_zero (y : ℤ) (hy : y ≠ 0) : 0 < Int.natAbs y := by grind

lemma E4_neg_gcd_le_D (x : ℕ+) (u : ℤ)
    (habs_pos : 1 ≤ |u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|)
    (_hD_neg : u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 ≤ 0) :
    (Nat.gcd (u.natAbs ^ 2) (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22).natAbs : ℝ) ≤
      ((u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22).natAbs : ℝ) := by
  have hne : u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 ≠ 0 := by
    intro h
    simp [h] at habs_pos
  exact_mod_cast Nat.le_of_dvd (natAbs_pos_of_ne_zero _ hne) (Nat.gcd_dvd_right _ _)

lemma abc_E4_case_neg (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε)
    (habc_ineq : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    (x : ℕ+) (u : ℤ)
    (hu_ne : u ≠ 0)
    (habs_pos : 1 ≤ |u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|)
    (hD_neg : u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 ≤ 0) :
    let D := (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22).natAbs
    5 * (x : ℝ) ^ 22 ≤
      (D : ℝ) * K * ((5 * (x : ℝ)) * (D : ℝ) * (Int.natAbs u : ℝ)) ^ (1 + ε) := by
  intro D
  set Dn := (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22).natAbs with hDn_def
  set a := u.natAbs ^ 2 with ha_def
  set c := 5 * (x : ℕ) ^ 22 with hc_def
  have ha : 0 < a := by positivity
  have hDn_pos : 0 < Dn := E4_neg_D_natAbs_pos u x habs_pos hD_neg
  have hc_pos : 0 < c := by positivity
  have hsum : a + Dn = c := E4_neg_abc_sum x u habs_pos hD_neg
  have hgcd : (Nat.gcd a Dn : ℝ) ≤ (Dn : ℝ) :=
    E4_neg_gcd_le_D x u habs_pos hD_neg
  have hrad_reorder := radical_E4_bound_reorder u.natAbs (x : ℕ) Dn
    (Int.natAbs_pos.mpr hu_ne) (x.pos) hDn_pos
  have hrad : (Nat.radical (a * Dn * c) : ℝ) ≤
    (5 * ((x : ℕ) : ℝ)) * (Dn : ℝ) * ((u.natAbs : ℕ) : ℝ) := by
    rw [show a * Dn * c = 5 * (x : ℕ) ^ 22 * Dn * (u.natAbs ^ 2) from by ring]
    calc (Nat.radical (5 * (x : ℕ) ^ 22 * Dn * u.natAbs ^ 2) : ℝ)
        ≤ (u.natAbs : ℝ) * (Dn : ℝ) * (5 * ((x : ℕ) : ℝ)) := hrad_reorder
      _ = (5 * ((x : ℕ) : ℝ)) * (Dn : ℝ) * ((u.natAbs : ℕ) : ℝ) := by ring
  have hrad_nn : (0 : ℝ) ≤ (5 * ((x : ℕ) : ℝ)) * (Dn : ℝ) * ((u.natAbs : ℕ) : ℝ) := by
    positivity
  have h := abc_triple_to_bound K hK ε hε habc_ineq a Dn c ha hDn_pos hc_pos hsum
    (Dn : ℝ) hgcd ((5 * ((x : ℕ) : ℝ)) * (Dn : ℝ) * ((u.natAbs : ℕ) : ℝ)) hrad hrad_nn
  have hc_cast : (c : ℝ) = 5 * ((x : ℕ) : ℝ) ^ 22 := by
    simp only [hc_def]; push_cast; ring
  rw [hc_cast] at h
  exact h

lemma natAbs_D_eq_abs_cast (x : ℕ+) (u : ℤ) :
    ((u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22).natAbs : ℝ) =
    |((u : ℤ) : ℝ) ^ 2 - 5 * ((↑(x : ℕ) : ℤ) : ℝ) ^ 22| := by
  rw [Nat.cast_natAbs]
  push_cast
  ring_nf

lemma combine_pos_case (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε)
    (habc_ineq : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    (x : ℕ+) (u : ℤ)
    (hu_ne : u ≠ 0)
    (habs_pos : 1 ≤ |u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|)
    (hsgn : u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 > 0) :
    5 * (x : ℝ) ^ 22 ≤
      (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) *
        K * (5 * (x : ℝ) * (Int.natAbs u : ℝ) *
          (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ)) ^ (1 + ε) := by
  have _ := habs_pos
  have h1 := abc_E4_case_pos K hK ε hε habc_ineq x u hu_ne hsgn
  simp only [] at h1
  set D := (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22).natAbs with hD_def
  have hD_eq : (D : ℝ) = |((u : ℤ) : ℝ) ^ 2 - 5 * ((↑(x : ℕ) : ℤ) : ℝ) ^ 22| :=
    natAbs_D_eq_abs_cast x u
  rw [hD_eq] at h1
  convert h1 using 2
  push_cast
  ring_nf

lemma combine_neg_case (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε)
    (habc_ineq : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    (x : ℕ+) (u : ℤ)
    (hu_ne : u ≠ 0)
    (habs_pos : 1 ≤ |u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|)
    (hsgn : u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 ≤ 0) :
    5 * (x : ℝ) ^ 22 ≤
      (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) *
        K * (5 * (x : ℝ) * (Int.natAbs u : ℝ) *
          (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ)) ^ (1 + ε) := by
  have h := abc_E4_case_neg K hK ε hε habc_ineq x u hu_ne habs_pos hsgn
  simp only [] at h
  set D := (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22).natAbs with hD_def
  have hD_eq : (D : ℝ) = (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) := by
    rw [hD_def]
    simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_pow, Int.cast_mul,
      Int.cast_ofNat, Int.cast_natCast]
  rw [hD_eq] at h
  calc 5 * (x : ℝ) ^ 22 ≤ _ := h
    _ = _ := by ring_nf

lemma abc_gives_5x22_bound (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε)
    (habc_ineq : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    (x : ℕ+) (u : ℤ) (X : ℝ) (_hX : 1 < X)
    (hu_ne : u ≠ 0)
    (habs_pos : 1 ≤ |u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|)
    (_habs_le : (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) ≤ 4 * X) :
    5 * (x : ℝ) ^ 22 ≤
      (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) *
        K * (5 * (x : ℝ) * (Int.natAbs u : ℝ) *
          (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ)) ^ (1 + ε) := by
  by_cases hsgn : u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 > 0
  · exact combine_pos_case K hK ε hε habc_ineq x u hu_ne habs_pos hsgn
  · push Not at hsgn
    exact combine_neg_case K hK ε hε habc_ineq x u hu_ne habs_pos hsgn

lemma product_bound_E4 (x : ℕ+) (u : ℤ) (D : ℝ)
    (hD : 0 ≤ D)
    (hu_bound : (Int.natAbs u : ℝ) ≤ 3 * (x : ℝ) ^ 11) :
    5 * (x : ℝ) * (Int.natAbs u : ℝ) * D ≤ 15 * (x : ℝ) ^ 12 * D := by
  calc
    5 * (x : ℝ) * (Int.natAbs u : ℝ) * D ≤ 5 * (x : ℝ) * (3 * (x : ℝ) ^ 11) * D := by
      gcongr
    _ = 15 * (x : ℝ) * (x : ℝ) ^ 11 * D := by ring
    _ = 15 * (x : ℝ) ^ 12 * D := by
      ring_nf
    _ = 15 * (x : ℝ) ^ 12 * D := by ring

lemma product_nonneg_E4 (x : ℕ+) (u : ℤ) (D : ℝ)
    (hD : 0 ≤ D) :
    0 ≤ 5 * (x : ℝ) * (Int.natAbs u : ℝ) * D := by positivity

lemma rpow_product_bound (x : ℕ+) (u : ℤ) (D : ℝ) (ε : ℝ)
    (hε : 0 < ε) (hD : 0 ≤ D)
    (hu_bound : (Int.natAbs u : ℝ) ≤ 3 * (x : ℝ) ^ 11) :
    (5 * (x : ℝ) * (Int.natAbs u : ℝ) * D) ^ (1 + ε) ≤
    (15 * (x : ℝ) ^ 12 * D) ^ (1 + ε) := by
  apply Real.rpow_le_rpow (product_nonneg_E4 x u D hD)
    (product_bound_E4 x u D hD hu_bound) (by linarith)

lemma combine_D_powers (D ε : ℝ) (hD : 0 < D) :
    D * D ^ (1 + ε) = D ^ (2 + ε) := by
  conv_lhs => lhs; rw [show D = D ^ (1 : ℝ) from (Real.rpow_one D).symm]
  rw [← Real.rpow_add hD, show (1 : ℝ) + (1 + ε) = 2 + ε from by ring]

lemma pnat_cast_nonneg (x : ℕ+) : (0 : ℝ) ≤ (x : ℝ) := by simp

lemma pnat_pow_rpow_eq (x : ℕ+) (ε : ℝ) :
    ((x : ℝ) ^ 12) ^ (1 + ε) = (x : ℝ) ^ (12 * (1 + ε)) :=
  (Real.rpow_natCast_mul (pnat_cast_nonneg x) 12 (1 + ε)).symm

lemma expand_rhs (K : ℝ) (ε : ℝ) (_hε : 0 < ε)
    (x : ℕ+) (D : ℝ) (hD_pos : 0 < D) :
    D * K * (15 * (x : ℝ) ^ 12 * D) ^ (1 + ε) =
    K * (15 : ℝ) ^ (1 + ε) * (x : ℝ) ^ (12 * (1 + ε)) * D ^ (2 + ε) := by
  have h15 : (0 : ℝ) ≤ 15 := by norm_num
  have hx12 : (0 : ℝ) ≤ (x : ℝ) ^ 12 := pow_nonneg (le_of_lt (Nat.cast_pos.mpr x.pos)) 12
  have hD_nn : (0 : ℝ) ≤ D := le_of_lt hD_pos
  rw [rpow_triple_mul_distrib 15 ((x : ℝ) ^ 12) D (1 + ε) h15 hx12 hD_nn]
  rw [pnat_pow_rpow_eq x ε]
  rw [show D * K * (15 ^ (1 + ε) * (x : ℝ) ^ (12 * (1 + ε)) * D ^ (1 + ε)) =
    K * 15 ^ (1 + ε) * (x : ℝ) ^ (12 * (1 + ε)) * (D * D ^ (1 + ε)) from by ring]
  rw [combine_D_powers D ε hD_pos]

lemma nat_pow_div_rpow_eq (x : ℝ) (hx : 0 < x) (e : ℝ) :
    (x ^ 22 : ℝ) / x ^ e = x ^ ((22 : ℝ) - e) := by
  rw [show (22 : ℝ) = ((22 : ℕ) : ℝ) from by norm_num,
      ← Real.rpow_natCast x 22, ← Real.rpow_sub hx]

lemma div_ineq_of_mul_le (a b c : ℝ) (hc : 0 < c)
    (h : 5 * a ≤ b * c) :
    a / c ≤ b / 5 := by
  rw [div_le_div_iff₀ hc (by norm_num : (0 : ℝ) < 5)]
  linarith

lemma divide_and_simplify (K : ℝ) (_hK : 0 < K)
    (ε : ℝ) (_hε : 0 < ε) (_hε_bound : ε ≤ 1 / 24)
    (x : ℕ+) (D : ℝ) (_hD_pos : 0 < D)
    (h : 5 * (x : ℝ) ^ 22 ≤
      K * (15 : ℝ) ^ (1 + ε) * (x : ℝ) ^ (12 * (1 + ε)) * D ^ (2 + ε)) :
    (x : ℝ) ^ (10 - 12 * ε) ≤ K * 15 ^ (1 + ε) / 5 * D ^ (2 + ε) := by
  have hx_pos : (0 : ℝ) < (x : ℝ) := Nat.cast_pos.mpr x.pos
  have hxrpow_pos : (0 : ℝ) < (x : ℝ) ^ (12 * (1 + ε)) := Real.rpow_pos_of_pos hx_pos _
  have h' : 5 * (x : ℝ) ^ 22 ≤
      (K * (15 : ℝ) ^ (1 + ε) * D ^ (2 + ε)) * (x : ℝ) ^ (12 * (1 + ε)) := by
    have : K * (15 : ℝ) ^ (1 + ε) * (x : ℝ) ^ (12 * (1 + ε)) * D ^ (2 + ε) =
        (K * (15 : ℝ) ^ (1 + ε) * D ^ (2 + ε)) * (x : ℝ) ^ (12 * (1 + ε)) := by ring
    linarith
  have h2 : (x : ℝ) ^ 22 / (x : ℝ) ^ (12 * (1 + ε)) ≤
      K * (15 : ℝ) ^ (1 + ε) * D ^ (2 + ε) / 5 :=
    div_ineq_of_mul_le _ _ _ hxrpow_pos h'
  rw [nat_pow_div_rpow_eq (x : ℝ) hx_pos (12 * (1 + ε))] at h2
  rw [show (22 : ℝ) - 12 * (1 + ε) = 10 - 12 * ε by ring] at h2
  have hrhs : K * (15 : ℝ) ^ (1 + ε) * D ^ (2 + ε) / 5 =
      K * 15 ^ (1 + ε) / 5 * D ^ (2 + ε) := by ring
  rw [hrhs] at h2
  exact h2

lemma rearrange_to_target (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε) (hε_bound : ε ≤ 1 / 24)
    (x : ℕ+) (D : ℝ)
    (hD_pos : 0 < D)
    (h : 5 * (x : ℝ) ^ 22 ≤ D * K * (15 * (x : ℝ) ^ 12 * D) ^ (1 + ε)) :
    (x : ℝ) ^ (10 - 12 * ε) ≤ K * 15 ^ (1 + ε) / 5 * D ^ (2 + ε) := by
  have hexp := expand_rhs K ε hε x D hD_pos
  rw [hexp] at h
  exact divide_and_simplify K hK ε hε hε_bound x D hD_pos h

lemma combine_h5x22_with_bound (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε)
    (x : ℕ+) (u : ℤ) (D : ℝ)
    (hD_pos : 0 < D)
    (hu_bound : (Int.natAbs u : ℝ) ≤ 3 * (x : ℝ) ^ 11)
    (h5x22 : 5 * (x : ℝ) ^ 22 ≤ D * K * (5 * (x : ℝ) * (Int.natAbs u : ℝ) * D) ^ (1 + ε)) :
    5 * (x : ℝ) ^ 22 ≤ D * K * (15 * (x : ℝ) ^ 12 * D) ^ (1 + ε) := by
  have hrpow := rpow_product_bound x u D ε hε (le_of_lt hD_pos) hu_bound
  have hDK : (0 : ℝ) ≤ D * K := mul_nonneg (le_of_lt hD_pos) (le_of_lt hK)
  calc 5 * (x : ℝ) ^ 22
      ≤ D * K * (5 * (x : ℝ) * (Int.natAbs u : ℝ) * D) ^ (1 + ε) := h5x22
    _ ≤ D * K * (15 * (x : ℝ) ^ 12 * D) ^ (1 + ε) :=
        mul_le_mul_of_nonneg_left hrpow hDK

lemma E4_algebraic_cleanup (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε) (hε_bound : ε ≤ 1 / 24)
    (x : ℕ+) (u : ℤ) (D : ℝ)
    (hD_pos : 0 < D) (_hD_ge_one : 1 ≤ D)
    (hu_bound : (Int.natAbs u : ℝ) ≤ 3 * (x : ℝ) ^ 11)
    (h5x22 : 5 * (x : ℝ) ^ 22 ≤ D * K * (5 * (x : ℝ) * (Int.natAbs u : ℝ) * D) ^ (1 + ε)) :
    (x : ℝ) ^ (10 - 12 * ε) ≤ K * 15 ^ (1 + ε) / 5 * D ^ (2 + ε) := by
  have h_combined := combine_h5x22_with_bound K hK ε hε x u D hD_pos hu_bound h5x22
  exact rearrange_to_target K hK ε hε hε_bound x D hD_pos h_combined

lemma exponent_cleanup_E4 (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε) (hε_bound : ε ≤ 1 / 24) :
    ∃ K₂ : ℝ, 0 < K₂ ∧ ∃ X₁ : ℝ, 0 < X₁ ∧
      ∀ X : ℝ, X₁ < X →
        ∀ (x : ℕ+) (u : ℤ),
          (x : ℝ) > X ^ ((1 : ℝ) / 11) →
          1 ≤ |u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| →
          (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) ≤ 4 * X →
          5 * (x : ℝ) ^ 22 ≤
            (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) *
              K * (5 * (x : ℝ) * (Int.natAbs u : ℝ) *
                (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ)) ^ (1 + ε) →
          (x : ℝ) ^ (10 - 12 * ε) ≤
            K₂ * (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) ^ (2 + ε) := by
  refine ⟨K * 15 ^ (1 + ε) / 5, by positivity, 1, one_pos, ?_⟩
  intro X hX x u hx_lower habs_pos habs_le h5x22
  have hXone : 1 < X := hX
  have hu_bound := u_bound_from_E4 x u X hXone hx_lower habs_le
  have hD_pos : (0 : ℝ) < (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_pos habs_pos
  have hD_ge_one : (1 : ℝ) ≤ (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) := by
    exact_mod_cast habs_pos
  exact E4_algebraic_cleanup K hK ε hε hε_bound x u _ hD_pos hD_ge_one hu_bound h5x22

lemma abc_core_E4 (habc : ABC) (ε : ℝ) (hε : 0 < ε) (hε_bound : ε ≤ 1 / 24) :
    ∃ K₂ : ℝ, 0 < K₂ ∧ ∃ X₁ : ℝ, 0 < X₁ ∧
      ∀ X : ℝ, X₁ < X →
        ∀ p : ℕ+ × ℤ, p ∈ E4Set X →
          (p.1 : ℝ) ^ (10 - 12 * ε) ≤
            K₂ * (|p.2 ^ 2 - 5 * (↑p.1 : ℤ) ^ 22| : ℝ) ^ (2 + ε) := by
  unfold ABC at habc
  obtain ⟨K, hK, habc_ineq⟩ := habc ε hε
  obtain ⟨K₂, hK₂, X₁, hX₁, hcleanup⟩ := exponent_cleanup_E4 K hK ε hε hε_bound
  refine ⟨K₂, hK₂, max X₁ 1, by positivity, ?_⟩
  intro X hX p hp
  have hX1 : X₁ < X := lt_of_le_of_lt (le_max_left _ _) hX
  have hXone : 1 < X := lt_of_le_of_lt (le_max_right _ _) hX
  have hu_ne : p.2 ≠ 0 := u_ne_zero_of_E4 X hXone p hp
  have ⟨habs_pos, habs_le⟩ := E4_set_D_bounds X p hp
  have hx_lower := hp.1
  have h5x22 := abc_gives_5x22_bound K hK ε hε habc_ineq p.1 p.2 X hXone hu_ne
    (by exact_mod_cast habs_pos) habs_le
  exact hcleanup X hX1 p.1 p.2 hx_lower (by exact_mod_cast habs_pos) habs_le h5x22

private lemma rpow_le_of_rpow_le (x K D α β : ℝ) (hx : 0 < x) (hK : 0 < K) (hD : 0 < D)
    (hα : 0 < α) (_hβ : 0 < β)
    (h : x ^ α ≤ K * D ^ β) :
    x ≤ K ^ (1 / α) * D ^ (β / α) := by
  have h1 : x ≤ (K * D ^ β) ^ (1 / α) := by
    rw [show x = (x ^ α) ^ (1 / α) by
      rw [← Real.rpow_mul (by positivity), show α * (1 / α) = 1 by field_simp, Real.rpow_one]]
    exact Real.rpow_le_rpow (by positivity) h (by positivity)
  rw [Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (le_of_lt hD), show β * (1 / α) = β / α by field_simp] at h1
  exact h1

lemma x_from_power_bound_E4 (ε : ℝ) (hε : 0 < ε) (hε_bound : ε ≤ 1 / 24)
    (K₂ : ℝ) (hK₂ : 0 < K₂) :
    ∃ K₃ : ℝ, 0 < K₃ ∧
      ∀ X : ℝ, 1 < X →
        ∀ p : ℕ+ × ℤ, p ∈ E4Set X →
          (p.1 : ℝ) ^ (10 - 12 * ε) ≤
            K₂ * (|p.2 ^ 2 - 5 * (↑p.1 : ℤ) ^ 22| : ℝ) ^ (2 + ε) →
          (p.1 : ℝ) ≤ K₃ * X ^ ((2 + ε) / (10 - 12 * ε)) := by
  set α := 10 - 12 * ε with hα_def
  set β := 2 + ε with hβ_def
  set γ := β / α with hγ_def
  have hα_pos : 0 < α := denom_pos_E4 ε hε hε_bound
  have hβ_pos : 0 < β := by linarith
  have hγ_pos : 0 < γ := div_pos hβ_pos hα_pos
  refine ⟨K₂ ^ (1 / α) * (4 : ℝ) ^ γ,
    mul_pos (Real.rpow_pos_of_pos hK₂ _) (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 4) _),
    ?_⟩
  intro X hX p hp hpow
  have ⟨hD_lb, hD_ub⟩ := E4_set_D_bounds X p hp
  set D := (|p.2 ^ 2 - 5 * (↑p.1 : ℤ) ^ 22| : ℝ) with hD_def
  have hD_pos : 0 < D := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hD_lb
  have hX_pos : 0 < X := lt_trans (by norm_num : (0:ℝ) < 1) hX
  have hx_pos : 0 < (p.1 : ℝ) := by positivity
  have h1 : (p.1 : ℝ) ≤ K₂ ^ (1 / α) * D ^ (β / α) :=
    rpow_le_of_rpow_le _ _ _ _ _ hx_pos hK₂ hD_pos hα_pos hβ_pos hpow
  have h2 : D ^ γ ≤ (4 * X) ^ γ :=
    Real.rpow_le_rpow (by linarith) hD_ub (by linarith)
  have h3 : (4 * X) ^ γ = (4 : ℝ) ^ γ * X ^ γ :=
    Real.mul_rpow (by positivity) (by positivity)
  calc (p.1 : ℝ) ≤ K₂ ^ (1 / α) * D ^ γ := h1
    _ ≤ K₂ ^ (1 / α) * ((4 : ℝ) ^ γ * X ^ γ) := by
        apply mul_le_mul_of_nonneg_left
        · calc D ^ γ ≤ (4 * X) ^ γ := h2
            _ = (4 : ℝ) ^ γ * X ^ γ := h3
        · exact le_of_lt (Real.rpow_pos_of_pos hK₂ _)
    _ = K₂ ^ (1 / α) * (4 : ℝ) ^ γ * X ^ γ := by ring

lemma rpow_le_rpow_of_le_exp' {X a b : ℝ} (hX : 1 ≤ X) (hab : a ≤ b) :
    X ^ a ≤ X ^ b :=
  Real.rpow_le_rpow_of_exponent_le hX hab

lemma x_bound_in_E4 (habc : ABC) (η : ℝ) (hη : 0 < η) :
    ∃ K₄ : ℝ, 0 < K₄ ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        ∀ p : ℕ+ × ℤ, p ∈ E4Set X →
          (p.1 : ℝ) ≤ K₄ * X ^ ((1 : ℝ) / 5 + η) := by
  set ε := min η (1 / 24) with hε_def
  have hε_pos : 0 < ε := lt_min hη (by positivity)
  have hε_η : ε ≤ η := min_le_left η (1 / 24)
  have hε_bound : ε ≤ 1 / 24 := min_le_right η (1 / 24)
  obtain ⟨K₂, hK₂_pos, X₁, hX₁_pos, hcore⟩ := abc_core_E4 habc ε hε_pos hε_bound
  obtain ⟨K₃, hK₃_pos, hx_bound⟩ := x_from_power_bound_E4 ε hε_pos hε_bound K₂ hK₂_pos
  have hexp : (2 + ε) / (10 - 12 * ε) ≤ 1 / 5 + η :=
    exponent_bound_E4 η ε hη hε_pos hε_η hε_bound
  refine ⟨K₃, hK₃_pos, max X₁ 1, by positivity, fun X hX p hp => ?_⟩
  have hX₁ : X₁ < X := lt_of_le_of_lt (le_max_left X₁ 1) hX
  have hX1 : 1 < X := lt_of_le_of_lt (le_max_right X₁ 1) hX
  have hx_le := hx_bound X hX1 p hp (hcore X hX₁ p hp)
  calc (p.1 : ℝ) ≤ K₃ * X ^ ((2 + ε) / (10 - 12 * ε)) := hx_le
    _ ≤ K₃ * X ^ (1 / 5 + η) := by
        apply mul_le_mul_of_nonneg_left _ hK₃_pos.le
        exact rpow_le_rpow_of_le_exp' hX1.le hexp

lemma cast_coercion_eq (p₁ : ℕ+) :
    (5 : ℝ) * (↑(↑(↑p₁ : ℕ) : ℤ) : ℝ) ^ 22 = 5 * (↑(↑p₁ : ℕ) : ℝ) ^ 22 := by
  push_cast
  ring

lemma abs_bound_to_upper_bound (u : ℤ) (p₁ : ℕ+) (X : ℝ)
    (h : (|u ^ 2 - 5 * (↑p₁ : ℤ) ^ 22| : ℝ) ≤ 4 * X) :
    (u ^ 2 : ℝ) ≤ 5 * (p₁ : ℝ) ^ 22 + 4 * X := by
  have h1 : (↑u : ℝ) ^ 2 - 5 * (↑(↑(↑p₁ : ℕ) : ℤ) : ℝ) ^ 22 ≤ 4 * X := by
    have := le_of_abs_le h
    push_cast at this ⊢
    linarith
  have h2 := cast_coercion_eq p₁
  linarith

lemma u_sq_le_of_mem_E4 (X : ℝ) (p : ℕ+ × ℤ) (hmem : p ∈ E4Set X) :
    (p.2 ^ 2 : ℝ) ≤ 5 * (p.1 : ℝ) ^ 22 + 4 * X := abs_bound_to_upper_bound p.2 p.1 X hmem.2.2

lemma u_sq_le_bound (X : ℝ) (p : ℕ+ × ℤ)
    (hmem : p ∈ E4Set X) (N : ℕ) (hN : (p.1 : ℕ) ≤ N) :
    (p.2 ^ 2 : ℝ) ≤ 5 * (N : ℝ) ^ 22 + 4 * X :=
  le_trans (u_sq_le_of_mem_E4 X p hmem) (by gcongr)

lemma cast_abs_le_sqrt_of_sq_le (u : ℤ) (B : ℝ)
    (hB : (u ^ 2 : ℝ) ≤ B) :
    (↑|u| : ℝ) ≤ Real.sqrt B := by
  rw [Int.cast_abs]
  rw [← Real.sqrt_sq (abs_nonneg (u : ℝ))]
  exact Real.sqrt_le_sqrt (by rwa [sq_abs])

lemma abs_le_ceil_of_cast_le_sqrt (u : ℤ) (B : ℝ)
    (h : (↑|u| : ℝ) ≤ Real.sqrt B) :
    |u| ≤ ↑(⌈Real.sqrt B⌉₊) := by
  have h1 : (↑|u| : ℝ) ≤ ↑(⌈Real.sqrt B⌉₊ : ℤ) := by
    calc (↑|u| : ℝ) ≤ Real.sqrt B := h
    _ ≤ ↑(⌈Real.sqrt B⌉₊) := Nat.le_ceil _
    _ = ↑(↑⌈Real.sqrt B⌉₊ : ℤ) := by push_cast; ring
  exact Int.cast_le.mp h1

lemma abs_le_ceil_sqrt_of_sq_le (u : ℤ) (B : ℝ)
    (hB : (u ^ 2 : ℝ) ≤ B) :
    |u| ≤ ↑(⌈Real.sqrt B⌉₊) := abs_le_ceil_of_cast_le_sqrt u B (cast_abs_le_sqrt_of_sq_le u B hB)

lemma u_bound_from_E4_membership (X : ℝ) (p : ℕ+ × ℤ)
    (hmem : p ∈ E4Set X) (N : ℕ) (hN : (p.1 : ℕ) ≤ N) :
    |p.2| ≤ ↑(⌈Real.sqrt (5 * (N : ℝ) ^ 22 + 4 * X)⌉₊) :=
    abs_le_ceil_sqrt_of_sq_le p.2 (5 * (N : ℝ) ^ 22 + 4 * X)
    (u_sq_le_bound X p hmem N hN)

lemma E4_set_bounded_of_abc (habc : ABC) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ < X →
      ∃ (N : ℕ) (M : ℕ),
        ∀ p : ℕ+ × ℤ, p ∈ E4Set X → (p.1 : ℕ) ≤ N ∧ |p.2| ≤ (M : ℤ) := by
  obtain ⟨K₄, hK₄_pos, X₀, hX₀_pos, hbound⟩ := x_bound_in_E4 habc 1 one_pos
  refine ⟨X₀, hX₀_pos, fun X hX => ?_⟩
  set B := K₄ * X ^ ((1 : ℝ) / 5 + 1) with hB_def
  set N := ⌈B⌉₊ with hN_def
  set M := ⌈Real.sqrt (5 * (N : ℝ) ^ 22 + 4 * X)⌉₊ with hM_def
  exact ⟨N, M, fun p hmem => by
    have hp_real := hbound X hX p hmem
    exact ⟨real_bound_to_nat_bound p B hp_real,
           u_bound_from_E4_membership X p hmem N (real_bound_to_nat_bound p B hp_real)⟩⟩

lemma E4_set_finite_of_abc (habc : ABC) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ < X → (E4Set X).Finite := by
  obtain ⟨X₀, hX₀, hbnd⟩ := E4_set_bounded_of_abc habc
  exact ⟨X₀, hX₀, fun X hX => by
    obtain ⟨N, M, hNM⟩ := hbnd X hX
    exact bounded_pnat_int_set_finite _ N M hNM⟩

private lemma abs_four_mul_tau_ge_one (R : RamanujanTau) (p : ℕ+)
    (ℓ : ℕ) (hℓ_prime : Nat.Prime ℓ) (hℓ_eq : (R.τ (p ^ 4)).natAbs = ℓ) :
    1 ≤ |4 * R.τ (p ^ 4)| := by
  have hℓ2 : 2 ≤ ℓ := hℓ_prime.two_le
  have hna : (R.τ (p ^ 4)).natAbs ≥ 2 := by omega
  have habs : (2 : ℤ) ≤ |R.τ (p ^ 4)| := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hna
  calc (1 : ℤ) ≤ 4 * 2 := by norm_num
    _ ≤ |4| * |R.τ (p ^ 4)| := by
        rw [show |(4 : ℤ)| = 4 from by norm_num]
        exact mul_le_mul_of_nonneg_left habs (by norm_num)
    _ = |4 * R.τ (p ^ 4)| := (abs_mul 4 (R.τ (p ^ 4))).symm

private lemma abs_cast_eq_cast_natAbs (a : ℤ) :
    |(a : ℝ)| = ((a.natAbs : ℤ) : ℝ) := by simp

private lemma cast_abs_four_mul_tau_eq (R : RamanujanTau) (p : ℕ+) (ℓ : ℕ)
    (hℓ_eq : (R.τ (p ^ 4)).natAbs = ℓ) :
    (|(4 : ℤ) * R.τ (p ^ 4)| : ℝ) = 4 * ((ℓ : ℤ) : ℝ) := by
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < ((4:ℤ):ℝ))]
  congr 1
  rw [abs_cast_eq_cast_natAbs, hℓ_eq]

private lemma cast_abs_lhs_eq_rhs (R : RamanujanTau) (p : ℕ+)
    (_hp : (p : ℕ).Prime) (_ℓ : ℕ)
    (_hℓ_eq : (R.τ (p ^ 4)).natAbs = _ℓ)
    (hid_abs : |(2 * R.τ p ^ 2 - 3 * (↑↑p : ℤ) ^ 11) ^ 2 - 5 * (↑↑p : ℤ) ^ 22| =
        |4 * R.τ (p ^ 4)|) :
    let q : ℕ+ × ℤ := (p, 2 * R.τ p ^ 2 - 3 * (↑↑p : ℤ) ^ 11)
    (|q.2 ^ 2 - 5 * (↑q.1 : ℤ) ^ 22| : ℝ) = (|4 * R.τ (p ^ 4)| : ℝ) := by
  simp only []
  exact_mod_cast hid_abs

private lemma cast_abs_eq_four_mul_ell (R : RamanujanTau) (_X : ℝ) (p : ℕ+)
    (hp : (p : ℕ).Prime) (ℓ : ℕ)
    (hℓ_eq : (R.τ (p ^ 4)).natAbs = ℓ)
    (hid_abs : |(2 * R.τ p ^ 2 - 3 * (↑↑p : ℤ) ^ 11) ^ 2 - 5 * (↑↑p : ℤ) ^ 22| =
        |4 * R.τ (p ^ 4)|) :
    let q : ℕ+ × ℤ := (p, 2 * R.τ p ^ 2 - 3 * (↑↑p : ℤ) ^ 11)
    (|q.2 ^ 2 - 5 * (↑q.1 : ℤ) ^ 22| : ℝ) = 4 * ((ℓ : ℤ) : ℝ) := by
  intro q
  have h1 := cast_abs_lhs_eq_rhs R p hp ℓ hℓ_eq hid_abs
  rw [h1]
  exact cast_abs_four_mul_tau_eq R p ℓ hℓ_eq

private lemma witness_in_E4_set_upper (R : RamanujanTau) (X : ℝ) (p : ℕ+)
    (hp : (p : ℕ).Prime) (ℓ : ℕ) (hℓ_le : (ℓ : ℝ) ≤ X)
    (hℓ_eq : (R.τ (p ^ 4)).natAbs = ℓ)
    (hid_abs : |(2 * R.τ p ^ 2 - 3 * (↑↑p : ℤ) ^ 11) ^ 2 - 5 * (↑↑p : ℤ) ^ 22| =
        |4 * R.τ (p ^ 4)|) :
    let q : ℕ+ × ℤ := (p, 2 * R.τ p ^ 2 - 3 * (↑↑p : ℤ) ^ 11)
    (|q.2 ^ 2 - 5 * (↑q.1 : ℤ) ^ 22| : ℝ) ≤ 4 * X := by
  have h1 := cast_abs_eq_four_mul_ell R X p hp ℓ hℓ_eq hid_abs
  simp only at h1 ⊢
  rw [h1]
  exact mul_le_mul_of_nonneg_left hℓ_le (show (0 : ℝ) ≤ 4 by norm_num)

lemma witness_in_E4_set (R : RamanujanTau) (X : ℝ) (p : ℕ+)
    (hp : (p : ℕ).Prime) (hp_large : (p : ℝ) > X ^ ((1 : ℝ) / 11))
    (ℓ : ℕ) (hℓ_prime : Nat.Prime ℓ) (hℓ_le : (ℓ : ℝ) ≤ X)
    (hℓ_eq : (R.τ (p ^ 4)).natAbs = ℓ) :
    (p, 2 * (R.τ p) ^ 2 - 3 * (↑(p : ℕ) : ℤ) ^ 11) ∈ E4Set X := by
  have hid := hecke_u_identity R p hp
  simp only at hid
  refine ⟨hp_large, ?_, ?_⟩
  · change 1 ≤ |(2 * R.τ p ^ 2 - 3 * (↑↑p) ^ 11) ^ 2 - 5 * (↑↑p : ℤ) ^ 22|
    rw [hid]
    exact abs_four_mul_tau_ge_one R p ℓ hℓ_prime hℓ_eq
  · have hid_abs : |(2 * R.τ p ^ 2 - 3 * (↑↑p : ℤ) ^ 11) ^ 2 - 5 * (↑↑p : ℤ) ^ 22| =
        |4 * R.τ (p ^ 4)| := congrArg (|·|) hid
    exact witness_in_E4_set_upper R X p hp ℓ hℓ_le hℓ_eq hid_abs

open Classical in
private noncomputable def witnessP (R : RamanujanTau) (X : ℝ) (ℓ : ℕ) : ℕ+ :=
  if h : ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((1 : ℝ) / 11) ∧
      (R.τ (p ^ 4)).natAbs = ℓ
  then h.choose
  else 1

private noncomputable def witnessMap (R : RamanujanTau) (X : ℝ) (ℓ : ℕ) : ℕ+ × ℤ :=
  let p := witnessP R X ℓ
  (p, 2 * (R.τ p) ^ 2 - 3 * (↑(p : ℕ) : ℤ) ^ 11)

private lemma witnessP_spec (R : RamanujanTau) (X : ℝ) (ℓ : ℕ)
    (hℓ : ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((1 : ℝ) / 11) ∧
      (R.τ (p ^ 4)).natAbs = ℓ) :
    ((witnessP R X ℓ : ℕ).Prime ∧
     (witnessP R X ℓ : ℝ) > X ^ ((1 : ℝ) / 11) ∧
     (R.τ (witnessP R X ℓ ^ 4)).natAbs = ℓ) := by
  unfold witnessP
  rw [dif_pos hℓ]
  exact hℓ.choose_spec

private lemma witnessMap_mapsTo (R : RamanujanTau) (X : ℝ) :
    ∀ ℓ ∈ {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((1 : ℝ) / 11) ∧
        (R.τ (p ^ 4)).natAbs = ℓ},
    witnessMap R X ℓ ∈ E4Set X := by
  intro ℓ hℓ
  simp only [Set.mem_setOf_eq] at hℓ
  obtain ⟨hℓ_prime, hℓ_le, hℓ_ex⟩ := hℓ
  have hspec := witnessP_spec R X ℓ hℓ_ex
  obtain ⟨hp_prime, hp_large, hp_eq⟩ := hspec
  unfold witnessMap
  exact witness_in_E4_set R X (witnessP R X ℓ) hp_prime hp_large ℓ hℓ_prime hℓ_le hp_eq

private lemma witnessMap_injOn (R : RamanujanTau) (X : ℝ) :
    Set.InjOn (witnessMap R X)
      {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((1 : ℝ) / 11) ∧
          (R.τ (p ^ 4)).natAbs = ℓ} := by
  intro ℓ₁ ⟨_, _, hex₁⟩ ℓ₂ ⟨_, _, hex₂⟩ heq
  have hpeq : witnessP R X ℓ₁ = witnessP R X ℓ₂ := congr_arg Prod.fst heq
  have h1 := (witnessP_spec R X ℓ₁ hex₁).2.2
  rw [hpeq] at h1
  exact h1.symm.trans (witnessP_spec R X ℓ₂ hex₂).2.2

lemma ncard_witness_le_E4 (R : RamanujanTau) (X : ℝ)
    (hfin : (E4Set X).Finite) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((1 : ℝ) / 11) ∧
        (R.τ (p ^ 4)).natAbs = ℓ}.ncard ≤ E4 X := by
  unfold E4
  exact Set.ncard_le_ncard_of_injOn (witnessMap R X)
    (witnessMap_mapsTo R X) (witnessMap_injOn R X) hfin

lemma large_primes_k2_bound (R : RamanujanTau) (habc : ABC) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ < X →
      ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
        ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((1 : ℝ) / 11) ∧
          (R.τ (p ^ 4)).natAbs = ℓ}.ncard : ℝ) ≤
      (E4 X : ℝ) := by
  obtain ⟨X₀, hX₀_pos, hX₀_fin⟩ := E4_set_finite_of_abc habc
  exact ⟨X₀, hX₀_pos, fun X hX => by
    exact Nat.cast_le.mpr (ncard_witness_le_E4 R X (hX₀_fin X hX))⟩



lemma k2_set_split (R : RamanujanTau) (X : ℝ) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 4)).natAbs = ℓ} ⊆
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11) ∧
        (R.τ (p ^ 4)).natAbs = ℓ} ∪
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((1 : ℝ) / 11) ∧
        (R.τ (p ^ 4)).natAbs = ℓ} := by
  intro ℓ hℓ
  simp only [Set.mem_setOf_eq] at hℓ ⊢
  obtain ⟨hprime, hle, p, hp, htau⟩ := hℓ
  by_cases h : (p : ℝ) ≤ X ^ ((1 : ℝ) / 11)
  · left
    exact ⟨hprime, hle, p, hp, h, htau⟩
  · right
    push Not at h
    exact ⟨hprime, hle, p, hp, h, htau⟩

lemma k2_target_set_finite (R : RamanujanTau) (X : ℝ) :
    Set.Finite {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧
        (R.τ (p ^ 4)).natAbs = ℓ} := by
  apply Set.Finite.subset (Set.finite_le_nat ⌊X⌋₊)
  intro ℓ hℓ
  simp only [Set.mem_setOf_eq] at hℓ ⊢
  exact Nat.le_floor hℓ.2.1

lemma k2_contribution_abc (R : RamanujanTau) (habc : ABC) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
          ∃ p : ℕ+, (p : ℕ).Prime ∧
            (R.τ (p ^ 4)).natAbs = ℓ}.ncard : ℝ) ≤
        (E4 X : ℝ) + X ^ ((6 : ℝ) / 11) := by
  obtain ⟨X₁, hX₁_pos, hsmall⟩ := small_primes_k2_bound R
  obtain ⟨X₂, hX₂_pos, hlarge⟩ := large_primes_k2_bound R habc
  refine ⟨max (max X₁ X₂) 1, by positivity, fun X hX => ?_⟩
  have hX₁ : X₁ < X := lt_of_le_of_lt (le_max_left X₁ X₂) (lt_of_le_of_lt (le_max_left _ _) hX)
  have hX₂ : X₂ < X := lt_of_le_of_lt (le_max_right X₁ X₂) (lt_of_le_of_lt (le_max_left _ _) hX)
  have hX1 : (1 : ℝ) < X := lt_of_le_of_lt (le_max_right _ _) hX
  have hsm := hsmall X hX₁
  have hlg := hlarge X hX₂
  have hsplit := k2_set_split R X
  have hfin := k2_target_set_finite R X
  set S_small := {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11) ∧
        (R.τ (p ^ 4)).natAbs = ℓ}
  set S_large := {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((1 : ℝ) / 11) ∧
        (R.τ (p ^ 4)).natAbs = ℓ}
  have hfin_small : S_small.Finite := hfin.subset (fun ℓ hℓ => by
    obtain ⟨h1, h2, p, h3, _, h5⟩ := hℓ; exact ⟨h1, h2, p, h3, h5⟩)
  have hfin_large : S_large.Finite := hfin.subset (fun ℓ hℓ => by
    obtain ⟨h1, h2, p, h3, _, h5⟩ := hℓ; exact ⟨h1, h2, p, h3, h5⟩)
  have hfin_union : (S_small ∪ S_large).Finite := hfin_small.union hfin_large
  have h1 : ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (R.τ (p ^ 4)).natAbs = ℓ}.ncard : ℝ) ≤
    (S_small.ncard : ℝ) + (S_large.ncard : ℝ) := by
    exact_mod_cast (Set.ncard_le_ncard hsplit hfin_union).trans (Set.ncard_union_le _ _)
  have h2 : X ^ ((1 : ℝ) / 11) ≤ X ^ ((6 : ℝ) / 11) :=
    Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num : (1 : ℝ) / 11 ≤ 6 / 11)
  linarith

lemma reduction_lemma_core (R : RamanujanTau) (habc : ABC) (h54 : Proposition54 R) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (S R X : ℝ) ≤ C * (X ^ ((1 : ℝ) / 2) * Real.log X +
          X ^ ((13 : ℝ) / 22) + X ^ ((6 : ℝ) / 11) +
          (E2 X : ℝ) + (E4 X : ℝ)) := by
  obtain ⟨C₃, hC₃, X₃, hX₃, h_k3⟩ := k_ge3_contribution R h54
  obtain ⟨X₁, hX₁, h_k1⟩ := k1_contribution_abc R habc
  obtain ⟨X₂, hX₂, h_k2⟩ := k2_contribution_abc R habc
  refine ⟨C₃ + 3, by linarith, max (max X₁ (max X₂ X₃)) 1, by positivity, ?_⟩
  intro X hX
  have hX_pos : 1 < X := lt_of_le_of_lt (le_max_right _ _) hX
  have hX1 : X₁ < X := lt_of_le_of_lt (le_max_of_le_left (le_max_left _ _)) hX
  have hX2 : X₂ < X :=
    lt_of_le_of_lt (le_max_of_le_left (le_max_of_le_right (le_max_left _ _))) hX
  have hX3 : X₃ < X :=
    lt_of_le_of_lt (le_max_of_le_left (le_max_of_le_right (le_max_right _ _))) hX
  have hS := S_decomposition R X hX_pos
  have hk1 := h_k1 X hX1
  have hk2 := h_k2 X hX2
  have hk3 := h_k3 X hX3
  have h_one_le : (1 : ℝ) ≤ X ^ ((13 : ℝ) / 22) := by
    rw [show (1 : ℝ) = 1 ^ ((13 : ℝ) / 22) by simp]
    exact Real.rpow_le_rpow (by linarith) (le_of_lt hX_pos) (by positivity)
  have hX_pos' : (0 : ℝ) < X := by linarith
  have hmul_nn : (0 : ℝ) ≤ X ^ ((1 : ℝ) / 2) * Real.log X :=
    mul_nonneg (Real.rpow_nonneg hX_pos'.le _) (Real.log_nonneg hX_pos.le)
  set T := X ^ ((1 : ℝ) / 2) * Real.log X +
    X ^ ((13 : ℝ) / 22) + X ^ ((6 : ℝ) / 11) +
    (E2 X : ℝ) + (E4 X : ℝ)
  have hS_bound : (S R X : ℝ) ≤ 2 * X ^ ((13 : ℝ) / 22) + (E2 X : ℝ) + (E4 X : ℝ) +
      X ^ ((6 : ℝ) / 11) + C₃ * (X ^ ((1 : ℝ) / 2) * Real.log X) := by
    linarith
  have hT_def : T = X ^ ((1 : ℝ) / 2) * Real.log X + X ^ ((13 : ℝ) / 22) +
    X ^ ((6 : ℝ) / 11) + (E2 X : ℝ) + (E4 X : ℝ) := rfl
  nlinarith [mul_nonneg (le_of_lt hC₃) hmul_nn,
             mul_nonneg (le_of_lt hC₃) (Real.rpow_nonneg hX_pos'.le ((13 : ℝ) / 22)),
             mul_nonneg (le_of_lt hC₃) (Real.rpow_nonneg hX_pos'.le ((6 : ℝ) / 11)),
             mul_nonneg (le_of_lt hC₃) (Nat.cast_nonneg (E2 X)),
             mul_nonneg (le_of_lt hC₃) (Nat.cast_nonneg (E4 X))]
theorem reduction_lemma (habc : ABC) (h54 : Proposition54 R) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (S R X : ℝ) ≤ C * (X ^ ((1 : ℝ) / 2) * Real.log X +
          X ^ ((13 : ℝ) / 22) + X ^ ((6 : ℝ) / 11) +
          (E2 X : ℝ) + (E4 X : ℝ)) :=
  reduction_lemma_core R habc h54

namespace E2Helpers
lemma eventually_rpow_ge_const {C a b : ℝ} (_hC : 0 < C) (hab : a < b) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ < X → C ≤ X ^ (b - a) := by
  have h_tendsto : Filter.Tendsto (fun X : ℝ => X ^ (b - a)) Filter.atTop Filter.atTop := by
    exact tendsto_rpow_atTop (by linarith)
  have h_exists_X₁ : ∃ (X₁ : ℝ), ∀ (X : ℝ), X₁ ≤ X → C ≤ X ^ (b - a) := by
    have h₃ : ∀ᶠ (X : ℝ) in Filter.atTop, C ≤ X ^ (b - a) := by
      filter_upwards [h_tendsto.eventually (Filter.eventually_gt_atTop C)] with X hX
      linarith
    obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp h₃
    refine ⟨X₁, ?_⟩
    intro X hX
    have h₄ : C ≤ X ^ (b - a) := hX₁ X hX
    linarith
  have h_main : ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ < X → C ≤ X ^ (b - a) := by
    obtain ⟨X₁, hX₁⟩ := h_exists_X₁
    use max 1 X₁
    constructor
    · have h₄ : max 1 X₁ ≥ 1 := by apply le_max_left
      linarith
    · intro X hX
      have h₄ : (max 1 X₁ : ℝ) ≥ X₁ := by
        apply le_max_right
      have h₅ : X₁ ≤ X := by linarith
      have h₆ : C ≤ X ^ (b - a) := hX₁ X h₅
      linarith
  exact h_main

lemma rpow_diff_mul_rpow_le {C a b X : ℝ} (hX : 0 < X) (h : C ≤ X ^ (b - a)) :
    C * X ^ a ≤ X ^ b := by
  have h₁ : C * X ^ a ≤ (X ^ (b - a)) * X ^ a := by
    have h₂ : 0 ≤ X ^ a := by positivity
    nlinarith [h, h₂]
  have h₂ : (X : ℝ) ^ (b - a) * (X : ℝ) ^ a = (X : ℝ) ^ ((b - a) + a : ℝ) := by
    rw [← Real.rpow_add hX]
  have h₃ : (X : ℝ) ^ ((b - a : ℝ) + a) = (X : ℝ) ^ b := by
    have h₄ : (b - a : ℝ) + a = b := by
      ring_nf
    rw [h₄]
  have h₄ : (X : ℝ) ^ (b - a) * (X : ℝ) ^ a = (X : ℝ) ^ b := by
    rw [h₂, h₃]
  have h₅ : C * X ^ a ≤ X ^ b := by
    calc
      C * X ^ a ≤ (X ^ (b - a)) * X ^ a := h₁
      _ = (X : ℝ) ^ (b - a) * (X : ℝ) ^ a := by norm_cast
      _ = (X : ℝ) ^ b := by rw [h₄]
      _ = X ^ b := by norm_cast
  exact h₅

lemma E2_caseA_mem (X : ℝ) (x : ℕ+) (y : ℤ)
    (h_abs_le : (|(↑↑x : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X)
    (h_sign : y ^ 2 ≤ (↑↑x : ℤ) ^ 11 - 1) :
    y ∈ ({y : ℤ | y ^ 2 ≤ (↑↑x : ℤ) ^ 11 - 1 ∧
        (((↑↑x : ℤ) ^ 11 - y ^ 2 : ℤ) : ℝ) ≤ X}) := by
  grind

lemma E2_caseB_mem (X : ℝ) (x : ℕ+) (y : ℤ)
    (h_abs_le : (|(↑↑x : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X)
    (h_sign : (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2) :
    y ∈ ({y : ℤ | (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2 ∧
        ((y ^ 2 - (↑↑x : ℤ) ^ 11 : ℤ) : ℝ) ≤ X}) := by
  grind

lemma E2_fiber_subset_union (X : ℝ) (_hX : 2 < X) (x : ℕ+)
    (_hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    {y : ℤ | (x, y) ∈ E2Set X} ⊆
      {y : ℤ | y ^ 2 ≤ (↑↑x : ℤ) ^ 11 - 1 ∧
        (((↑↑x : ℤ) ^ 11 - y ^ 2 : ℤ) : ℝ) ≤ X} ∪
      {y : ℤ | (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2 ∧
        ((y ^ 2 - (↑↑x : ℤ) ^ 11 : ℤ) : ℝ) ≤ X} := by
  intro y hy
  simp only [Set.mem_setOf_eq, E2Set] at hy
  obtain ⟨_, h_abs_ge, h_abs_le⟩ := hy
  rcases show y ^ 2 ≤ (↑↑x : ℤ) ^ 11 - 1 ∨ (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2 from by
      rcases abs_cases ((↑↑x : ℤ) ^ 11 - y ^ 2) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    with h_caseA | h_caseB
  · left
    exact E2_caseA_mem X x y h_abs_le h_caseA
  · right
    exact E2_caseB_mem X x y h_abs_le h_caseB

lemma sq_le_imp_mem_Icc (x : ℕ+) (y : ℤ)
    (hy : y ^ 2 ≤ (↑↑x : ℤ) ^ 11 - 1) :
    y ∈ Set.Icc (-(↑↑x : ℤ) ^ 11) ((↑↑x : ℤ) ^ 11) := by
  have hx11_pos := pow_pos (by positivity : (0 : ℤ) < (↑↑x : ℤ)) 11
  constructor
  · by_contra h
    nlinarith [sq_nonneg (y + (↑↑x : ℤ) ^ 11 + 1)]
  · by_contra h
    nlinarith

lemma E2_caseA_finite (X : ℝ) (_hX : 2 < X) (x : ℕ+)
    (_hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    Set.Finite {y : ℤ | y ^ 2 ≤ (↑↑x : ℤ) ^ 11 - 1 ∧
      (((↑↑x : ℤ) ^ 11 - y ^ 2 : ℤ) : ℝ) ≤ X} := by
  apply Set.Finite.subset (Set.finite_Icc (-(↑↑x : ℤ) ^ 11) ((↑↑x : ℤ) ^ 11))
  intro y hy
  exact sq_le_imp_mem_Icc x y hy.1

lemma nonneg_int_short_interval_finite (a b : ℝ) (_hab : a ≤ b) :
    {n : ℤ | 0 ≤ n ∧ (a : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ b}.Finite := by
  apply Set.Finite.subset (Set.finite_Icc ⌈a⌉ ⌊b⌋)
  intro n ⟨_, ha, hb⟩
  exact ⟨Int.ceil_le.mpr ha, Int.le_floor.mpr hb⟩

lemma int_eq_of_cast_in_short_interval (n₁ n₂ : ℤ) (a b : ℝ)
    (hlen : b - a < 1)
    (ha1 : a ≤ (n₁ : ℝ)) (hb1 : (n₁ : ℝ) ≤ b)
    (ha2 : a ≤ (n₂ : ℝ)) (hb2 : (n₂ : ℝ) ≤ b) :
    n₁ = n₂ := by
  have h1 : (n₁ - n₂ : ℤ) < 1 := by exact_mod_cast show (n₁ - n₂ : ℝ) < 1 by linarith
  have h2 : (n₁ - n₂ : ℤ) > -1 := by exact_mod_cast show (n₁ - n₂ : ℝ) > -1 by linarith
  omega

lemma ncard_nonneg_int_in_short_interval (a b : ℝ) (hab : a ≤ b) (hlen : b - a < 1)
    (_ha : 0 ≤ a) :
    Set.ncard {n : ℤ | 0 ≤ n ∧ (a : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ b} ≤ 1 := by
  have hfin := nonneg_int_short_interval_finite a b hab
  apply (Set.ncard_le_one_iff hfin).mpr
  intro n₁ n₂ hn₁ hn₂
  exact int_eq_of_cast_in_short_interval _ _ a b hlen hn₁.2.1 hn₁.2.2 hn₂.2.1 hn₂.2.2

lemma rpow_two_eleven_eq_sq (X : ℝ) (hX : 0 < X) :
    (X ^ ((2 : ℝ) / 11)) ^ (11 : ℕ) = X ^ (2 : ℕ) := by
  rw [show (X ^ ((2 : ℝ) / 11)) ^ (11 : ℕ) = (X ^ ((2 : ℝ) / 11)) ^ (11 : ℝ) from by norm_cast,
    ← Real.rpow_mul hX.le, show (2 : ℝ) / 11 * 11 = 2 from by norm_num]
  norm_cast

lemma pow_eleven_strict_mono (X : ℝ) (hX : 0 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    (X ^ ((2 : ℝ) / 11)) ^ (11 : ℕ) < (↑↑x : ℝ) ^ 11 :=
  pow_lt_pow_left₀ (by linarith) (Real.rpow_nonneg hX.le _) (by norm_num)

lemma x11_gt_X_sq (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    (↑↑x : ℝ) ^ 11 > X ^ 2 := by
  have hXpos : 0 < X := by linarith
  calc X ^ 2 = (X ^ ((2 : ℝ) / 11)) ^ (11 : ℕ) := (rpow_two_eleven_eq_sq X hXpos).symm
    _ < (↑↑x : ℝ) ^ 11 := pow_eleven_strict_mono X hXpos x hx

lemma x11_sub_X_pos (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    (↑↑x : ℝ) ^ 11 - X > 0 := by
  have h := x11_gt_X_sq X hX x hx
  have : X ^ 2 > X := by nlinarith
  linarith

lemma x11_sub_one_pos (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    (↑↑x : ℝ) ^ 11 - 1 > 0 := by
  have h := x11_gt_X_sq X hX x hx
  nlinarith

lemma sqrt_x11_sub_one_gt_one (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    Real.sqrt ((↑↑x : ℝ) ^ 11 - 1) > 1 := by
  have h11 := x11_gt_X_sq X hX x hx
  have hx11_gt : (↑↑x : ℝ) ^ 11 - 1 > 1 := by nlinarith [sq_nonneg (X - 2)]
  calc 1 = Real.sqrt 1 := Real.sqrt_one.symm
    _ < Real.sqrt ((↑↑x : ℝ) ^ 11 - 1) := Real.sqrt_lt_sqrt (by norm_num) hx11_gt

lemma x11_sub_X_gt_X_mul_X_sub_one (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    (↑↑x : ℝ) ^ 11 - X > X * (X - 1) := by
  have h := x11_gt_X_sq X hX x hx
  nlinarith [sq X]

lemma sqrt_x11_sub_X_gt (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    Real.sqrt ((↑↑x : ℝ) ^ 11 - X) > Real.sqrt (X * (X - 1)) := by
  apply Real.sqrt_lt_sqrt
  · have hX1 : X > 0 := by linarith
    have hX2 : X - 1 > 0 := by linarith
    exact le_of_lt (mul_pos hX1 hX2)
  · exact x11_sub_X_gt_X_mul_X_sub_one X hX x hx

lemma sq_sub_two_lt_mul (X : ℝ) (hX : 2 < X) :
    (X - 2) ^ 2 < X * (X - 1) := by grind

lemma one_plus_sqrt_gt_X_sub_one (X : ℝ) (hX : 2 < X) :
    1 + Real.sqrt (X * (X - 1)) > X - 1 := by
  have h0 : (0 : ℝ) ≤ X - 2 := by linarith
  have hsq : (X - 2) ^ 2 < X * (X - 1) := sq_sub_two_lt_mul X hX
  have hlt : X - 2 < Real.sqrt (X * (X - 1)) := by
    rwa [Real.lt_sqrt h0]
  linarith

lemma denom_gt_X_sub_one (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    Real.sqrt ((↑↑x : ℝ) ^ 11 - 1) + Real.sqrt ((↑↑x : ℝ) ^ 11 - X) > X - 1 := by
  have h1 : Real.sqrt ((↑↑x : ℝ) ^ 11 - 1) > 1 :=
    sqrt_x11_sub_one_gt_one X hX x hx
  have h2 : Real.sqrt ((↑↑x : ℝ) ^ 11 - X) > Real.sqrt (X * (X - 1)) :=
    sqrt_x11_sub_X_gt X hX x hx
  have h3 : 1 + Real.sqrt (X * (X - 1)) > X - 1 :=
    one_plus_sqrt_gt_X_sub_one X hX
  linarith

lemma interval_length_lt_one (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    Real.sqrt ((↑↑x : ℝ) ^ 11 - 1) - Real.sqrt ((↑↑x : ℝ) ^ 11 - X) < 1 := by
  have h1pos : (↑↑x : ℝ) ^ 11 - 1 > 0 := x11_sub_one_pos X hX x hx
  have hXpos : (↑↑x : ℝ) ^ 11 - X > 0 := x11_sub_X_pos X hX x hx
  have hlt : (↑↑x : ℝ) ^ 11 - X < (↑↑x : ℝ) ^ 11 - 1 := by linarith
  rw [sqrt_sub_eq_div _ _ h1pos (le_of_lt hXpos) hlt]
  have hdenom_pos : Real.sqrt ((↑↑x : ℝ) ^ 11 - 1) + Real.sqrt ((↑↑x : ℝ) ^ 11 - X) > 0 := by
    have : Real.sqrt ((↑↑x : ℝ) ^ 11 - 1) > 0 := Real.sqrt_pos_of_pos h1pos
    have : Real.sqrt ((↑↑x : ℝ) ^ 11 - X) > 0 := Real.sqrt_pos_of_pos hXpos
    linarith
  rw [div_lt_one hdenom_pos]
  rw [show (↑↑x : ℝ) ^ 11 - 1 - ((↑↑x : ℝ) ^ 11 - X) = X - 1 by ring]
  exact denom_gt_X_sub_one X hX x hx

lemma pair_ncard_le_two (n : ℕ) :
    ({(n : ℤ), -(n : ℤ)} : Set ℤ).ncard ≤ 2 := by
  calc ({(n : ℤ), -(n : ℤ)} : Set ℤ).ncard
      ≤ ({-(n : ℤ)} : Set ℤ).ncard + 1 := Set.ncard_insert_le _ _
    _ = 1 + 1 := by rw [Set.ncard_singleton]
    _ = 2 := by norm_num

lemma subset_natAbs_eq_ncard_le_two (n : ℕ) (T : Set ℤ) (_hfin : T.Finite)
    (hT : ∀ y ∈ T, y.natAbs = n) :
    T.ncard ≤ 2 := by
  have hsub : T ⊆ {(n : ℤ), -(n : ℤ)} := fun y hy => by
    rcases show y = ↑n ∨ y = -↑n by grind with h | h <;> simp [h]
  have hfin2 : ({(n : ℤ), -(n : ℤ)} : Set ℤ).Finite := Set.Finite.insert _ (Set.finite_singleton _)
  calc T.ncard ≤ ({(n : ℤ), -(n : ℤ)} : Set ℤ).ncard := Set.ncard_le_ncard hsub hfin2
    _ ≤ 2 := pair_ncard_le_two n

lemma ncard_le_two_of_natAbs_image_le_one (S : Set ℤ) (hfin : S.Finite)
    (himg : Set.ncard (Int.natAbs '' S) ≤ 1) :
    S.ncard ≤ 2 := by
  rw [Set.ncard_le_one_iff_eq (hfin.image _)] at himg
  rcases himg with hempty | ⟨n, hn⟩
  · rw [Set.image_eq_empty.mp hempty, Set.ncard_empty]
    omega
  · apply subset_natAbs_eq_ncard_le_two n S hfin
    intro y hy
    have : y.natAbs ∈ Int.natAbs '' S := Set.mem_image_of_mem _ hy
    rw [hn] at this
    exact this

lemma natAbs_cast_sq_eq (y : ℤ) :
    ((Int.natAbs y : ℤ) : ℝ) ^ 2 = ((y ^ 2 : ℤ) : ℝ) := by
  have h := Int.natAbs_sq y
  exact_mod_cast h

lemma natAbs_sq_le_cast_real (x : ℕ+) (y : ℤ)
    (hy_sq : y ^ 2 ≤ (↑↑x : ℤ) ^ 11 - 1) :
    ((Int.natAbs y : ℤ) : ℝ) ^ 2 ≤ (↑↑x : ℝ) ^ 11 - 1 := by
  have h1 : (Int.natAbs y : ℤ) ^ 2 ≤ (↑↑x : ℤ) ^ 11 - 1 := by
    rw [Int.natAbs_sq]
    exact hy_sq
  exact_mod_cast h1

lemma upper_bound_from_sq_le (x : ℕ+) (y : ℤ) (X : ℝ) (hX : 2 < X)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11))
    (hy_sq : y ^ 2 ≤ (↑↑x : ℤ) ^ 11 - 1) :
    ((Int.natAbs y : ℤ) : ℝ) ≤ Real.sqrt ((↑↑x : ℝ) ^ 11 - 1) := by
  rw [Real.le_sqrt (by positivity) (le_of_lt (x11_sub_one_pos X hX x hx))]
  exact natAbs_sq_le_cast_real x y hy_sq

lemma natAbs_cast_sq_eq' (y : ℤ) :
    ((Int.natAbs y : ℤ) : ℝ) ^ 2 = ((y : ℤ) : ℝ) ^ 2 := by
  norm_cast
  exact_mod_cast Int.natAbs_sq y

lemma rearrange_diff_le (x : ℕ+) (y : ℤ) (X : ℝ)
    (hy_diff : (((↑↑x : ℤ) ^ 11 - y ^ 2 : ℤ) : ℝ) ≤ X) :
    (↑↑x : ℝ) ^ 11 - X ≤ ((Int.natAbs y : ℤ) : ℝ) ^ 2 := by
  have h1 := natAbs_cast_sq_eq' y
  rw [h1]
  have h2 : (((↑↑x : ℤ) ^ 11 - y ^ 2 : ℤ) : ℝ) = (↑↑x : ℝ) ^ 11 - ((y : ℤ) : ℝ) ^ 2 := by
    push_cast
    ring
  rw [h2] at hy_diff
  linarith

lemma lower_bound_from_diff_le (x : ℕ+) (y : ℤ) (X : ℝ) (_hX : 2 < X)
    (_hx : (x : ℝ) > X ^ ((2 : ℝ) / 11))
    (hy_diff : (((↑↑x : ℤ) ^ 11 - y ^ 2 : ℤ) : ℝ) ≤ X) :
    Real.sqrt ((↑↑x : ℝ) ^ 11 - X) ≤ ((Int.natAbs y : ℤ) : ℝ) := by
  rw [Real.sqrt_le_left (by positivity)]
  exact rearrange_diff_le x y X hy_diff

lemma natAbs_image_subset_nonneg_interval (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    (Nat.cast '' (Int.natAbs '' {y : ℤ | y ^ 2 ≤ (↑↑x : ℤ) ^ 11 - 1 ∧
      (((↑↑x : ℤ) ^ 11 - y ^ 2 : ℤ) : ℝ) ≤ X}) : Set ℤ) ⊆
    {n : ℤ | 0 ≤ n ∧ Real.sqrt ((↑↑x : ℝ) ^ 11 - X) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ Real.sqrt ((↑↑x : ℝ) ^ 11 - 1)} := by
  intro n hn
  simp only [Set.mem_image, Set.mem_setOf_eq] at hn
  obtain ⟨m, ⟨y, ⟨hy_sq, hy_diff⟩, rfl⟩, rfl⟩ := hn
  refine ⟨Nat.cast_nonneg _, ?_, ?_⟩
  · exact lower_bound_from_diff_le x y X hX hx hy_diff
  · exact upper_bound_from_sq_le x y X hX hx hy_sq

lemma E2_caseA_abs_image_ncard (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    Set.ncard (Int.natAbs '' {y : ℤ | y ^ 2 ≤ (↑↑x : ℤ) ^ 11 - 1 ∧
      (((↑↑x : ℤ) ^ 11 - y ^ 2 : ℤ) : ℝ) ≤ X}) ≤ 1 := by
  have h_inj : Function.Injective (Nat.cast : ℕ → ℤ) := Nat.cast_injective
  set S := {y : ℤ | y ^ 2 ≤ (↑↑x : ℤ) ^ 11 - 1 ∧
    (((↑↑x : ℤ) ^ 11 - y ^ 2 : ℤ) : ℝ) ≤ X}
  set img := Int.natAbs '' S
  have h_eq : (Nat.cast '' img : Set ℤ).ncard = img.ncard :=
    Set.ncard_image_of_injective img h_inj
  have h_sub := natAbs_image_subset_nonneg_interval X hX x hx
  have h_sqrt_le : Real.sqrt ((↑↑x : ℝ) ^ 11 - X) ≤ Real.sqrt ((↑↑x : ℝ) ^ 11 - 1) := by
    apply Real.sqrt_le_sqrt
    linarith
  have h_sqrt_nn : (0 : ℝ) ≤ Real.sqrt ((↑↑x : ℝ) ^ 11 - X) := Real.sqrt_nonneg _
  have h_len := interval_length_lt_one X hX x hx
  have h_ncard := ncard_nonneg_int_in_short_interval
    (Real.sqrt ((↑↑x : ℝ) ^ 11 - X)) (Real.sqrt ((↑↑x : ℝ) ^ 11 - 1))
    h_sqrt_le h_len h_sqrt_nn
  have h_fin := nonneg_int_short_interval_finite
    (Real.sqrt ((↑↑x : ℝ) ^ 11 - X)) (Real.sqrt ((↑↑x : ℝ) ^ 11 - 1))
    h_sqrt_le
  have h_le : (Nat.cast '' img : Set ℤ).ncard ≤ 1 :=
    le_trans (Set.ncard_le_ncard h_sub h_fin) h_ncard
  linarith

lemma E2_caseA_ncard (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    Set.ncard {y : ℤ | y ^ 2 ≤ (↑↑x : ℤ) ^ 11 - 1 ∧
      (((↑↑x : ℤ) ^ 11 - y ^ 2 : ℤ) : ℝ) ≤ X} ≤ 2 :=
    ncard_le_two_of_natAbs_image_le_one _ (E2_caseA_finite X hX x hx)
    (E2_caseA_abs_image_ncard X hX x hx)

lemma int_abs_le_ceil_sqrt (y : ℤ) (M : ℝ) (_hM : 0 ≤ M)
    (hy : (y : ℝ) ^ 2 ≤ M) :
    |y| ≤ ⌈Real.sqrt M⌉ := by
  rw [← @Int.cast_le ℝ]
  calc (↑|y| : ℝ) = |(↑y : ℝ)| := by rw [Int.cast_abs]
    _ ≤ Real.sqrt M := Real.abs_le_sqrt hy
    _ ≤ ↑⌈Real.sqrt M⌉ := Int.le_ceil _

lemma int_mem_Icc_ceil_sqrt_of_sq_le (y : ℤ) (M : ℝ) (_hM : 0 ≤ M)
    (hy : (y : ℝ) ^ 2 ≤ M) :
    y ∈ Set.Icc (-⌈Real.sqrt M⌉) (⌈Real.sqrt M⌉) := by
  rw [Set.mem_Icc]
  constructor
  · linarith [neg_abs_le y, int_abs_le_ceil_sqrt y M _hM hy]
  · exact le_trans (le_abs_self y) (int_abs_le_ceil_sqrt y M _hM hy)

lemma y_sq_le_x11_add_X_from_set (X : ℝ) (x : ℕ+) (y : ℤ)
    (h : ((y ^ 2 - (↑↑x : ℤ) ^ 11 : ℤ) : ℝ) ≤ X) :
    (y : ℝ) ^ 2 ≤ (↑↑x : ℝ) ^ 11 + X := by
  have h1 : (↑(y ^ 2 - (↑↑x : ℤ) ^ 11) : ℝ) = (y : ℝ) ^ 2 - (↑↑x : ℝ) ^ 11 := by push_cast; ring
  linarith [h1]

lemma E2_caseB_subset_Icc (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (_hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    {y : ℤ | (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2 ∧
      ((y ^ 2 - (↑↑x : ℤ) ^ 11 : ℤ) : ℝ) ≤ X} ⊆
    Set.Icc (-⌈Real.sqrt ((↑↑x : ℝ) ^ 11 + X)⌉) (⌈Real.sqrt ((↑↑x : ℝ) ^ 11 + X)⌉) := by
  intro y hy
  exact int_mem_Icc_ceil_sqrt_of_sq_le y _
    (add_nonneg (pow_nonneg (Nat.cast_nonneg' _) _) (by linarith))
    (y_sq_le_x11_add_X_from_set X x y hy.2)

lemma E2_caseB_finite (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    {y : ℤ | (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2 ∧
      ((y ^ 2 - (↑↑x : ℤ) ^ 11 : ℤ) : ℝ) ≤ X}.Finite :=
    Set.Finite.subset (Set.finite_Icc _ _) (E2_caseB_subset_Icc X hX x hx)

lemma sqrt_x11_add_one_gt_X (X : ℝ) (_hX_pos : 0 < X) (x_pow : ℝ)
    (hx_pow : x_pow > X ^ 2) :
    X < Real.sqrt (x_pow + 1) := Real.lt_sqrt_of_sq_lt (by linarith)

lemma sq_lt_xpow_add_X (X : ℝ) (_hX_pos : 0 < X) (x_pow : ℝ)
    (hx_pow : x_pow > X ^ 2) :
    X ^ 2 < x_pow + X := by
  grind

lemma sqrt_x11_add_X_gt_X (X : ℝ) (hX_pos : 0 < X) (x_pow : ℝ)
    (hx_pow : x_pow > X ^ 2) :
    X < Real.sqrt (x_pow + X) := Real.lt_sqrt_of_sq_lt (sq_lt_xpow_add_X X hX_pos x_pow hx_pow)

lemma denom_gt_two_X (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    Real.sqrt ((↑↑x : ℝ) ^ 11 + X) + Real.sqrt ((↑↑x : ℝ) ^ 11 + 1) > 2 * X := by
  have hx11 := x11_gt_X_sq X hX x hx
  linarith [sqrt_x11_add_one_gt_X X (by linarith) _ hx11,
            sqrt_x11_add_X_gt_X X (by linarith) _ hx11]

lemma X_sub_one_div_two_X_lt_one (X : ℝ) (hX : 2 < X) :
    (X - 1) / (2 * X) < 1 := by
  rw [div_lt_one (by linarith : (0 : ℝ) < 2 * X)]
  linarith

lemma caseB_interval_length_lt_one (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    Real.sqrt ((↑↑x : ℝ) ^ 11 + X) - Real.sqrt ((↑↑x : ℝ) ^ 11 + 1) < 1 := by
  have hx11_pos : (0 : ℝ) < (↑↑x : ℝ) ^ 11 := by positivity
  have h_a_pos : (0 : ℝ) < (↑↑x : ℝ) ^ 11 + X := by linarith
  have h_b_nonneg : (0 : ℝ) ≤ (↑↑x : ℝ) ^ 11 + 1 := by linarith
  have h_b_lt_a : (↑↑x : ℝ) ^ 11 + 1 < (↑↑x : ℝ) ^ 11 + X := by linarith
  rw [sqrt_sub_eq_div _ _ h_a_pos h_b_nonneg h_b_lt_a]
  rw [show (↑↑x : ℝ) ^ 11 + X - ((↑↑x : ℝ) ^ 11 + 1) = X - 1 by ring]
  have h_denom := denom_gt_two_X X hX x hx
  have h_X_sub_one_nonneg : (0 : ℝ) ≤ X - 1 := by linarith
  calc (X - 1) / (Real.sqrt ((↑↑x : ℝ) ^ 11 + X) + Real.sqrt ((↑↑x : ℝ) ^ 11 + 1))
      ≤ (X - 1) / (2 * X) := by
        apply div_le_div_of_nonneg_left h_X_sub_one_nonneg (by linarith) (le_of_lt h_denom)
    _ < 1 := X_sub_one_div_two_X_lt_one X hX

lemma caseB_lower_bound_cast_ineq (x : ℕ+) (y : ℤ)
    (h : (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2) :
    (↑↑x : ℝ) ^ 11 + 1 ≤ (y.natAbs : ℝ) ^ 2 := by
  rw [natAbs_sq_real]
  exact_mod_cast h

lemma caseB_lower_bound (x : ℕ+) (y : ℤ)
    (hy_lower : (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2) :
    Real.sqrt ((↑↑x : ℝ) ^ 11 + 1) ≤ (y.natAbs : ℝ) := by
  rw [Real.sqrt_le_left (Nat.cast_nonneg y.natAbs)]
  exact caseB_lower_bound_cast_ineq x y hy_lower

lemma caseB_upper_bound (X : ℝ) (x : ℕ+) (y : ℤ)
    (_hy_lower : (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2)
    (hy_upper : ((y ^ 2 - (↑↑x : ℤ) ^ 11 : ℤ) : ℝ) ≤ X) :
    (y.natAbs : ℝ) ≤ Real.sqrt ((↑↑x : ℝ) ^ 11 + X) := by
  have h_ysq : (y : ℝ) ^ 2 ≤ (↑↑x : ℝ) ^ 11 + X :=
    y_sq_le_x11_add_X_from_set X x y hy_upper
  have h_natAbs_sq : (y.natAbs : ℝ) ^ 2 = (y : ℝ) ^ 2 :=
    natAbs_sq_real y
  have h_sq_le : (y.natAbs : ℝ) ^ 2 ≤ (↑↑x : ℝ) ^ 11 + X := by
    rw [h_natAbs_sq]; exact h_ysq
  exact Real.le_sqrt_of_sq_le h_sq_le

lemma caseB_natAbs_bounds (X : ℝ) (x : ℕ+) (y : ℤ)
    (hy_lower : (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2)
    (hy_upper : ((y ^ 2 - (↑↑x : ℤ) ^ 11 : ℤ) : ℝ) ≤ X) :
    Real.sqrt ((↑↑x : ℝ) ^ 11 + 1) ≤ (y.natAbs : ℝ) ∧
    (y.natAbs : ℝ) ≤ Real.sqrt ((↑↑x : ℝ) ^ 11 + X) :=
  ⟨caseB_lower_bound x y hy_lower, caseB_upper_bound X x y hy_lower hy_upper⟩

lemma caseB_natAbs_image_subset (X : ℝ) (_hX : 2 < X) (x : ℕ+)
    (_hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    Int.natAbs '' {y : ℤ | (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2 ∧
      ((y ^ 2 - (↑↑x : ℤ) ^ 11 : ℤ) : ℝ) ≤ X} ⊆
    {n : ℕ | Real.sqrt ((↑↑x : ℝ) ^ 11 + 1) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ Real.sqrt ((↑↑x : ℝ) ^ 11 + X)} := by
  intro n hn
  obtain ⟨y, ⟨hy_lower, hy_upper⟩, rfl⟩ := hn
  exact caseB_natAbs_bounds X x y hy_lower hy_upper

lemma nat_image_subset_int_set (a b : ℝ) :
    (Nat.cast : ℕ → ℤ) '' {n : ℕ | (a : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ b} ⊆
    {n : ℤ | 0 ≤ n ∧ (a : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ b} := by
  rintro m ⟨n, ⟨ha, hb⟩, rfl⟩
  refine ⟨Int.natCast_nonneg n, ?_, ?_⟩
  · exact_mod_cast ha
  · exact_mod_cast hb

lemma ncard_nat_in_short_interval (a b : ℝ) (hab : a ≤ b) (hlen : b - a < 1)
    (ha : 0 ≤ a) :
    Set.ncard {n : ℕ | (a : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ b} ≤ 1 := by
  calc Set.ncard {n : ℕ | (a : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ b}
      = Set.ncard ((Nat.cast : ℕ → ℤ) '' {n : ℕ | (a : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ b}) :=
        (Set.ncard_image_of_injective _ Nat.cast_injective).symm
    _ ≤ Set.ncard {n : ℤ | 0 ≤ n ∧ (a : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ b} :=
        Set.ncard_le_ncard (nat_image_subset_int_set a b)
          (nonneg_int_short_interval_finite a b hab)
    _ ≤ 1 := ncard_nonneg_int_in_short_interval a b hab hlen ha

lemma caseB_nat_interval_subset_Iic (X : ℝ) (x : ℕ+) :
    {n : ℕ | Real.sqrt ((↑↑x : ℝ) ^ 11 + 1) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ Real.sqrt ((↑↑x : ℝ) ^ 11 + X)} ⊆
    {n : ℕ | n ≤ ⌈Real.sqrt ((↑↑x : ℝ) ^ 11 + X)⌉₊} := by
  intro n hn
  simp only [Set.mem_setOf_eq] at hn ⊢
  exact Nat.cast_le.mp (hn.2.trans (Nat.le_ceil _))

lemma caseB_nat_interval_finite (X : ℝ) (_hX : 2 < X) (x : ℕ+)
    (_hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    {n : ℕ | Real.sqrt ((↑↑x : ℝ) ^ 11 + 1) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ Real.sqrt ((↑↑x : ℝ) ^ 11 + X)}.Finite :=
  (Set.finite_le_nat _).subset (caseB_nat_interval_subset_Iic X x)

lemma E2_caseB_abs_image_ncard (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    Set.ncard (Int.natAbs '' {y : ℤ | (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2 ∧
      ((y ^ 2 - (↑↑x : ℤ) ^ 11 : ℤ) : ℝ) ≤ X}) ≤ 1 := by
  calc Set.ncard (Int.natAbs '' {y : ℤ | (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2 ∧
      ((y ^ 2 - (↑↑x : ℤ) ^ 11 : ℤ) : ℝ) ≤ X})
      ≤ Set.ncard {n : ℕ | Real.sqrt ((↑↑x : ℝ) ^ 11 + 1) ≤ (n : ℝ) ∧
          (n : ℝ) ≤ Real.sqrt ((↑↑x : ℝ) ^ 11 + X)} :=
        Set.ncard_le_ncard (caseB_natAbs_image_subset X hX x hx)
          (caseB_nat_interval_finite X hX x hx)
    _ ≤ 1 := ncard_nat_in_short_interval
          (Real.sqrt ((↑↑x : ℝ) ^ 11 + 1))
          (Real.sqrt ((↑↑x : ℝ) ^ 11 + X))
          (Real.sqrt_le_sqrt (by linarith))
          (caseB_interval_length_lt_one X hX x hx)
          (Real.sqrt_nonneg _)

lemma E2_caseB_finite_and_abs_image (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    let S := {y : ℤ | (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2 ∧
      ((y ^ 2 - (↑↑x : ℤ) ^ 11 : ℤ) : ℝ) ≤ X}
    S.Finite ∧ Set.ncard (Int.natAbs '' S) ≤ 1 := by
  intro S
  exact ⟨E2_caseB_finite X hX x hx, E2_caseB_abs_image_ncard X hX x hx⟩

lemma E2_caseB_ncard (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    Set.ncard {y : ℤ | (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2 ∧
      ((y ^ 2 - (↑↑x : ℤ) ^ 11 : ℤ) : ℝ) ≤ X} ≤ 2 := by
  have ⟨hfin, himg⟩ := E2_caseB_finite_and_abs_image X hX x hx
  exact ncard_le_two_of_natAbs_image_le_one _ hfin himg

lemma E2_cases_finite (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    Set.Finite (
      {y : ℤ | y ^ 2 ≤ (↑↑x : ℤ) ^ 11 - 1 ∧
        (((↑↑x : ℤ) ^ 11 - y ^ 2 : ℤ) : ℝ) ≤ X} ∪
      {y : ℤ | (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2 ∧
        ((y ^ 2 - (↑↑x : ℤ) ^ 11 : ℤ) : ℝ) ≤ X}) := by
  apply Set.Finite.union
  · exact E2_caseA_finite X hX x hx
  · exact (E2_caseB_finite_and_abs_image X hX x hx).1

lemma E2_fiber_bound (X : ℝ) (hX : 2 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    Set.ncard {y : ℤ | (x, y) ∈ E2Set X} ≤ 4 := by
  calc Set.ncard {y : ℤ | (x, y) ∈ E2Set X}
      ≤ Set.ncard (
        {y : ℤ | y ^ 2 ≤ (↑↑x : ℤ) ^ 11 - 1 ∧
          (((↑↑x : ℤ) ^ 11 - y ^ 2 : ℤ) : ℝ) ≤ X} ∪
        {y : ℤ | (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2 ∧
          ((y ^ 2 - (↑↑x : ℤ) ^ 11 : ℤ) : ℝ) ≤ X}) :=
      Set.ncard_le_ncard (E2_fiber_subset_union X hX x hx) (E2_cases_finite X hX x hx)
    _ ≤ Set.ncard {y : ℤ | y ^ 2 ≤ (↑↑x : ℤ) ^ 11 - 1 ∧
          (((↑↑x : ℤ) ^ 11 - y ^ 2 : ℤ) : ℝ) ≤ X} +
        Set.ncard {y : ℤ | (↑↑x : ℤ) ^ 11 + 1 ≤ y ^ 2 ∧
          ((y ^ 2 - (↑↑x : ℤ) ^ 11 : ℤ) : ℝ) ≤ X} := Set.ncard_union_le _ _
    _ ≤ 2 + 2 := Nat.add_le_add (E2_caseA_ncard X hX x hx) (E2_caseB_ncard X hX x hx)
    _ = 4 := by norm_num
namespace E2XBoundHelpers

lemma denom_pos (ε : ℝ) (hε1 : 0 < ε) (hε3 : ε ≤ 1 / 10) :
    (0 : ℝ) < 9 - 13 * ε := show 0 < 9 - 13 * ε from by linarith

lemma cleared_ineq (η ε : ℝ) (hη : 0 < η)
    (hε1 : 0 < ε) (hε2 : ε ≤ η / 4) (hε3 : ε ≤ 1 / 10) :
    (4 : ℝ) + 2 * ε < (4 / 9 + η) * (9 - 13 * ε) := by
  nlinarith [sq_nonneg (ε - 9 / 70), sq_nonneg (η - 4 * ε),
    mul_nonneg hε1.le hη.le, mul_nonneg hε1.le (sub_nonneg.mpr hε2),
    mul_nonneg hε1.le (sub_nonneg.mpr hε3)]

lemma X_lt_X_sq (X : ℝ) (hX : 1 < X) : X < X ^ (2 : ℕ) := by
  have h : X < X ^ 2 := by
    have h₁ : X ^ 2 - X > 0 := by
      rw [show X ^ 2 - X = X * (X - 1) by ring]
      have h₃ : X - 1 > 0 := by linarith
      have h₅ : X * (X - 1) > 0 := by positivity
      linarith
    linarith
  simpa [pow_two] using h

lemma x11_pow_gt_X (x : ℕ+) (X : ℝ) (hX : 1 < X)
    (hx_lower : (x : ℝ) > X ^ ((2 : ℝ) / 11)) :
    (↑↑x : ℝ) ^ (11 : ℕ) > X := by
  have hX0 : 0 < X := by linarith
  have h1 : (X ^ ((2 : ℝ) / 11)) ^ (11 : ℕ) < (↑↑x : ℝ) ^ 11 :=
    pow_eleven_strict_mono X hX0 x hx_lower
  have h2 : (X ^ ((2 : ℝ) / 11)) ^ (11 : ℕ) = X ^ (2 : ℕ) :=
    rpow_two_eleven_eq_sq X hX0
  have h3 : X < X ^ (2 : ℕ) := X_lt_X_sq X hX
  linarith

lemma y_ne_zero_of_E2
    (x : ℕ+) (y : ℤ) (X : ℝ) (hX : 1 < X)
    (hx_lower : (x : ℝ) > X ^ ((2 : ℝ) / 11))
    (habs_pos : 1 ≤ |(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2|)
    (habs_le : (|(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X) :
    y ≠ 0 := by
  intro hy
  subst hy
  have h1 : (↑↑x : ℝ) ^ (11 : ℕ) > X := x11_pow_gt_X x X hX hx_lower
  rw [show (|(↑(x : ℕ) : ℤ) ^ 11 - (0 : ℤ) ^ 2| : ℝ) = (↑↑x : ℝ) ^ 11 from by norm_num] at habs_le
  linarith

lemma radical_mul_le (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Nat.radical (m * n) ≤ Nat.radical m * Nat.radical n := by
  have hm' : m ≠ 0 := ne_of_gt hm
  have hn' : n ≠ 0 := ne_of_gt hn
  have hmn' : m * n ≠ 0 := Nat.mul_ne_zero hm' hn'
  simp only [Nat.radical, hmn', ↓reduceIte, hm', hn']
  exact radical_mul_le_aux m n hm hn

lemma radical_abc_bound (x : ℕ) (Y B : ℕ) (hx : 0 < x) (hY : 0 < Y) (hB : 0 < B) :
    (Nat.radical (Y ^ 2 * B * (x ^ 11)) : ℝ) ≤ (Y : ℝ) * (B : ℝ) * (x : ℝ) := by
  have h : (Y ^ 2 * B * x ^ 11).radical ≤ Y * B * x := by
    calc Nat.radical (Y ^ 2 * B * x ^ 11)
        _ ≤ Nat.radical (Y ^ 2 * B) * Nat.radical (x ^ 11) :=
            radical_mul_le _ _ (by positivity) (by positivity)
        _ ≤ (Nat.radical (Y ^ 2) * Nat.radical B) * Nat.radical (x ^ 11) :=
            Nat.mul_le_mul_right _ (radical_mul_le _ _ (by positivity) hB)
        _ = (Nat.radical Y * Nat.radical B) * Nat.radical x := by
            rw [radical_pow Y 2 hY (by norm_num), radical_pow x 11 hx (by norm_num)]
        _ ≤ (Y * B) * x :=
            Nat.mul_le_mul (Nat.mul_le_mul (radical_le_self Y hY) (radical_le_self B hB))
              (radical_le_self x hx)
        _ = Y * B * x := by ring
  calc (Nat.radical (Y ^ 2 * B * x ^ 11) : ℝ) ≤ (Y * B * x : ℕ) := by exact_mod_cast h
    _ = (Y : ℝ) * (B : ℝ) * (x : ℝ) := by push_cast; ring

lemma radical_abc_bound'_nat (x : ℕ) (Y B : ℕ) (hx : 0 < x) (hY : 0 < Y) (hB : 0 < B) :
    Nat.radical (x ^ 11 * B * (Y ^ 2)) ≤ x * B * Y := by
  calc Nat.radical (x ^ 11 * B * (Y ^ 2))
      _ ≤ Nat.radical (x ^ 11 * B) * Nat.radical (Y ^ 2) :=
          radical_mul_le _ _ (by positivity) (by positivity)
      _ ≤ (Nat.radical (x ^ 11) * Nat.radical B) * Nat.radical (Y ^ 2) :=
          Nat.mul_le_mul_right _ (radical_mul_le _ _ (by positivity) hB)
      _ = (Nat.radical x * Nat.radical B) * Nat.radical Y := by
          rw [radical_pow x 11 hx (by norm_num), radical_pow Y 2 hY (by norm_num)]
      _ ≤ (x * B) * Y :=
          Nat.mul_le_mul (Nat.mul_le_mul (radical_le_self x hx) (radical_le_self B hB))
            (radical_le_self Y hY)
      _ = x * B * Y := by ring

lemma radical_abc_bound' (x : ℕ) (Y B : ℕ) (hx : 0 < x) (hY : 0 < Y) (hB : 0 < B) :
    (Nat.radical (x ^ 11 * B * (Y ^ 2)) : ℝ) ≤ (x : ℝ) * (B : ℝ) * (Y : ℝ) := by
  have h := radical_abc_bound'_nat x Y B hx hY hB
  exact_mod_cast h

lemma abc_triple_sum_case1
    (x : ℕ+) (y : ℤ)
    (hge : (↑(x : ℕ) : ℤ) ^ 11 ≥ y ^ 2) :
    (Int.natAbs y) ^ 2 + Int.natAbs ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2) = (x : ℕ) ^ 11 := by
  have hsub_nonneg : 0 ≤ (↑(x : ℕ) : ℤ) ^ 11 - y ^ 2 := by linarith
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_add, Nat.cast_pow]
  rw [abs_of_nonneg hsub_nonneg, sq_abs]
  ring

lemma natAbs_pos_of_ne_zero (y : ℤ) (hy : y ≠ 0) : 0 < Int.natAbs y := by
  have h : y ≠ 0 := hy
  have h₁ : 0 < Int.natAbs y := by
    apply Int.natAbs_pos.mpr
    exact (by
      intro h₂
      apply h
      simp_all)
  exact h₁

lemma B_nat_pos
    (x : ℕ+) (y : ℤ)
    (habs_pos : 1 ≤ |(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2|) :
    0 < Int.natAbs ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2) := by
  have h₂ : 0 < Int.natAbs ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2) := by
    linarith
  exact h₂

lemma natAbs_cast_le_X
    (x : ℕ+) (y : ℤ) (X : ℝ)
    (habs_le : (|(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X)
    (_hge : (↑(x : ℕ) : ℤ) ^ 11 ≥ y ^ 2) :
    (Int.natAbs ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2) : ℝ) ≤ X := by simp_all

lemma gcd_le_natAbs
    (x : ℕ+) (y : ℤ)
    (hpos : 0 < ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2).natAbs) :
    Nat.gcd ((Int.natAbs y) ^ 2) ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2).natAbs ≤
    ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2).natAbs := by exact Nat.gcd_le_right (y.natAbs ^ 2) hpos

lemma gcd_le_X_case1
    (x : ℕ+) (y : ℤ) (X : ℝ)
    (habs_pos : 1 ≤ |(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2|)
    (habs_le : (|(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X)
    (hge : (↑(x : ℕ) : ℤ) ^ 11 ≥ y ^ 2) :
    (Nat.gcd ((Int.natAbs y) ^ 2) (Int.natAbs ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2)) : ℝ) ≤ X := by
  have hBpos : 0 < ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2).natAbs := B_nat_pos x y habs_pos
  have h1 : Nat.gcd ((Int.natAbs y) ^ 2) ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2).natAbs ≤
    ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2).natAbs := gcd_le_natAbs x y hBpos
  have h2 : (Int.natAbs ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2) : ℝ) ≤ X :=
    natAbs_cast_le_X x y X habs_le hge
  exact le_trans (Nat.cast_le.mpr h1) h2

lemma rad_bound_le_case1
    (x : ℕ+) (y : ℤ) (X : ℝ)
    (habs_le : (|(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X)
    (_hge : (↑(x : ℕ) : ℤ) ^ 11 ≥ y ^ 2) :
    (Int.natAbs y : ℝ) * (Int.natAbs ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2) : ℝ) * (x : ℝ)
      ≤ (x : ℝ) * (Int.natAbs y : ℝ) * X := by
  have hz : (Int.natAbs ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2) : ℝ) ≤ X := by
    simp only [Nat.cast_natAbs, Int.cast_abs]
    exact_mod_cast habs_le
  calc (Int.natAbs y : ℝ) * (Int.natAbs ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2) : ℝ) * (x : ℝ)
      ≤ (Int.natAbs y : ℝ) * X * (x : ℝ) := by gcongr
    _ = (x : ℝ) * (Int.natAbs y : ℝ) * X := by ring

lemma chain_bound_case1 (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε)
    (x : ℕ+) (y : ℤ) (X : ℝ) (hX : 1 < X)
    (h_abc : ((x : ℕ) ^ 11 : ℝ) ≤ X * K *
      ((Int.natAbs y : ℝ) * (Int.natAbs ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2) : ℝ) * (x : ℝ)) ^ (1 + ε))
    (h_rad_le : (Int.natAbs y : ℝ) * (Int.natAbs ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2) : ℝ) * (x : ℝ)
      ≤ (x : ℝ) * (Int.natAbs y : ℝ) * X) :
    (x : ℝ) ^ 11 ≤ K * X * ((x : ℝ) * (Int.natAbs y : ℝ) * X) ^ (1 + ε) := by
  have hcast : ((x : ℕ) ^ 11 : ℝ) = (x : ℝ) ^ 11 := by norm_cast
  rw [hcast] at h_abc
  refine le_trans h_abc ?_
  rw [mul_comm X K]
  gcongr

lemma abc_case_x11_ge_y2 (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε)
    (habc_ineq : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    (x : ℕ+) (y : ℤ) (X : ℝ) (hX : 1 < X)
    (hy_ne : y ≠ 0)
    (habs_pos : 1 ≤ |(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2|)
    (habs_le : (|(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X)
    (hge : (↑(x : ℕ) : ℤ) ^ 11 ≥ y ^ 2) :
    (x : ℝ) ^ 11 ≤ K * X * ((x : ℝ) * (Int.natAbs y : ℝ) * X) ^ (1 + ε) := by
  have hY_pos : 0 < Int.natAbs y := natAbs_pos_of_ne_zero y hy_ne
  have hB_pos : 0 < Int.natAbs ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2) := B_nat_pos x y habs_pos
  have hx_pos : 0 < (x : ℕ) := x.pos
  have hx11_pos : 0 < (x : ℕ) ^ 11 := Nat.pos_of_ne_zero (by positivity)
  have hsum := abc_triple_sum_case1 x y hge
  have h_abc := abc_triple_to_bound K hK ε hε habc_ineq
    ((Int.natAbs y) ^ 2)
    (Int.natAbs ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2))
    ((x : ℕ) ^ 11)
    (by positivity) hB_pos hx11_pos
    hsum
    X (gcd_le_X_case1 x y X habs_pos habs_le hge)
    ((Int.natAbs y : ℝ) * (Int.natAbs ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2) : ℝ) * (x : ℝ))
    (radical_abc_bound (x : ℕ) (Int.natAbs y)
      (Int.natAbs ((↑(x : ℕ) : ℤ) ^ 11 - y ^ 2)) hx_pos hY_pos hB_pos)
    (by positivity)
  exact chain_bound_case1 K hK ε hε x y X hX
    (by exact_mod_cast h_abc)
    (rad_bound_le_case1 x y X habs_le hge)

lemma x11_le_natAbs_sq (x : ℕ+) (y : ℤ)
    (hlt : (↑(x : ℕ) : ℤ) ^ 11 < y ^ 2) :
    (x : ℕ) ^ 11 ≤ y.natAbs ^ 2 := by
  have h1 : (↑((x : ℕ) ^ 11) : ℤ) < ↑(y.natAbs ^ 2) := by
    rw [Nat.cast_pow, Nat.cast_pow, Int.natAbs_sq y]
    exact hlt
  exact_mod_cast h1.le

lemma B_pos_of_x11_lt_y2 (x : ℕ+) (y : ℤ)
    (hlt : (↑(x : ℕ) : ℤ) ^ 11 < y ^ 2) :
    0 < y.natAbs ^ 2 - (x : ℕ) ^ 11 := by
  apply Nat.sub_pos_of_lt
  rw [← Int.natAbs_sq y] at hlt
  exact_mod_cast hlt

lemma abc_sum_eq_of_x11_lt_y2 (x : ℕ+) (y : ℤ)
    (hlt : (↑(x : ℕ) : ℤ) ^ 11 < y ^ 2) :
    (x : ℕ) ^ 11 + (y.natAbs ^ 2 - (x : ℕ) ^ 11) = y.natAbs ^ 2 := by
  have h₁ : (x : ℕ) ^ 11 ≤ y.natAbs ^ 2 := x11_le_natAbs_sq x y hlt
  omega

lemma gcd_le_B (x : ℕ+) (y : ℤ)
    (hlt : (↑(x : ℕ) : ℤ) ^ 11 < y ^ 2) :
    (Nat.gcd ((x : ℕ) ^ 11) (y.natAbs ^ 2 - (x : ℕ) ^ 11) : ℝ) ≤
      (y.natAbs ^ 2 - (x : ℕ) ^ 11 : ℕ) := by
  have hB_pos := B_pos_of_x11_lt_y2 x y hlt
  exact_mod_cast Nat.le_of_dvd hB_pos (Nat.gcd_dvd_right _ _)

lemma abs_int_sub_eq_reverse (x : ℕ+) (y : ℤ)
    (hlt : (↑(x : ℕ) : ℤ) ^ 11 < y ^ 2) :
    |(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2| = y ^ 2 - (↑(x : ℕ) : ℤ) ^ 11 := by grind

lemma abs_eq_reverse_sub_real (x : ℕ+) (y : ℤ)
    (hlt : (↑(x : ℕ) : ℤ) ^ 11 < y ^ 2) :
    (|(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2| : ℝ) = ((y ^ 2 - (↑(x : ℕ) : ℤ) ^ 11 : ℤ) : ℝ) := by
  exact_mod_cast abs_int_sub_eq_reverse x y hlt

lemma B_cast_le_X (x : ℕ+) (y : ℤ) (X : ℝ)
    (habs_le : (|(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X)
    (hlt : (↑(x : ℕ) : ℤ) ^ 11 < y ^ 2) :
    (↑(y.natAbs ^ 2 - (x : ℕ) ^ 11) : ℝ) ≤ X := by
  have hle := x11_le_natAbs_sq x y hlt
  have h_abs_eq := abs_eq_reverse_sub_real x y hlt
  have h_sq := natAbs_cast_sq_eq y
  have h1 : (↑(y.natAbs ^ 2 - (x : ℕ) ^ 11) : ℝ) =
    ((y.natAbs : ℤ) : ℝ) ^ 2 - ((x : ℕ) : ℝ) ^ 11 := by
      rw [show (↑(y.natAbs ^ 2 - (x : ℕ) ^ 11) : ℝ) =
        ((↑(y.natAbs ^ 2 - (x : ℕ) ^ 11) : ℤ) : ℝ) from by push_cast; ring]
      rw [Nat.cast_sub hle]
      push_cast; ring
  rw [h1, h_sq]
  rw [show ((y ^ 2 : ℤ) : ℝ) - ((x : ℕ) : ℝ) ^ 11 =
    ((y ^ 2 - (↑(x : ℕ) : ℤ) ^ 11 : ℤ) : ℝ) from by push_cast; ring]
  rw [← h_abs_eq]
  exact habs_le

lemma rad_bound_le (x : ℕ+) (y : ℤ) (X : ℝ)
    (habs_le : (|(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X)
    (hlt : (↑(x : ℕ) : ℤ) ^ 11 < y ^ 2) :
    (↑(x : ℕ) : ℝ) * (↑(y.natAbs ^ 2 - (x : ℕ) ^ 11) : ℝ) * (↑y.natAbs : ℝ) ≤
      (↑(x : ℕ) : ℝ) * (↑y.natAbs : ℝ) * X := by
  have hB : (↑(y.natAbs ^ 2 - (x : ℕ) ^ 11) : ℝ) ≤ X := B_cast_le_X x y X habs_le hlt
  have hx_pos : (0 : ℝ) ≤ (↑(x : ℕ) : ℝ) := Nat.cast_nonneg _
  have hy_pos : (0 : ℝ) ≤ (↑y.natAbs : ℝ) := Nat.cast_nonneg _
  calc (↑(x : ℕ) : ℝ) * (↑(y.natAbs ^ 2 - (x : ℕ) ^ 11) : ℝ) * (↑y.natAbs : ℝ)
      = (↑(x : ℕ) : ℝ) * (↑y.natAbs : ℝ) * (↑(y.natAbs ^ 2 - (x : ℕ) ^ 11) : ℝ) := by ring
    _ ≤ (↑(x : ℕ) : ℝ) * (↑y.natAbs : ℝ) * X := by
        apply mul_le_mul_of_nonneg_left hB
        exact mul_nonneg hx_pos hy_pos

lemma x11_le_y2_real (x : ℕ+) (y : ℤ)
    (hlt : (↑(x : ℕ) : ℤ) ^ 11 < y ^ 2) :
    (x : ℝ) ^ 11 ≤ (↑(y.natAbs ^ 2) : ℝ) := by
  have h_nat := x11_le_natAbs_sq x y hlt
  exact_mod_cast h_nat

lemma rad_bound_nonneg (x : ℕ+) (y : ℤ) (X : ℝ) (hX : 1 < X) :
    0 ≤ (↑(x : ℕ) : ℝ) * (↑y.natAbs : ℝ) * X := by positivity

lemma abc_case_x11_lt_y2 (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε)
    (habc_ineq : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    (x : ℕ+) (y : ℤ) (X : ℝ) (hX : 1 < X)
    (hy_ne : y ≠ 0)
    (_habs_pos : 1 ≤ |(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2|)
    (habs_le : (|(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X)
    (hlt : (↑(x : ℕ) : ℤ) ^ 11 < y ^ 2) :
    (x : ℝ) ^ 11 ≤ K * X * ((x : ℝ) * (Int.natAbs y : ℝ) * X) ^ (1 + ε) := by
  set A := (x : ℕ) ^ 11
  set Y := y.natAbs
  set B := Y ^ 2 - A
  have hA_pos : 0 < A := Nat.pos_of_ne_zero (by positivity)
  have hB_pos : 0 < B := B_pos_of_x11_lt_y2 x y hlt
  have hY_pos : 0 < Y := by positivity
  have hC_pos : 0 < Y ^ 2 := by positivity
  have hsum : A + B = Y ^ 2 := abc_sum_eq_of_x11_lt_y2 x y hlt
  have hgcd_le : (Nat.gcd A B : ℝ) ≤ (B : ℝ) := gcd_le_B x y hlt
  have hB_le_X : (B : ℝ) ≤ X := B_cast_le_X x y X habs_le hlt
  have hgcd_le_X : (Nat.gcd A B : ℝ) ≤ X := le_trans hgcd_le hB_le_X
  have hrad : (Nat.radical (A * B * Y ^ 2) : ℝ) ≤ (x : ℝ) * (B : ℝ) * (Y : ℝ) :=
    radical_abc_bound' (x : ℕ) Y B x.pos hY_pos hB_pos
  have hrad_le : (x : ℝ) * (B : ℝ) * (Y : ℝ) ≤ (x : ℝ) * (Y : ℝ) * X :=
    rad_bound_le x y X habs_le hlt
  have hrad_final : (Nat.radical (A * B * Y ^ 2) : ℝ) ≤ (x : ℝ) * (Y : ℝ) * X :=
    le_trans hrad hrad_le
  have hrad_nn : 0 ≤ (x : ℝ) * (Y : ℝ) * X := rad_bound_nonneg x y X hX
  have hC_bound : (↑(Y ^ 2) : ℝ) ≤ X * K * ((x : ℝ) * (Y : ℝ) * X) ^ (1 + ε) :=
    abc_triple_to_bound K hK ε hε habc_ineq A B (Y ^ 2) hA_pos hB_pos hC_pos
      hsum X hgcd_le_X ((x : ℝ) * (Y : ℝ) * X) hrad_final hrad_nn
  have hx11_le : (x : ℝ) ^ 11 ≤ (↑(Y ^ 2) : ℝ) := x11_le_y2_real x y hlt
  calc (x : ℝ) ^ 11
      ≤ (↑(Y ^ 2) : ℝ) := hx11_le
    _ ≤ X * K * ((x : ℝ) * (↑Y : ℝ) * X) ^ (1 + ε) := hC_bound
    _ = K * X * ((x : ℝ) * (↑Y : ℝ) * X) ^ (1 + ε) := by ring

lemma abc_gives_x11_bound (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε)
    (habc_ineq : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    (x : ℕ+) (y : ℤ) (X : ℝ) (hX : 1 < X)
    (hx_lower : (x : ℝ) > X ^ ((2 : ℝ) / 11))
    (habs_pos : 1 ≤ |(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2|)
    (habs_le : (|(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X) :
    (x : ℝ) ^ 11 ≤ K * X * ((x : ℝ) * (Int.natAbs y : ℝ) * X) ^ (1 + ε) := by
  have hy_ne := y_ne_zero_of_E2 x y X hX hx_lower habs_pos habs_le
  rcases le_or_gt (y ^ 2) ((↑(x : ℕ) : ℤ) ^ 11) with hge | hgt
  · exact abc_case_x11_ge_y2 K hK ε hε habc_ineq x y X hX hy_ne habs_pos habs_le hge
  · exact abc_case_x11_lt_y2 K hK ε hε habc_ineq x y X hX hy_ne habs_pos habs_le hgt

lemma y_sq_le_x11_add_X (x : ℕ+) (y : ℤ) (X : ℝ)
    (habs_le : (|(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X) :
    (y : ℝ) ^ 2 ≤ (↑↑x : ℝ) ^ (11 : ℕ) + X := by
  have habs_real : (|(↑(x : ℕ) : ℝ) ^ 11 - (y : ℝ) ^ 2| : ℝ) ≤ X := by
    rw [show (|(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2| : ℝ) = (|(↑(x : ℕ) : ℝ) ^ 11 - (y : ℝ) ^ 2| : ℝ)
      from by norm_cast] at habs_le
    exact habs_le
  have h_split := (abs_sub_le_iff.mp habs_real)
  linarith [h_split.2]

lemma natAbs_y_sq_le_two_mul_x11 (x : ℕ+) (y : ℤ) (X : ℝ) (hX : 1 < X)
    (hx_lower : (x : ℝ) > X ^ ((2 : ℝ) / 11))
    (habs_le : (|(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X) :
    ((Int.natAbs y : ℕ) : ℝ) ^ 2 ≤ 2 * (↑↑x : ℝ) ^ (11 : ℕ) := by
  have hx11_gt_X := x11_pow_gt_X x X hX hx_lower
  have hy_sq_le := y_sq_le_x11_add_X x y X habs_le
  have hnatabs : ((Int.natAbs y : ℕ) : ℝ) ^ 2 = (y : ℝ) ^ 2 := by
    have h1 : ((Int.natAbs y : ℕ) : ℝ) = |((y : ℤ) : ℝ)| := by
      exact_mod_cast Nat.cast_natAbs y
    rw [h1, sq_abs]
  rw [hnatabs]
  linarith

lemma sqrt_two_mul_x11_eq (x : ℕ+) :
    Real.sqrt (2 * (↑↑x : ℝ) ^ (11 : ℕ)) = Real.sqrt 2 * (↑↑x : ℝ) ^ ((11 : ℝ) / 2) := by
  rw [Real.sqrt_mul (by positivity)]
  congr 1
  rw [Real.sqrt_eq_rpow,
    show ((↑↑x : ℝ) ^ (11 : ℕ) : ℝ) = (↑↑x : ℝ) ^ (11 : ℝ) from by norm_cast,
    ← Real.rpow_mul (by positivity)]
  norm_num

lemma natAbs_le_sqrt_of_sq_le (y : ℤ) (b : ℝ)
    (_hb : 0 ≤ b) (h : ((Int.natAbs y : ℕ) : ℝ) ^ 2 ≤ b) :
    (Int.natAbs y : ℝ) ≤ Real.sqrt b := by
  have hnn : (0 : ℝ) ≤ ((Int.natAbs y : ℕ) : ℝ) := by positivity
  rw [← Real.sqrt_sq hnn]
  exact Real.sqrt_le_sqrt h

lemma Y_bound_from_E2 (x : ℕ+) (y : ℤ) (X : ℝ) (hX : 1 < X)
    (hx_lower : (x : ℝ) > X ^ ((2 : ℝ) / 11))
    (_habs_pos : 1 ≤ |(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2|)
    (habs_le : (|(↑(x : ℕ) : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X) :
    (Int.natAbs y : ℝ) ≤ Real.sqrt 2 * (x : ℝ) ^ ((11 : ℝ) / 2) := by
  have hsq := natAbs_y_sq_le_two_mul_x11 x y X hX hx_lower habs_le
  have hle := natAbs_le_sqrt_of_sq_le y (2 * (↑↑x : ℝ) ^ (11 : ℕ)) (by positivity) hsq
  rw [sqrt_two_mul_x11_eq] at hle
  exact hle

lemma combine_bounds_to_x_bound (K : ℝ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 9 / 13)
    (x : ℕ+) (X : ℝ) (hX : 1 < X) (Y : ℝ) (hY : 0 ≤ Y)
    (h_x11 : (x : ℝ) ^ 11 ≤ K * X * ((x : ℝ) * Y * X) ^ (1 + ε))
    (h_Y : Y ≤ Real.sqrt 2 * (x : ℝ) ^ ((11 : ℝ) / 2)) :
    (x : ℝ) ≤ (K * Real.sqrt 2 ^ (1 + ε)) ^ ((2 : ℝ) / (9 - 13 * ε)) *
      X ^ (((4 : ℝ) + 2 * ε) / (9 - 13 * ε)) := by
  have step1 := substitute_Y_bound K hK ε hε x X hX Y hY h_x11 h_Y
  have step2 := isolate_x_power K hK ε hε hε' x X hX step1
  exact raise_to_reciprocal_power K hK ε hε hε' x X hX step2

lemma cx_pos (K : ℝ) (hK : 0 < K) (ε : ℝ) (_hε : 0 < ε) (_hε' : ε < 9 / 13) :
    0 < (K * Real.sqrt 2 ^ (1 + ε)) ^ ((2 : ℝ) / (9 - 13 * ε)) := by
  have h₁ : 0 < K * Real.sqrt 2 ^ (1 + ε) := show 0 < K * Real.sqrt 2 ^ (1 + ε) from by positivity
  have h₄ : 0 < (K * Real.sqrt 2 ^ (1 + ε)) ^ ((2 : ℝ) / (9 - 13 * ε)) := by
    apply Real.rpow_pos_of_pos h₁ _
  exact h₄

lemma E2_x_bound_from_abc (habc : ABC) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 9 / 13) :
    ∃ Cx : ℝ, 0 < Cx ∧ ∃ X₁ : ℝ, 0 < X₁ ∧
      ∀ X : ℝ, X₁ < X →
        ∀ p : ℕ+ × ℤ, p ∈ E2Set X →
          (p.1 : ℝ) ≤ Cx * X ^ (((4 : ℝ) + 2 * ε) / (9 - 13 * ε)) := by
  obtain ⟨K, hK, habc_ineq⟩ := habc ε hε
  refine ⟨(K * Real.sqrt 2 ^ (1 + ε)) ^ ((2 : ℝ) / (9 - 13 * ε)),
    cx_pos K hK ε hε hε', 1, one_pos, ?_⟩
  intro X hX p hp
  obtain ⟨hx_lower, habs_pos, habs_le⟩ := hp
  have hY := Y_bound_from_E2 p.1 p.2 X hX hx_lower habs_pos habs_le
  have h_x11 := abc_gives_x11_bound K hK ε hε habc_ineq p.1 p.2 X hX
    hx_lower habs_pos habs_le
  exact combine_bounds_to_x_bound K hK ε hε hε' p.1 X hX
    (Int.natAbs p.2 : ℝ) (Nat.cast_nonneg _) h_x11 hY
end E2XBoundHelpers

lemma E2_x_bound_from_abc (habc : ABC) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 9 / 13) :
    ∃ Cx : ℝ, 0 < Cx ∧ ∃ X₁ : ℝ, 0 < X₁ ∧
      ∀ X : ℝ, X₁ < X →
        ∀ p : ℕ+ × ℤ, p ∈ E2Set X →
          (p.1 : ℝ) ≤ Cx * X ^ (((4 : ℝ) + 2 * ε) / (9 - 13 * ε)) :=
  E2XBoundHelpers.E2_x_bound_from_abc habc ε hε hε'

private lemma denom_pos (ε : ℝ) (_hε1 : 0 < ε) (hε3 : ε ≤ 1 / 10) :
    (0 : ℝ) < 9 - 13 * ε := by linarith

private lemma cleared_ineq (η ε : ℝ) (hη : 0 < η)
    (hε1 : 0 < ε) (hε2 : ε ≤ η / 4) (hε3 : ε ≤ 1 / 10) :
    (4 : ℝ) + 2 * ε < (4 / 9 + η) * (9 - 13 * ε) := by
  nlinarith [sq_nonneg (ε - 9 / 70), sq_nonneg (η - 4 * ε),
    mul_nonneg hε1.le hη.le, mul_nonneg hε1.le (sub_nonneg.mpr hε2),
    mul_nonneg hε1.le (sub_nonneg.mpr hε3)]

lemma exponent_comparison_strict (η ε : ℝ) (hη : 0 < η)
    (hε1 : 0 < ε) (hε2 : ε ≤ η / 4) (hε3 : ε ≤ 1 / 10) :
    ((4 : ℝ) + 2 * ε) / (9 - 13 * ε) < 4 / 9 + η := by
  have h_denom : (0 : ℝ) < 9 - 13 * ε := denom_pos ε hε1 hε3
  rw [div_lt_iff₀ h_denom]
  exact cleared_ineq η ε hη hε1 hε2 hε3

namespace E2NcardHelpers

/-
MATHLIB COVERAGE:
- Finiteness of E2Set: needs helper; bounded subsets of ℕ+ × ℤ are finite
  when x-coords bounded and y-coords bounded by a function of x.
  Relevant: `Set.Finite.subset`, `Set.Finite.prod`
- Fiber counting: `Set.ncard_le_ncard` for subset bounds,
  `Set.Finite.ncard_biUnion_le` for biUnion decomposition
- Floor bound: `Nat.floor_le : 0 ≤ a → ↑⌊a⌋₊ ≤ a`
- Cast: `Nat.cast_le` for ℕ → ℝ monotonicity
-/

lemma pnat_bounded_finite (B : ℝ) (_hB : 0 < B) :
    {x : ℕ+ | (x : ℝ) ≤ B}.Finite :=
  _root_.pnat_bounded_finite B

lemma y_sq_le_real_of_E2_cond (x : ℕ+) (y : ℤ) (X : ℝ)
    (h2 : (|(↑↑x : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X) :
    (y : ℝ) ^ 2 ≤ (↑↑x : ℝ) ^ 11 + X := by
  have h3 : (|(↑↑x : ℤ) ^ 11 - y ^ 2| : ℝ) = (|(↑↑x : ℝ) ^ 11 - (y : ℝ) ^ 2| : ℝ) := by
    simp [abs_sub_comm]
  have h4 : (|(↑↑x : ℝ) ^ 11 - (y : ℝ) ^ 2| : ℝ) ≤ X := by
    rw [← h3]
    exact h2
  have h5 : (y : ℝ) ^ 2 ≤ (↑↑x : ℝ) ^ 11 + X := by
    have h6 : (|(↑↑x : ℝ) ^ 11 - (y : ℝ) ^ 2| : ℝ) ≤ X := h4
    have h9 : (y : ℝ) ^ 2 - (↑↑x : ℝ) ^ 11 ≤ X := by
      linarith [abs_le.mp h6]
    linarith
  exact h5

lemma pnatLe_ceil_of_le (x : ℕ+) (B : ℝ) (_hB : 0 < B) (hx : (x : ℝ) ≤ B) :
    (x : ℕ) ≤ ⌈B⌉₊ := by
  have h_ceil : (B : ℝ) ≤ ⌈B⌉₊ := Nat.le_ceil B
  have h_x_le_ceil : (x : ℝ) ≤ (⌈B⌉₊ : ℝ) := by
    calc
      (x : ℝ) ≤ B := hx
      _ ≤ (⌈B⌉₊ : ℝ) := by exact_mod_cast h_ceil
  have h_main : (x : ℕ) ≤ ⌈B⌉₊ := by
    norm_cast at h_x_le_ceil ⊢
  exact h_main

lemma y_sq_le_ceil_pow_add (x : ℕ+) (y : ℤ) (X B : ℝ) (hB : 0 < B)
    (hx_le_B : (x : ℝ) ≤ B)
    (hy_sq : (y : ℝ) ^ 2 ≤ (↑↑x : ℝ) ^ 11 + X) :
    (y : ℝ) ^ 2 ≤ (↑⌈B⌉₊ : ℝ) ^ 11 + X := by
  have hxN : (x : ℕ) ≤ ⌈B⌉₊ := pnatLe_ceil_of_le x B hB hx_le_B
  have hxR : (↑↑x : ℝ) ≤ (↑⌈B⌉₊ : ℝ) := by exact_mod_cast hxN
  have hpow : (↑↑x : ℝ) ^ 11 ≤ (↑⌈B⌉₊ : ℝ) ^ 11 := by
    apply pow_le_pow_left₀ (by positivity) hxR
  linarith

lemma E2_set_subset_bounded_prod (X B : ℝ) (hX : 2 < X) (hB : 0 < B)
    (hxbound : ∀ p : ℕ+ × ℤ, p ∈ E2Set X → (p.1 : ℝ) ≤ B) :
    E2Set X ⊆ {x : ℕ+ | (x : ℝ) ≤ B} ×ˢ
      Set.Icc (-⌈Real.sqrt (↑⌈B⌉₊ ^ 11 + X)⌉) ⌈Real.sqrt (↑⌈B⌉₊ ^ 11 + X)⌉ := by
  intro ⟨x, y⟩ hp
  have hmem : (x, y) ∈ E2Set X := hp
  obtain ⟨_, _, h2⟩ := hmem
  simp only [Set.mem_prod, Set.mem_setOf_eq]
  constructor
  · exact hxbound ⟨x, y⟩ hp
  · have hy_sq_real : (y : ℝ) ^ 2 ≤ (↑↑x : ℝ) ^ 11 + X :=
      y_sq_le_real_of_E2_cond x y X h2
    have hy_sq_bound : (y : ℝ) ^ 2 ≤ (↑⌈B⌉₊ : ℝ) ^ 11 + X :=
      y_sq_le_ceil_pow_add x y X B hB (hxbound ⟨x, y⟩ hp) hy_sq_real
    have hM_nonneg : (0 : ℝ) ≤ (↑⌈B⌉₊ : ℝ) ^ 11 + X := by positivity
    exact int_mem_Icc_ceil_sqrt_of_sq_le y _ hM_nonneg hy_sq_bound

lemma E2_set_finite (X B : ℝ) (hX : 2 < X) (hB : 0 < B)
    (hxbound : ∀ p : ℕ+ × ℤ, p ∈ E2Set X → (p.1 : ℝ) ≤ B) :
    (E2Set X).Finite := (Set.Finite.prod (pnat_bounded_finite B hB) (Set.finite_Icc _ _)).subset
    (E2_set_subset_bounded_prod X B hX hB hxbound)

lemma E2_fst_gt_of_mem_image (X : ℝ) (hfin : (E2Set X).Finite)
    (x : ℕ+) (hx : x ∈ Finset.image Prod.fst hfin.toFinset) :
    (x : ℝ) > X ^ ((2 : ℝ) / 11) := by
  rw [Finset.mem_image] at hx
  obtain ⟨a, ha_mem, ha_eq⟩ := hx
  rw [Set.Finite.mem_toFinset] at ha_mem
  have h := ha_mem.1
  rw [← ha_eq]
  exact h

lemma E2_fiber_finite (X : ℝ) (hfin : (E2Set X).Finite) (x : ℕ+) :
    Set.Finite {y : ℤ | (x, y) ∈ E2Set X} := by
  have : {y : ℤ | (x, y) ∈ E2Set X} = (fun y => (x, y)) ⁻¹' (E2Set X) := rfl
  rw [this]
  exact hfin.preimage (fun a _ b _ h => by exact congr_arg Prod.snd h)

lemma E2_filter_eq_image (X : ℝ) (hfin : (E2Set X).Finite) (x : ℕ+)
    (hfib : Set.Finite {y : ℤ | (x, y) ∈ E2Set X}) :
    Finset.filter (fun a => a.1 = x) hfin.toFinset =
    Finset.image (fun y => (x, y)) hfib.toFinset := by
  ext ⟨a₁, a₂⟩
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_image]
  constructor
  · rintro ⟨hmem, heq⟩
    exact ⟨a₂, by subst heq; exact hmem, by subst heq; rfl⟩
  · rintro ⟨y, hymem, heq⟩
    have h1 : a₁ = x := by have := congr_arg Prod.fst heq; simpa using this.symm
    have h2 : a₂ = y := by have := congr_arg Prod.snd heq; simpa using this.symm
    exact ⟨by rw [h1, h2]; exact hymem, h1⟩

lemma E2_filter_card_le_fiber_ncard (X : ℝ) (hfin : (E2Set X).Finite)
    (x : ℕ+) :
    (Finset.filter (fun a => a.1 = x) hfin.toFinset).card ≤
    Set.ncard {y : ℤ | (x, y) ∈ E2Set X} := by
  have hfib := E2_fiber_finite X hfin x
  rw [E2_filter_eq_image X hfin x hfib]
  rw [Finset.card_image_of_injective _ (fun a b h => by exact Prod.mk.inj h |>.2)]
  rw [Set.ncard_eq_toFinset_card _ hfib]

lemma E2_finset_fiber_card_le (X : ℝ) (_hX : 2 < X)
    (hfin : (E2Set X).Finite)
    (hfiber : ∀ x : ℕ+, (x : ℝ) > X ^ ((2 : ℝ) / 11) →
      Set.ncard {y : ℤ | (x, y) ∈ E2Set X} ≤ 4)
    (x : ℕ+) (hx : x ∈ Finset.image Prod.fst hfin.toFinset) :
    (Finset.filter (fun a => a.1 = x) hfin.toFinset).card ≤ 4 := by
  have hgt := E2_fst_gt_of_mem_image X hfin x hx
  have hncard := hfiber x hgt
  exact le_trans (E2_filter_card_le_fiber_ncard X hfin x) hncard

lemma pnat_image_val_card_eq (s : Finset ℕ+) :
    (Finset.image (fun x : ℕ+ => (x : ℕ)) s).card = s.card := by
  apply Finset.card_image_of_injective
  intro x y h
  have h₁ : (x : ℕ) = (y : ℕ) := h
  apply PNat.coe_injective
  exact h₁

lemma pnat_nat_image_subset_Icc (X B : ℝ) (_hB : 0 < B)
    (hfin : (E2Set X).Finite)
    (hxbound : ∀ p : ℕ+ × ℤ, p ∈ E2Set X → (p.1 : ℝ) ≤ B) :
    Finset.image (fun x : ℕ+ => (x : ℕ)) (Finset.image Prod.fst hfin.toFinset) ⊆
      Finset.Icc 1 ⌊B⌋₊ := by
  intro n hn
  rw [Finset.mem_Icc]
  simp only [Finset.mem_image] at hn
  obtain ⟨x, hx_mem, rfl⟩ := hn
  obtain ⟨p, hp_mem, rfl⟩ := hx_mem
  rw [Set.Finite.mem_toFinset] at hp_mem
  constructor
  · exact PNat.pos p.1
  · exact natLe_floor_of_cast_le B (p.1 : ℕ) (hxbound p hp_mem)

lemma Icc_card_le_floor_add_one (B : ℝ) :
    (Finset.Icc 1 ⌊B⌋₊).card ≤ ⌊B⌋₊ + 1 := by
  have h₁ : (Finset.Icc 1 ⌊B⌋₊).card = (⌊B⌋₊ : ℕ) := by
    simp
  linarith

theorem E2_fst_image_card_le (X B : ℝ) (hB : 0 < B)
    (hfin : (E2Set X).Finite)
    (hxbound : ∀ p : ℕ+ × ℤ, p ∈ E2Set X → (p.1 : ℝ) ≤ B) :
    (Finset.image Prod.fst hfin.toFinset).card ≤ Nat.floor B + 1 := by
  have h1 := pnat_image_val_card_eq (Finset.image Prod.fst hfin.toFinset)
  have h2 := pnat_nat_image_subset_Icc X B hB hfin hxbound
  have h3 := Finset.card_le_card h2
  have h4 := Icc_card_le_floor_add_one B
  omega

lemma E2_ncard_le_nat (X B : ℝ) (hX : 2 < X) (hB : 0 < B)
    (hfin : (E2Set X).Finite)
    (hfiber : ∀ x : ℕ+, (x : ℝ) > X ^ ((2 : ℝ) / 11) →
      Set.ncard {y : ℤ | (x, y) ∈ E2Set X} ≤ 4)
    (hxbound : ∀ p : ℕ+ × ℤ, p ∈ E2Set X → (p.1 : ℝ) ≤ B) :
    E2 X ≤ 4 * (Nat.floor B + 1) := by
  unfold E2
  rw [Set.ncard_eq_toFinset_card _ hfin]
  calc hfin.toFinset.card
      ≤ 4 * (Finset.image Prod.fst hfin.toFinset).card := by
        apply Finset.card_le_mul_card_image
        intro b hb
        exact E2_finset_fiber_card_le X hX hfin hfiber b hb
    _ ≤ 4 * (Nat.floor B + 1) := by
        apply Nat.mul_le_mul_left
        exact E2_fst_image_card_le X B hB hfin hxbound

lemma E2_ncard_le_via_fibers (X B : ℝ) (hX : 2 < X) (hB : 0 < B)
    (hfiber : ∀ x : ℕ+, (x : ℝ) > X ^ ((2 : ℝ) / 11) →
      Set.ncard {y : ℤ | (x, y) ∈ E2Set X} ≤ 4)
    (hxbound : ∀ p : ℕ+ × ℤ, p ∈ E2Set X → (p.1 : ℝ) ≤ B) :
    (E2 X : ℝ) ≤ 4 * (B + 1) := by
  have hfin := E2_set_finite X B hX hB hxbound
  have h1 := E2_ncard_le_nat X B hX hB hfin hfiber hxbound
  have h2 : (E2 X : ℝ) ≤ ↑(4 * (Nat.floor B + 1)) := by exact_mod_cast h1
  calc (E2 X : ℝ) ≤ ↑(4 * (Nat.floor B + 1)) := h2
    _ = 4 * (↑(Nat.floor B) + 1) := by push_cast; ring
    _ ≤ 4 * (B + 1) := by
        gcongr
        exact Nat.floor_le (le_of_lt hB)
end E2NcardHelpers

lemma E2_ncard_le_via_fibers (X B : ℝ) (hX : 2 < X) (hB : 0 < B)
    (hfiber : ∀ x : ℕ+, (x : ℝ) > X ^ ((2 : ℝ) / 11) →
      Set.ncard {y : ℤ | (x, y) ∈ E2Set X} ≤ 4)
    (hxbound : ∀ p : ℕ+ × ℤ, p ∈ E2Set X → (p.1 : ℝ) ≤ B) :
    (E2 X : ℝ) ≤ 4 * (B + 1) :=
  E2NcardHelpers.E2_ncard_le_via_fibers X B hX hB hfiber hxbound

end E2Helpers

open E2Helpers in
lemma abc_bound_E2_core (habc : ABC) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (E2 X : ℝ) ≤ C * X ^ ((4 : ℝ) / 9 + η) := by
  set ε := min (1/10 : ℝ) (η/4) with hε_def
  have hε_pos : (0 : ℝ) < ε := by positivity
  have hε_le_tenth : ε ≤ 1/10 := min_le_left _ _
  have hε_le_eta4 : ε ≤ η/4 := min_le_right _ _
  have hε_lt : ε < 9/13 := by linarith
  obtain ⟨Cx, hCx_pos, X₁, hX₁_pos, hxbound⟩ := E2_x_bound_from_abc habc ε hε_pos hε_lt
  set exp := ((4 : ℝ) + 2 * ε) / (9 - 13 * ε) with hexp_def
  have hexp_strict : exp < (4 : ℝ) / 9 + η :=
    exponent_comparison_strict η ε hη hε_pos hε_le_eta4 hε_le_tenth
  have hCx1_pos : (0 : ℝ) < Cx + 1 := by linarith
  obtain ⟨X₂, hX₂_pos, hCx_absorb⟩ := eventually_rpow_ge_const hCx1_pos hexp_strict
  refine ⟨8, by positivity, max (max X₁ X₂) 3, by positivity, fun X hX => ?_⟩
  have hX₁_lt : X₁ < X :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX₂_lt : X₂ < X :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX3 : (3 : ℝ) ≤ X := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hX)
  have hX2 : (2 : ℝ) < X := by linarith
  have hX_pos : (0 : ℝ) < X := by linarith
  have hB_pos : (0 : ℝ) < Cx * X ^ exp := by positivity
  have step1 := E2_ncard_le_via_fibers X (Cx * X ^ exp)
    hX2 hB_pos (E2_fiber_bound X hX2) (hxbound X hX₁_lt)
  have hCx_le : Cx + 1 ≤ X ^ ((4 : ℝ) / 9 + η - exp) := hCx_absorb X hX₂_lt
  have hkey : (Cx + 1) * X ^ exp ≤ X ^ ((4 : ℝ) / 9 + η) :=
    rpow_diff_mul_rpow_le hX_pos hCx_le
  have hexp_nonneg : (0 : ℝ) ≤ exp := div_nonneg (by linarith) (by linarith)
  have hXexp_ge1 : (1 : ℝ) ≤ X ^ exp := Real.one_le_rpow (by linarith) hexp_nonneg
  calc (E2 X : ℝ)
      ≤ 4 * (Cx * X ^ exp + 1) := step1
    _ ≤ 4 * (Cx * X ^ exp + 1 * X ^ exp) := by
        gcongr
        simpa using hXexp_ge1
    _ = 4 * ((Cx + 1) * X ^ exp) := by ring
    _ ≤ 4 * X ^ ((4 : ℝ) / 9 + η) := by gcongr
    _ ≤ 8 * X ^ ((4 : ℝ) / 9 + η) := by
      nlinarith [Real.rpow_nonneg (le_of_lt hX_pos) ((4 : ℝ) / 9 + η)]
theorem abc_bound_E2 (habc : ABC) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (E2 X : ℝ) ≤ C * X ^ ((4 : ℝ) / 9 + η) :=
  abc_bound_E2_core habc η hη

namespace E4Helpers

lemma u_fiber_bound :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        ∀ x : ℕ+,
          ({u : ℤ | (x, u) ∈ E4Set X}).ncard ≤ 10 := by
  refine ⟨4, by norm_num, fun X hX x => ?_⟩
  by_cases hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)
  · calc ({u : ℤ | (x, u) ∈ E4Set X}).ncard
        ≤ 4 := E4_fiber_ncard_le_four X hX x hx
      _ ≤ 10 := by norm_num
  · rw [E4_fiber_empty_of_le X x hx, Set.ncard_empty]
    norm_num

lemma E4_fiber_ncard_le (X : ℝ) (hX : 4 < X) (x : ℕ+) :
    {u : ℤ | (x, u) ∈ E4Set X}.ncard ≤ 4 := by
  by_cases hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)
  · exact E4_fiber_ncard_le_four X hX x hx
  · simp [E4_fiber_empty_of_le X x hx]

lemma pnat_bounded_finite (B : ℝ) (_hB : 0 < B) :
    {x : ℕ+ | (x : ℝ) ≤ B}.Finite :=
  _root_.pnat_bounded_finite B

lemma pow22_le_of_le (x : ℕ+) (B : ℝ) (hxB : (x : ℝ) ≤ B) :
    (↑↑x : ℝ) ^ 22 ≤ B ^ 22 := pow_le_pow_left₀ (pnat_cast_nonneg x) hxB 22

lemma u_sq_le_of_E4 (X B : ℝ) (hx : ∀ p ∈ E4Set X, (p.1 : ℝ) ≤ B)
    (p : ℕ+ × ℤ) (hp : p ∈ E4Set X) :
    (p.2 : ℝ) ^ 2 ≤ 5 * B ^ 22 + 4 * X := by
  have hD := (E4_set_D_bounds X p hp).2
  have hinterval := u_sq_le_of_abs_le p.1 p.2 X hD
  have hxB := hx p hp
  have hpow := pow22_le_of_le p.1 B hxB
  calc (↑p.2 : ℝ) ^ 2
      ≤ 5 * (↑↑p.1 : ℝ) ^ 22 + 4 * X := hinterval
    _ ≤ 5 * B ^ 22 + 4 * X := by linarith [hpow]

lemma bound_nonneg_of_E4 (X B : ℝ) (hx : ∀ p ∈ E4Set X, (p.1 : ℝ) ≤ B)
    (p : ℕ+ × ℤ) (hp : p ∈ E4Set X) :
    0 ≤ 5 * B ^ 22 + 4 * X :=
  le_trans (sq_nonneg (p.2 : ℝ)) (u_sq_le_of_E4 X B hx p hp)

lemma u_in_Icc_of_E4 (X B : ℝ) (hx : ∀ p ∈ E4Set X, (p.1 : ℝ) ≤ B)
    (p : ℕ+ × ℤ) (hp : p ∈ E4Set X) :
    p.2 ∈ Set.Icc (-⌈Real.sqrt (5 * B ^ 22 + 4 * X)⌉)
                    ⌈Real.sqrt (5 * B ^ 22 + 4 * X)⌉ :=
    int_mem_Icc_ceil_sqrt_of_sq_le p.2 (5 * B ^ 22 + 4 * X)
    (bound_nonneg_of_E4 X B hx p hp) (u_sq_le_of_E4 X B hx p hp)

lemma E4_set_subset_prod (X B : ℝ) (hx : ∀ p ∈ E4Set X, (p.1 : ℝ) ≤ B) :
    E4Set X ⊆
      {x : ℕ+ | (x : ℝ) ≤ B} ×ˢ
      Set.Icc (-⌈Real.sqrt (5 * B ^ 22 + 4 * X)⌉)
              ⌈Real.sqrt (5 * B ^ 22 + 4 * X)⌉ := by
  intro p hp
  simp only [Set.mem_prod, Set.mem_setOf_eq]
  exact ⟨hx p hp, u_in_Icc_of_E4 X B hx p hp⟩

lemma E4_set_finite_of_bounded (X B : ℝ) (hB : 0 < B) (_hX : 4 < X)
    (hx : ∀ p ∈ E4Set X, (p.1 : ℝ) ≤ B) :
    (E4Set X).Finite := by
  apply Set.Finite.subset _ (E4_set_subset_prod X B hx)
  exact Set.Finite.prod (pnat_bounded_finite B hB) (Set.finite_Icc _ _)

lemma E4_fiber_finite (X : ℝ) (hfin : (E4Set X).Finite) (x : ℕ+) :
    {u : ℤ | (x, u) ∈ E4Set X}.Finite := by
  have : {u : ℤ | (x, u) ∈ E4Set X} = Prod.mk x ⁻¹' (E4Set X) := by
    ext u; simp [Set.mem_preimage]
  rw [this]
  apply Set.Finite.preimage _ hfin
  exact (Prod.mk_right_injective x).injOn

lemma E4_filter_image_subset_fiber (X : ℝ) (hfin : (E4Set X).Finite) (x : ℕ+) :
    Finset.image Prod.snd (Finset.filter (fun a => a.1 = x) hfin.toFinset) ⊆
    (E4_fiber_finite X hfin x).toFinset := by
  intro u hu
  rw [Finset.mem_image] at hu
  obtain ⟨a, ha_mem, rfl⟩ := hu
  rw [Finset.mem_filter] at ha_mem
  obtain ⟨ha_set, ha_fst⟩ := ha_mem
  rw [Set.Finite.mem_toFinset] at ha_set ⊢
  change (x, a.2) ∈ E4Set X
  rwa [← ha_fst, Prod.mk.eta]

lemma E4_snd_injOn_filter (X : ℝ) (hfin : (E4Set X).Finite) (x : ℕ+) :
    Set.InjOn Prod.snd (↑(Finset.filter (fun a => a.1 = x) hfin.toFinset) : Set (ℕ+ × ℤ)) := by
  intro a ha b hb heq
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
  exact Prod.ext (ha.2.trans hb.2.symm) heq

lemma E4_filter_card_le_fiber_ncard (X : ℝ) (hfin : (E4Set X).Finite)
    (x : ℕ+) :
    ({a ∈ hfin.toFinset | a.1 = x}).card ≤ {u : ℤ | (x, u) ∈ E4Set X}.ncard := by
  rw [Set.ncard_eq_toFinset_card _ (E4_fiber_finite X hfin x)]
  have h1 := Finset.card_image_of_injOn (E4_snd_injOn_filter X hfin x)
  linarith [Finset.card_le_card (E4_filter_image_subset_fiber X hfin x)]

lemma E4_finset_fiber_card_le (X : ℝ) (hX : 4 < X) (hfin : (E4Set X).Finite)
    (x : ℕ+) :
    ({a ∈ hfin.toFinset | a.1 = x}).card ≤ 4 := by
  calc ({a ∈ hfin.toFinset | a.1 = x}).card
      ≤ {u : ℤ | (x, u) ∈ E4Set X}.ncard := E4_filter_card_le_fiber_ncard X hfin x
    _ ≤ 4 := E4_fiber_ncard_le X hX x

lemma pnat_image_val_card_eq (s : Finset ℕ+) :
    (Finset.image (fun x : ℕ+ => (x : ℕ)) s).card = s.card := by
  apply Finset.card_image_of_injective
  intro x y h
  have h₁ : (x : ℕ) = (y : ℕ) := h
  apply PNat.coe_injective
  exact h₁

lemma pnat_finset_card_le_floor_add_one (s : Finset ℕ+) (B : ℝ)
    (hs : ∀ x ∈ s, (x : ℝ) ≤ B) :
    s.card ≤ ⌊B⌋₊ + 1 := by
  rw [← pnat_image_val_card_eq s]
  apply le_trans (Finset.card_le_card _)
  · rw [Finset.card_range]
  · intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨x, hx_mem, rfl⟩ := hn
    rw [Finset.mem_range]
    exact Nat.lt_add_one_iff.mpr (natLe_floor_of_cast_le B x (hs x hx_mem))

lemma E4_fst_image_card_le (X B : ℝ) (hB : 0 < B) (hfin : (E4Set X).Finite)
    (hx : ∀ p ∈ E4Set X, (p.1 : ℝ) ≤ B) :
    (Finset.image Prod.fst hfin.toFinset).card ≤ ⌊B⌋₊ + 1 := by
  have _ : (0 : ℝ) < B := hB
  apply pnat_finset_card_le_floor_add_one
  intro x hx_mem
  rw [Finset.mem_image] at hx_mem
  obtain ⟨p, hp_mem, rfl⟩ := hx_mem
  exact hx p (hfin.mem_toFinset.mp hp_mem)

lemma E4_ncard_le_mul_floor (X B : ℝ) (hB : 0 < B) (hX : 4 < X)
    (hfin : (E4Set X).Finite)
    (hx : ∀ p ∈ E4Set X, (p.1 : ℝ) ≤ B) :
    E4 X ≤ 4 * (⌊B⌋₊ + 1) := by
  unfold E4
  rw [Set.ncard_eq_toFinset_card _ hfin]
  set s := hfin.toFinset
  set t := Finset.image Prod.fst s
  have hmaps : Set.MapsTo Prod.fst (↑s : Set (ℕ+ × ℤ)) (↑t : Set ℕ+) := by
    intro a ha
    simp only [t, Finset.coe_image, Set.mem_image]
    exact ⟨a, ha, rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfiber : ∀ x ∈ t, ({a ∈ s | a.1 = x}).card ≤ 4 := by
    intro x _
    exact E4_finset_fiber_card_le X hX hfin x
  calc ∑ b ∈ t, ({a ∈ s | a.1 = b}).card
      ≤ t.card * 4 := Finset.sum_le_card_nsmul _ _ 4 hfiber
    _ ≤ (⌊B⌋₊ + 1) * 4 := by
        apply Nat.mul_le_mul_right
        exact E4_fst_image_card_le X B hB hfin hx
    _ = 4 * (⌊B⌋₊ + 1) := by ring

lemma E4_real_bound_from_nat (X B : ℝ) (hB : 0 < B)
    (h : E4 X ≤ 4 * (⌊B⌋₊ + 1)) :
    (E4 X : ℝ) ≤ 4 * (B + 1) := by
  have h₁ : (E4 X : ℝ) ≤ 4 * (⌊B⌋₊ + 1 : ℝ) := by
    exact_mod_cast h
  have h₂ : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le (by linarith)
  linarith

lemma absorb_additive_const (η K₄ : ℝ) (hη : 0 < η) (_hK₄ : 0 < K₄) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ < X →
      4 * (K₄ * X ^ ((1 : ℝ) / 5 + η) + 1) ≤ 4 * (K₄ + 1) * X ^ ((1 : ℝ) / 5 + η) := by
  use 1
  constructor
  · norm_num
  intro X hX
  have h₁ : (1 : ℝ) < X := by linarith
  have h₃ : (1 : ℝ) < X ^ ((1 : ℝ) / 5 + η) := Real.one_lt_rpow h₁ (by linarith)
  have h₆ : 4 * (K₄ * X ^ ((1 : ℝ) / 5 + η) + 1) ≤ 4 * (K₄ + 1) * X ^ ((1 : ℝ) / 5 + η) := by
    have h₆₁ : 4 * (K₄ * X ^ ((1 : ℝ) / 5 + η) + 1) = 4 * K₄ * X ^ ((1 : ℝ) / 5 + η) + 4 := by ring
    have h₆₂ : 4 * (K₄ + 1) * X ^ ((1 : ℝ) / 5 + η)
        = 4 * K₄ * X ^ ((1 : ℝ) / 5 + η) + 4 * X ^ ((1 : ℝ) / 5 + η) := by ring
    rw [h₆₁, h₆₂]
    nlinarith
  exact h₆

lemma E4_bound_from_x_and_fiber (η : ℝ) (hη : 0 < η)
    (K₄ : ℝ) (hK₄ : 0 < K₄)
    (X₀_x : ℝ) (hX₀_x : 0 < X₀_x)
    (hx_bound : ∀ X : ℝ, X₀_x < X →
      ∀ p : ℕ+ × ℤ, p ∈ E4Set X →
        (p.1 : ℝ) ≤ K₄ * X ^ ((1 : ℝ) / 5 + η))
    (X₀_u : ℝ) (_hX₀_u : 0 < X₀_u)
    (_hu_bound : ∀ X : ℝ, X₀_u < X →
      ∀ x : ℕ+,
        ({u : ℤ | (x, u) ∈ E4Set X}).ncard ≤ 10) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (E4 X : ℝ) ≤ C * X ^ ((1 : ℝ) / 5 + η) := by
  obtain ⟨X₀_abs, _, habs⟩ := absorb_additive_const η K₄ hη hK₄
  refine ⟨4 * (K₄ + 1), by positivity, max X₀_x (max 4 X₀_abs), by positivity, ?_⟩
  intro X hX
  have hX_x : X₀_x < X := lt_of_le_of_lt (le_max_left _ _) hX
  have hX_4 : 4 < X := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX_abs : X₀_abs < X := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hx := hx_bound X hX_x
  have hX_pos : (0 : ℝ) < X := lt_trans (by norm_num : (0:ℝ) < 4) hX_4
  have hB_pos : 0 < K₄ * X ^ ((1 : ℝ) / 5 + η) := mul_pos hK₄ (Real.rpow_pos_of_pos hX_pos _)
  have hfin := E4_set_finite_of_bounded X (K₄ * X ^ ((1 : ℝ) / 5 + η)) hB_pos hX_4 hx
  have hnat := E4_ncard_le_mul_floor X (K₄ * X ^ ((1 : ℝ) / 5 + η)) hB_pos hX_4 hfin hx
  have hreal := E4_real_bound_from_nat X (K₄ * X ^ ((1 : ℝ) / 5 + η)) hB_pos hnat
  calc (E4 X : ℝ) ≤ 4 * (K₄ * X ^ ((1 : ℝ) / 5 + η) + 1) := hreal
    _ ≤ 4 * (K₄ + 1) * X ^ ((1 : ℝ) / 5 + η) := habs X hX_abs

end E4Helpers

open E4Helpers in
lemma abc_bound_E4_core (habc : ABC) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (E4 X : ℝ) ≤ C * X ^ ((1 : ℝ) / 5 + η) := by
  obtain ⟨K₄, hK₄, X₀_x, hX₀_x, hx⟩ := x_bound_in_E4 habc η hη
  obtain ⟨X₀_u, hX₀_u, hu⟩ := E4Helpers.u_fiber_bound
  exact E4Helpers.E4_bound_from_x_and_fiber η hη K₄ hK₄ X₀_x hX₀_x hx X₀_u hX₀_u hu
theorem abc_bound_E4 (habc : ABC) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (E4 X : ℝ) ≤ C * X ^ ((1 : ℝ) / 5 + η) :=
  abc_bound_E4_core habc η hη

lemma absorb_const_rpow {C a b : ℝ} (_hC : 0 < C) (hab : a < b) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ < X → C * X ^ a ≤ X ^ b := by
  have hba : 0 < b - a := by linarith
  have h_tendsto : Filter.Tendsto (fun X : ℝ => X ^ (b - a)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hba
  obtain ⟨X₁, hX₁⟩ := (h_tendsto.eventually (Filter.eventually_ge_atTop C)).exists_forall_of_atTop
  refine ⟨max 1 X₁, by positivity, fun X hX => ?_⟩
  have h1 : 1 ≤ X := by linarith [le_max_left 1 X₁]
  have h2 : X₁ ≤ X := by linarith [le_max_right 1 X₁]
  have h3 : C ≤ X ^ (b - a) := le_trans (hX₁ X h2) (Real.rpow_le_rpow_of_exponent_le h1 le_rfl)
  calc C * X ^ a ≤ X ^ (b - a) * X ^ a := by
        nlinarith [Real.rpow_nonneg (by linarith : (0:ℝ) ≤ X) a]
    _ = X ^ b := by rw [← Real.rpow_add (by linarith : (0:ℝ) < X), show b - a + a = b by ring]

private lemma log_le_rpow_one_eleventh :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ < X →
      Real.log X ≤ X ^ ((1 : ℝ) / 11) := by
  obtain ⟨X₀, hX₀_pos, habs⟩ :=
    absorb_const_rpow (by norm_num : (0 : ℝ) < 22) (by norm_num : (1 : ℝ) / 22 < 1 / 11)
  exact ⟨X₀, hX₀_pos, fun X hX => by
    have hX_pos : 0 < X := lt_trans hX₀_pos hX
    have hX_nn : 0 ≤ X := le_of_lt hX_pos
    have h1 := Real.log_le_rpow_div hX_nn (by norm_num : (0 : ℝ) < 1 / 22)
    rw [show X ^ ((1 : ℝ) / 22) / ((1 : ℝ) / 22) = 22 * X ^ ((1 : ℝ) / 22) by ring] at h1
    exact le_trans h1 (habs X hX)⟩

lemma half_log_le_13_22 :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ < X →
      X ^ ((1 : ℝ) / 2) * Real.log X ≤ X ^ ((13 : ℝ) / 22) := by
  obtain ⟨X₀, hX₀pos, hX₀⟩ := log_le_rpow_one_eleventh
  refine ⟨max X₀ 0, by positivity, fun X hX => ?_⟩
  have hXgt0 : 0 < X := by linarith [le_max_right X₀ 0]
  have hXgtX₀ : X₀ < X := lt_of_le_of_lt (le_max_left X₀ 0) hX
  have hlog := hX₀ X hXgtX₀
  calc X ^ ((1 : ℝ) / 2) * Real.log X
      ≤ X ^ ((1 : ℝ) / 2) * X ^ ((1 : ℝ) / 11) := by
        apply mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg (le_of_lt hXgt0) _)
    _ = X ^ ((13 : ℝ) / 22) := by
        rw [← Real.rpow_add hXgt0, show (1 : ℝ) / 2 + 1 / 11 = 13 / 22 from by norm_num]

lemma combine_five_bounds {S t₁ t₂ t₃ t₄ t₅ B C₁ : ℝ}
    (hS : S ≤ C₁ * (t₁ + t₂ + t₃ + t₄ + t₅))
    (h1 : t₁ ≤ B) (h2 : t₂ ≤ B) (h3 : t₃ ≤ B) (h4 : t₄ ≤ B) (h5 : t₅ ≤ B)
    (hC₁ : 0 < C₁) :
    S ≤ 5 * C₁ * B := by
  have hsum : t₁ + t₂ + t₃ + t₄ + t₅ ≤ 5 * B := by
    linarith
  calc
    S ≤ C₁ * (t₁ + t₂ + t₃ + t₄ + t₅) := hS
    _ ≤ C₁ * (5 * B) := by gcongr
    _ = 5 * C₁ * B := by ring

theorem main_theorem (habc : ABC) (h54 : Proposition54 R) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (S R X : ℝ) ≤ C * X ^ ((13 : ℝ) / 22) := by
  obtain ⟨C₁, hC₁, X₁, hX₁, hred⟩ := reduction_lemma R habc h54
  obtain ⟨C₂, hC₂, X₂, hX₂, hE2⟩ := abc_bound_E2 habc (1/198) (by positivity)
  obtain ⟨C₃, hC₃, X₃, hX₃, hE4⟩ := abc_bound_E4 habc (1/220) (by norm_num)
  obtain ⟨X₄, hX₄, hlog⟩ := half_log_le_13_22
  obtain ⟨X₅, hX₅, habsE2⟩ := absorb_const_rpow hC₂ (show (89 : ℝ) / 198 < 13 / 22 by norm_num)
  obtain ⟨X₆, hX₆, habsE4⟩ := absorb_const_rpow hC₃ (show (9 : ℝ) / 44 < 13 / 22 by norm_num)
  set X₀ := max 1 (max X₁ (max X₂ (max X₃ (max X₄ (max X₅ X₆))))) with hX₀_def
  refine ⟨5 * C₁, by positivity, X₀, by positivity, fun X hX => ?_⟩
  have hlt : ∀ y, y ≤ X₀ → y < X := fun y hy => lt_of_le_of_lt hy hX
  have hX1 : (1 : ℝ) < X := hlt _ (le_max_left _ _)
  have hXX₁ : X₁ < X := hlt _ (by simp [hX₀_def])
  have hXX₂ : X₂ < X := hlt _ (by simp [hX₀_def])
  have hXX₃ : X₃ < X := hlt _ (by simp [hX₀_def])
  have hXX₄ : X₄ < X := hlt _ (by simp [hX₀_def])
  have hXX₅ : X₅ < X := hlt _ (by simp [hX₀_def])
  have hXX₆ : X₆ < X := hlt _ (by simp [hX₀_def])
  have hSred := hred X hXX₁
  have hE2X := hE2 X hXX₂
  have hE4X := hE4 X hXX₃
  have hlogX := hlog X hXX₄
  have h611 : X ^ ((6 : ℝ) / 11) ≤ X ^ ((13 : ℝ) / 22) :=
    rpow_le_rpow_of_le_exp (le_of_lt hX1) (by norm_num)
  have habsE2X := habsE2 X hXX₅
  have hE2_absorb : (E2 X : ℝ) ≤ X ^ ((13 : ℝ) / 22) := by
    calc (E2 X : ℝ) ≤ C₂ * X ^ ((4 : ℝ) / 9 + 1 / 198) := hE2X
    _ = C₂ * X ^ ((89 : ℝ) / 198) := by rw [show (4 : ℝ) / 9 + 1 / 198 = 89 / 198 from by norm_num]
    _ ≤ X ^ ((13 : ℝ) / 22) := habsE2X
  have habsE4X := habsE4 X hXX₆
  have hE4_absorb : (E4 X : ℝ) ≤ X ^ ((13 : ℝ) / 22) := by
    calc (E4 X : ℝ) ≤ C₃ * X ^ ((1 : ℝ) / 5 + 1 / 220) := hE4X
    _ = C₃ * X ^ ((9 : ℝ) / 44) := by rw [show (1 : ℝ) / 5 + 1 / 220 = 9 / 44 from by norm_num]
    _ ≤ X ^ ((13 : ℝ) / 22) := habsE4X
  exact combine_five_bounds hSred hlogX (le_refl _) h611 hE2_absorb hE4_absorb hC₁
