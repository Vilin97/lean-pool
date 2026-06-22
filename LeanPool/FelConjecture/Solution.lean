/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang
-/
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.WellKnown
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
/-! # Fel's Conjecture for Numerical Semigroups -/
/-- A *numerical semigroup*: an additive submonoid of `ℕ` with finite complement. -/
structure NumericalSemigroup where
  /-- The underlying set of natural numbers comprising the semigroup. -/
  carrier : Set ℕ
  zero_mem : 0 ∈ carrier
  add_mem : ∀ a b, a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  finite_complement : (carrier)ᶜ.Finite

namespace NumericalSemigroup

-- The gap set (complement of the semigroup in ℕ)
/-- The *gaps* of `S`: the (finite) complement `ℕ \ S` as a `Finset`. -/
noncomputable def gaps (S : NumericalSemigroup) : Finset ℕ := S.finite_complement.toFinset

-- Gap power sum: G_r(S) = sum_{g in Delta} g^r (Definition 3)
/-- The gap power sum `G_r(S) = ∑_{g ∈ Δ} g^r` (Definition 3 in the paper). -/
noncomputable def gapPowerSum (S : NumericalSemigroup) (r : ℕ) : ℚ :=
  ∑ g ∈ S.gaps, (g : ℚ) ^ r

-- Gap polynomial: Phi_S(z) = sum_{g in Delta} z^g (Definition 4)
/-- The gap polynomial `Φ_S(z) = ∑_{g ∈ Δ} z^g` (Definition 4 in the paper). -/
noncomputable def gapPolynomial (S : NumericalSemigroup) : Polynomial ℚ :=
  ∑ g ∈ S.gaps, Polynomial.X ^ g

-- Hilbert series: H_S(z) = sum_{s in S} z^s (Definition 5)
-- Defined as a formal power series
-- We use Classical decidability since membership in S.carrier is not decidable in general
/-- The Hilbert series `H_S(z) = ∑_{s ∈ S} z^s`, expressed as a formal power series. -/
noncomputable def hilbertSeries (S : NumericalSemigroup) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if Classical.propDecidable (n ∈ S.carrier) |>.decide then 1 else 0

/-- The coefficient of the Hilbert series at position n is 1 if n ∈ S.carrier, else 0. -/
lemma hilbertSeries_coeff (S : NumericalSemigroup) (n : ℕ) :
    (PowerSeries.coeff n) S.hilbertSeries =
    if Classical.propDecidable (n ∈ S.carrier) |>.decide then 1 else 0 := by
  simp only [hilbertSeries, PowerSeries.coeff_mk]

/-- The coefficient of the gap polynomial (viewed as a power series) at position n is 1 if n ∈
  S.gaps, else 0. -/
lemma gapPolynomial_coeff (S : NumericalSemigroup) (n : ℕ) :
    (PowerSeries.coeff n) (S.gapPolynomial : PowerSeries ℚ) =
    if n ∈ S.gaps then 1 else 0 := by
  unfold gapPolynomial
  rw [Polynomial.coeff_coe]
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_X_pow]
  exact Finset.sum_ite_eq S.gaps n (fun _ => 1)

/-- For any n, we have n ∈ S.gaps ↔ n ∉ S.carrier. -/
lemma mem_gaps_iff_not_mem_carrier (S : NumericalSemigroup) (n : ℕ) :
    n ∈ S.gaps ↔ n ∉ S.carrier := by
  simp only [gaps, Set.Finite.mem_toFinset, Set.mem_compl_iff]

lemma semigroupGapDecomposition_aux (S : NumericalSemigroup) (n : ℕ) :
    (PowerSeries.coeff n) (S.hilbertSeries + (S.gapPolynomial : PowerSeries ℚ)) =
    (PowerSeries.coeff n) (PowerSeries.mk (1 : ℕ → ℚ)) := by
  rw [map_add]
  rw [hilbertSeries_coeff, gapPolynomial_coeff]
  rw [PowerSeries.coeff_mk]
  simp only [Pi.one_apply]
  by_cases h : n ∈ S.carrier
  · simp only [decide_eq_true_eq, h, ↓reduceIte]
    rw [if_neg]
    · ring
    · rw [mem_gaps_iff_not_mem_carrier]; exact not_not.mpr h
  · simp only [decide_eq_true_eq, h, ↓reduceIte]
    rw [if_pos]
    · ring
    · rw [mem_gaps_iff_not_mem_carrier]; exact h

theorem semigroupGapDecomposition (S : NumericalSemigroup) :
    S.hilbertSeries + (S.gapPolynomial : PowerSeries ℚ) = PowerSeries.mk (1 : ℕ → ℚ) := by
  apply PowerSeries.ext
  exact semigroupGapDecomposition_aux S

end NumericalSemigroup

/-- A choice of generators for a numerical semigroup `S`: positive integers `d₁, …,
  d_m` with `gcd = 1` whose nonneg-integer combinations recover `S.carrier`. -/
structure NumericalSemigroupGenerators (S : NumericalSemigroup) where
  /-- The number of generators (embedding dimension of `S`). -/
  m : ℕ                           -- number of generators (embedding dimension)
  hm_pos : 0 < m                  -- at least one generator
  /-- The chosen generators `d₁, …, d_m`. -/
  d : Fin m → ℕ                   -- the generators d_1, ..., d_m
  hd_pos : ∀ i, 0 < d i           -- each generator is positive
  hgcd : (Finset.univ.image d).gcd id = 1  -- gcd of generators is 1
  generates : S.carrier = {n : ℕ | ∃ (c : Fin m → ℕ), n = ∑ i, c i * d i}

namespace NumericalSemigroupGenerators

/-- The product of generators `π_m = ∏ᵢ dᵢ` (Definition 6 in the paper). -/
def piM {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) : ℕ :=
  ∏ i : Fin G.m, G.d i

/-- The product polynomial `P_S(z) = ∏ᵢ (1 - z^{dᵢ})` (Definition 6 in the paper). -/
noncomputable def productPolynomial {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    Polynomial ℤ :=
  ∏ i : Fin G.m, (1 - Polynomial.X ^ (G.d i))

/-- Upper bound on the degree of the Hilbert numerator `Q_S(z)`. -/
noncomputable def hilbertNumeratorDegBound {S : NumericalSemigroup} (G :
  NumericalSemigroupGenerators S) :
    ℕ :=
  G.productPolynomial.natDegree + S.gaps.sup id + 1

/-- The Hilbert numerator `Q_S(z)`, computed coefficient-wise from `P_S` and the gaps. -/
noncomputable def hilbertNumerator {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    Polynomial ℤ :=
  let P := G.productPolynomial
  let bound := G.hilbertNumeratorDegBound
  ∑ n ∈ Finset.range bound,
    Polynomial.monomial n
      ((∑ k ∈ Finset.range (n + 1), P.coeff k) -
       (∑ g ∈ S.gaps.filter (· ≤ n), P.coeff (n - g)))

lemma coeff_polynomial_map_coe {P : Polynomial ℤ} (n : ℕ) :
    (PowerSeries.coeff n) (P.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
    (Int.castRingHom ℚ) (P.coeff n) := by simp

lemma coeff_mul_hilbert_product {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n :
  ℕ) :
    (PowerSeries.coeff n) (S.hilbertSeries *
      (G.productPolynomial.map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
    ∑ k ∈ Finset.range (n + 1),
      (PowerSeries.coeff k) S.hilbertSeries *
        (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) := by
  have h1 : (PowerSeries.coeff n) (S.hilbertSeries *
    (G.productPolynomial.map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
      ∑ k ∈ Finset.range (n + 1), (PowerSeries.coeff k) S.hilbertSeries *
        (PowerSeries.coeff (n - k)) (G.productPolynomial.map (Int.castRingHom ℚ)) := by
    rw [PowerSeries.coeff_mul]
    simp_all [Finset.Nat.antidiagonal_eq_image, Finset.sum_image]
  have h2 : ∀ k ∈ Finset.range (n + 1),
    (PowerSeries.coeff (n - k)) (G.productPolynomial.map (Int.castRingHom ℚ)) =
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) := by
    intro k _
    simp [PowerSeries.coeff_map]
  calc
    (PowerSeries.coeff n) (S.hilbertSeries *
      (G.productPolynomial.map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
        ∑ k ∈ Finset.range (n + 1), (PowerSeries.coeff k) S.hilbertSeries *
          (PowerSeries.coeff (n - k)) (G.productPolynomial.map (Int.castRingHom ℚ)) := by
      rw [h1]
    _ = ∑ k ∈ Finset.range (n + 1), (PowerSeries.coeff k) S.hilbertSeries *
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [h2 k hk]
    _ = ∑ k ∈ Finset.range (n + 1),
      (PowerSeries.coeff k) S.hilbertSeries *
        (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) := by
      rfl

lemma hilbertNumerator_coeff_lt {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n :
  ℕ)
    (hn : n < G.hilbertNumeratorDegBound) :
    G.hilbertNumerator.coeff n =
      (∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k) -
       (∑ g ∈ S.gaps.filter (· ≤ n), G.productPolynomial.coeff (n - g)) := by
  unfold hilbertNumerator
  simp only
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  have hn_mem : n ∈ Finset.range G.hilbertNumeratorDegBound := Finset.mem_range.mpr hn
  rw [Finset.sum_eq_single_of_mem n hn_mem]
  · simp only [ite_true]
  · intro b _ hbn
    simp only [hbn, ite_false]

lemma hilbertNumerator_coeff_ge {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n :
  ℕ)
    (hn : n ≥ G.hilbertNumeratorDegBound) :
    G.hilbertNumerator.coeff n = 0 := by
  unfold hilbertNumerator
  simp only [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Polynomial.coeff_monomial]
  simp only [ite_eq_right_iff]
  intro heq
  exfalso
  rw [Finset.mem_range] at hi
  omega

lemma coeff_hilbertNumerator_formula {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
  (n : ℕ) :
    (PowerSeries.coeff n) (G.hilbertNumerator.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
    if n < G.hilbertNumeratorDegBound then
      (Int.castRingHom ℚ) ((∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k) -
       (∑ g ∈ S.gaps.filter (· ≤ n), G.productPolynomial.coeff (n - g)))
    else 0 := by
  rw [Polynomial.coeff_coe, Polynomial.coeff_map]
  split_ifs with h
  · rw [hilbertNumerator_coeff_lt G n h]
  · simp only [hilbertNumerator_coeff_ge G n (le_of_not_gt h), map_zero]

lemma lhs_eq_sum_over_carrier {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
  :
    ∑ k ∈ Finset.range (n + 1),
      (if (Classical.propDecidable (k ∈ S.carrier)).decide then 1 else 0) *
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) =
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => (Classical.propDecidable (k ∈ S.carrier)).decide),
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) := by
  have h₁ : ∑ k ∈ Finset.range (n + 1),
    (if (Classical.propDecidable (k ∈ S.carrier)).decide then 1 else 0) *
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) =
    ∑ k ∈ Finset.range (n + 1),
      (if (Classical.propDecidable (k ∈
        S.carrier)).decide then (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) else 0) :=
          by
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp [*]
  have h₂ : ∑ k ∈ Finset.range (n + 1),
    (if (Classical.propDecidable (k ∈
      S.carrier)).decide then (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) else 0) =
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => (Classical.propDecidable (k ∈ S.carrier)).decide),
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) := by
    rw [← Finset.sum_filter]
  rw [h₁, h₂]

lemma partition_sum {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) =
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => (Classical.propDecidable (k ∈ S.carrier)).decide),
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) +
    ∑ k ∈ (Finset.range (n +
      1)).filter (fun k => !(Classical.propDecidable (k ∈ S.carrier)).decide),
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) := by
  have h := @Finset.sum_filter_add_sum_filter_not _ _ _ (Finset.range (n + 1))
    (fun k => k ∈ S.carrier) (Classical.decPred _) (fun x => Classical.dec _)
    (fun k => (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)))
  rw [← h]
  congr 1
  · congr 1
    ext k
    simp only [Finset.mem_filter, decide_eq_true_eq]
  · congr 1
    ext k
    simp only [Finset.mem_filter]
    constructor
    · intro ⟨hk, hnot⟩
      refine ⟨hk, ?_⟩
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      exact hnot
    · intro ⟨hk, hbool⟩
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hbool
      exact ⟨hk, hbool⟩

lemma filter_not_carrier_eq_gaps {S : NumericalSemigroup} (n : ℕ) :
    (Finset.range (n + 1)).filter (fun k => !(Classical.propDecidable (k ∈ S.carrier)).decide) =
    S.gaps.filter (· ≤ n) := by
  have h_main : (Finset.range (n +
    1)).filter (fun k => !(Classical.propDecidable (k ∈ S.carrier)).decide) =
      S.gaps.filter (· ≤ n) := by
    apply Finset.ext
    intro k
    simp only [Finset.mem_filter, Finset.mem_range, NumericalSemigroup.gaps,
      Set.Finite.mem_toFinset,
      Set.mem_compl_iff]
    constructor
    · intro h
      have h₂ : ¬(k ∈ S.carrier) := by
        simpa [Classical.propDecidable] using h.2
      have h₃ : k ≤ n := by
        omega
      have h₄ : ¬(k ∈ S.carrier) := h₂
      exact ⟨h₄, h₃⟩
    · intro h
      have h₁ : ¬(k ∈ S.carrier) := h.1
      have h₃ : k < n + 1 := by
        omega
      have h₄ : ¬(k ∈ S.carrier) := h₁
      exact ⟨h₃, by simpa [Classical.propDecidable] using h₄⟩
  apply h_main

lemma carrier_sum_eq_full_minus_gaps {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
  (n : ℕ) :
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => (Classical.propDecidable (k ∈ S.carrier)).decide),
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) =
    ∑ k ∈ Finset.range (n + 1), (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) -
    ∑ g ∈ S.gaps.filter (· ≤ n), (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - g)) := by
  have hpart := partition_sum G n
  have hfilter := filter_not_carrier_eq_gaps (S := S) n
  rw [hfilter] at hpart
  linarith

lemma indicator_sum_eq_full_minus_gaps {S : NumericalSemigroup} (G : NumericalSemigroupGenerators
  S) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (if Classical.propDecidable (k ∈ S.carrier) |>.decide then 1 else 0) *
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) =
    ∑ k ∈ Finset.range (n + 1), (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) -
    ∑ g ∈ S.gaps.filter (· ≤ n), (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - g)) := by
  rw [lhs_eq_sum_over_carrier, carrier_sum_eq_full_minus_gaps]

lemma sum_coeff_reindex {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) =
    ∑ j ∈ Finset.range (n + 1), (Int.castRingHom ℚ) (G.productPolynomial.coeff j) := by
  apply Finset.sum_bij' (fun j _ => n - j) (fun j _ => n - j)
  · intros j hj; rw [Finset.mem_range] at hj ⊢; omega
  · intros j hj; rw [Finset.mem_range] at hj ⊢; omega
  · intros j hj; rw [Finset.mem_range] at hj; omega
  · intros j hj; rw [Finset.mem_range] at hj; omega
  · intros j _; rfl

lemma lhs_eq_hilbertNumerator_coeff {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
  (n : ℕ)
    (hn : n < G.hilbertNumeratorDegBound) :
    ∑ k ∈ Finset.range (n + 1),
      (if Classical.propDecidable (k ∈ S.carrier) |>.decide then 1 else 0) *
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) =
    (Int.castRingHom ℚ) (G.hilbertNumerator.coeff n) := by
  rw [indicator_sum_eq_full_minus_gaps]
  rw [sum_coeff_reindex]
  rw [hilbertNumerator_coeff_lt G n hn]
  simp only [map_sub, map_sum]

lemma sum_range_reindex (f : ℕ → ℚ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), f (n - k) = ∑ j ∈ Finset.range (n + 1), f j := by
  apply Finset.sum_bij' (fun k _ => n - k) (fun k _ => n - k)
  · intros k hk; rw [Finset.mem_range] at hk ⊢; omega
  · intros k hk; rw [Finset.mem_range] at hk ⊢; omega
  · intros k hk; rw [Finset.mem_range] at hk; omega
  · intros k hk; rw [Finset.mem_range] at hk; omega
  · intros k _; rfl

lemma large_n_both_zero {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
    (_hn : n ≥ G.hilbertNumeratorDegBound) :
    (∑ k ∈ Finset.range (n + 1),
      (if Classical.propDecidable (k ∈ S.carrier) |>.decide then 1 else 0) *
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) =
    (Int.castRingHom ℚ) ((∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k) -
     (∑ g ∈ S.gaps.filter (· ≤ n), G.productPolynomial.coeff (n - g)))) := by
  rw [lhs_eq_sum_over_carrier]
  rw [carrier_sum_eq_full_minus_gaps]
  rw [sum_range_reindex (fun k => (Int.castRingHom ℚ) (G.productPolynomial.coeff k)) n]
  rw [map_sub, map_sum, map_sum]

lemma sum_over_semigroup_eq_diff {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n :
  ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (if Classical.propDecidable (k ∈ S.carrier) |>.decide then 1 else 0) *
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) =
    (Int.castRingHom ℚ) ((∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k) -
     (∑ g ∈ S.gaps.filter (· ≤ n), G.productPolynomial.coeff (n - g))) := by
  by_cases hn : n < G.hilbertNumeratorDegBound
  · rw [lhs_eq_hilbertNumerator_coeff G n hn]
    congr 1
    exact hilbertNumerator_coeff_lt G n hn
  · push Not at hn
    exact large_n_both_zero G n hn

lemma coeff_mul_eq_indicator_sum {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n :
  ℕ) :
    (PowerSeries.coeff n) (S.hilbertSeries *
      (G.productPolynomial.map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
    ∑ k ∈ Finset.range (n + 1),
      (if Classical.propDecidable (k ∈ S.carrier) |>.decide then 1 else 0) *
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) := by
  rw [coeff_mul_hilbert_product]
  apply Finset.sum_congr rfl
  intro k _
  rw [S.hilbertSeries_coeff]

lemma productPolynomial_eval_one {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    Polynomial.eval 1 G.productPolynomial = 0 := by
  unfold productPolynomial
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := ⟨0, G.hm_pos⟩) (Finset.mem_univ _)
  simp

lemma sum_coeff_eq_eval_one {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1), G.productPolynomial.coeff k =
    Polynomial.eval 1 G.productPolynomial := by
  have h₁ : ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
    G.productPolynomial.coeff k = G.productPolynomial.eval 1 := by
    rw [Polynomial.eval_eq_sum_range]
    simp [add_comm]
  rw [h₁]

lemma coeff_Ico_eq_zero {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (n : ℕ) (_hn : G.productPolynomial.natDegree + 1 ≤ n)
    (k : ℕ) (hk : k ∈ Finset.Ico (G.productPolynomial.natDegree + 1) (n + 1)) :
    G.productPolynomial.coeff k = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  simp only [Finset.mem_Ico] at hk
  omega

lemma sum_coeff_large_eq_sum_coeff_deg {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (n : ℕ) (hn : G.productPolynomial.natDegree + 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k =
    ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1), G.productPolynomial.coeff k := by
  have hsplit := Finset.sum_range_add_sum_Ico (f := fun k => G.productPolynomial.coeff k)
    (m := G.productPolynomial.natDegree + 1) (n := n + 1) (by omega)
  have htail : ∑ k ∈ Finset.Ico (G.productPolynomial.natDegree + 1) (n + 1),
    G.productPolynomial.coeff k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact coeff_Ico_eq_zero G n hn k hk
  linarith [hsplit, htail]

lemma first_sum_zero {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
    (hn : n ≥ G.hilbertNumeratorDegBound) :
    ∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k = 0 := by
  have h1 : G.productPolynomial.natDegree + 1 ≤ n := by
    unfold hilbertNumeratorDegBound at hn
    omega
  rw [sum_coeff_large_eq_sum_coeff_deg G n h1]
  rw [sum_coeff_eq_eval_one G]
  exact productPolynomial_eval_one G

lemma coeff_n_minus_gap_zero {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (n g : ℕ) (hn : n ≥ G.hilbertNumeratorDegBound) (hg : g ∈ S.gaps) (hgn : g ≤ n) :
    G.productPolynomial.coeff (n - g) = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have hge : g ≤ S.gaps.sup id := Finset.le_sup (f := id) hg
  have hn' : n ≥ G.productPolynomial.natDegree + S.gaps.sup id + 1 := hn
  omega

lemma second_sum_zero {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
    (hn : n ≥ G.hilbertNumeratorDegBound) :
    ∑ g ∈ S.gaps.filter (· ≤ n), G.productPolynomial.coeff (n - g) = 0 := by
  apply Finset.sum_eq_zero
  intro g hg
  rw [Finset.mem_filter] at hg
  exact coeff_n_minus_gap_zero G n g hn hg.1 hg.2

lemma rhs_zero_of_large {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
    (hn : n ≥ G.hilbertNumeratorDegBound) :
    (∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k) -
     (∑ g ∈ S.gaps.filter (· ≤ n), G.productPolynomial.coeff (n - g)) = 0 := by
  rw [first_sum_zero G n hn, second_sum_zero G n hn]
  ring

lemma coeff_eq_zero_of_large {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
    (hn : n ≥ G.hilbertNumeratorDegBound) :
    (PowerSeries.coeff n) (S.hilbertSeries *
      (G.productPolynomial.map (Int.castRingHom ℚ) : PowerSeries ℚ)) = 0 := by
  rw [coeff_mul_eq_indicator_sum]
  rw [large_n_both_zero G n hn]
  rw [rhs_zero_of_large G n hn]
  simp

lemma numeratorIdentity_coeff {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
  :
    (PowerSeries.coeff n) (S.hilbertSeries *
      (G.productPolynomial.map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
    (PowerSeries.coeff n) (G.hilbertNumerator.map (Int.castRingHom ℚ) : PowerSeries ℚ) := by
  by_cases h : n < G.hilbertNumeratorDegBound
  · -- Case n < bound: use the formula
    rw [coeff_mul_hilbert_product, coeff_hilbertNumerator_formula, if_pos h]
    simp only [NumericalSemigroup.hilbertSeries_coeff]
    exact sum_over_semigroup_eq_diff G n
  · -- Case n >= bound: both sides are 0
    push Not at h
    rw [coeff_eq_zero_of_large G n h]
    rw [coeff_hilbertNumerator_formula, if_neg (by omega)]

theorem numeratorIdentity {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    S.hilbertSeries * (G.productPolynomial.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
    (G.hilbertNumerator.map (Int.castRingHom ℚ) : PowerSeries ℚ) := by
  apply PowerSeries.ext
  exact numeratorIdentity_coeff G

/-- The coefficients `cⱼ` in the expansion `Q_S(z) = 1 - ∑_{j ≥ 1} cⱼ z^j`. -/
noncomputable def numeratorCoeff {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (j : ℕ) : ℤ :=
  if j = 0 then 0 else -G.hilbertNumerator.coeff j

/-- The alternating power sum `C_n(S) = ∑_{j ≥ 1} cⱼ · jⁿ` (Definition 8). -/
noncomputable def alternatingPowerSum {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range G.hilbertNumeratorDegBound,
    (G.numeratorCoeff j : ℚ) * (j : ℚ) ^ n

/-- The invariant `K_p(S) =
  ((-1)^m · p!) / ((m+p)! · π_m) · C_{m+p}(S)` (Definition 9 in the paper). -/
noncomputable def KInvariant {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (p : ℕ) : ℚ :=
  ((-1 : ℚ) ^ G.m * (p.factorial : ℚ)) / (((G.m + p).factorial : ℚ) * (G.piM : ℚ)) *
    G.alternatingPowerSum (G.m + p)

/-- The single factor `(e^{dᵢ t} -
  1) / (dᵢ t) = ∑_k dᵢ^k · t^k / (k+1)!` of the `A` generating series. -/
noncomputable def scaledExpFactor {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (i : Fin G.m) : PowerSeries ℚ :=
  PowerSeries.mk fun k => (G.d i : ℚ) ^ k / ((k + 1).factorial : ℚ)

/-- The generating series `A(t) = ∏ᵢ (e^{dᵢ t} - 1) / (dᵢ t)` (Definition 10). -/
noncomputable def ASeries {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    PowerSeries ℚ :=
  ∏ i : Fin G.m, G.scaledExpFactor i

/-- The symbol `T_n(σ) = n! · [t^n] A(t)` (Definition 10). -/
noncomputable def TSigma {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) : ℚ
  :=
  (n.factorial : ℚ) * (PowerSeries.coeff n) (G.ASeries)

/-- The generating series `B(t) = (t / (e^t - 1)) · A(t)` (Definition 11). -/
noncomputable def BSeries {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    PowerSeries ℚ :=
  bernoulliPowerSeries ℚ * G.ASeries

/-- The symbol `T_n(δ) = (n! / 2^n) · [t^n] B(t)` (Definition 11). -/
noncomputable def TDelta {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) : ℚ
  :=
  (n.factorial : ℚ) / (2 ^ n : ℚ) * (PowerSeries.coeff n) (G.BSeries)

end NumericalSemigroupGenerators

namespace FelsConjectureProof

lemma pi_m_pos {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    0 < G.piM := by
  apply Finset.prod_pos
  intro i _
  exact G.hd_pos i

lemma choose_mul_sub_factorial_eq_div (n r : ℕ) (hr : r ≤ n) :
    ((n.choose r : ℚ) * ((n - r).factorial : ℚ)) = (n.factorial : ℚ) / (r.factorial : ℚ) := by
  have h₁ : (n.choose r : ℚ) * (r.factorial : ℚ) * ((n - r).factorial : ℚ) = (n.factorial : ℚ) := by
    norm_cast
    rw [← Nat.choose_mul_factorial_mul_factorial hr]
  have h₂ : (r.factorial : ℚ) ≠ 0 := by positivity
  field_simp [h₂]
  linarith

lemma bernoulli_term_simplify (m p : ℕ) (piM : ℕ) (hpi : 0 < piM)
    (coeff : ℚ) :
    ((-1 : ℚ)^m * (p.factorial : ℚ)) / (((m + p).factorial : ℚ) * (piM : ℚ)) *
      ((-1 : ℚ)^m * (piM : ℚ) * ((m + p).factorial : ℚ) * coeff) =
    (p.factorial : ℚ) * coeff := by
  have hpi' : (piM : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpi)
  have hfac : ((m + p).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h_neg_sq : ((-1 : ℚ)^(m * 2)) = 1 := by
    rw [mul_comm]
    exact Even.neg_one_pow (even_two_mul m)
  field_simp [hpi', hfac]
  ring_nf
  rw [h_neg_sq]
  ring

lemma outer_factor_cancel {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ)
    (sum_term : ℚ) :
    ((-1 : ℚ)^G.m * (p.factorial : ℚ)) / (((G.m + p).factorial : ℚ) * (G.piM : ℚ)) *
      ((-1 : ℚ)^G.m * (G.piM : ℚ) * sum_term) =
    (p.factorial : ℚ) / ((G.m + p).factorial : ℚ) * sum_term := by
  have hpi : (G.piM : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (pi_m_pos G))
  have hfac : ((G.m + p).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h1 : ((-1 : ℚ)^G.m)^2 = 1 := by
    rw [← pow_mul, mul_comm]
    exact Even.neg_one_pow (even_two_mul G.m)
  field_simp
  rw [h1]
  ring

lemma term_simplify (m p r : ℕ) (hr : r ≤ p) (A_coeff G_r : ℚ) :
    (p.factorial : ℚ) / ((m + p).factorial : ℚ) *
      (((m + p).choose r : ℚ) * ((m + p - r).factorial : ℚ) * A_coeff * G_r) =
    (p.factorial : ℚ) / (r.factorial : ℚ) * A_coeff * G_r := by
  have hr_mp : r ≤ m + p := Nat.le_add_left r m |>.trans (Nat.add_le_add_left hr m)
  have h := choose_mul_sub_factorial_eq_div (m + p) r hr_mp
  have h₁ : ((m + p).choose r : ℚ) *
    ((m + p - r).factorial : ℚ) = ( (m + p).factorial : ℚ ) / ( r.factorial : ℚ ) := by
    exact h
  calc
    (p.factorial : ℚ) / ((m + p).factorial : ℚ) * (((m + p).choose r : ℚ) *
      ((m + p - r).factorial : ℚ) * A_coeff * G_r) =
        (p.factorial : ℚ) / ((m + p).factorial : ℚ) *
          ((( (m + p).factorial : ℚ ) / ( r.factorial : ℚ )) * A_coeff * G_r) := by
      rw [h₁]
    _ = (p.factorial : ℚ) / ((m + p).factorial : ℚ) *
      (((m + p).factorial : ℚ) / (r.factorial : ℚ)) * A_coeff * G_r := by
      ring_nf
    _ = (p.factorial : ℚ) / (r.factorial : ℚ) * A_coeff * G_r := by
      by_cases h₂ : (m + p).factorial = 0 <;>
        by_cases h₃ : (r.factorial : ℚ) = 0 <;>
          by_cases h₄ : (p.factorial : ℚ) = 0 <;>
            field_simp [h₂, h₃, h₄]

lemma gap_sum_simplify {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    ((-1 : ℚ)^G.m * (p.factorial : ℚ)) / (((G.m + p).factorial : ℚ) * (G.piM : ℚ)) *
      ((-1 : ℚ)^G.m * (G.piM : ℚ) *
        ∑ r ∈ Finset.range (p + 1),
          ((G.m + p).choose r : ℚ) * ((G.m + p - r).factorial : ℚ) *
            (PowerSeries.coeff (p - r)) G.ASeries * S.gapPowerSum r) =
    ∑ r ∈ Finset.range (p + 1),
      ((p.factorial : ℚ) / (r.factorial : ℚ)) *
        (PowerSeries.coeff (p - r)) G.ASeries * S.gapPowerSum r := by
  rw [outer_factor_cancel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  exact term_simplify G.m p r (Nat.lt_succ_iff.mp hr)
    ((PowerSeries.coeff (p - r)) G.ASeries) (S.gapPowerSum r)

/-- Auxiliary series obtained by evaluating `Q_S` at `t ↦ ∑ jⁿ t^n / n!` per coordinate. -/
noncomputable def QExpSeries {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    PowerSeries ℚ :=
  ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) •
    (PowerSeries.X ^ (G.m - 1) * G.BSeries +
     PowerSeries.X ^ G.m * G.ASeries *
       PowerSeries.mk fun n => ∑ g ∈ S.gaps, (g : ℚ)^n / (n.factorial : ℚ))

/-- Auxiliary helper: `Q_S` minus its constant term,
  evaluated coefficient-wise on the exponential expansion. -/
noncomputable def hilbertNumeratorExpSub {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    (∑ j ∈ Finset.range G.hilbertNumeratorDegBound, (G.hilbertNumerator.coeff j : ℚ) * (j : ℚ)^n) /
      (n.factorial : ℚ)

lemma hilbertNumerator_exp_sub_coeff {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (PowerSeries.coeff n) (hilbertNumeratorExpSub G) =
      (∑ j ∈ Finset.range G.hilbertNumeratorDegBound,
        (G.hilbertNumerator.coeff j : ℚ) * (j : ℚ)^n) /
        (n.factorial : ℚ) := by
  simp only [hilbertNumeratorExpSub, PowerSeries.coeff_mk]

lemma alternatingPowerSum_eq_neg_sum {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) (hn : 1 ≤ n) :
    G.alternatingPowerSum n =
      -(∑ j ∈ Finset.range G.hilbertNumeratorDegBound,
        (G.hilbertNumerator.coeff j : ℚ) * (j : ℚ)^n) := by
  unfold NumericalSemigroupGenerators.alternatingPowerSum
    NumericalSemigroupGenerators.numeratorCoeff
  have hn_ne : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have h0_pow : (0 : ℚ) ^ n = 0 := zero_pow hn_ne
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj0 : j = 0
  · subst hj0
    simp only [↓reduceIte, Int.cast_zero, Nat.cast_zero, h0_pow, mul_zero, neg_zero]
  · simp only [hj0, ↓reduceIte, Int.cast_neg, neg_mul]

lemma alternatingPowerSum_eq_coeff_hilbert_exp {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) (hn : 1 ≤ n) :
    G.alternatingPowerSum n =
      -((n.factorial : ℚ) * (PowerSeries.coeff n) (hilbertNumeratorExpSub G)) := by
  rw [hilbertNumerator_exp_sub_coeff, alternatingPowerSum_eq_neg_sum G n hn]
  congr 1
  have hfact : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp

lemma B_term_coeff_shift {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    (PowerSeries.coeff (G.m + p)) (PowerSeries.X ^ (G.m - 1) * G.BSeries) =
    (PowerSeries.coeff (p + 1)) G.BSeries := by
  have hm_pos : 1 ≤ G.m := G.hm_pos
  have h₁ : (G.m : ℕ) - 1 ≤ G.m + p := by omega
  have h₂ : (G.m + p : ℕ) - (G.m - 1 : ℕ) = p + 1 := by omega
  have h₃ : (PowerSeries.coeff (G.m + p)) (PowerSeries.X ^ (G.m - 1) *
    G.BSeries) = (PowerSeries.coeff ((G.m + p) - (G.m - 1))) G.BSeries := by
    rw [PowerSeries.coeff_X_pow_mul']
    simp [h₁]
  rw [h₃, h₂]

lemma coeff_A_mul_E {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    (PowerSeries.coeff p) (G.ASeries * PowerSeries.mk fun n => ∑ g ∈ S.gaps,
      (g : ℚ)^n / (n.factorial : ℚ)) =
    ∑ r ∈ Finset.range (p + 1), (PowerSeries.coeff (p - r)) G.ASeries * (∑ g ∈ S.gaps,
      (g : ℚ)^r / (r.factorial : ℚ)) := by
  have h₁ : (PowerSeries.coeff p) (G.ASeries * PowerSeries.mk fun n => ∑ g ∈ S.gaps,
    (g : ℚ)^n / (n.factorial : ℚ)) =
      ∑ ij ∈ Finset.antidiagonal p,
        (PowerSeries.coeff ij.1) G.ASeries *
          (PowerSeries.coeff ij.2 (PowerSeries.mk fun n => ∑ g ∈ S.gaps,
            (g : ℚ)^n / (n.factorial : ℚ))) := by
    rw [PowerSeries.coeff_mul]
  have h₂ : ∑ ij ∈ Finset.antidiagonal p,
    (PowerSeries.coeff ij.1) G.ASeries *
      (PowerSeries.coeff ij.2 (PowerSeries.mk fun n => ∑ g ∈ S.gaps,
        (g : ℚ)^n / (n.factorial : ℚ))) =
      ∑ r ∈ Finset.range (p + 1), (PowerSeries.coeff (p - r)) G.ASeries * (∑ g ∈ S.gaps,
        (g : ℚ)^r / (r.factorial : ℚ)) := by
    have h₃ : ∑ ij ∈ Finset.antidiagonal p,
      (PowerSeries.coeff ij.1) G.ASeries *
        (PowerSeries.coeff ij.2 (PowerSeries.mk fun n => ∑ g ∈ S.gaps,
          (g : ℚ)^n / (n.factorial : ℚ))) =
        ∑ ij ∈ Finset.antidiagonal p, (PowerSeries.coeff ij.1) G.ASeries * (∑ g ∈ S.gaps,
          (g : ℚ)^ij.2 / (ij.2.factorial : ℚ)) := by
      apply Finset.sum_congr rfl
      intro ij _
      rw [PowerSeries.coeff_mk]
    rw [h₃]
    apply Eq.symm
    apply Finset.sum_bij (fun (r : ℕ) _ => (⟨p - r, r⟩ : ℕ × ℕ))
    · intros r hr
      rw [Finset.mem_range] at hr
      rw [Finset.mem_antidiagonal]
      omega
    · intros r1 _ r2 _ heq
      simp only [Prod.mk.injEq] at heq
      exact heq.2
    · rintro ⟨a, b⟩ hab
      rw [Finset.mem_antidiagonal] at hab
      refine ⟨b, ?_, ?_⟩
      · rw [Finset.mem_range]; omega
      · simp only [Prod.mk.injEq]
        exact ⟨by omega, trivial⟩
    · intros r _; rfl
  calc
    (PowerSeries.coeff p) (G.ASeries * PowerSeries.mk fun n => ∑ g ∈ S.gaps,
      (g : ℚ)^n / (n.factorial : ℚ)) = ∑ ij ∈ Finset.antidiagonal p,
        (PowerSeries.coeff ij.1) G.ASeries *
          (PowerSeries.coeff ij.2 (PowerSeries.mk fun n => ∑ g ∈ S.gaps,
            (g : ℚ)^n / (n.factorial : ℚ))) := by rw [h₁]
    _ = ∑ r ∈ Finset.range (p + 1), (PowerSeries.coeff (p - r)) G.ASeries * (∑ g ∈ S.gaps,
      (g : ℚ)^r / (r.factorial : ℚ)) := by rw [h₂]

lemma sum_swap_gaps_range {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    ∑ r ∈ Finset.range (p + 1), (PowerSeries.coeff (p - r)) G.ASeries * (∑ g ∈ S.gaps,
      (g : ℚ)^r / (r.factorial : ℚ)) =
    ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
      (PowerSeries.coeff (p - r)) G.ASeries * (g : ℚ)^r / (r.factorial : ℚ) := by
  have h₁ : ∑ r ∈ Finset.range (p + 1), (PowerSeries.coeff (p - r)) G.ASeries * (∑ g ∈ S.gaps,
    (g : ℚ)^r / (r.factorial : ℚ)) = ∑ r ∈ Finset.range (p + 1), ∑ g ∈ S.gaps,
      (PowerSeries.coeff (p - r)) G.ASeries * ((g : ℚ)^r / (r.factorial : ℚ)) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
  rw [h₁]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro r _
  ring

lemma gap_term_coeff_shift {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    (PowerSeries.coeff (G.m + p)) (PowerSeries.X ^ G.m * G.ASeries *
       PowerSeries.mk fun n => ∑ g ∈ S.gaps, (g : ℚ)^n / (n.factorial : ℚ)) =
    ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
      (PowerSeries.coeff (p - r)) G.ASeries * (g : ℚ)^r / (r.factorial : ℚ) := by
  have h1 : PowerSeries.X ^ G.m * G.ASeries *
            (PowerSeries.mk fun n => ∑ g ∈ S.gaps, (g : ℚ)^n / (n.factorial : ℚ)) =
            PowerSeries.X ^ G.m * (G.ASeries *
            (PowerSeries.mk fun n => ∑ g ∈ S.gaps, (g : ℚ)^n / (n.factorial : ℚ))) := by ring
  rw [h1]
  rw [add_comm]
  rw [PowerSeries.coeff_X_pow_mul]
  rw [coeff_A_mul_E]
  exact sum_swap_gaps_range G p

lemma Q_exp_coeff_at_m_plus_p {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ)
  :
    (PowerSeries.coeff (G.m + p)) (QExpSeries G) =
    ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) *
      ((PowerSeries.coeff (p + 1)) G.BSeries +
       ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
         (PowerSeries.coeff (p - r)) G.ASeries * (g : ℚ)^r / (r.factorial : ℚ)) := by
  unfold QExpSeries
  rw [PowerSeries.coeff_smul]
  rw [map_add]
  rw [B_term_coeff_shift, gap_term_coeff_shift]
  simp only [smul_eq_mul]

lemma gap_coeff_to_leibniz {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    ((G.m + p).factorial : ℚ) *
      ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
        (PowerSeries.coeff (p - r)) G.ASeries * (g : ℚ)^r / (r.factorial : ℚ) =
    ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
        ((G.m + p).factorial : ℚ) / (r.factorial : ℚ) *
          (PowerSeries.coeff (p - r)) G.ASeries * (g : ℚ)^r := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hr_fac : (r.factorial : ℚ) ≠ 0 := by positivity
  field_simp [hr_fac]

lemma gap_sum_swap {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
        ((G.m + p).factorial : ℚ) / (r.factorial : ℚ) *
          (PowerSeries.coeff (p - r)) G.ASeries * (g : ℚ)^r =
    ∑ r ∈ Finset.range (p + 1),
      ((G.m + p).choose r : ℚ) * ((G.m + p - r).factorial : ℚ) *
        (PowerSeries.coeff (p - r)) G.ASeries * S.gapPowerSum r := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  have hrp : r ≤ p := Nat.lt_succ_iff.mp hr
  have hr_mp : r ≤ G.m + p := Nat.le_add_left r G.m |>.trans (Nat.add_le_add_left hrp G.m)
  have h_choose := choose_mul_sub_factorial_eq_div (G.m + p) r hr_mp
  unfold NumericalSemigroup.gapPowerSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  calc ((G.m + p).factorial : ℚ) / (r.factorial : ℚ) *
        (PowerSeries.coeff (p - r)) G.ASeries * (g : ℚ)^r
      = (((G.m + p).choose r : ℚ) * ((G.m + p - r).factorial : ℚ)) *
        (PowerSeries.coeff (p - r)) G.ASeries * (g : ℚ)^r := by rw [h_choose]
    _ = ((G.m + p).choose r : ℚ) * ((G.m + p - r).factorial : ℚ) *
        (PowerSeries.coeff (p - r)) G.ASeries * (g : ℚ)^r := by ring

lemma gap_term_final_form {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    ((G.m + p).factorial : ℚ) *
      ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
        (PowerSeries.coeff (p - r)) G.ASeries * (g : ℚ)^r / (r.factorial : ℚ) =
    ∑ r ∈ Finset.range (p + 1),
      ((G.m + p).choose r : ℚ) * ((G.m + p - r).factorial : ℚ) *
        (PowerSeries.coeff (p - r)) G.ASeries * S.gapPowerSum r := by
  rw [gap_coeff_to_leibniz, gap_sum_swap]

/-- For a polynomial `P : ℤ[X]`,
  the formal power series `∑ₙ (P.coeff n : ℚ) · t^n / n!` minus its constant term. -/
noncomputable def expPolySub (P : Polynomial ℤ) : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    (∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j : ℚ) * (j : ℚ)^n) / (n.factorial : ℚ)

lemma exp_poly_sub_coeff (P : Polynomial ℤ) (n : ℕ) :
    (PowerSeries.coeff n) (expPolySub P) =
    (∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j : ℚ) * (j : ℚ)^n) / (n.factorial : ℚ) := by
  simp only [expPolySub, PowerSeries.coeff_mk]

lemma exp_poly_sub_sum_extend (P : Polynomial ℤ) (k : ℕ) (n : ℕ) (hk : P.natDegree + 1 ≤ k) :
    ∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j : ℚ) * (j : ℚ)^n =
    ∑ j ∈ Finset.range k, (P.coeff j : ℚ) * (j : ℚ)^n := by
  have h_subset : Finset.range (P.natDegree + 1) ⊆ Finset.range k := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have h_extra_zero : ∀ (j : ℕ),
    j ∈ Finset.range k → j ∉ Finset.range (P.natDegree + 1) → (P.coeff j : ℚ) * (j : ℚ)^n = 0 := by
    intro j _ hj'
    have h₂ : ¬(j < P.natDegree + 1) := by
      intro h
      apply hj'
      simp_all [Finset.mem_range]
    have h₄ : (P.coeff j : ℤ) = 0 := by
      have h₅ : P.natDegree < j := by omega
      have h₆ : P.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt h₅
      simp_all
    have h₅ : (P.coeff j : ℚ) = 0 := by norm_cast at h₄ ⊢
    simp [h₅]
  apply Finset.sum_subset h_subset
  intro j hj hj'
  exact h_extra_zero j hj hj'

lemma hilbertNumerator_natDegree_le_pred_bound {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) :
    G.hilbertNumerator.natDegree ≤ G.hilbertNumeratorDegBound - 1 := by
  unfold NumericalSemigroupGenerators.hilbertNumerator
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  calc ((Polynomial.monomial n) _).natDegree
      ≤ n := Polynomial.natDegree_monomial_le _
    _ ≤ G.hilbertNumeratorDegBound - 1 := by
        rw [Finset.mem_range] at hn
        omega

lemma hilbertNumeratorDegBound_pos {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) :
    0 < G.hilbertNumeratorDegBound := by
  unfold NumericalSemigroupGenerators.hilbertNumeratorDegBound
  omega

lemma hilbertNumerator_natDegree_lt_bound {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) :
    G.hilbertNumerator.natDegree + 1 ≤ G.hilbertNumeratorDegBound := by
  have h := hilbertNumerator_natDegree_le_pred_bound G
  have hpos := hilbertNumeratorDegBound_pos G
  omega

lemma hilbertNumerator_exp_sub_eq_exp_poly_sub {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) :
    hilbertNumeratorExpSub G = expPolySub G.hilbertNumerator := by
  apply PowerSeries.ext
  intro n
  simp only [hilbertNumeratorExpSub, expPolySub, PowerSeries.coeff_mk]
  congr 1
  exact (exp_poly_sub_sum_extend G.hilbertNumerator G.hilbertNumeratorDegBound n
    (hilbertNumerator_natDegree_lt_bound G)).symm

lemma Q_exp_series_coeff {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (PowerSeries.coeff n) (QExpSeries G) =
    ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) *
      ((PowerSeries.coeff n) (PowerSeries.X ^ (G.m - 1) * G.BSeries) +
       (PowerSeries.coeff n) (PowerSeries.X ^ G.m * G.ASeries *
         PowerSeries.mk fun k => ∑ g ∈ S.gaps, (g : ℚ)^k / (k.factorial : ℚ))) := by
  simp only [QExpSeries, PowerSeries.coeff_smul, smul_eq_mul, map_add]

lemma j_lt_bound_of_mem_range_natDegree {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (j : ℕ)
    (hj : j ∈ Finset.range (G.hilbertNumerator.natDegree + 1)) :
    j < G.hilbertNumeratorDegBound := by
  have hj_lt := Finset.mem_range.mp hj
  exact Nat.lt_of_lt_of_le hj_lt (hilbertNumerator_natDegree_lt_bound G)

lemma hilbert_sum_decomposition_natDegree {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) :
    ∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (G.hilbertNumerator.coeff j : ℚ) * (j : ℚ)^n =
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ k ∈ Finset.range (j + 1), (G.productPolynomial.coeff k : ℚ)) * (j : ℚ)^n) -
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ g ∈ S.gaps.filter (· ≤ j), (G.productPolynomial.coeff (j - g) : ℚ)) * (j : ℚ)^n) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj_lt : j < G.hilbertNumeratorDegBound := j_lt_bound_of_mem_range_natDegree G j hj
  have coeff_eq := NumericalSemigroupGenerators.hilbertNumerator_coeff_lt G j hj_lt
  simp only [coeff_eq, Int.cast_sub, Int.cast_sum]
  ring

lemma partial_sum_eq_zero_when_large {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (D : ℕ) (hD : G.productPolynomial.natDegree ≤ D) :
    (∑ k ∈ Finset.range (D + 1), (G.productPolynomial.coeff k : ℚ)) = 0 := by
  have h1 : ∑ k ∈ Finset.range (D + 1), G.productPolynomial.coeff k =
            ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
              G.productPolynomial.coeff k := by
    rcases Nat.eq_or_lt_of_le hD with heq | hlt
    · rw [heq]
    · exact NumericalSemigroupGenerators.sum_coeff_large_eq_sum_coeff_deg G D (by omega)
  have h2 : ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1), G.productPolynomial.coeff k =
            Polynomial.eval 1 G.productPolynomial :=
              NumericalSemigroupGenerators.sum_coeff_eq_eval_one G
  have h3 : Polynomial.eval 1 G.productPolynomial = 0 :=
    NumericalSemigroupGenerators.productPolynomial_eval_one G
  simp only [← Int.cast_sum]
  rw [h1, h2, h3]
  simp

lemma leadingCoeff_one_sub_X_pow (k : ℕ) (hk : 0 < k) :
    (1 - Polynomial.X ^ k : Polynomial ℤ).leadingCoeff = -1 := by
  have h₁ : (1 - Polynomial.X ^ k : Polynomial ℤ) = -(Polynomial.X ^ k - 1 : Polynomial ℤ) :=
    by ring
  have h₂ : (Polynomial.X ^ k - 1 : Polynomial ℤ).Monic := by
    apply Polynomial.monic_X_pow_sub_C
    omega
  simp only [h₁, Polynomial.leadingCoeff_neg, h₂.leadingCoeff]

lemma productPolynomial_leadingCoeff {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    G.productPolynomial.leadingCoeff = (-1 : ℤ) ^ G.m := by
  unfold NumericalSemigroupGenerators.productPolynomial
  rw [Polynomial.leadingCoeff_prod]
  have h : ∀ i : Fin G.m, (1 - Polynomial.X ^ G.d i : Polynomial ℤ).leadingCoeff = -1 := by
    intro i
    exact leadingCoeff_one_sub_X_pow (G.d i) (G.hd_pos i)
  simp only [h]
  exact Fin.prod_const G.m (-1 : ℤ)

lemma natDegree_ge_of_gaps_nonempty {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (h : S.gaps.Nonempty) :
    G.productPolynomial.natDegree ≤ G.hilbertNumerator.natDegree := by
  have hge : G.productPolynomial.natDegree + S.gaps.sup id ≤ G.hilbertNumerator.natDegree := by
    apply Polynomial.le_natDegree_of_ne_zero
    unfold NumericalSemigroupGenerators.hilbertNumerator
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single (G.productPolynomial.natDegree + S.gaps.sup id)]
    · simp only [↓reduceIte, ne_eq, sub_eq_zero]
      intro hcontra
      obtain ⟨gmax, hgmax_mem, hgmax_eq⟩ := Finset.exists_mem_eq_sup S.gaps h id
      simp only [id_eq] at hgmax_eq
      have hfilter : S.gaps.filter (· ≤ G.productPolynomial.natDegree + S.gaps.sup id) = S.gaps :=
        by
        apply Finset.filter_true_of_mem
        intro g hg
        calc g ≤ S.gaps.sup id := Finset.le_sup (f := id) hg
             _ ≤ G.productPolynomial.natDegree + S.gaps.sup id := le_add_self
      have hsum_partial : ∑ k ∈ Finset.range (G.productPolynomial.natDegree + S.gaps.sup id + 1),
          G.productPolynomial.coeff k = 0 := by
        have hge : 1 ≤ S.gaps.sup id := by
          rw [hgmax_eq]
          have hgap_pos : 0 < gmax := by
            by_contra h0
            push Not at h0
            interval_cases gmax
            · have : (0 : ℕ) ∈ S.gaps := hgmax_mem
              have hmem : 0 ∈ S.carrier := S.zero_mem
              have hnotmem : 0 ∉ S.carrier := by
                have : S.gaps = S.finite_complement.toFinset := rfl
                rw [this] at hgmax_mem
                rw [Set.Finite.mem_toFinset] at hgmax_mem
                exact hgmax_mem
              contradiction
          omega
        have h1 :=
          NumericalSemigroupGenerators.sum_coeff_large_eq_sum_coeff_deg G
            (G.productPolynomial.natDegree + S.gaps.sup id) (by omega)
        rw [h1, NumericalSemigroupGenerators.sum_coeff_eq_eval_one G,
          NumericalSemigroupGenerators.productPolynomial_eval_one G]
      rw [hfilter] at hcontra
      rw [Finset.sum_eq_single_of_mem gmax hgmax_mem] at hcontra
      · have hsub : G.productPolynomial.natDegree +
        S.gaps.sup id - gmax = G.productPolynomial.natDegree := by
          rw [hgmax_eq, Nat.add_sub_cancel]
        rw [hsub, Polynomial.coeff_natDegree, productPolynomial_leadingCoeff G] at hcontra
        simp only [hsum_partial] at hcontra
        exact Int.neg_one_pow_ne_zero hcontra.symm
      · intro g hg hne
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hle : g ≤ gmax := by
          have := Finset.le_sup (f := id) hg
          simp only [id_eq, hgmax_eq] at this
          exact this
        have hlt : g < gmax := lt_of_le_of_ne hle hne
        simp only [hgmax_eq]
        omega
    · intro j _ hj
      simp [hj]
    · intro hn
      simp only [Finset.mem_range, not_lt] at hn
      unfold NumericalSemigroupGenerators.hilbertNumeratorDegBound at hn
      omega
  omega

lemma telescoping_general (D n : ℕ) (P : Polynomial ℤ) :
    (∑ j ∈ Finset.range (D + 1),
      (∑ k ∈ Finset.range (j + 1), (P.coeff k : ℚ)) *
      (((j : ℚ) + 1)^n - (j : ℚ)^n)) =
    (∑ k ∈ Finset.range (D + 1), (P.coeff k : ℚ)) * ((D : ℚ) + 1)^n -
    (∑ j ∈ Finset.range (D + 1), (P.coeff j : ℚ) * (j : ℚ)^n) := by
  have h₀ : ∀ (m : ℕ), (∑ j ∈ Finset.range (m + 1),
      (∑ k ∈ Finset.range (j + 1), (P.coeff k : ℚ)) *
      (((j : ℚ) + 1)^n - (j : ℚ)^n)) =
    (∑ k ∈ Finset.range (m + 1), (P.coeff k : ℚ)) * ((m : ℚ) + 1)^n -
    (∑ j ∈ Finset.range (m + 1), (P.coeff j : ℚ) * (j : ℚ)^n) := by
    intro m
    induction m with
    | zero =>
      simp [Finset.sum_range_succ]
      ring_nf
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      simp [Finset.sum_range_succ, add_assoc] at *
      ring_nf at *
  exact h₀ D

lemma telescoping_sum_gaps_nonempty {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (n : ℕ) (hgaps : S.gaps.Nonempty) :
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ k ∈ Finset.range (j + 1), (G.productPolynomial.coeff k : ℚ)) *
      (((j : ℚ) + 1)^n - (j : ℚ)^n)) =
    - (∑ j ∈ Finset.range (G.productPolynomial.natDegree + 1),
        (G.productPolynomial.coeff j : ℚ) * (j : ℚ)^n) := by
  set D := G.hilbertNumerator.natDegree with hD_def
  set d := G.productPolynomial.natDegree with hd_def
  have htele := telescoping_general D n G.productPolynomial
  have hDge : d ≤ D := natDegree_ge_of_gaps_nonempty G hgaps
  have hSD : ∑ k ∈ Finset.range (D + 1), (G.productPolynomial.coeff k : ℚ) = 0 :=
    partial_sum_eq_zero_when_large G D hDge
  rw [htele, hSD, zero_mul, zero_sub]
  have hext : ∑ j ∈ Finset.range (d + 1), (G.productPolynomial.coeff j : ℚ) * (j : ℚ)^n =
              ∑ j ∈ Finset.range (D + 1), (G.productPolynomial.coeff j : ℚ) * (j : ℚ)^n :=
    exp_poly_sub_sum_extend G.productPolynomial (D + 1) n (Nat.add_le_add_right hDge 1)
  rw [← hext]

lemma hilbertNumerator_coeff_eq_partial_sum_gaps_empty {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (hgaps : ¬S.gaps.Nonempty) (j : ℕ)
    (hj : j < G.hilbertNumeratorDegBound) :
    G.hilbertNumerator.coeff j = ∑ k ∈ Finset.range (j + 1), G.productPolynomial.coeff k := by
  have h₁ : S.gaps = ∅ := by
    by_contra h
    have h₂ : S.gaps.Nonempty := Finset.nonempty_iff_ne_empty.mpr h
    contradiction
  have h₂ : ∀ (n : ℕ), ∑ g ∈ S.gaps.filter (· ≤ n), G.productPolynomial.coeff (n - g) = 0 := by
    intro n
    rw [h₁]
    simp [Finset.filter_empty]
  have h₃ : ∀ (n : ℕ), n < G.hilbertNumeratorDegBound →
      G.hilbertNumerator.coeff n = ∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k := by
    intro n hn
    have h₄ : G.hilbertNumerator.coeff n =
        (∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k) -
        ∑ g ∈ S.gaps.filter (· ≤ n), G.productPolynomial.coeff (n - g) := by
      simp only [NumericalSemigroupGenerators.hilbertNumerator]
      simp [Polynomial.coeff_monomial, Finset.mem_range, hn]
    rw [h₄, h₂ n, sub_zero]
  exact h₃ j hj

lemma partial_sum_zero_after_natDegree_gaps_empty {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (hgaps : ¬S.gaps.Nonempty) (j : ℕ)
    (hj1 : G.hilbertNumerator.natDegree < j) (hj2 : j < G.hilbertNumeratorDegBound) :
    (∑ k ∈ Finset.range (j + 1), (G.productPolynomial.coeff k : ℚ)) = 0 := by
  have h_coeff_eq := hilbertNumerator_coeff_eq_partial_sum_gaps_empty G hgaps j hj2
  have h_coeff_zero : G.hilbertNumerator.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hj1
  have h_sum_zero : ∑ k ∈ Finset.range (j + 1), G.productPolynomial.coeff k = 0 := by
    rw [← h_coeff_eq, h_coeff_zero]
  rw [← Int.cast_sum]
  simp only [h_sum_zero, Int.cast_zero]

lemma coeff_eq_partial_sum_diff (P : Polynomial ℤ) (n : ℕ) :
    (P.coeff n : ℚ) = (∑ k ∈ Finset.range (n + 1), (P.coeff k : ℚ)) -
                      (∑ k ∈ Finset.range n, (P.coeff k : ℚ)) := by
  have h_sum_split : (∑ k ∈ Finset.range (n + 1), (P.coeff k : ℚ)) =
      (∑ k ∈ Finset.range n, (P.coeff k : ℚ)) + (P.coeff n : ℚ) := by
    rw [Finset.sum_range_succ]
  rw [h_sum_split]
  ring

lemma coeff_at_D_plus_one_gaps_empty {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (hgaps : ¬S.gaps.Nonempty)
    (hbound : G.hilbertNumerator.natDegree + 1 < G.hilbertNumeratorDegBound) :
    (G.productPolynomial.coeff (G.hilbertNumerator.natDegree + 1) : ℚ) =
    -(∑ k ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ)) := by
  set D := G.hilbertNumerator.natDegree with hD_def
  have h1 : (G.productPolynomial.coeff (D + 1) : ℚ) =
      (∑ k ∈ Finset.range (D + 1 + 1), (G.productPolynomial.coeff k : ℚ)) -
      (∑ k ∈ Finset.range (D + 1), (G.productPolynomial.coeff k : ℚ)) :=
    coeff_eq_partial_sum_diff G.productPolynomial (D + 1)
  have h2 : (∑ k ∈ Finset.range (D + 1 + 1), (G.productPolynomial.coeff k : ℚ)) = 0 := by
    apply partial_sum_zero_after_natDegree_gaps_empty G hgaps (D + 1)
    · exact Nat.lt_add_one D
    · exact hbound
  rw [h1, h2, zero_sub]

lemma coeff_zero_after_D_plus_one_gaps_empty {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (hgaps : ¬S.gaps.Nonempty)
    (_hbound : G.hilbertNumerator.natDegree + 1 < G.hilbertNumeratorDegBound)
    (j : ℕ) (hj_lo : G.hilbertNumerator.natDegree + 2 ≤ j)
    (hj_hi : j ≤ G.productPolynomial.natDegree) :
    (G.productPolynomial.coeff j : ℚ) = 0 := by
  set D := G.hilbertNumerator.natDegree with hD_def
  have hcoeff_rel : (G.productPolynomial.coeff j : ℚ) =
      (∑ k ∈ Finset.range (j + 1), (G.productPolynomial.coeff k : ℚ)) -
      (∑ k ∈ Finset.range j, (G.productPolynomial.coeff k : ℚ)) :=
    coeff_eq_partial_sum_diff G.productPolynomial j
  rw [hcoeff_rel]
  have hj_bound : j < G.hilbertNumeratorDegBound := by
    unfold NumericalSemigroupGenerators.hilbertNumeratorDegBound at _hbound ⊢
    omega
  have hjm1_bound : j - 1 < G.hilbertNumeratorDegBound := by omega
  have hj_gt_D : D < j := by omega
  have hjm1_gt_D : D < j - 1 := by omega
  have hS_j_zero : (∑ k ∈ Finset.range (j + 1), (G.productPolynomial.coeff k : ℚ)) = 0 :=
    partial_sum_zero_after_natDegree_gaps_empty G hgaps j hj_gt_D hj_bound
  have hS_jm1_zero : (∑ k ∈ Finset.range j, (G.productPolynomial.coeff k : ℚ)) = 0 := by
    have heq : j = (j - 1) + 1 := by omega
    rw [heq]
    exact partial_sum_zero_after_natDegree_gaps_empty G hgaps (j - 1) hjm1_gt_D hjm1_bound
  rw [hS_j_zero, hS_jm1_zero]
  ring

lemma sum_tail_eq_zero {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) (hgaps : ¬S.gaps.Nonempty)
    (hbound : G.hilbertNumerator.natDegree + 1 < G.hilbertNumeratorDegBound) :
    (∑ j ∈ Finset.Ico (G.hilbertNumerator.natDegree + 2) (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff j : ℚ) * (j : ℚ)^n) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.mem_Ico] at hj
  have hj_lo : G.hilbertNumerator.natDegree + 2 ≤ j := hj.1
  have hj_hi : j ≤ G.productPolynomial.natDegree := by omega
  have hcoeff_zero : (G.productPolynomial.coeff j : ℚ) = 0 :=
    coeff_zero_after_D_plus_one_gaps_empty G hgaps hbound j hj_lo hj_hi
  rw [hcoeff_zero]
  ring

lemma poly_sum_tail_eq_neg_partial_gaps_empty {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) (hgaps : ¬S.gaps.Nonempty)
    (hbound : G.hilbertNumerator.natDegree + 1 < G.hilbertNumeratorDegBound) :
    (∑ j ∈ Finset.Ico (G.hilbertNumerator.natDegree + 1) (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff j : ℚ) * (j : ℚ)^n) =
    -(∑ k ∈ Finset.range (G.hilbertNumerator.natDegree + 1), (G.productPolynomial.coeff k : ℚ)) *
     ((G.hilbertNumerator.natDegree : ℚ) + 1)^n := by
  set D := G.hilbertNumerator.natDegree with hD_def
  set d := G.productPolynomial.natDegree with hd_def
  by_cases hcase : D + 1 > d
  · have hempty : Finset.Ico (D + 1) (d + 1) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    simp only [hempty, Finset.sum_empty]
    have hDd : d ≤ D := by omega
    have hS_D_zero : (∑ k ∈ Finset.range (D + 1), (G.productPolynomial.coeff k : ℚ)) = 0 :=
      partial_sum_eq_zero_when_large G D hDd
    rw [hS_D_zero]
    ring
  · push Not at hcase
    have hsplit : Finset.Ico (D + 1) (d + 1) = {D + 1} ∪ Finset.Ico (D + 2) (d + 1) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]
      constructor
      · intro ⟨hlo, hhi⟩
        by_cases hx : x = D + 1
        · left; exact hx
        · right; constructor <;> omega
      · intro h
        cases h with
        | inl h => rw [h]; constructor <;> omega
        | inr h => obtain ⟨hlo, hhi⟩ := h; constructor <;> omega
    have hdisj : Disjoint ({D + 1} : Finset ℕ) (Finset.Ico (D + 2) (d + 1)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_singleton] at hx
      simp only [Finset.mem_Ico] at hx'
      omega
    rw [hsplit, Finset.sum_union hdisj]
    simp only [Finset.sum_singleton]
    rw [sum_tail_eq_zero G n hgaps hbound]
    rw [add_zero]
    rw [coeff_at_D_plus_one_gaps_empty G hgaps hbound]
    simp only [← hD_def, Nat.cast_add, Nat.cast_one, neg_mul]

lemma telescoping_sum_gaps_empty {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (n : ℕ) (hgaps : ¬S.gaps.Nonempty) :
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ k ∈ Finset.range (j + 1), (G.productPolynomial.coeff k : ℚ)) *
      (((j : ℚ) + 1)^n - (j : ℚ)^n)) =
    - (∑ j ∈ Finset.range (G.productPolynomial.natDegree + 1),
        (G.productPolynomial.coeff j : ℚ) * (j : ℚ)^n) := by
  set D := G.hilbertNumerator.natDegree with hD_def
  set d := G.productPolynomial.natDegree with hd_def
  rw [telescoping_general D n G.productPolynomial]
  simp only [Finset.not_nonempty_iff_eq_empty] at hgaps
  have hgaps_sup : S.gaps.sup id = 0 := by rw [hgaps]; simp
  by_cases hbound : D + 1 < G.hilbertNumeratorDegBound
  · have hle : D + 1 ≤ d + 1 := by
      unfold NumericalSemigroupGenerators.hilbertNumeratorDegBound at hbound
      rw [hgaps_sup] at hbound
      omega
    rw [← Finset.sum_range_add_sum_Ico _ hle]
    have hgaps' : ¬S.gaps.Nonempty := by simp [hgaps]
    have htail := poly_sum_tail_eq_neg_partial_gaps_empty G n hgaps' hbound
    rw [htail]
    ring
  · push Not at hbound
    unfold NumericalSemigroupGenerators.hilbertNumeratorDegBound at hbound
    rw [hgaps_sup] at hbound
    have hDge : d ≤ D := Nat.lt_succ_iff.mp (Nat.succ_le_iff.mpr hbound)
    have hS_D_zero : (∑ k ∈ Finset.range (D + 1), (G.productPolynomial.coeff k : ℚ)) = 0 :=
      partial_sum_eq_zero_when_large G D hDge
    have hext := exp_poly_sub_sum_extend G.productPolynomial (D + 1) n (by omega)
    rw [← hext, hS_D_zero]
    ring

lemma telescoping_sum {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ k ∈ Finset.range (j + 1), (G.productPolynomial.coeff k : ℚ)) *
      (((j : ℚ) + 1)^n - (j : ℚ)^n)) =
    - (∑ j ∈ Finset.range (G.productPolynomial.natDegree + 1),
        (G.productPolynomial.coeff j : ℚ) * (j : ℚ)^n) := by
  by_cases hgaps : S.gaps.Nonempty
  · exact telescoping_sum_gaps_nonempty G n hgaps
  · exact telescoping_sum_gaps_empty G n hgaps


/-- Generating function for the partial sums of `P_S.coeff` along `Finset.range`. -/
noncomputable def partialSumGenFunc {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ k ∈ Finset.range (j + 1),
        (G.productPolynomial.coeff k : ℚ)) * (j : ℚ)^n) / (n.factorial : ℚ)

lemma partialSumGenFunc_coeff {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
  :
    (PowerSeries.coeff n) (partialSumGenFunc G) =
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ k ∈ Finset.range (j + 1),
        (G.productPolynomial.coeff k : ℚ)) * (j : ℚ)^n) / (n.factorial : ℚ) := by
  simp only [partialSumGenFunc, PowerSeries.coeff_mk]

lemma exp_poly_sub_one : expPolySub 1 = 1 := by
  ext n
  simp only [expPolySub, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  simp only [Polynomial.natDegree_one, Polynomial.coeff_one]
  rw [Finset.range_one, Finset.sum_singleton]
  simp only [↓reduceIte, CharP.cast_eq_zero]
  cases n with
  | zero => simp
  | succ n => simp [zero_pow (Nat.succ_ne_zero n)]

lemma coeff_mul_expand (P Q : Polynomial ℤ) (n : ℕ) :
    (PowerSeries.coeff n) (expPolySub P * expPolySub Q) =
    ∑ k ∈ Finset.range (n + 1),
      ((∑ a ∈ Finset.range (P.natDegree + 1), (P.coeff a : ℚ) * (a : ℚ)^k) / k.factorial) *
      ((∑ b ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff b : ℚ) * (b : ℚ)^(n - k)) / (n - k).factorial) := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  congr 1
  ext k
  simp only [expPolySub, PowerSeries.coeff_mk]

lemma lhs_to_triple_sum (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ((∑ a ∈ Finset.range (P.natDegree + 1), (P.coeff a : ℚ) * (a : ℚ)^k) / k.factorial) *
      ((∑ b ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff b : ℚ) * (b : ℚ)^(n - k)) / (n - k).factorial) =
    ∑ k ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (P.natDegree + 1),
        ∑ b ∈ Finset.range (Q.natDegree + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) / (k.factorial *
            (n - k).factorial) := by
  apply Finset.sum_congr rfl
  intro k _
  have h₂ : ((∑ a ∈ Finset.range (P.natDegree + 1), (P.coeff a : ℚ) * (a : ℚ)^k) / k.factorial) *
      ((∑ b ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff b : ℚ) * (b : ℚ)^(n - k)) / (n - k).factorial) =
    ((∑ a ∈ Finset.range (P.natDegree + 1),
      (P.coeff a : ℚ) * (a : ℚ)^k) * (∑ b ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff b : ℚ) * (b : ℚ)^(n - k))) / (k.factorial * (n - k).factorial) := by
    field_simp [mul_comm]
  rw [h₂]
  have h₃ : (∑ a ∈ Finset.range (P.natDegree + 1),
    (P.coeff a : ℚ) * (a : ℚ)^k) * (∑ b ∈ Finset.range (Q.natDegree + 1),
      (Q.coeff b : ℚ) * (b : ℚ)^(n - k)) =
      ∑ a ∈ Finset.range (P.natDegree + 1), ∑ b ∈ Finset.range (Q.natDegree + 1),
        (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) := by
    calc
      (∑ a ∈ Finset.range (P.natDegree + 1),
        (P.coeff a : ℚ) * (a : ℚ)^k) * (∑ b ∈ Finset.range (Q.natDegree + 1),
          (Q.coeff b : ℚ) * (b : ℚ)^(n - k)) =
          ∑ a ∈ Finset.range (P.natDegree + 1), ∑ b ∈ Finset.range (Q.natDegree + 1),
            ((P.coeff a : ℚ) * (a : ℚ)^k) * ((Q.coeff b : ℚ) * (b : ℚ)^(n - k)) := by
        rw [Finset.sum_mul_sum]
      _ = ∑ a ∈ Finset.range (P.natDegree + 1), ∑ b ∈ Finset.range (Q.natDegree + 1),
        (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring_nf
  rw [h₃]
  simp only [Finset.sum_div]

lemma term_factorial_to_choose (Pa Qb : ℚ) (a b k n : ℕ) (hk : k ≤ n) :
    Pa * Qb * (a : ℚ)^k * (b : ℚ)^(n - k) / (k.factorial * (n - k).factorial) =
    Pa * Qb * (a : ℚ)^k * (b : ℚ)^(n - k) * ((n.choose k : ℚ) / (n.factorial : ℚ)) := by
  have h₁ : (1 : ℚ) / (k.factorial * (n - k).factorial) = (n.choose k : ℚ) / (n.factorial : ℚ) := by
    have h₂ : (n.choose k : ℕ) * k.factorial * (n - k).factorial = n.factorial := by
      rw [Nat.choose_mul_factorial_mul_factorial hk]
    have h₃ : (n.choose k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ) = (n.factorial : ℚ) :=
      by
      norm_cast at h₂ ⊢
    have h₄ : (k.factorial : ℚ) ≠ 0 := by positivity
    have h₅ : ((n - k).factorial : ℚ) ≠ 0 := by positivity
    have h₆ : (n.factorial : ℚ) ≠ 0 := by positivity
    field_simp [h₄, h₅, h₆] at h₃ ⊢
    nlinarith
  have h₂ : Pa * Qb * (a : ℚ)^k * (b : ℚ)^(n - k) / (k.factorial * (n - k).factorial : ℚ) =
      Pa * Qb * (a : ℚ)^k * (b : ℚ)^(n - k) * ((n.choose k : ℚ) / (n.factorial : ℚ)) := by
    have h₃ : (Pa * Qb * (a : ℚ)^k * (b : ℚ)^(n - k) : ℚ) / (k.factorial * (n - k).factorial : ℚ) =
        (Pa * Qb * (a : ℚ)^k * (b : ℚ)^(n - k) : ℚ) * ((1 : ℚ) / (k.factorial *
          (n - k).factorial : ℚ)) := by
      ring_nf
    rw [h₃]
    rw [h₁]
  exact h₂

lemma natDegree_one_sub_X_pow_le (k : ℕ) :
    (1 - Polynomial.X ^ k : Polynomial ℤ).natDegree ≤ k := by
  have h₁ : (1 -
    Polynomial.X ^ k : Polynomial ℤ).natDegree ≤
      max (Polynomial.natDegree (1 : Polynomial ℤ)) (Polynomial.natDegree (Polynomial.X ^ k :
        Polynomial ℤ)) := by
    apply Polynomial.natDegree_sub_le
  have h₂ : Polynomial.natDegree (1 : Polynomial ℤ) = 0 := by
    simp [Polynomial.natDegree_one]
  have h₃ : Polynomial.natDegree (Polynomial.X ^ k : Polynomial ℤ) = k := by
    simp [Polynomial.natDegree_pow, Polynomial.natDegree_X]
  have h₄ : max (Polynomial.natDegree (1 : Polynomial ℤ)) (Polynomial.natDegree (Polynomial.X ^ k :
    Polynomial ℤ)) ≤ k := by
    rw [h₂, h₃]
    exact max_le_iff.mpr ⟨by simp, by simp⟩
  calc
    (1 - Polynomial.X ^ k : Polynomial ℤ).natDegree ≤
      max (Polynomial.natDegree (1 : Polynomial ℤ)) (Polynomial.natDegree (Polynomial.X ^ k :
        Polynomial ℤ)) := h₁
    _ ≤ k := h₄

lemma sum_coeff_one_sub_X_pow (k : ℕ) (_hk : 0 < k) :
    ∑ j ∈ Finset.range (k + 1), ((1 - Polynomial.X ^ k : Polynomial ℤ).coeff j : ℚ) = 0 := by
  aesop

lemma exp_poly_sub_one_sub_X_pow_coeff_zero (k : ℕ) (hk : 0 < k) :
    (PowerSeries.coeff 0) (expPolySub (1 - Polynomial.X ^ k)) = 0 := by
  unfold expPolySub
  rw [PowerSeries.coeff_mk]
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
  have h_deg : (1 - Polynomial.X ^ k : Polynomial ℤ).natDegree ≤ k := natDegree_one_sub_X_pow_le k
  have h_sum := sum_coeff_one_sub_X_pow k hk
  convert h_sum using 1
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro j hj hj_not
    simp only [Finset.mem_range] at hj hj_not
    have : (1 - Polynomial.X ^ k : Polynomial ℤ).natDegree < j := by omega
    simp only [Int.cast_eq_zero]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt this

lemma natDegree_one_sub_X_pow_eq (k : ℕ) (hk : 0 < k) :
    (1 - Polynomial.X ^ k : Polynomial ℤ).natDegree = k := by
  have h₁ : (1 - Polynomial.X ^ k : Polynomial ℤ).natDegree ≤ k := by
    have h₂ : (1 : Polynomial ℤ).natDegree = 0 := by
      simp [Polynomial.natDegree_one]
    have h₃ : (Polynomial.X ^ k : Polynomial ℤ).natDegree = k := by
      simp [Polynomial.natDegree_pow, Polynomial.natDegree_X]
    have h₄ : (1 -
      Polynomial.X ^ k : Polynomial ℤ).natDegree ≤
        max (1 : Polynomial ℤ).natDegree (Polynomial.X ^ k : Polynomial ℤ).natDegree := by
      apply Polynomial.natDegree_sub_le
    have h₅ : max (1 : Polynomial ℤ).natDegree (Polynomial.X ^ k : Polynomial ℤ).natDegree ≤ k := by
      simp [h₂, h₃]
    linarith
  have h₂ : (1 - Polynomial.X ^ k : Polynomial ℤ).natDegree ≥ k := by
    have h₃ : (1 - Polynomial.X ^ k : Polynomial ℤ).coeff k = -1 := by
      simp [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow]
      cases k <;> simp_all
    have h₅ : (1 - Polynomial.X ^ k : Polynomial ℤ).natDegree ≥ k := by
      by_contra h₆
      have h₇ : (1 - Polynomial.X ^ k : Polynomial ℤ).natDegree < k := by
        linarith
      have h₈ : (1 - Polynomial.X ^ k : Polynomial ℤ).coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        exact_mod_cast h₇
      rw [h₃] at h₈
      norm_num at h₈
    exact h₅
  linarith

lemma one_sub_X_pow_term_eq_zero (k n j : ℕ) (_hk : 0 < k) (hn : 1 ≤ n)
    (_hj_mem : j ∈ Finset.range (k + 1)) (hj_ne : j ≠ k) :
    ((1 - Polynomial.X ^ k : Polynomial ℤ).coeff j : ℚ) * (j : ℚ)^n = 0 := by
  have h₂ : ((1 - Polynomial.X ^ k : Polynomial ℤ).coeff j : ℚ) = 0 ∨ (j : ℚ) = 0 := by
    by_cases h : j = 0
    · right
      norm_cast
    · left
      have h₈ : (1 - Polynomial.X ^ k : Polynomial ℤ).coeff j = 0 := by
        have h₉ : (1 - Polynomial.X ^ k : Polynomial ℤ).coeff j = (1 : Polynomial ℤ).coeff j -
          (Polynomial.X ^ k : Polynomial ℤ).coeff j := by
          simp [Polynomial.coeff_sub]
        rw [h₉]
        have h₁₀ : (1 : Polynomial ℤ).coeff j = if j = 0 then 1 else 0 := by
          simp [Polynomial.coeff_one]
        have h₁₁ : (Polynomial.X ^ k : Polynomial ℤ).coeff j = if j = k then 1 else 0 := by
          simp [Polynomial.coeff_X_pow]
        rw [h₁₀, h₁₁]
        split_ifs at *
        simp_all (config := {decide := true})
      norm_cast at h₈ ⊢
  cases h₂ with
  | inl h₂ =>
    rw [h₂]
    norm_num
  | inr h₂ =>
    have h₃ : (j : ℕ) = 0 := by norm_cast at h₂ ⊢
    have h₅ : (j : ℚ) ^ n = 0 := by
      have h₈ : (j : ℚ) = 0 := by simp_all
      rw [h₈]
      have h₁₁ : n ≠ 0 := by linarith
      simp [h₁₁]
    calc
      ((1 - Polynomial.X ^ k : Polynomial ℤ).coeff j : ℚ) *
        (j : ℚ) ^ n = ((1 - Polynomial.X ^ k : Polynomial ℤ).coeff j : ℚ) * 0 := by rw [h₅]
      _ = 0 := by ring

lemma one_sub_X_pow_term_at_k (k n : ℕ) (hk : 0 < k) :
    ((1 - Polynomial.X ^ k : Polynomial ℤ).coeff k : ℚ) * (k : ℚ)^n = -((k : ℚ)^n) := by
  have h₁ : (1 - Polynomial.X ^ k : Polynomial ℤ).coeff k = (-1 : ℤ) := by
    simp [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow]
    cases k <;> simp_all
  rw [h₁]
  norm_cast
  simp

lemma one_sub_X_pow_sum_eq (k n : ℕ) (hk : 0 < k) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range ((1 - Polynomial.X ^ k : Polynomial ℤ).natDegree + 1),
      ((1 - Polynomial.X ^ k : Polynomial ℤ).coeff j : ℚ) * (j : ℚ)^n = -((k : ℚ)^n) := by
  rw [natDegree_one_sub_X_pow_eq k hk]
  have hk_mem : k ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_self k)
  rw [Finset.sum_eq_single_of_mem k hk_mem]
  · exact one_sub_X_pow_term_at_k k n hk
  · intro j hj_mem hj_ne
    exact one_sub_X_pow_term_eq_zero k n j hk hn hj_mem hj_ne

lemma exp_poly_sub_one_sub_X_pow_coeff_pos (k n : ℕ) (hk : 0 < k) (hn : 1 ≤ n) :
    (PowerSeries.coeff n) (expPolySub (1 -
      Polynomial.X ^ k)) = -((k : ℚ)^n) / (n.factorial : ℚ) := by
  rw [exp_poly_sub_coeff]
  rw [one_sub_X_pow_sum_eq k n hk hn]

lemma rhs_coeff_zero {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (i : Fin G.m) :
    (PowerSeries.coeff 0) (-(G.d i : ℚ) • (PowerSeries.X * G.scaledExpFactor i)) = 0 := by
  have h₁ : (PowerSeries.coeff 0) (PowerSeries.X * G.scaledExpFactor i) = 0 := by
    simp
  have h₂ : (PowerSeries.coeff 0) (-(G.d i : ℚ) • (PowerSeries.X *
    G.scaledExpFactor i)) = (-(G.d i : ℚ)) * (PowerSeries.coeff 0) (PowerSeries.X *
      G.scaledExpFactor i) := by
    simp
  rw [h₂, h₁]
  ring_nf

lemma rhs_coeff_pos {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (i : Fin G.m)
    (n : ℕ) (hn : 1 ≤ n) :
    (PowerSeries.coeff n) (-(G.d i : ℚ) • (PowerSeries.X * G.scaledExpFactor i)) =
    -((G.d i : ℚ)^n) / (n.factorial : ℚ) := by
  rw [PowerSeries.coeff_smul]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  subst hk
  rw [PowerSeries.coeff_succ_X_mul]
  simp only [NumericalSemigroupGenerators.scaledExpFactor, PowerSeries.coeff_mk]
  simp only [smul_eq_mul, Nat.succ_eq_add_one]
  ring

lemma single_factor_exp_transform {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (i : Fin G.m) :
    expPolySub (1 - Polynomial.X ^ (G.d i)) =
    -(G.d i : ℚ) • (PowerSeries.X * G.scaledExpFactor i) := by
  apply PowerSeries.ext
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [exp_poly_sub_one_sub_X_pow_coeff_zero (G.d i) (G.hd_pos i)]
    rw [rhs_coeff_zero G i]
  · rw [exp_poly_sub_one_sub_X_pow_coeff_pos (G.d i) n (G.hd_pos i) hn]
    rw [rhs_coeff_pos G i n hn]

lemma prod_smul_eq_smul_prod (m : ℕ) (c : Fin m → ℚ) (f : Fin m → PowerSeries ℚ) :
    ∏ i : Fin m, (c i • f i) = (∏ i : Fin m, c i) • (∏ i : Fin m, f i) := by
  simp only [MvPowerSeries.smul_eq_C_mul]
  rw [Finset.prod_mul_distrib]
  rw [← map_prod]

lemma prod_X_mul_eq_X_pow_mul (m : ℕ) (f : Fin m → PowerSeries ℚ) :
    ∏ i : Fin m, (PowerSeries.X * f i) = PowerSeries.X ^ m * ∏ i : Fin m, f i := by
  simp_rw [Finset.prod_mul_distrib, Fin.prod_const]

lemma prod_neg_eq_neg_one_pow_mul (m : ℕ) (c : Fin m → ℚ) :
    ∏ i : Fin m, (-c i) = (-1 : ℚ) ^ m * ∏ i : Fin m, c i := by
  calc
    _ = ∏ i : Fin m, (-1 : ℚ) * c i := by
      apply Finset.prod_congr rfl
      intro i _
      ring
    _ = (∏ i : Fin m, (-1 : ℚ)) * ∏ i : Fin m, c i := by
      rw [Finset.prod_mul_distrib]
    _ = ((-1 : ℚ) ^ m) * ∏ i : Fin m, c i := by
      have h2 : ∏ i : Fin m, (-1 : ℚ) = (-1 : ℚ) ^ m := by
        simp [Finset.prod_const]
      rw [h2]

lemma prod_single_factor_eq_final_form {S : NumericalSemigroup} (G : NumericalSemigroupGenerators
  S) :
    ∏ i : Fin G.m, (-(G.d i : ℚ) • (PowerSeries.X * G.scaledExpFactor i)) =
    ((-1 : ℚ)^G.m * (G.piM : ℚ)) • (PowerSeries.X ^ G.m * G.ASeries) := by
  rw [prod_smul_eq_smul_prod]
  rw [prod_X_mul_eq_X_pow_mul]
  have h1 : (∏ i : Fin G.m, -(G.d i : ℚ)) = (-1 : ℚ) ^ G.m * (G.piM : ℚ) := by
    rw [prod_neg_eq_neg_one_pow_mul]
    congr 1
    simp only [NumericalSemigroupGenerators.piM]
    rw [Nat.cast_prod]
  rw [h1]
  rfl

-- productPolynomial_exp_transform: defined later at productPolynomial_exp_transform'

lemma triple_sum_factorial_to_choose (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (P.natDegree + 1),
        ∑ b ∈ Finset.range (Q.natDegree + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) / (k.factorial *
            (n - k).factorial) =
    ∑ k ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (P.natDegree + 1),
        ∑ b ∈ Finset.range (Q.natDegree + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) *
            ((n.choose k : ℚ) / (n.factorial : ℚ)) := by
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact term_factorial_to_choose (P.coeff a : ℚ) (Q.coeff b : ℚ) a b k n hkn

lemma factor_out_factorial (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (P.natDegree + 1),
        ∑ b ∈ Finset.range (Q.natDegree + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) *
            ((n.choose k : ℚ) / (n.factorial : ℚ)) =
    (1 / n.factorial) * ∑ k ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (P.natDegree + 1),
        ∑ b ∈ Finset.range (Q.natDegree + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (n.choose k : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) := by
  calc
    ∑ k ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (P.natDegree + 1),
        ∑ b ∈ Finset.range (Q.natDegree + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) *
            ((n.choose k : ℚ) / (n.factorial : ℚ)) = ∑ k ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (P.natDegree + 1),
        ∑ b ∈ Finset.range (Q.natDegree + 1),
          ((1 : ℚ) / (n.factorial : ℚ)) * ((P.coeff a : ℚ) * (Q.coeff b : ℚ) * (n.choose k : ℚ) *
            (a : ℚ)^k * (b : ℚ)^(n - k)) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring_nf
    _ = (1 / (n.factorial : ℚ)) * ∑ k ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (P.natDegree + 1),
        ∑ b ∈ Finset.range (Q.natDegree + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (n.choose k : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) := by
      simp [Finset.mul_sum, mul_assoc]
    _ = (1 / n.factorial) * ∑ k ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (P.natDegree + 1),
        ∑ b ∈ Finset.range (Q.natDegree + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (n.choose k : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) := by
      simp_all [div_eq_mul_inv]

lemma sum_rearrange (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (P.natDegree + 1),
        ∑ b ∈ Finset.range (Q.natDegree + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (n.choose k : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) =
    ∑ a ∈ Finset.range (P.natDegree + 1),
      ∑ b ∈ Finset.range (Q.natDegree + 1),
        ∑ k ∈ Finset.range (n + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (n.choose k : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

lemma factor_coeffs_from_inner_sum (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ a ∈ Finset.range (P.natDegree + 1),
      ∑ b ∈ Finset.range (Q.natDegree + 1),
        ∑ k ∈ Finset.range (n + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (n.choose k : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) =
    ∑ a ∈ Finset.range (P.natDegree + 1),
      ∑ b ∈ Finset.range (Q.natDegree + 1),
        (P.coeff a : ℚ) * (Q.coeff b : ℚ) *
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma binomial_sum_eq_power (a b n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) = ((a : ℚ) + b)^n := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [mul_comm ((n.choose k : ℚ)) _]
  ring

lemma apply_binomial_to_inner_sum (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ a ∈ Finset.range (P.natDegree + 1),
      ∑ b ∈ Finset.range (Q.natDegree + 1),
        (P.coeff a : ℚ) * (Q.coeff b : ℚ) *
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) =
    ∑ a ∈ Finset.range (P.natDegree + 1),
      ∑ b ∈ Finset.range (Q.natDegree + 1),
        (P.coeff a : ℚ) * (Q.coeff b : ℚ) * ((a : ℚ) + b)^n := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [binomial_sum_eq_power]

lemma exp_poly_sub_mul_coeff_eq (P Q : Polynomial ℤ) (n : ℕ) :
    (PowerSeries.coeff n) (expPolySub P * expPolySub Q) =
    (∑ a ∈ Finset.range (P.natDegree + 1),
     ∑ b ∈ Finset.range (Q.natDegree + 1),
       (P.coeff a : ℚ) * (Q.coeff b : ℚ) * ((a : ℚ) + b)^n) / (n.factorial : ℚ) := by
  rw [coeff_mul_expand]
  rw [lhs_to_triple_sum]
  rw [triple_sum_factorial_to_choose]
  rw [factor_out_factorial]
  rw [sum_rearrange]
  rw [factor_coeffs_from_inner_sum]
  rw [apply_binomial_to_inner_sum]
  ring

lemma convolution_sum_eq (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ j ∈ Finset.range ((P * Q).natDegree + 1), ((P * Q).coeff j : ℚ) * (j : ℚ)^n =
    ∑ j ∈ Finset.range (P.natDegree + Q.natDegree + 1),
      ∑ ab ∈ Finset.antidiagonal j,
        (P.coeff ab.1 : ℚ) * (Q.coeff ab.2 : ℚ) * ((ab.1 : ℚ) + ab.2)^n := by
  have h_deg : (P * Q).natDegree ≤ P.natDegree + Q.natDegree := Polynomial.natDegree_mul_le
  rw [exp_poly_sub_sum_extend (P * Q) (P.natDegree + Q.natDegree + 1) n (by omega)]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < P.natDegree + Q.natDegree + 1 := Finset.mem_range.mp hj
  have h1 : ((P * Q).coeff j : ℚ) = ∑ k ∈ Finset.range (j + 1),
    (P.coeff k : ℚ) * (Q.coeff (j - k) : ℚ) := by
    rw [Polynomial.coeff_mul]
    simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_cast
  rw [h1]
  have h2 : (∑ k ∈ Finset.range (j + 1), (P.coeff k : ℚ) * (Q.coeff (j - k) : ℚ)) * (j : ℚ) ^ n =
      ∑ k ∈ Finset.range (j + 1), (P.coeff k : ℚ) * (Q.coeff (j - k) : ℚ) * (j : ℚ) ^ n := by
    rw [Finset.sum_mul]
  rw [h2]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h_eq : ((k : ℚ) + (j - k : ℕ)) = j := by
    simp only [Nat.cast_sub hk']
    ring
  simp only [h_eq]

lemma rectangle_subset_triangle (P Q : Polynomial ℤ) :
    Finset.range (P.natDegree + 1) ×ˢ Finset.range (Q.natDegree + 1) ⊆
    (Finset.range (P.natDegree + Q.natDegree + 1)).biUnion Finset.antidiagonal := by
  intro ab hab
  simp only [Finset.mem_product, Finset.mem_range] at hab
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_antidiagonal]
  refine ⟨ab.1 + ab.2, ?_, rfl⟩
  omega

lemma term_vanishes_outside_rectangle (P Q : Polynomial ℤ) (n : ℕ) (ab : ℕ × ℕ)
    (_h_in_tri : ab ∈ (Finset.range (P.natDegree + Q.natDegree + 1)).biUnion Finset.antidiagonal)
    (h_not_rect : ab ∉ Finset.range (P.natDegree + 1) ×ˢ Finset.range (Q.natDegree + 1)) :
    (P.coeff ab.1 : ℚ) * (Q.coeff ab.2 : ℚ) * ((ab.1 : ℚ) + ab.2)^n = 0 := by
  have h₁ : ab.1 > P.natDegree ∨ ab.2 > Q.natDegree := by
    by_contra! h
    have h₄ : ab.1 < P.natDegree + 1 := by linarith
    have h₅ : ab.2 < Q.natDegree + 1 := by linarith
    have h₆ : ab ∈ Finset.range (P.natDegree + 1) ×ˢ Finset.range (Q.natDegree + 1) := by
      simp [Finset.mem_product, Finset.mem_range, h₄, h₅]
    contradiction
  cases h₁ with
  | inl h₁ =>
    have h₂ : (P.coeff ab.1 : ℚ) = 0 := by
      have h₃ : (P.natDegree : ℕ) < ab.1 := h₁
      have h₄ : P.coeff ab.1 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt h₃
      norm_cast
    rw [h₂]
    simp
  | inr h₁ =>
    have h₂ : (Q.coeff ab.2 : ℚ) = 0 := by
      have h₃ : (Q.natDegree : ℕ) < ab.2 := h₁
      have h₄ : Q.coeff ab.2 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt h₃
      norm_cast
    rw [h₂]
    simp

lemma pairwiseDisjoint_antidiagonal (s : Finset ℕ) :
    (s : Set ℕ).PairwiseDisjoint Finset.antidiagonal := by
  intro j₁ _ j₂ _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx₁ hx₂
  rw [Finset.mem_antidiagonal] at hx₁ hx₂
  exact hne (hx₁.symm.trans hx₂)

lemma nested_sum_eq_biUnion_sum (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ j ∈ Finset.range (P.natDegree + Q.natDegree + 1),
      ∑ ab ∈ Finset.antidiagonal j,
        (P.coeff ab.1 : ℚ) * (Q.coeff ab.2 : ℚ) * ((ab.1 : ℚ) + ab.2)^n =
    ∑ ab ∈ (Finset.range (P.natDegree + Q.natDegree + 1)).biUnion Finset.antidiagonal,
      (P.coeff ab.1 : ℚ) * (Q.coeff ab.2 : ℚ) * ((ab.1 : ℚ) + ab.2)^n := by
  exact (Finset.sum_biUnion (pairwiseDisjoint_antidiagonal _)).symm

lemma product_sum_eq_nested (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ ab ∈ Finset.range (P.natDegree + 1) ×ˢ Finset.range (Q.natDegree + 1),
      (P.coeff ab.1 : ℚ) * (Q.coeff ab.2 : ℚ) * ((ab.1 : ℚ) + ab.2)^n =
    ∑ a ∈ Finset.range (P.natDegree + 1),
      ∑ b ∈ Finset.range (Q.natDegree + 1),
        (P.coeff a : ℚ) * (Q.coeff b : ℚ) * ((a : ℚ) + b)^n := by
  rw [Finset.sum_product]

lemma triangular_to_rectangular_sum (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ j ∈ Finset.range (P.natDegree + Q.natDegree + 1),
      ∑ ab ∈ Finset.antidiagonal j,
        (P.coeff ab.1 : ℚ) * (Q.coeff ab.2 : ℚ) * ((ab.1 : ℚ) + ab.2)^n =
    ∑ a ∈ Finset.range (P.natDegree + 1),
      ∑ b ∈ Finset.range (Q.natDegree + 1),
        (P.coeff a : ℚ) * (Q.coeff b : ℚ) * ((a : ℚ) + b)^n := by
  rw [nested_sum_eq_biUnion_sum]
  rw [← product_sum_eq_nested]
  symm
  apply Finset.sum_subset (rectangle_subset_triangle P Q)
  intro ab h_in_tri h_not_rect
  exact term_vanishes_outside_rectangle P Q n ab h_in_tri h_not_rect

lemma exp_poly_sub_prod_coeff_eq (P Q : Polynomial ℤ) (n : ℕ) :
    (PowerSeries.coeff n) (expPolySub (P * Q)) =
    (∑ a ∈ Finset.range (P.natDegree + 1),
     ∑ b ∈ Finset.range (Q.natDegree + 1),
       (P.coeff a : ℚ) * (Q.coeff b : ℚ) * ((a : ℚ) + b)^n) / (n.factorial : ℚ) := by
  rw [exp_poly_sub_coeff]
  rw [convolution_sum_eq]
  rw [triangular_to_rectangular_sum]

lemma exp_poly_sub_mul (P Q : Polynomial ℤ) :
    expPolySub (P * Q) = expPolySub P * expPolySub Q := by
  apply PowerSeries.ext
  intro n
  rw [exp_poly_sub_prod_coeff_eq, exp_poly_sub_mul_coeff_eq]

lemma exp_poly_sub_prod' {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    expPolySub G.productPolynomial =
    ∏ i : Fin G.m, expPolySub (1 - Polynomial.X ^ (G.d i)) := by
  unfold NumericalSemigroupGenerators.productPolynomial
  have h := Finset.prod_hom_rel (s := Finset.univ) (r := fun P F => expPolySub P = F)
    (f := fun i : Fin G.m => (1 - Polynomial.X ^ (G.d i)))
    (g := fun i : Fin G.m => expPolySub (1 - Polynomial.X ^ (G.d i)))
  rw [h]
  · exact exp_poly_sub_one
  · intro a b c hbc
    rw [exp_poly_sub_mul, hbc]

lemma productPolynomial_exp_transform {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
  :
    expPolySub G.productPolynomial =
    ((-1 : ℚ)^G.m * (G.piM : ℚ)) • (PowerSeries.X ^ G.m * G.ASeries) := by
  rw [exp_poly_sub_prod']
  conv_lhs => arg 2; ext i; rw [single_factor_exp_transform]
  exact prod_single_factor_eq_final_form G

lemma coeff_one_sub_exp (n : ℕ) :
    (PowerSeries.coeff n) (1 - PowerSeries.exp ℚ) =
    if n = 0 then 0 else -1 / (n.factorial : ℚ) := by
  rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_exp]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  split_ifs with h
  · simp [h]
  · ring

lemma binomial_sum_minus_j_pow (j n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), if k = 0 then 0 else (n.choose k : ℚ) * (j : ℚ)^(n - k)) =
    ((j : ℚ) + 1)^n - (j : ℚ)^n := by
  have h := add_pow (1 : ℚ) (j : ℚ) n
  simp only [one_pow, add_comm] at h
  rw [Finset.sum_eq_add_sum_sdiff_singleton 0 _
      (fun hnot => absurd (Finset.mem_range.mpr (Nat.zero_lt_succ n)) hnot)]
  simp only [↓reduceIte, zero_add]
  have hne : ∀ x ∈ (Finset.range n.succ \ {0}), x ≠ 0 := by
    simp [Finset.mem_sdiff, Finset.mem_singleton]
  rw [Finset.sum_congr rfl (fun x hx => if_neg (hne x hx))]
  rw [Finset.sum_eq_add_sum_sdiff_singleton 0 _
      (fun hnot => absurd (Finset.mem_range.mpr (Nat.zero_lt_succ n)) hnot)] at h
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero] at h
  calc
    ∑ k ∈ Finset.range n.succ \ {0}, (n.choose k : ℚ) * (j : ℚ)^(n - k)
      = ∑ k ∈ Finset.range n.succ \ {0}, (j : ℚ)^(n - k) * (n.choose k : ℚ) := by
        apply Finset.sum_congr rfl; intro k _; ring
    _ = ((j : ℚ) + 1)^n - (j : ℚ)^n := by linarith

lemma coeff_mul_as_range_sum {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (PowerSeries.coeff n) ((1 - PowerSeries.exp ℚ) * partialSumGenFunc G) =
    ∑ k ∈ Finset.range (n + 1),
      (PowerSeries.coeff k) (1 - PowerSeries.exp ℚ) *
      (PowerSeries.coeff (n - k)) (partialSumGenFunc G) := by
  rw [PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k m => (PowerSeries.coeff k) (1 - PowerSeries.exp ℚ) *
      (PowerSeries.coeff m) (partialSumGenFunc G)) n

lemma coeff_sum_substitute {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (PowerSeries.coeff k) (1 - PowerSeries.exp ℚ) *
      (PowerSeries.coeff (n - k)) (partialSumGenFunc G) =
    ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else -1 / (k.factorial : ℚ)) *
      ((∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
        (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) /
       ((n - k).factorial : ℚ)) := by
  apply Finset.sum_congr rfl
  intro k _
  rw [coeff_one_sub_exp, partialSumGenFunc_coeff]

lemma drop_k_eq_zero_term {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else -1 / (k.factorial : ℚ)) *
      ((∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
        (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) /
       ((n - k).factorial : ℚ)) =
    ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else
        (-1 / (k.factorial : ℚ)) *
        ((∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
          (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) /
         ((n - k).factorial : ℚ))) := by
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hk
  · simp
  · ring

lemma summand_eq_for_pos {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n k : ℕ)
    (_hk_pos : k ≠ 0) (hk_le : k ≤ n) :
    (-1 / (k.factorial : ℚ)) *
      ((∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
        (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) /
       ((n - k).factorial : ℚ)) =
    (-(n.choose k : ℚ) / (n.factorial : ℚ)) *
      (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
        (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) := by
  have h₈ : (n.choose k : ℚ) / (n.factorial : ℚ) = 1 / (k.factorial : ℚ) / ((n -
    k).factorial : ℚ) := by
    have h₉ : (n.choose k : ℕ) * k.factorial * (n - k).factorial = n.factorial := by
      rw [← Nat.choose_mul_factorial_mul_factorial hk_le]
    have h₁₂ : (n.choose k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ) = (n.factorial : ℚ) :=
      by
      norm_cast at h₉ ⊢
    have h₁₄ : (n.factorial : ℚ) ≠ 0 := by positivity
    have h₁₅ : (k.factorial : ℚ) ≠ 0 := by positivity
    have h₁₆ : ((n - k).factorial : ℚ) ≠ 0 := by positivity
    field_simp [h₁₄, h₁₅, h₁₆] at h₁₂ ⊢
    nlinarith
  calc
    (-1 / (k.factorial : ℚ)) * ((∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ m ∈ Finset.range (j + 1),
        (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) / ((n - k).factorial : ℚ))
      = (-(∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1), (∑ m ∈ Finset.range (j + 1),
        (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) : ℚ) / ((k.factorial : ℚ) *
          ((n - k).factorial : ℚ)) := by ring_nf
      _ = (-(∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1), (∑ m ∈ Finset.range (j + 1),
        (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) : ℚ) * (1 / ((k.factorial : ℚ) *
          ((n - k).factorial : ℚ))) := by field_simp
      _ = (-(∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1), (∑ m ∈ Finset.range (j + 1),
        (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) : ℚ) *
          (1 / (k.factorial : ℚ) / ((n - k).factorial : ℚ)) := by field_simp
      _ = (-(∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1), (∑ m ∈ Finset.range (j + 1),
        (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) : ℚ) *
          ((n.choose k : ℚ) / (n.factorial : ℚ)) := by rw [h₈]
      _ = (-(n.choose k : ℚ) / (n.factorial : ℚ)) *
        (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1), (∑ m ∈ Finset.range (j + 1),
          (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) := by ring_nf

lemma apply_factorial_identity {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n :
  ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else
        (-1 / (k.factorial : ℚ)) *
        ((∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
          (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) /
         ((n - k).factorial : ℚ))) =
    ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else
        (-(n.choose k : ℚ) / (n.factorial : ℚ)) *
        (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
          (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k))) := by
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs with hk_zero
  · rfl
  · have hk_le : k ≤ n := by
      simp only [Finset.mem_range] at hk
      omega
    exact summand_eq_for_pos G n k hk_zero hk_le

lemma factor_neg_choose_div_factorial (D n : ℕ) (coeff : ℕ → ℚ) :
    ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else
        (-(n.choose k : ℚ) / (n.factorial : ℚ)) *
        (∑ j ∈ Finset.range (D + 1), coeff j * (j : ℚ)^(n - k))) =
    (-1 / (n.factorial : ℚ)) *
    (∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else
        (n.choose k : ℚ) *
        (∑ j ∈ Finset.range (D + 1), coeff j * (j : ℚ)^(n - k)))) := by
  have h₁ : ∑ k ∈ Finset.range (n + 1),
    (if k = 0 then 0 else (-(n.choose k : ℚ) / (n.factorial : ℚ)) * (∑ j ∈ Finset.range (D + 1),
      coeff j * (j : ℚ)^(n - k))) = ∑ k ∈ Finset.range (n + 1),
        (if k = 0 then 0 else (-1 / (n.factorial : ℚ)) * ((n.choose k : ℚ) *
          (∑ j ∈ Finset.range (D + 1), coeff j * (j : ℚ)^(n - k)))) := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk0 : k = 0
    · simp [hk0]
    · have h₂ : (-(n.choose k : ℚ) / (n.factorial : ℚ)) = (-1 / (n.factorial : ℚ)) *
      (n.choose k : ℚ) := by
        field_simp [Nat.cast_ne_zero, Nat.factorial_ne_zero]
      rw [h₂]; ring_nf
  have h₂ : ∑ k ∈ Finset.range (n + 1),
    (if k = 0 then 0 else (-1 / (n.factorial : ℚ)) * ((n.choose k : ℚ) *
      (∑ j ∈ Finset.range (D + 1),
        coeff j * (j : ℚ)^(n - k)))) = (-1 / (n.factorial : ℚ)) * ∑ k ∈ Finset.range (n + 1),
          (if k = 0 then 0 else (n.choose k : ℚ) * (∑ j ∈ Finset.range (D + 1),
            coeff j * (j : ℚ)^(n - k))) := by
    calc
      ∑ k ∈ Finset.range (n + 1),
        (if k = 0 then 0 else (-1 / (n.factorial : ℚ)) * ((n.choose k : ℚ) *
          (∑ j ∈ Finset.range (D + 1), coeff j * (j : ℚ)^(n - k)))) =
          ∑ k ∈ Finset.range (n + 1),
            (-1 / (n.factorial : ℚ)) * (if k = 0 then 0 else (n.choose k : ℚ) *
              (∑ j ∈ Finset.range (D + 1), coeff j * (j : ℚ)^(n - k))) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk0 : k = 0
        · simp [hk0]
        · have h₄ : (if k = 0 then 0 else (-1 / (n.factorial : ℚ)) * ((n.choose k : ℚ) *
          (∑ j ∈ Finset.range (D + 1),
            coeff j * (j : ℚ)^(n - k)))) = (-1 / (n.factorial : ℚ)) *
              (if k = 0 then 0 else (n.choose k : ℚ) * (∑ j ∈ Finset.range (D + 1),
                coeff j * (j : ℚ)^(n - k))) := by
            simp [hk0]
          rw [h₄]
      _ = (-1 / (n.factorial : ℚ)) * ∑ k ∈ Finset.range (n + 1),
        (if k = 0 then 0 else (n.choose k : ℚ) * (∑ j ∈ Finset.range (D + 1),
          coeff j * (j : ℚ)^(n - k))) := by
        rw [Finset.mul_sum]
  calc
    ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else (-(n.choose k : ℚ) / (n.factorial : ℚ)) * (∑ j ∈ Finset.range (D + 1),
        coeff j * (j : ℚ)^(n - k))) = ∑ k ∈ Finset.range (n + 1),
          (if k = 0 then 0 else (-1 / (n.factorial : ℚ)) * ((n.choose k : ℚ) *
            (∑ j ∈ Finset.range (D + 1), coeff j * (j : ℚ)^(n - k)))) := h₁
    _ = (-1 / (n.factorial : ℚ)) * ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else (n.choose k : ℚ) * (∑ j ∈ Finset.range (D + 1),
        coeff j * (j : ℚ)^(n - k))) := h₂

lemma swap_and_apply_binomial (D n : ℕ) (coeff : ℕ → ℚ) :
    ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else
        (n.choose k : ℚ) *
        (∑ j ∈ Finset.range (D + 1), coeff j * (j : ℚ)^(n - k))) =
    ∑ j ∈ Finset.range (D + 1), coeff j * (((j : ℚ) + 1)^n - (j : ℚ)^n) := by
  conv_lhs =>
    arg 2
    ext k
    rw [show (if k = 0 then (0 : ℚ) else (n.choose k : ℚ) * ∑ j ∈ Finset.range (D + 1),
      coeff j * (j : ℚ)^(n - k))
           = ∑ j ∈ Finset.range (D + 1),
             (if k = 0 then 0 else (n.choose k : ℚ) * (coeff j * (j : ℚ)^(n - k)))
        by split_ifs with h
           · simp only [Finset.sum_const_zero]
           · rw [Finset.mul_sum]]
  rw [Finset.sum_comm]
  congr 1
  ext j
  conv_lhs =>
    arg 2
    ext k
    rw [show (if k = 0 then (0 : ℚ) else (n.choose k : ℚ) * (coeff j * (j : ℚ)^(n - k)))
           = coeff j * (if k = 0 then 0 else (n.choose k : ℚ) * (j : ℚ)^(n - k))
        by split_ifs <;> ring]
  rw [← Finset.mul_sum]
  rw [binomial_sum_minus_j_pow]

lemma factor_and_apply_binomial {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n :
  ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else
        (-(n.choose k : ℚ) / (n.factorial : ℚ)) *
        (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
          (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k))) =
    (-1 / (n.factorial : ℚ)) *
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) *
      (((j : ℚ) + 1)^n - (j : ℚ)^n)) := by
  have step1 := factor_neg_choose_div_factorial G.hilbertNumerator.natDegree n
    (fun j => ∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ))
  have step2 := swap_and_apply_binomial G.hilbertNumerator.natDegree n
    (fun j => ∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ))
  rw [step1, step2]

lemma coeff_lhs_expand {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (PowerSeries.coeff n) ((1 - PowerSeries.exp ℚ) * partialSumGenFunc G) =
    (-1 / (n.factorial : ℚ)) *
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ k ∈ Finset.range (j + 1), (G.productPolynomial.coeff k : ℚ)) *
      (((j : ℚ) + 1)^n - (j : ℚ)^n)) := by
  rw [coeff_mul_as_range_sum]
  rw [coeff_sum_substitute]
  rw [drop_k_eq_zero_term]
  rw [apply_factorial_identity]
  rw [factor_and_apply_binomial]

lemma coeff_lhs_eq_rhs {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (PowerSeries.coeff n) ((1 - PowerSeries.exp ℚ) * partialSumGenFunc G) =
    (PowerSeries.coeff n) (expPolySub G.productPolynomial) := by
  rw [coeff_lhs_expand, telescoping_sum, exp_poly_sub_coeff]
  ring

lemma partialSumGenFunc_mul_one_sub_exp {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) :
    (1 - PowerSeries.exp ℚ) * partialSumGenFunc G = expPolySub G.productPolynomial := by
  ext n
  exact coeff_lhs_eq_rhs G n

lemma partialSumGenFunc_identity {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    PowerSeries.X * partialSumGenFunc G =
    ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) • (PowerSeries.X ^ G.m * G.BSeries) := by
  have h1 : (1 - PowerSeries.exp ℚ) * partialSumGenFunc G = expPolySub G.productPolynomial :=
    partialSumGenFunc_mul_one_sub_exp G
  have h2 : expPolySub G.productPolynomial =
      ((-1 : ℚ)^G.m * (G.piM : ℚ)) • (PowerSeries.X ^ G.m * G.ASeries) :=
    productPolynomial_exp_transform G
  have h3 : (1 - PowerSeries.exp ℚ) * partialSumGenFunc G =
      ((-1 : ℚ)^G.m * (G.piM : ℚ)) • (PowerSeries.X ^ G.m * G.ASeries) := h1.trans h2
  have h4 : (PowerSeries.exp ℚ - 1) * partialSumGenFunc G =
      ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) • (PowerSeries.X ^ G.m * G.ASeries) := by
    have neg_eq : PowerSeries.exp ℚ - 1 = -(1 - PowerSeries.exp ℚ) := by ring
    rw [neg_eq, neg_mul, h3]
    rw [show -(((-1 : ℚ)^G.m * (G.piM : ℚ)) • (PowerSeries.X ^ G.m * G.ASeries)) =
        (-((-1 : ℚ)^G.m * (G.piM : ℚ))) • (PowerSeries.X ^ G.m * G.ASeries)
        from (neg_smul _ _).symm]
    congr 1
    ring
  have h5 : bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1) * partialSumGenFunc G =
      bernoulliPowerSeries ℚ * (((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) • (PowerSeries.X ^ G.m *
        G.ASeries)) := by
    rw [mul_assoc, h4]
  have h6 : bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1) = PowerSeries.X :=
    bernoulliPowerSeries_mul_exp_sub_one ℚ
  rw [h6] at h5
  have h7 : bernoulliPowerSeries ℚ * (((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) • (PowerSeries.X ^ G.m *
    G.ASeries)) =
      ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) • (PowerSeries.X ^ G.m * G.BSeries) := by
    simp only [NumericalSemigroupGenerators.BSeries, mul_smul_comm]
    ring_nf
  rw [h7] at h5
  exact h5

lemma cond_equiv (m n : ℕ) : (m ≤ n + 1) ↔ (m - 1 ≤ n) := by aesop

lemma index_eq (m n : ℕ) (hm : 0 < m) (h : m ≤ n + 1) : (n + 1) - m = n - (m - 1) := by omega

lemma coeff_X_pow_shift {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (PowerSeries.coeff (n + 1)) (PowerSeries.X ^ G.m * G.BSeries) =
    (PowerSeries.coeff n) (PowerSeries.X ^ (G.m - 1) * G.BSeries) := by
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  simp only [cond_equiv]
  split_ifs with h
  · rw [index_eq G.m n G.hm_pos (cond_equiv G.m n |>.mpr h)]
  · rfl

lemma partialSumGenFunc_coeff_eq_bernoulli_term {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (PowerSeries.coeff n) (partialSumGenFunc G) =
    ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) *
      (PowerSeries.coeff n) (PowerSeries.X ^ (G.m - 1) * G.BSeries) := by
  have h_identity := partialSumGenFunc_identity G
  have h_coeff : (PowerSeries.coeff (n + 1)) (PowerSeries.X * partialSumGenFunc G) =
      (PowerSeries.coeff (n + 1)) (((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) • (PowerSeries.X ^ G.m *
        G.BSeries)) := by
    rw [h_identity]
  rw [PowerSeries.coeff_succ_X_mul] at h_coeff
  rw [PowerSeries.coeff_smul] at h_coeff
  rw [coeff_X_pow_shift G n] at h_coeff
  simp only [smul_eq_mul] at h_coeff
  exact h_coeff

lemma sum_part_equals_bernoulli_term_natDegree {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ k ∈ Finset.range (j + 1),
        (G.productPolynomial.coeff k : ℚ)) * (j : ℚ)^n) / (n.factorial : ℚ) =
    ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) *
      (PowerSeries.coeff n) (PowerSeries.X ^ (G.m - 1) * G.BSeries) := by
  rw [← partialSumGenFunc_coeff, partialSumGenFunc_coeff_eq_bernoulli_term]

lemma gap_le_sup {S : NumericalSemigroup} (g : ℕ) (hg : g ∈ S.gaps) : g ≤ S.gaps.sup id :=
  Finset.le_sup (f := id) hg

lemma neg_neg_one_pow_eq (m : ℕ) : -((-1 : ℤ) ^ m) = (-1 : ℤ) ^ (m + 1) := by ring

lemma gap_sum_at_jstar {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (hnonempty : S.gaps.Nonempty) :
    ∑ g ∈ S.gaps.filter (· ≤ G.productPolynomial.natDegree + S.gaps.sup id),
      G.productPolynomial.coeff (G.productPolynomial.natDegree + S.gaps.sup id - g) =
    (-1) ^ G.m := by
  obtain ⟨gmax, hgmax_mem, hgmax_eq⟩ := Finset.exists_mem_eq_sup S.gaps hnonempty id
  simp only [id_eq] at hgmax_eq
  have hfilter : S.gaps.filter (· ≤ G.productPolynomial.natDegree + S.gaps.sup id) = S.gaps := by
    apply Finset.filter_true_of_mem
    intro g hg
    calc g ≤ S.gaps.sup id := Finset.le_sup (f := id) hg
         _ ≤ G.productPolynomial.natDegree + S.gaps.sup id := le_add_self
  rw [hfilter]
  rw [Finset.sum_eq_single_of_mem gmax hgmax_mem]
  · have hsub : G.productPolynomial.natDegree +
    S.gaps.sup id - gmax = G.productPolynomial.natDegree := by
      rw [hgmax_eq, Nat.add_sub_cancel]
    rw [hsub, Polynomial.coeff_natDegree, productPolynomial_leadingCoeff G]
  · intro g hg hne
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hle : g ≤ gmax := by
      have := Finset.le_sup (f := id) hg
      simp only [id_eq, hgmax_eq] at this
      exact this
    have hlt : g < gmax := lt_of_le_of_ne hle hne
    simp only [hgmax_eq]
    omega

lemma hilbertNumerator_coeff_at_jstar {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (hnonempty : S.gaps.Nonempty) :
    G.hilbertNumerator.coeff (G.productPolynomial.natDegree + S.gaps.sup id) = (-1 : ℤ) ^ (G.m +
      1) := by
  set jstar := G.productPolynomial.natDegree + S.gaps.sup id with hjstar_def
  have hjstar_bound : jstar < G.hilbertNumeratorDegBound := by
    unfold NumericalSemigroupGenerators.hilbertNumeratorDegBound
    omega
  have hcoeff : G.hilbertNumerator.coeff jstar =
      (∑ k ∈ Finset.range (jstar + 1), G.productPolynomial.coeff k) -
      (∑ g ∈ S.gaps.filter (· ≤ jstar), G.productPolynomial.coeff (jstar - g)) := by
    simp only [NumericalSemigroupGenerators.hilbertNumerator]
    simp [Polynomial.coeff_monomial, Finset.mem_range, hjstar_bound]
  have h1 : ∑ k ∈ Finset.range (jstar + 1), G.productPolynomial.coeff k = 0 := by
    have hge : 1 ≤ S.gaps.sup id := by
      obtain ⟨gmax, hgmax_mem, hgmax_eq⟩ := Finset.exists_mem_eq_sup S.gaps hnonempty id
      simp only [id_eq] at hgmax_eq
      rw [hgmax_eq]
      have hgap_pos : 0 < gmax := by
        by_contra h0
        push Not at h0
        interval_cases gmax
        · have : (0 : ℕ) ∈ S.gaps := hgmax_mem
          have hmem : 0 ∈ S.carrier := S.zero_mem
          have hnotmem : 0 ∉ S.carrier := by
            have : S.gaps = S.finite_complement.toFinset := rfl
            rw [this] at hgmax_mem
            rw [Set.Finite.mem_toFinset] at hgmax_mem
            exact hgmax_mem
          contradiction
      omega
    have h1 := NumericalSemigroupGenerators.sum_coeff_large_eq_sum_coeff_deg G jstar (by omega)
    rw [h1, NumericalSemigroupGenerators.sum_coeff_eq_eval_one G,
      NumericalSemigroupGenerators.productPolynomial_eval_one G]
  rw [hcoeff, h1, zero_sub]
  have hgap := gap_sum_at_jstar G hnonempty
  rw [hgap, neg_neg_one_pow_eq]

lemma neg_one_pow_ne_zero' (m : ℕ) : ((-1 : ℤ) ^ (m + 1)) ≠ 0 := by
  exact Int.neg_one_pow_ne_zero

lemma hilbertNumerator_natDegree_ge_jstar {S : NumericalSemigroup} (G :
  NumericalSemigroupGenerators S)
    (hnonempty : S.gaps.Nonempty) :
    G.productPolynomial.natDegree + S.gaps.sup id ≤ G.hilbertNumerator.natDegree := by
  apply Polynomial.le_natDegree_of_ne_zero
  rw [hilbertNumerator_coeff_at_jstar G hnonempty]
  exact neg_one_pow_ne_zero' G.m

lemma hilbertNumerator_natDegree_ge_prod_plus_gap {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (g : ℕ) (hg : g ∈ S.gaps) :
    G.productPolynomial.natDegree + g ≤ G.hilbertNumerator.natDegree := by
  have hnonempty : S.gaps.Nonempty := ⟨g, hg⟩
  have hle : g ≤ S.gaps.sup id := gap_le_sup g hg
  calc G.productPolynomial.natDegree + g
      ≤ G.productPolynomial.natDegree + S.gaps.sup id := by omega
    _ ≤ G.hilbertNumerator.natDegree := hilbertNumerator_natDegree_ge_jstar G hnonempty

lemma forward_map_mem {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (g j : ℕ)
    (hj : j ∈ (Finset.range (G.hilbertNumerator.natDegree + 1)).filter (g ≤ ·)) :
    j - g ∈ Finset.range (G.hilbertNumerator.natDegree + 1 - g) := by
  simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
  omega

lemma inverse_map_mem {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (g k : ℕ)
    (hk : k ∈ Finset.range (G.hilbertNumerator.natDegree + 1 - g)) :
    k + g ∈ (Finset.range (G.hilbertNumerator.natDegree + 1)).filter (g ≤ ·) := by
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  omega

lemma forward_inverse_id' {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (g j : ℕ)
    (hj : j ∈ (Finset.range (G.hilbertNumerator.natDegree + 1)).filter (g ≤ ·)) :
    (j - g) + g = j := by aesop

lemma inverse_forward_id' {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (g k : ℕ)
    (_hk : k ∈ Finset.range (G.hilbertNumerator.natDegree + 1 - g)) :
    (k + g) - g = k := by aesop

lemma summand_eq' {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n g j : ℕ)
    (hj : j ∈ (Finset.range (G.hilbertNumerator.natDegree + 1)).filter (g ≤ ·)) :
    (G.productPolynomial.coeff (j - g) : ℚ) * (j : ℚ)^n =
    (G.productPolynomial.coeff (j - g) : ℚ) * ((↑(j - g) : ℚ) + (g : ℚ))^n := by aesop

lemma inner_sum_reindex {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n g : ℕ) (_hg : g ∈ S.gaps) :
    ∑ j ∈ (Finset.range (G.hilbertNumerator.natDegree + 1)).filter (g ≤ ·),
      (G.productPolynomial.coeff (j - g) : ℚ) * (j : ℚ)^n =
    ∑ k ∈ Finset.range (G.hilbertNumerator.natDegree + 1 - g),
      (G.productPolynomial.coeff k : ℚ) * ((k : ℚ) + (g : ℚ))^n := by
  apply Finset.sum_bij'
    (i := fun j _ => j - g)
    (j := fun k _ => k + g)
    (hi := fun j hj => forward_map_mem G g j hj)
    (hj := fun k hk => inverse_map_mem G g k hk)
  · intro j hj
    exact forward_inverse_id' G g j hj
  · intro k hk
    exact inverse_forward_id' G g k hk
  · intro j hj
    exact summand_eq' G n g j hj

lemma range_subset_from_degree_bound' {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (g : ℕ) (hg : g ∈ S.gaps) :
    Finset.range (G.productPolynomial.natDegree + 1) ⊆
    Finset.range (G.hilbertNumerator.natDegree + 1 - g) := by
  rw [Finset.range_subset_range]
  have h := hilbertNumerator_natDegree_ge_prod_plus_gap G g hg
  omega

lemma summand_zero_beyond_degree' {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (g n k : ℕ)
    (_hk : k ∈ Finset.range (G.hilbertNumerator.natDegree + 1 - g))
    (hk_not : k ∉ Finset.range (G.productPolynomial.natDegree + 1)) :
    (G.productPolynomial.coeff k : ℚ) * ((k : ℚ) + (g : ℚ))^n = 0 := by
  have h₁ : (G.productPolynomial.coeff k : ℤ) = 0 := by
    have h₂ : k > G.productPolynomial.natDegree := by
      have h₃ : k ≥ G.productPolynomial.natDegree + 1 := by
        by_contra h
        have h₄ : k < G.productPolynomial.natDegree + 1 := by linarith
        have h₅ : k ∈ Finset.range (G.productPolynomial.natDegree + 1) := by
          simp [Finset.mem_range]
          omega
        exact hk_not h₅
      omega
    have h₃ : G.productPolynomial.coeff k = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      exact h₂
    norm_cast at h₃ ⊢
  have h₂ : (G.productPolynomial.coeff k : ℚ) = 0 := by
    norm_cast at h₁ ⊢
  calc
    (G.productPolynomial.coeff k : ℚ) * ((k : ℚ) + (g : ℚ)) ^ n = 0 * ((k : ℚ) + (g : ℚ)) ^ n :=
      by rw [h₂]
    _ = 0 := by simp

lemma inner_sum_extend_range' {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n g : ℕ) (hg : g ∈ S.gaps) :
    ∑ k ∈ Finset.range (G.hilbertNumerator.natDegree + 1 - g),
      (G.productPolynomial.coeff k : ℚ) * ((k : ℚ) + (g : ℚ))^n =
    ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ) * ((k : ℚ) + (g : ℚ))^n := by
  symm
  apply Finset.sum_subset (range_subset_from_degree_bound' G g hg)
  intro k hk hk_not
  exact summand_zero_beyond_degree' G g n k hk hk_not

lemma distribute_j_pow_into_sum {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n j : ℕ) :
    (∑ g ∈ S.gaps.filter (· ≤ j), (G.productPolynomial.coeff (j - g) : ℚ)) * (j : ℚ)^n =
    ∑ g ∈ S.gaps.filter (· ≤ j), (G.productPolynomial.coeff (j - g) : ℚ) * (j : ℚ)^n := by
  rw [Finset.sum_mul]

lemma sum_exchange_condition' {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) :
    ∀ (j : ℕ) (g : ℕ),
      (j ∈ Finset.range (G.hilbertNumerator.natDegree + 1) ∧
       g ∈ S.gaps.filter (· ≤ j)) ↔
      (j ∈ (Finset.range (G.hilbertNumerator.natDegree + 1)).filter (g ≤ ·) ∧
       g ∈ S.gaps) := by
  aesop

lemma distribute_and_swap_sums {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) :
    ∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ g ∈ S.gaps.filter (· ≤ j), (G.productPolynomial.coeff (j - g) : ℚ)) * (j : ℚ)^n =
    ∑ g ∈ S.gaps, ∑ j ∈ (Finset.range (G.hilbertNumerator.natDegree + 1)).filter (g ≤ ·),
      (G.productPolynomial.coeff (j - g) : ℚ) * (j : ℚ)^n := by
  conv_lhs =>
    congr
    · skip
    · ext j
      rw [distribute_j_pow_into_sum G n j]
  exact Finset.sum_comm' (sum_exchange_condition' G)

lemma gap_sum_exchange {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    ∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ g ∈ S.gaps.filter (· ≤ j), (G.productPolynomial.coeff (j - g) : ℚ)) * (j : ℚ)^n =
    ∑ g ∈ S.gaps, ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ) * ((k : ℚ) + (g : ℚ))^n := by
  rw [distribute_and_swap_sums]
  apply Finset.sum_congr rfl
  intro g hg
  rw [inner_sum_reindex G n g hg, inner_sum_extend_range' G n g hg]

lemma binomial_sum_eq_add_pow (a b : ℚ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * a^k * b^(n - k) = (a + b)^n := by
  have h₁ : (a + b)^n = ∑ k ∈ Finset.range (n + 1),
    (a : ℚ)^k * (b : ℚ)^(n - k) * (n.choose k : ℚ) := by
    rw [add_pow]
  have h₂ : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * a^k * b^(n - k) =
      ∑ k ∈ Finset.range (n + 1), (a : ℚ)^k * (b : ℚ)^(n - k) * (n.choose k : ℚ) := by
    apply Finset.sum_congr rfl
    intro k _
    have h₃ : (n.choose k : ℚ) * a ^ k * b ^ (n - k) = (a : ℚ) ^ k * (b : ℚ) ^ (n - k) *
      (n.choose k : ℚ) := by
      ring_nf
    rw [h₃]
  have h₃ : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * a^k * b^(n - k) = (a + b)^n := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1),
        (a : ℚ) ^ k * (b : ℚ) ^ (n - k) * (n.choose k : ℚ) := by rw [h₂]
      _ = (a + b) ^ n := by
        linarith
  apply h₃

lemma triple_sum_exchange (gaps : Finset ℕ) (degP : ℕ) (coeff : ℕ → ℚ) (n : ℕ) :
    ∑ g ∈ gaps, ∑ k ∈ Finset.range (degP + 1), ∑ r ∈ Finset.range (n + 1),
      (coeff k) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) =
    ∑ r ∈ Finset.range (n + 1), ∑ g ∈ gaps, ∑ k ∈ Finset.range (degP + 1),
      (coeff k) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) := by
  have h₁ : ∑ g ∈ gaps, ∑ k ∈ Finset.range (degP + 1), ∑ r ∈ Finset.range (n + 1),
      (coeff k) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) =
    ∑ g ∈ gaps, ∑ r ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (degP + 1),
      (coeff k) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) := by
    apply Finset.sum_congr rfl
    intro g _
    have h₂ : ∑ k ∈ Finset.range (degP + 1), ∑ r ∈ Finset.range (n + 1),
        (coeff k) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) =
      ∑ r ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (degP + 1),
        (coeff k) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) := by
      apply Finset.sum_comm
    rw [h₂]
  have h₂ : ∑ g ∈ gaps, ∑ r ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (degP + 1),
      (coeff k) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) =
    ∑ r ∈ Finset.range (n + 1), ∑ g ∈ gaps, ∑ k ∈ Finset.range (degP + 1),
      (coeff k) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) := by
    have h₃ : ∑ g ∈ gaps, ∑ r ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (degP + 1),
        (coeff k) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) =
      ∑ r ∈ Finset.range (n + 1), ∑ g ∈ gaps, ∑ k ∈ Finset.range (degP + 1),
        (coeff k) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) := by
      rw [Finset.sum_comm]
    exact h₃
  calc
    ∑ g ∈ gaps, ∑ k ∈ Finset.range (degP + 1), ∑ r ∈ Finset.range (n + 1),
        (coeff k) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) =
      ∑ g ∈ gaps, ∑ r ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (degP + 1),
        (coeff k) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) := by rw [h₁]
    _ = ∑ r ∈ Finset.range (n + 1), ∑ g ∈ gaps, ∑ k ∈ Finset.range (degP + 1),
        (coeff k) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) := by rw [h₂]

lemma factor_binomial_coeff_from_double_sum (gaps : Finset ℕ) (degP : ℕ) (coeff : ℕ → ℚ) (n r : ℕ) :
    ∑ g ∈ gaps, ∑ k ∈ Finset.range (degP + 1),
      (coeff k) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) =
    (n.choose r : ℚ) * (∑ k ∈ Finset.range (degP + 1), (coeff k) * (k : ℚ)^r) *
      (∑ g ∈ gaps, (g : ℚ)^(n - r)) := by
  have h1 : ∑ g ∈ gaps, ∑ k ∈ Finset.range (degP + 1),
    (coeff k) * (n.choose r : ℚ) * (k : ℚ) ^ r * (g : ℚ) ^ (n - r) =
       ∑ g ∈ gaps, (n.choose r : ℚ) * ∑ k ∈ Finset.range (degP + 1),
         (coeff k) * (k : ℚ) ^ r * (g : ℚ) ^ (n - r) := by
    apply Finset.sum_congr rfl
    intro g _
    have h2 : ∑ k ∈ Finset.range (degP + 1),
      (coeff k) * (n.choose r : ℚ) * (k : ℚ) ^ r * (g : ℚ) ^ (n - r) =
      (n.choose r : ℚ) * ∑ k ∈ Finset.range (degP + 1),
        (coeff k) * (k : ℚ) ^ r * (g : ℚ) ^ (n - r) := by
      calc
        ∑ k ∈ Finset.range (degP + 1),
          (coeff k) * (n.choose r : ℚ) * (k : ℚ) ^ r * (g : ℚ) ^ (n - r) =
            ∑ k ∈ Finset.range (degP + 1),
              (n.choose r : ℚ) * ((coeff k) * (k : ℚ) ^ r * (g : ℚ) ^ (n - r)) := by
          apply Finset.sum_congr rfl; intro k _; ring
        _ = (n.choose r : ℚ) * ∑ k ∈ Finset.range (degP + 1),
          (coeff k) * (k : ℚ) ^ r * (g : ℚ) ^ (n - r) := by
          rw [Finset.mul_sum]
    exact h2
  have h2 : ∑ g ∈ gaps, (n.choose r : ℚ) * ∑ k ∈ Finset.range (degP + 1),
    (coeff k) * (k : ℚ) ^ r * (g : ℚ) ^ (n - r) =
       (n.choose r : ℚ) * ∑ g ∈ gaps, ∑ k ∈ Finset.range (degP + 1),
         (coeff k) * (k : ℚ) ^ r * (g : ℚ) ^ (n - r) := by
    rw [Finset.mul_sum]
  have h3 : (n.choose r : ℚ) * ∑ g ∈ gaps, ∑ k ∈ Finset.range (degP + 1),
    (coeff k) * (k : ℚ) ^ r * (g : ℚ) ^ (n - r) =
      (n.choose r : ℚ) * (∑ k ∈ Finset.range (degP + 1), (coeff k) * (k : ℚ) ^ r) * (∑ g ∈ gaps,
        (g : ℚ) ^ (n - r)) := by
    have h4 : ∑ g ∈ gaps, ∑ k ∈ Finset.range (degP + 1),
      (coeff k) * (k : ℚ) ^ r * (g : ℚ) ^ (n - r) =
        ∑ k ∈ Finset.range (degP + 1), ∑ g ∈ gaps, (coeff k) * (k : ℚ) ^ r * (g : ℚ) ^ (n - r) := by
      rw [Finset.sum_comm]
    have h5 : ∑ k ∈ Finset.range (degP + 1), ∑ g ∈ gaps,
      (coeff k) * (k : ℚ) ^ r * (g : ℚ) ^ (n - r) =
        ∑ k ∈ Finset.range (degP + 1), (coeff k) * (k : ℚ) ^ r * ∑ g ∈ gaps, (g : ℚ) ^ (n - r) := by
      apply Finset.sum_congr rfl
      intro k _
      have h6 : ∑ g ∈ gaps, (coeff k) * (k : ℚ) ^ r * (g : ℚ) ^ (n - r) =
          (coeff k) * (k : ℚ) ^ r * ∑ g ∈ gaps, (g : ℚ) ^ (n - r) := by
        simp [Finset.mul_sum, mul_assoc]
      rw [h6]
    have h6 : ∑ k ∈ Finset.range (degP + 1), (coeff k) * (k : ℚ) ^ r * ∑ g ∈ gaps,
      (g : ℚ) ^ (n - r) =
        (∑ k ∈ Finset.range (degP + 1), (coeff k) * (k : ℚ) ^ r) * (∑ g ∈ gaps,
          (g : ℚ) ^ (n - r)) := by
      calc
        ∑ k ∈ Finset.range (degP + 1), (coeff k) * (k : ℚ) ^ r * ∑ g ∈ gaps, (g : ℚ) ^ (n - r) =
            ∑ k ∈ Finset.range (degP + 1), ((coeff k) * (k : ℚ) ^ r * ∑ g ∈ gaps,
              (g : ℚ) ^ (n - r)) := by simp [mul_assoc]
        _ = ∑ k ∈ Finset.range (degP + 1), ((coeff k) * (k : ℚ) ^ r) * (∑ g ∈ gaps,
          (g : ℚ) ^ (n - r)) := by
          apply Finset.sum_congr rfl
          intro k _
          ring_nf
        _ = (∑ k ∈ Finset.range (degP + 1), (coeff k) * (k : ℚ) ^ r) * (∑ g ∈ gaps,
          (g : ℚ) ^ (n - r)) := by
          simp [Finset.sum_mul]
    rw [h4, h5, h6]
    ring
  calc
    ∑ g ∈ gaps, ∑ k ∈ Finset.range (degP + 1),
      (coeff k) * (n.choose r : ℚ) * (k : ℚ) ^ r * (g : ℚ) ^ (n - r) =
        ∑ g ∈ gaps, (n.choose r : ℚ) * ∑ k ∈ Finset.range (degP + 1),
          (coeff k) * (k : ℚ) ^ r * (g : ℚ) ^ (n - r) := by
      exact h1
    _ = (n.choose r : ℚ) * ∑ g ∈ gaps, ∑ k ∈ Finset.range (degP + 1),
      (coeff k) * (k : ℚ) ^ r * (g : ℚ) ^ (n - r) := by
      exact h2
    _ = (n.choose r : ℚ) * (∑ k ∈ Finset.range (degP + 1), (coeff k) * (k : ℚ) ^ r) * (∑ g ∈ gaps,
      (g : ℚ) ^ (n - r)) := by
      exact h3

lemma sum_choose_mul_div_factorial_eq_sum_div_factorials (n : ℕ) (A B : ℕ → ℚ) :
    ∑ r ∈ Finset.range (n + 1), ((n.choose r : ℚ) * A r * B r) / (n.factorial : ℚ) =
    ∑ r ∈ Finset.range (n + 1), (A r / (r.factorial : ℚ)) * (B r / ((n - r).factorial : ℚ)) := by
  have h_main : ∀ (r : ℕ),
    r ∈ Finset.range (n + 1) → ((n.choose r : ℚ) * A r *
      B r) / (n.factorial : ℚ) = (A r / (r.factorial : ℚ)) * (B r / ((n - r).factorial : ℚ)) := by
    intro r hr
    have h₁ : r ≤ n := by
      simp only [Finset.mem_range] at hr
      omega
    have h₂ : (n.choose r : ℕ) * r.factorial * (n - r).factorial = n.factorial := by
      rw [Nat.choose_mul_factorial_mul_factorial h₁]
    have h₃ : (n.choose r : ℚ) * (r.factorial : ℚ) * ((n - r).factorial : ℚ) = (n.factorial : ℚ) :=
      by
      norm_cast at h₂ ⊢
    have h₄ : (n.factorial : ℚ) ≠ 0 := by positivity
    have h₅ : (r.factorial : ℚ) ≠ 0 := by positivity
    have h₆ : ((n - r).factorial : ℚ) ≠ 0 := by positivity
    have h₇ : ((n.choose r : ℚ) : ℚ) / (n.factorial : ℚ) = 1 / ((r.factorial : ℚ) *
      ((n - r).factorial : ℚ)) := by
      have h₇₁ : (n.choose r : ℚ) * (r.factorial : ℚ) *
        ((n - r).factorial : ℚ) = (n.factorial : ℚ) := by
        exact_mod_cast h₃
      have h₇₂ : (r.factorial : ℚ) * ((n - r).factorial : ℚ) ≠ 0 := by positivity
      field_simp [h₄, h₅, h₆, h₇₂] at h₇₁ ⊢
      nlinarith
    calc
      ((n.choose r : ℚ) * A r * B r) / (n.factorial : ℚ) = (n.choose r : ℚ) / (n.factorial : ℚ) *
        (A r * B r) := by
        field_simp [h₄]
      _ = (1 / ((r.factorial : ℚ) * ((n - r).factorial : ℚ))) * (A r * B r) := by rw [h₇]
      _ = (A r / (r.factorial : ℚ)) * (B r / ((n - r).factorial : ℚ)) := by
        have h₈ : (r.factorial : ℚ) ≠ 0 := by positivity
        have h₉ : ((n - r).factorial : ℚ) ≠ 0 := by positivity
        field_simp [h₈, h₉]
  have h_sum_eq : ∑ r ∈ Finset.range (n + 1),
    ((n.choose r : ℚ) * A r * B r) / (n.factorial : ℚ) = ∑ r ∈ Finset.range (n + 1),
      (A r / (r.factorial : ℚ)) * (B r / ((n - r).factorial : ℚ)) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [h_main r hr]
  apply h_sum_eq

lemma gap_sum_binomial_expand {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
  :
    (∑ g ∈ S.gaps, ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ) * ((k : ℚ) + (g : ℚ))^n) / (n.factorial : ℚ) =
    ∑ r ∈ Finset.range (n + 1),
      ((∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
        (G.productPolynomial.coeff k : ℚ) * (k : ℚ)^r) / (r.factorial : ℚ)) *
      ((∑ g ∈ S.gaps, (g : ℚ)^(n - r)) / ((n - r).factorial : ℚ)) := by
  have binom_expand : ∀ (k g : ℕ),
      ((k : ℚ) + (g : ℚ))^n = ∑ r ∈ Finset.range (n + 1),
        (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) := by
    intro k g
    exact (binomial_sum_eq_add_pow k g n).symm
  have step1 : ∑ g ∈ S.gaps, ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ) * ((k : ℚ) + (g : ℚ))^n =
    ∑ g ∈ S.gaps, ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      ∑ r ∈ Finset.range (n + 1),
        (G.productPolynomial.coeff k : ℚ) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) := by
    congr 1
    ext g
    congr 1
    ext k
    rw [binom_expand k g]
    rw [Finset.mul_sum]
    congr 1
    ext r
    ring
  have step2 : ∑ g ∈ S.gaps, ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      ∑ r ∈ Finset.range (n + 1),
        (G.productPolynomial.coeff k : ℚ) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) =
    ∑ r ∈ Finset.range (n + 1), ∑ g ∈ S.gaps,
      ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) := by
    exact triple_sum_exchange S.gaps G.productPolynomial.natDegree (fun k =>
      (G.productPolynomial.coeff k : ℚ)) n
  have step3 : ∀ r, ∑ g ∈ S.gaps, ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) =
    (n.choose r : ℚ) * (∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
        (G.productPolynomial.coeff k : ℚ) * (k : ℚ)^r) *
      (∑ g ∈ S.gaps, (g : ℚ)^(n - r)) := by
    intro r
    exact factor_binomial_coeff_from_double_sum S.gaps G.productPolynomial.natDegree
      (fun k => (G.productPolynomial.coeff k : ℚ)) n r
  rw [step1, step2]
  simp_rw [step3]
  rw [Finset.sum_div]
  exact sum_choose_mul_div_factorial_eq_sum_div_factorials n
    (fun r => ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
        (G.productPolynomial.coeff k : ℚ) * (k : ℚ)^r)
    (fun r => ∑ g ∈ S.gaps, (g : ℚ)^(n - r))

lemma P_sum_to_exp_coeff {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (r : ℕ) :
    (∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ) * (k : ℚ)^r) / (r.factorial : ℚ) =
    ((-1 : ℚ)^G.m * (G.piM : ℚ)) * (PowerSeries.coeff r) (PowerSeries.X ^ G.m * G.ASeries) := by
  rw [← exp_poly_sub_coeff]
  rw [productPolynomial_exp_transform]
  simp only [map_smul, smul_eq_mul]

lemma gap_sum_to_coeff {S : NumericalSemigroup} (k : ℕ) :
    (∑ g ∈ S.gaps, (g : ℚ)^k) / (k.factorial : ℚ) =
    (PowerSeries.coeff k) (PowerSeries.mk fun j => ∑ g ∈ S.gaps,
      (g : ℚ)^j / (j.factorial : ℚ)) := by
  simp [PowerSeries.coeff_mk, Finset.sum_div]

lemma coeff_mul_range' {R : Type*} [Semiring R] (φ ψ : PowerSeries R) (n : ℕ) :
    (PowerSeries.coeff n) (φ * ψ) =
    ∑ r ∈ Finset.range (n + 1), (PowerSeries.coeff r) φ * (PowerSeries.coeff (n - r)) ψ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

lemma sum_factor_scalar' {α : Type*} (s : Finset α) (c : ℚ) (a b : α → ℚ) :
    ∑ r ∈ s, (c * a r) * b r = c * ∑ r ∈ s, a r * b r := by
  simp_rw [mul_assoc, Finset.mul_sum]

lemma binomial_sum_to_convolution {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n
  : ℕ) :
    ∑ r ∈ Finset.range (n + 1),
      ((∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
        (G.productPolynomial.coeff k : ℚ) * (k : ℚ)^r) / (r.factorial : ℚ)) *
      ((∑ g ∈ S.gaps, (g : ℚ)^(n - r)) / ((n - r).factorial : ℚ)) =
    ((-1 : ℚ)^G.m * (G.piM : ℚ)) *
      (PowerSeries.coeff n) (PowerSeries.X ^ G.m * G.ASeries *
        PowerSeries.mk fun k => ∑ g ∈ S.gaps, (g : ℚ)^k / (k.factorial : ℚ)) := by
  have h1 : ∀ r, (∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ) * (k : ℚ)^r) / (r.factorial : ℚ) =
      ((-1 : ℚ)^G.m * (G.piM : ℚ)) * (PowerSeries.coeff r) (PowerSeries.X ^ G.m * G.ASeries) :=
    fun r => P_sum_to_exp_coeff G r
  have h2 : ∀ r, (∑ g ∈ S.gaps, (g : ℚ)^r) / (r.factorial : ℚ) =
      (PowerSeries.coeff r) (PowerSeries.mk fun j => ∑ g ∈ S.gaps, (g : ℚ)^j / (j.factorial : ℚ)) :=
    fun r => gap_sum_to_coeff r
  conv_lhs => arg 2; ext r; rw [h1 r, h2 (n - r)]
  rw [sum_factor_scalar']
  congr 1
  rw [← coeff_mul_range']

lemma gap_part_equals_gap_term_natDegree {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ g ∈ S.gaps.filter (· ≤ j),
        (G.productPolynomial.coeff (j - g) : ℚ)) * (j : ℚ)^n) / (n.factorial : ℚ) =
    ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) * (-(PowerSeries.coeff n) (PowerSeries.X ^ G.m *
      G.ASeries *
         PowerSeries.mk fun k => ∑ g ∈ S.gaps, (g : ℚ)^k / (k.factorial : ℚ))) := by
  rw [gap_sum_exchange]
  rw [gap_sum_binomial_expand]
  rw [binomial_sum_to_convolution]
  ring

lemma exp_poly_sub_hilbertNumerator_eq {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) :
    expPolySub G.hilbertNumerator = QExpSeries G := by
  ext n
  rw [exp_poly_sub_coeff, Q_exp_series_coeff]
  rw [hilbert_sum_decomposition_natDegree]
  rw [sub_div]
  rw [sum_part_equals_bernoulli_term_natDegree, gap_part_equals_gap_term_natDegree]
  ring

lemma hilbertNumerator_exp_eq_Q_exp {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) :
    hilbertNumeratorExpSub G = QExpSeries G := by
  rw [hilbertNumerator_exp_sub_eq_exp_poly_sub, exp_poly_sub_hilbertNumerator_eq]

lemma alternatingPowerSum_eq_neg_factorial_coeff
    {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) (hn : 1 ≤ n) :
    G.alternatingPowerSum n = -((n.factorial : ℚ) * (PowerSeries.coeff n) (QExpSeries G)) := by
  rw [alternatingPowerSum_eq_coeff_hilbert_exp G n hn, hilbertNumerator_exp_eq_Q_exp]

lemma C_m_plus_p_formula {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    G.alternatingPowerSum (G.m + p) =
    ((-1 : ℚ)^G.m * (G.piM : ℚ) * ((G.m + p).factorial : ℚ) *
      (PowerSeries.coeff (p + 1)) G.BSeries) +
    ((-1 : ℚ)^G.m * (G.piM : ℚ) *
      ∑ r ∈ Finset.range (p + 1),
        ((G.m + p).choose r : ℚ) * ((G.m + p - r).factorial : ℚ) *
          (PowerSeries.coeff (p - r)) G.ASeries * S.gapPowerSum r) := by
  -- Step 1: Establish 1 ≤ m + p (needed for alternatingPowerSum_eq_neg_factorial_coeff)
  have hmp : 1 ≤ G.m + p := Nat.le_add_right 1 p |>.trans (Nat.add_le_add_right G.hm_pos p)
  -- Step 2: Relate to QExpSeries coefficient via the bridge lemmas
  rw [alternatingPowerSum_eq_neg_factorial_coeff G (G.m + p) hmp]
  -- Step 3: Extract the coefficient
  rw [Q_exp_coeff_at_m_plus_p]
  -- Step 4: Use gap_term_final_form
  have h_gap := gap_term_final_form G p
  -- Step 5: Combine by distributing (m+p)! over the addition
  -- and applying the sign identity (-1)^{m+1} * (-1) = (-1)^{m+2} = (-1)^m
  calc -((↑(G.m + p).factorial : ℚ) *
          ((-1) ^ (G.m + 1) * ↑G.piM *
            ((PowerSeries.coeff (p + 1)) G.BSeries +
             ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
               (PowerSeries.coeff (p - r)) G.ASeries * (↑g) ^ r / (↑r.factorial))))
      = (-1) ^ G.m * ↑G.piM * ↑(G.m + p).factorial * (PowerSeries.coeff (p + 1)) G.BSeries +
        (-1) ^ G.m * ↑G.piM * (↑(G.m + p).factorial *
          ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
            (PowerSeries.coeff (p - r)) G.ASeries * (↑g) ^ r / (↑r.factorial)) := by ring
    _ = (-1) ^ G.m * ↑G.piM * ↑(G.m + p).factorial * (PowerSeries.coeff (p + 1)) G.BSeries +
        (-1) ^ G.m * ↑G.piM *
          ∑ r ∈ Finset.range (p + 1),
            ↑((G.m + p).choose r) * ↑(G.m + p - r).factorial *
              (PowerSeries.coeff (p - r)) G.ASeries * S.gapPowerSum r := by rw [h_gap]

lemma K_invariant_expanded {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    G.KInvariant p =
    (p.factorial : ℚ) * (PowerSeries.coeff (p + 1)) G.BSeries +
    ∑ r ∈ Finset.range (p + 1),
      ((p.factorial : ℚ) / (r.factorial : ℚ)) *
        (PowerSeries.coeff (p - r)) G.ASeries * S.gapPowerSum r := by
  -- Step 1: Unfold KInvariant and substitute C_m_plus_p_formula
  unfold NumericalSemigroupGenerators.KInvariant
  rw [C_m_plus_p_formula]
  -- Step 2: Distribute the coefficient over the addition
  rw [mul_add]
  -- Step 3: Simplify the Bernoulli term
  have hpi : 0 < G.piM := pi_m_pos G
  rw [bernoulli_term_simplify G.m p G.piM hpi]
  -- Step 4: Simplify the gap sum term
  rw [gap_sum_simplify]

lemma bernoulli_coeff_to_T_delta {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p :
  ℕ) :
    (p.factorial : ℚ) * (PowerSeries.coeff (p + 1)) G.BSeries =
    (2 ^ (p + 1) : ℚ) / ((p : ℚ) + 1) * G.TDelta (p + 1) := by
  -- Expand TDelta definition
  unfold NumericalSemigroupGenerators.TDelta
  ring_nf
  -- Goal: p! * coeff = coeff * (1+p)^{-1} * (1+p)! * 2^{-p} * 2^p
  -- Use: 2^{-p} * 2^p = 1 and (1+p)!/(1+p) = p!
  have h1 : (2 : ℚ)⁻¹ ^ p * 2 ^ p = 1 := by
    rw [← mul_pow]
    simp
  rw [mul_assoc, mul_assoc, mul_assoc, h1, mul_one]
  -- Goal: p! * coeff = coeff * ((1+p)^{-1} * (1+p)!)
  -- We have (1+p)! = (1+p) * p!, so (1+p)^{-1} * (1+p)! = p!
  have h2 : (1 + (p : ℚ))⁻¹ * ((1 + p).factorial : ℚ) = (p.factorial : ℚ) := by
    rw [Nat.add_comm 1 p, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    rw [add_comm]
    field_simp
  rw [h2]
  ring

lemma factorial_div_eq_choose_mul {p r : ℕ} (hr : r ≤ p) :
    (p.factorial : ℚ) / r.factorial = (p.choose r : ℚ) * (p - r).factorial := by
  have h_main : ((p.choose r : ℕ) : ℚ) * (r.factorial : ℚ) *
    ((p - r).factorial : ℚ) = (p.factorial : ℚ) := by
    have h₁ : (p.choose r : ℕ) * r.factorial * (p - r).factorial = p.factorial := by
      rw [← Nat.choose_mul_factorial_mul_factorial hr]
    norm_cast at h₁ ⊢
  have h_r_pos : (r.factorial : ℚ) ≠ 0 := by positivity
  field_simp [h_r_pos]
  linarith

lemma A_coeff_to_T_sigma {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p r : ℕ)
    (hr : r ≤ p) :
    ((p.factorial : ℚ) / (r.factorial : ℚ)) * (PowerSeries.coeff (p - r)) G.ASeries =
    (p.choose r : ℚ) * G.TSigma (p - r) := by
  -- Use the factorial identity: p!/r! = C(p,r) * (p-r)!
  have hfact := factorial_div_eq_choose_mul hr
  -- TSigma (p - r) = (p-r)! * coeff (p - r) ASeries by definition
  unfold NumericalSemigroupGenerators.TSigma
  -- Substitute and rearrange
  rw [hfact]
  ring

lemma sum_A_coeff_eq_sum_T_sigma {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p :
  ℕ) :
    ∑ r ∈ Finset.range (p + 1),
      ((p.factorial : ℚ) / (r.factorial : ℚ)) *
        (PowerSeries.coeff (p - r)) G.ASeries * S.gapPowerSum r =
    ∑ r ∈ Finset.range (p + 1),
      (p.choose r : ℚ) * G.TSigma (p - r) * S.gapPowerSum r := by
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  have hrp : r ≤ p := Nat.lt_succ_iff.mp hr
  have h := A_coeff_to_T_sigma G p r hrp
  calc (p.factorial : ℚ) / (r.factorial : ℚ) *
        (PowerSeries.coeff (p - r)) G.ASeries * S.gapPowerSum r
      = ((p.factorial : ℚ) / (r.factorial : ℚ) *
        (PowerSeries.coeff (p - r)) G.ASeries) * S.gapPowerSum r := by ring
    _ = ((p.choose r : ℚ) * G.TSigma (p - r)) * S.gapPowerSum r := by rw [h]
    _ = (p.choose r : ℚ) * G.TSigma (p - r) * S.gapPowerSum r := by ring

lemma fels_conjecture_main {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    G.KInvariant p =
      ∑ r ∈ Finset.range (p + 1),
        (p.choose r : ℚ) * G.TSigma (p - r) * S.gapPowerSum r +
      (2 ^ (p + 1) : ℚ) / ((p : ℚ) + 1) * G.TDelta (p + 1) := by
  rw [K_invariant_expanded]
  rw [bernoulli_coeff_to_T_delta]
  rw [sum_A_coeff_eq_sum_T_sigma]
  ring

end FelsConjectureProof

theorem fels_conjecture (S : NumericalSemigroup) (G : NumericalSemigroupGenerators S) (p : ℕ) :
    G.KInvariant p =
      ∑ r ∈ Finset.range (p + 1),
        (p.choose r : ℚ) * G.TSigma (p - r) * S.gapPowerSum r +
      (2 ^ (p + 1) : ℚ) / ((p : ℚ) + 1) * G.TDelta (p + 1) :=
  FelsConjectureProof.fels_conjecture_main G p
