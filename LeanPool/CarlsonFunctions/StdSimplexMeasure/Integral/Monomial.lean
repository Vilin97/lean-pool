/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Integral.Slicing

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Measure
public import LeanPool.CarlsonFunctions.Pochhammer.BetaIntegral
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.PositiveSimplex

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import LeanPool.CarlsonFunctions.StdSimplexMeasure.EuclideanCrossSection
import all LeanPool.CarlsonFunctions.StdSimplexMeasure.Measure.Basic

/-! # Monomial and polynomial integrals on the standard simplex -/

open Fintype (card)

public noncomputable section StdSimplexIntegral

namespace MeasureTheory

open Measure MeasureTheory

universe u

variable {ι : Type u} [Fintype ι]


open scoped Classical in
/-- Reduce a monomial integral on a nontrivial simplex to the monomial integral on the simplex
obtained by deleting coordinate `i`. -/
theorem integral_stdSimplex_explicit_monomial_succ [Nontrivial ι] (i : ι) (m : ι → ℕ) :
  ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, (∏ j, u j ^ m j) ∂stdSimplexMeasure =
    (Nat.factorial (m i) * Nat.factorial (card ι + (∑ j, m j) - 2 - m i)
      / Nat.factorial (card ι + ∑ j, m j - 1) : ℝ)
      * ∫ u in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i}, (∏ j, u j ^ m j.val)
        ∂stdSimplexMeasure := by
  have hf : IntegrableOn (fun u : ι → ℝ => ∏ j, u j ^ m j)
      (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure := by
    apply ContinuousOn.integrableOn_stdSimplex
    fun_prop
  rw [integral_stdSimplex_split_at i _ hf]
  have hfactor (t : ℝ) (v : {j : ι // j ≠ i} → ℝ)
      (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i}) :
      (∏ j, stdSimplexCoordMap i (fun q => (1 - t) * v q) j ^ m j) =
        t ^ m i * (1 - t) ^ (∑ q : {j : ι // j ≠ i}, m q.val) *
          ∏ q : {j : ι // j ≠ i}, v q ^ m q.val := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    have hvsum : ∑ q, v q = 1 := hv.2
    rw [stdSimplexCoordMap_apply_self, ← Finset.mul_sum, hvsum]
    simp only [mul_one, sub_sub_cancel]
    have hprod :
        (∏ q : {j : ι // j ≠ i},
          stdSimplexCoordMap i (fun q => (1 - t) * v q) q.val ^ m q.val) =
        (1 - t) ^ (∑ q : {j : ι // j ≠ i}, m q.val) *
          ∏ q : {j : ι // j ≠ i}, v q ^ m q.val := by
      calc
        _ = ∏ q : {j : ι // j ≠ i}, ((1 - t) * v q) ^ m q.val := by
          apply Finset.prod_congr rfl
          intro q _
          rw [stdSimplexCoordMap_apply_of_ne i q.val q.property]
        _ = _ := by
          simp_rw [mul_pow, Finset.prod_mul_distrib,
            ← Finset.prod_pow_eq_pow_sum]
    rw [hprod]
    ring
  have hinner (t : ℝ) :
      ∫ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
          (∏ j, stdSimplexCoordMap i (fun q => (1 - t) * v q) j ^ m j)
          ∂stdSimplexMeasure =
        (t ^ m i * (1 - t) ^ (∑ q : {j : ι // j ≠ i}, m q.val)) *
          ∫ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
            (∏ q, v q ^ m q.val) ∂stdSimplexMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict
      (μ := stdSimplexMeasure) (Convexity.StdSimplex.isClosed_coordinateSet ℝ _).measurableSet]
        with v hv
    exact hfactor t v hv
  simp_rw [hinner]
  simp only [smul_eq_mul]
  have hcard : 2 ≤ card ι := Nat.succ_le_iff.mpr Fintype.one_lt_card
  have hsum : ∑ j, m j = m i + ∑ q : {j : ι // j ≠ i}, m q.val :=
    Fintype.sum_eq_add_sum_subtype_ne m i
  let b : ℕ := card ι - 2 + ∑ q : {j : ι // j ≠ i}, m q.val
  have hb : card ι + (∑ j, m j) - 2 - m i = b := by
    rw [hsum]
    dsimp [b]
    omega
  have hden : card ι + (∑ j, m j) - 1 = m i + b + 1 := by
    rw [hsum]
    dsimp [b]
    omega
  let A : ℝ := ∫ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
    (∏ q, v q ^ m q.val) ∂stdSimplexMeasure
  calc
    ∫ t in Set.Icc (0 : ℝ) 1,
        (1 - t) ^ (card ι - 2) *
          ((t ^ m i * (1 - t) ^ (∑ q : {j : ι // j ≠ i}, m q.val)) * A) =
        A * ∫ t in Set.Icc (0 : ℝ) 1, t ^ m i * (1 - t) ^ b := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [show b = (card ι - 2) + ∑ q : {j : ι // j ≠ i}, m q.val by rfl,
        pow_add]
      ring
    _ = A * ((Nat.factorial (m i) * Nat.factorial b : ℝ) /
        Nat.factorial (m i + b + 1)) := by
      rw [integral_Icc_pow_mul_one_sub_pow]
    _ = _ := by
      rw [hb, hden]
      dsimp [A]
      ring

/-- The integral of a monomial with natural exponents over the standard simplex. -/
theorem integral_stdSimplex_explicit_monomial (m : ι → ℕ) [Nonempty ι] :
    ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, (∏ i, u i ^ m i) ∂stdSimplexMeasure =
      (∏ i, Nat.factorial (m i)) / (Nat.factorial (card ι + (∑ i, m i) - 1) : ℝ) := by
  classical
  suffices h : ∀ n : ℕ, ∀ (α : Type u) [Fintype α], card α = n →
      ∀ (a : α → ℕ), Nonempty α →
        ∫ u in Convexity.StdSimplex.coordinateSet ℝ α, (∏ j, u j ^ a j) ∂stdSimplexMeasure =
          (∏ j, Nat.factorial (a j)) /
            (Nat.factorial (card α + (∑ j, a j) - 1) : ℝ) by
    exact h (card ι) ι rfl m inferInstance
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro α _ hα a hne
      let : Nonempty α := hne
      cases subsingleton_or_nontrivial α with
      | inl hs =>
          let : Unique α := ⟨⟨Classical.choice hne⟩, fun x => hs.elim x _⟩
          rw [integral_stdSimplex_unique]
          simp
          field_simp
      | inr hn =>
          let : Nontrivial α := hn
          let i : α := Classical.choice hne
          rw [integral_stdSimplex_explicit_monomial_succ i a]
          have hlt : card {j : α // j ≠ i} < n := by
            rw [← hα, Fintype.card_subtype_compl]
            exact Nat.sub_lt (Fintype.card_pos_iff.mpr hne) Nat.zero_lt_one
          have hsub : Nonempty {j : α // j ≠ i} := by
            obtain ⟨j, hj⟩ := exists_ne i
            exact ⟨⟨j, hj⟩⟩
          rw [ih (card {j : α // j ≠ i}) hlt {j : α // j ≠ i} rfl
            (fun j => a j.val) hsub]
          have hsum : ∑ j, a j = a i + ∑ q : {j : α // j ≠ i}, a q.val :=
            Fintype.sum_eq_add_sum_subtype_ne a i
          have hcardsub : card {j : α // j ≠ i} = card α - 1 := by
            simp
          have hidx : card {j : α // j ≠ i} +
              (∑ q : {j : α // j ≠ i}, a q.val) - 1 =
              card α + (∑ j, a j) - 2 - a i := by
            rw [hcardsub, hsum]
            have hc : 2 ≤ card α := Nat.succ_le_iff.mpr Fintype.one_lt_card
            omega
          rw [hidx, Fintype.prod_eq_mul_prod_subtype_ne _ i]
          field_simp
          norm_cast

/-- The integral of the constant function 1 over the standard simplex. -/
theorem integral_stdSimplex_constant [Nonempty ι] :
    ∫ _ in Convexity.StdSimplex.coordinateSet ℝ ι, (1 : ℝ) ∂stdSimplexMeasure =
      1 / (Nat.factorial (card ι - 1) : ℝ) := by
  rw [MeasureTheory.setIntegral_const, Measure.real, stdSimplexMeasure_stdSimplex_toReal]
  ring

/-- The integral of a `MvPolynomial` monomial over the standard simplex. -/
theorem integral_stdSimplex_MvPolynomial_monomial (m : ι →₀ ℕ) [Nonempty ι] :
    ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, m.prod (fun i n => u i ^ n) ∂stdSimplexMeasure =
      (∏ i, Nat.factorial (m i)) / (Nat.factorial (card ι + (∑ i, m i) - 1) : ℝ) := by
  simp_rw [m.prod_fintype _ fun _ ↦ pow_zero _]
  exact integral_stdSimplex_explicit_monomial (⇑m)

end MeasureTheory

end StdSimplexIntegral
