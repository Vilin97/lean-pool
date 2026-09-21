/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.CoarseAverages
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.Basic

/-! # High Scale Averages -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open scoped BigOperators

/-!
# High-scale average terms for the coarse-fluctuation lemma

This file contains the proof-internal deterministic conversion of the paired
high-scale average terms from `WeakNormsMaximizer` at the Section 5.3 special
vectors into the weighted descendant average of the normalized full-block
operator-norm-square fluctuation.
-/

noncomputable section

private theorem finset_weighted_sqrt_sum_sq_le_sum_mul_sum
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w A : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hA : ∀ i, 0 ≤ A i) :
    (∑ i ∈ S, w i * Real.sqrt (A i)) ^ 2 ≤
      (∑ i ∈ S, w i) * ∑ i ∈ S, w i * A i := by
  have hsum_eq :
      (∑ i ∈ S, Real.sqrt (w i) * Real.sqrt (w i * A i)) =
        ∑ i ∈ S, w i * Real.sqrt (A i) := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [Real.sqrt_mul (hw i) (A i)]
    rw [← mul_assoc, ← sq, Real.sq_sqrt (hw i)]
  have hCauchy :
      (∑ i ∈ S, w i * Real.sqrt (A i)) ≤
        Real.sqrt (∑ i ∈ S, w i) *
          Real.sqrt (∑ i ∈ S, w i * A i) := by
    simpa [hsum_eq] using
      (Real.sum_sqrt_mul_sqrt_le (s := S) (f := w) (g := fun i => w i * A i)
        hw (fun i => mul_nonneg (hw i) (hA i)))
  have hleft_nonneg : 0 ≤ ∑ i ∈ S, w i * Real.sqrt (A i) :=
    Finset.sum_nonneg fun i _hi => mul_nonneg (hw i) (Real.sqrt_nonneg _)
  have hW_nonneg : 0 ≤ ∑ i ∈ S, w i :=
    Finset.sum_nonneg fun i _hi => hw i
  have hWA_nonneg : 0 ≤ ∑ i ∈ S, w i * A i :=
    Finset.sum_nonneg fun i _hi => mul_nonneg (hw i) (hA i)
  have hsq :=
    pow_le_pow_left₀ hleft_nonneg hCauchy 2
  calc
    (∑ i ∈ S, w i * Real.sqrt (A i)) ^ 2
        ≤ (Real.sqrt (∑ i ∈ S, w i) *
            Real.sqrt (∑ i ∈ S, w i * A i)) ^ 2 := hsq
    _ = (∑ i ∈ S, w i) * ∑ i ∈ S, w i * A i := by
          rw [mul_pow, Real.sq_sqrt hW_nonneg, Real.sq_sqrt hWA_nonneg]

private theorem finset_weighted_sqrt_sum_sq_le_of_weight_le
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (v w A : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) (hvw : ∀ i, v i ≤ w i)
    (hA : ∀ i, 0 ≤ A i) :
    (∑ i ∈ S, v i * Real.sqrt (A i)) ^ 2 ≤
      (∑ i ∈ S, w i) * ∑ i ∈ S, w i * A i := by
  have hsum_le :
      (∑ i ∈ S, v i * Real.sqrt (A i)) ≤
        ∑ i ∈ S, w i * Real.sqrt (A i) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact mul_le_mul_of_nonneg_right (hvw i) (Real.sqrt_nonneg _)
  have hleft_nonneg : 0 ≤ ∑ i ∈ S, v i * Real.sqrt (A i) :=
    Finset.sum_nonneg fun i _hi => mul_nonneg (hv i) (Real.sqrt_nonneg _)
  have hright_nonneg : 0 ≤ ∑ i ∈ S, w i * Real.sqrt (A i) :=
    Finset.sum_nonneg fun i _hi => mul_nonneg (hw i) (Real.sqrt_nonneg _)
  have hsq_le :=
    pow_le_pow_left₀ hleft_nonneg hsum_le 2
  exact hsq_le.trans
    (finset_weighted_sqrt_sum_sq_le_sum_mul_sum S w A hw hA)

private theorem highScaleWeight_le_betaWeight
    (β s : ℝ) (hβs : β ≤ s) (r : ℕ) :
    Real.rpow (3 : ℝ) (-s * (r : ℝ)) ≤
      Real.rpow (3 : ℝ) (-β * (r : ℝ)) := by
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
  have hr : 0 ≤ (r : ℝ) := by positivity
  nlinarith

private theorem sigmaHatAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ) :
    0 ≤ sigmaHatAtScale hP hStruct m := by
  exact Real.sqrt_nonneg _

/-- Deterministic finite-sum/Cauchy conversion for the paired high-scale
average terms at the Section 5.3 special vectors.  The right side is the
weighted descendant average of the normalized full-block operator-norm-square
fluctuation. -/
theorem paired_highScaleAverageTerms_special_le_weighted_fullBlockNormalized_fluctuation
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    {k m : ℕ} (β s t : ℝ) (hβs : β ≤ s) (hβt : β ≤ t) (e : Vec d)
    (hb : 0 < hP.barSigmaAtScale hStruct (m : ℤ))
    (hc : 0 < hP.barSigmaStarAtScale hStruct (m : ℤ))
    (he : vecNormSq e = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    let σ := sigmaHatAtScale hP hStruct (m : ℤ)
    let θ := thetaAtScale hP hStruct (m : ℤ)
    let S := Finset.Icc ((k : ℤ) + 1) (m : ℤ)
    let wβ : ℤ → ℝ :=
      fun n => Real.rpow (3 : ℝ)
        (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
    σ *
        (WeakNormsMaximizer.gradientAverageTermAtScale
          (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxAverageTermAtScale
          (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2 ≤
      (∑ n ∈ S, wβ n) *
        ∑ n ∈ S, wβ n *
          descendantsAverage (originCube d (m : ℤ))
            (Int.toNat ((m : ℤ) - n))
            (fun R =>
              2 * θ *
                fullBlockNormalizedFluctuationOperatorNormSqAtScale
                  hP hStruct (m : ℤ) R a) := by
  dsimp only
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let S := Finset.Icc ((k : ℤ) + 1) (m : ℤ)
  let wβ : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ)
      (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
  let ws : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ)
      (-s * (Int.toNat ((m : ℤ) - n) : ℝ))
  let wt : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ)
      (-t * (Int.toNat ((m : ℤ) - n) : ℝ))
  let G : ℤ → ℝ :=
    fun n =>
      descendantsAverage (originCube d (m : ℤ))
        (Int.toNat ((m : ℤ) - n))
        (fun R =>
          vecNormSq
            (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun - p0_e))
  let F : ℤ → ℝ :=
    fun n =>
      descendantsAverage (originCube d (m : ℤ))
        (Int.toNat ((m : ℤ) - n))
        (fun R =>
          vecNormSq
            (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun - q0_e))
  let H : ℤ → ℝ :=
    fun n =>
      descendantsAverage (originCube d (m : ℤ))
        (Int.toNat ((m : ℤ) - n))
        (fun R =>
          2 * θ *
            fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct (m : ℤ) R a)
  have hwβ : ∀ n, 0 ≤ wβ n := by
    intro n
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hws : ∀ n, 0 ≤ ws n := by
    intro n
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hwt : ∀ n, 0 ≤ wt n := by
    intro n
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hws_le : ∀ n, ws n ≤ wβ n := by
    intro n
    exact highScaleWeight_le_betaWeight β s hβs (Int.toNat ((m : ℤ) - n))
  have hwt_le : ∀ n, wt n ≤ wβ n := by
    intro n
    exact highScaleWeight_le_betaWeight β t hβt (Int.toNat ((m : ℤ) - n))
  have hG_nonneg : ∀ n, 0 ≤ G n := by
    intro n
    exact descendantsAverage_nonneg _ _ _ fun R _hR => vecNormSq_nonneg _
  have hF_nonneg : ∀ n, 0 ≤ F n := by
    intro n
    exact descendantsAverage_nonneg _ _ _ fun R _hR => vecNormSq_nonneg _
  have hσ_nonneg : 0 ≤ σ := by
    change 0 ≤ sigmaHatAtScale hP hStruct (m : ℤ)
    exact sigmaHatAtScale_nonneg hP hStruct (m : ℤ)
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hgrad_cauchy :
      (∑ n ∈ S, ws n * Real.sqrt (G n)) ^ 2 ≤
        (∑ n ∈ S, wβ n) * ∑ n ∈ S, wβ n * G n :=
    finset_weighted_sqrt_sum_sq_le_of_weight_le S ws wβ G hws hwβ hws_le hG_nonneg
  have hflux_cauchy :
      (∑ n ∈ S, wt n * Real.sqrt (F n)) ^ 2 ≤
        (∑ n ∈ S, wβ n) * ∑ n ∈ S, wβ n * F n :=
    finset_weighted_sqrt_sum_sq_le_of_weight_le S wt wβ F hwt hwβ hwt_le hF_nonneg
  have hgrad_scaled :
      σ * (∑ n ∈ S, ws n * Real.sqrt (G n)) ^ 2 ≤
        (∑ n ∈ S, wβ n) * (∑ n ∈ S, wβ n * (σ * G n)) := by
    have h := mul_le_mul_of_nonneg_left hgrad_cauchy hσ_nonneg
    simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h
  have hflux_scaled :
      σ⁻¹ * (∑ n ∈ S, wt n * Real.sqrt (F n)) ^ 2 ≤
        (∑ n ∈ S, wβ n) * (∑ n ∈ S, wβ n * (σ⁻¹ * F n)) := by
    have h := mul_le_mul_of_nonneg_left hflux_cauchy hσ_inv_nonneg
    simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h
  have hpaired_sums :
      σ * (∑ n ∈ S, ws n * Real.sqrt (G n)) ^ 2 +
          σ⁻¹ * (∑ n ∈ S, wt n * Real.sqrt (F n)) ^ 2 ≤
        (∑ n ∈ S, wβ n) *
          (∑ n ∈ S, wβ n * (σ * G n + σ⁻¹ * F n)) := by
    have hsum_nonneg : 0 ≤ ∑ n ∈ S, wβ n :=
      Finset.sum_nonneg fun n _hn => hwβ n
    have h := add_le_add hgrad_scaled hflux_scaled
    calc
      σ * (∑ n ∈ S, ws n * Real.sqrt (G n)) ^ 2 +
          σ⁻¹ * (∑ n ∈ S, wt n * Real.sqrt (F n)) ^ 2
          ≤
        (∑ n ∈ S, wβ n) * (∑ n ∈ S, wβ n * (σ * G n)) +
          (∑ n ∈ S, wβ n) * (∑ n ∈ S, wβ n * (σ⁻¹ * F n)) := h
      _ =
        (∑ n ∈ S, wβ n) *
          (∑ n ∈ S, wβ n * (σ * G n + σ⁻¹ * F n)) := by
          rw [← mul_add, ← Finset.sum_add_distrib]
          congr 2
          ext n
          ring
  have hpoint :
      ∀ n ∈ S, σ * G n + σ⁻¹ * F n ≤ H n := by
    intro n _hn
    let j := Int.toNat ((m : ℤ) - n)
    let Q : TriadicCube d := originCube d (m : ℤ)
    let Grad : TriadicCube d → ℝ :=
      fun R =>
        vecNormSq
          (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun - p0_e)
    let Flux : TriadicCube d → ℝ :=
      fun R =>
        vecNormSq
          (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun - q0_e)
    have hlinear :
        descendantsAverage Q j (fun R => σ * Grad R + σ⁻¹ * Flux R) =
          σ * G n + σ⁻¹ * F n := by
      rw [descendantsAverage_add, descendantsAverage_mul_left,
        descendantsAverage_mul_left]
    have hbase :=
      descendantsAverage_weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation
        hP hStruct a ha m Q j e hb hc he
    calc
      σ * G n + σ⁻¹ * F n =
          descendantsAverage Q j (fun R => σ * Grad R + σ⁻¹ * Flux R) := hlinear.symm
      _ ≤ H n := by
          simpa [H, Q, j, Grad, Flux, σ, θ, p_e, q_e, p0_e, q0_e] using hbase
  have hsum_point :
      (∑ n ∈ S, wβ n * (σ * G n + σ⁻¹ * F n)) ≤
        ∑ n ∈ S, wβ n * H n := by
    refine Finset.sum_le_sum ?_
    intro n hn
    exact mul_le_mul_of_nonneg_left (hpoint n hn) (hwβ n)
  have hsum_nonneg : 0 ≤ ∑ n ∈ S, wβ n :=
    Finset.sum_nonneg fun n _hn => hwβ n
  have hfluct :=
    mul_le_mul_of_nonneg_left hsum_point hsum_nonneg
  calc
    σ *
        (WeakNormsMaximizer.gradientAverageTermAtScale
          (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxAverageTermAtScale
          (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2
      =
        σ * (∑ n ∈ S, ws n * Real.sqrt (G n)) ^ 2 +
          σ⁻¹ * (∑ n ∈ S, wt n * Real.sqrt (F n)) ^ 2 := by
          simp [WeakNormsMaximizer.gradientAverageTermAtScale,
            WeakNormsMaximizer.fluxAverageTermAtScale, S, ws, wt, G, F,
            p_e, q_e, p0_e, q0_e]
    _ ≤
        (∑ n ∈ S, wβ n) *
          (∑ n ∈ S, wβ n * (σ * G n + σ⁻¹ * F n)) := hpaired_sums
    _ ≤
        (∑ n ∈ S, wβ n) * ∑ n ∈ S, wβ n * H n := hfluct

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
