/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Basic

/-! # Weighted Children -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# WeightedChildren

Weighted child response observables and stationarity cancellations.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- Private Section 5.3 stationarity cancellation for weighted child
responses.

The manuscript later supplies `weight R = 1 - (phi)_R`; the only stochastic
input here is the Ch4 source theorem for weighted descendant response
expectations. -/
theorem integral_weightedChildResponseJ_eq_zero_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    (weight : TriadicCube d → ℝ) (p q : Vec d)
    (hweight :
      descendantsAverage (originCube d m) (Int.toNat (m - k)) weight = 0)
    (hJ : ∀ R, R ∈ descendantsAtScale (originCube d m) k →
      Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P) :
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - k))
          (fun R => weight R * Ch04.restrictionResponseJObservableCubeSet R p q a) ∂P = 0 := by
  rw [
    hP.integral_weightedDescendantsAverage_restrictionResponseJObservableCubeSet_eq_weight_average_mul_originCube_of_stationary
      hstat hk_nonneg hkm weight p q hJ,
    hweight]
  ring

/-- Manuscript cutoff child weight `1 - (phi)_R`.  This is deterministic;
measurability and stationarity enter only through the response observable that
it weights. -/
noncomputable def cutoffChildWeight {d : ℕ}
    (φ : Vec d → ℝ) (R : TriadicCube d) : ℝ :=
  1 - cubeAverage R φ

/-- If the cutoff has parent average one, then the finite average of the child
weights `1 - (phi)_R` is zero. -/
theorem descendantsAverage_cutoffChildWeight_eq_zero_of_cubeAverage_eq_one
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (φ : Vec d → ℝ)
    (hφ_int : IntegrableOn φ (cubeSet Q) volume)
    (hMean : cubeAverage Q φ = 1) :
    descendantsAverage Q j (fun R => cutoffChildWeight φ R) = 0 := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtDepth_nonempty Q j
  have hcard_ne : ((D.card : ℝ) ≠ 0) := by
    exact_mod_cast Finset.card_ne_zero.mpr hD_nonempty
  have hdesc :
      descendantsAverage Q j (fun R => cubeAverage R φ) = 1 := by
    rw [← cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      (Q := Q) (j := j) (f := φ) hφ_int]
    exact hMean
  have hsum_avg : ∑ R ∈ D, cubeAverage R φ = (D.card : ℝ) := by
    have hscaled :
        (D.card : ℝ)⁻¹ * (∑ R ∈ D, cubeAverage R φ) = 1 := by
      simpa [descendantsAverage, D] using hdesc
    have hmul := congrArg (fun x : ℝ => (D.card : ℝ) * x) hscaled
    simpa [mul_assoc, hcard_ne] using hmul
  unfold descendantsAverage cutoffChildWeight
  change (D.card : ℝ)⁻¹ * ∑ R ∈ D, (1 - cubeAverage R φ) = 0
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hsum_avg]
  ring

/-- Cutoff-weighted child response average from the manuscript splitting. -/
noncomputable def cutoffWeightedChildResponseJAtScale {d : ℕ}
    (m k : ℤ) (φ : Vec d → ℝ) (p q : Vec d) :
    RegCoeffField d → ℝ :=
  fun a =>
    descendantsAverage (originCube d m) (Int.toNat (m - k))
      (fun R => cutoffChildWeight φ R *
        Ch04.restrictionResponseJObservableCubeSet R p q a)

/-- Childwise response integrability makes the cutoff-weighted child average
integrable.  The cutoff weights are deterministic scalars. -/
theorem integrable_cutoffWeightedChildResponseJAtScale
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {k m : ℤ} (hkm : k ≤ m)
    (φ : Vec d → ℝ) (p q : Vec d)
    (hJ : ∀ R, R ∈ descendantsAtScale (originCube d m) k →
      Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P) :
    Integrable (cutoffWeightedChildResponseJAtScale m k φ p q) P := by
  have hDepth :
      ∀ R, R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - k)) →
        Integrable
          (fun a : RegCoeffField d =>
            cutoffChildWeight φ R *
              Ch04.restrictionResponseJObservableCubeSet R p q a) P := by
    intro R hR
    have hRscale : R ∈ descendantsAtScale (originCube d m) k := by
      simpa [descendantsAtScale_eq_descendantsAtDepth (originCube d m) hkm] using! hR
    exact (hJ R hRscale).const_mul (cutoffChildWeight φ R)
  simpa [cutoffWeightedChildResponseJAtScale] using!
    Ch04.integrable_descendantsAverage
      (P := P) (Q := originCube d m) (j := Int.toNat (m - k))
      (F := fun R a =>
        cutoffChildWeight φ R * Ch04.restrictionResponseJObservableCubeSet R p q a) hDepth

/-- The manuscript cutoff-weighted child response has zero expectation under
stationarity once the cutoff is normalized to have parent average one. -/
theorem integral_cutoffWeightedChildResponseJAtScale_eq_zero_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    (φ : Vec d → ℝ) (p q : Vec d)
    (hφ_int : IntegrableOn φ (cubeSet (originCube d m)) volume)
    (hMean : cubeAverage (originCube d m) φ = 1)
    (hJ : ∀ R, R ∈ descendantsAtScale (originCube d m) k →
      Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P) :
    ∫ a, cutoffWeightedChildResponseJAtScale m k φ p q a ∂P = 0 := by
  have hweight :
      descendantsAverage (originCube d m) (Int.toNat (m - k))
        (fun R => cutoffChildWeight φ R) = 0 :=
    descendantsAverage_cutoffChildWeight_eq_zero_of_cubeAverage_eq_one
      (Q := originCube d m) (j := Int.toNat (m - k)) (φ := φ) hφ_int hMean
  simpa [cutoffWeightedChildResponseJAtScale] using
    integral_weightedChildResponseJ_eq_zero_of_stationary
      (P := P) hP hstat hk_nonneg hkm
      (fun R => cutoffChildWeight φ R) p q hweight hJ

/-- Parent centered response in the Section 5.3 notation. -/
noncomputable def centeredResponseJAtScale {d : ℕ}
    (m : ℤ) (p q p0 q0 : Vec d) : RegCoeffField d → ℝ :=
  Ch04.restrictionCenteredResponseJObservableCubeSet (originCube d m) p q p0 q0

/-- The centered parent response minus the cutoff-weighted child response
average.  This is the stochastic side of the manuscript's centered splitting. -/
noncomputable def centeredJMinusCutoffWeightedChildAtScale {d : ℕ}
    (m k : ℤ) (φ : Vec d → ℝ) (p q p0 q0 : Vec d) :
    RegCoeffField d → ℝ :=
  fun a =>
    centeredResponseJAtScale m p q p0 q0 a -
      cutoffWeightedChildResponseJAtScale m k φ p q a

/-- The expectation of the centered splitting term is just the centered parent
expectation: the cutoff-weighted child contribution cancels by stationarity and
normalization. -/
theorem integral_centeredJMinusCutoffWeightedChildAtScale_eq_expectedResponseJCubeSet_sub_half_dot
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    (φ : Vec d → ℝ) (p q p0 q0 : Vec d)
    (hφ_int : IntegrableOn φ (cubeSet (originCube d m)) volume)
    (hMean : cubeAverage (originCube d m) φ = 1)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hJ : ∀ R, R ∈ descendantsAtScale (originCube d m) k →
      Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P) :
    ∫ a, centeredJMinusCutoffWeightedChildAtScale m k φ p q p0 q0 a ∂P =
      Ch04.expectedResponseJCubeSet P (originCube d m) p q -
        (1 / 2 : ℝ) * vecDot p0 q0 := by
  let : IsProbabilityMeasure P := hP.isProbability
  have hWeightedInt :
      Integrable (cutoffWeightedChildResponseJAtScale m k φ p q) P :=
    integrable_cutoffWeightedChildResponseJAtScale (P := P) hkm φ p q hJ
  have hCenteredInt :
      Integrable (centeredResponseJAtScale m p q p0 q0) P := by
    simpa [centeredResponseJAtScale] using
      Ch04.integrable_restrictionCenteredResponseJObservableCubeSet
        (P := P) (Q := originCube d m) p q p0 q0 hParent
  have hCenteredIntegral :
      ∫ a, centeredResponseJAtScale m p q p0 q0 a ∂P =
        Ch04.expectedResponseJCubeSet P (originCube d m) p q -
          (1 / 2 : ℝ) * vecDot p0 q0 := by
    simpa [centeredResponseJAtScale] using
      Ch04.integral_restrictionCenteredResponseJObservableCubeSet_eq_expectedResponseJCubeSet_sub_half_dot
        (P := P) (Q := originCube d m) p q p0 q0 hParent
  have hWeightedZero :
      ∫ a, cutoffWeightedChildResponseJAtScale m k φ p q a ∂P = 0 :=
    integral_cutoffWeightedChildResponseJAtScale_eq_zero_of_stationary
      (P := P) hP hstat hk_nonneg hkm φ p q hφ_int hMean hJ
  calc
    ∫ a, centeredJMinusCutoffWeightedChildAtScale m k φ p q p0 q0 a ∂P =
        ∫ a, centeredResponseJAtScale m p q p0 q0 a ∂P -
          ∫ a, cutoffWeightedChildResponseJAtScale m k φ p q a ∂P := by
        change
          ∫ a,
              centeredResponseJAtScale m p q p0 q0 a -
                cutoffWeightedChildResponseJAtScale m k φ p q a ∂P =
            ∫ a, centeredResponseJAtScale m p q p0 q0 a ∂P -
              ∫ a, cutoffWeightedChildResponseJAtScale m k φ p q a ∂P
        rw [integral_sub hCenteredInt hWeightedInt]
    _ =
        (Ch04.expectedResponseJCubeSet P (originCube d m) p q -
            (1 / 2 : ℝ) * vecDot p0 q0) - 0 := by
        rw [hCenteredIntegral, hWeightedZero]
    _ =
        Ch04.expectedResponseJCubeSet P (originCube d m) p q -
          (1 / 2 : ℝ) * vecDot p0 q0 := by
        ring

/-- Private additivity-defect observable from the manuscript proof:
child-scale average of `J` minus parent-scale `J`. -/
noncomputable def responseJAdditivityDefectAtScale {d : ℕ}
    (m k : ℤ) (p q : Vec d) : RegCoeffField d → ℝ :=
  fun a =>
    descendantsAverage (originCube d m) (Int.toNat (m - k))
      (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) -
      Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a

/-- The additivity-defect observable has expectation `tau_{m,k}` under
stationarity.  This is the stochastic identity used in the square-root
Cauchy step of Lemma `l.J.upper.bound.weak.norms.homogenization.scale`. -/
theorem integral_responseJAdditivityDefectAtScale_eq_tauAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m) (p q : Vec d)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hDesc : ∀ R, R ∈ descendantsAtScale (originCube d m) k →
      Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P) :
    ∫ a, responseJAdditivityDefectAtScale m k p q a ∂P =
      tauAtScale P m k p q := by
  have hDescDepth :
      ∀ R, R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - k)) →
        Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P := by
    intro R hR
    exact hDesc R (by
      simpa [descendantsAtScale_eq_descendantsAtDepth (originCube d m) hkm] using! hR)
  have hAvgInt :
      Integrable
        (fun a : RegCoeffField d =>
          descendantsAverage (originCube d m) (Int.toNat (m - k))
            (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a)) P :=
    Ch04.integrable_descendantsAverage_restrictionResponseJObservableCubeSet hDescDepth
  calc
    ∫ a, responseJAdditivityDefectAtScale m k p q a ∂P
        =
      ∫ a,
          descendantsAverage (originCube d m) (Int.toNat (m - k))
            (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) ∂P -
        ∫ a, Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a ∂P := by
          change
            ∫ a,
              (descendantsAverage (originCube d m) (Int.toNat (m - k))
                (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) -
                Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a) ∂P =
            ∫ a,
                descendantsAverage (originCube d m) (Int.toNat (m - k))
                  (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) ∂P -
              ∫ a, Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a ∂P
          rw [integral_sub hAvgInt hParent]
    _ =
      Ch04.expectedResponseJCubeSet P (originCube d k) p q -
        Ch04.expectedResponseJCubeSet P (originCube d m) p q := by
        rw [
          hP.integral_descendantsAverage_restrictionResponseJObservableCubeSet_eq_originCube_of_stationary
            hstat hk_nonneg hkm p q hDesc]
        rfl
    _ = tauAtScale P m k p q := by
        rfl

/-- If a scalar observable is a.e. bounded in absolute value by an integrable
right-hand side, then its expectation is bounded by the expectation of that
right-hand side. -/
theorem integral_le_integral_of_ae_abs_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {X Y : α → ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ)
    (hXY : ∀ᵐ a ∂μ, |X a| ≤ Y a) :
    ∫ a, X a ∂μ ≤ ∫ a, Y a ∂μ := by
  exact integral_mono_ae hX hY <|
    hXY.mono fun a ha => (le_abs_self (X a)).trans ha

/-- Expectation assembly for the centered-minus-child split: stationarity turns
the left side into the centered parent expectation, and an a.e. deterministic
absolute-value bound controls it by the expectation of any integrable RHS. -/
theorem integral_centeredJMinusCutoffWeightedChildAtScale_le_integral_of_ae_abs_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    (φ : Vec d → ℝ) (p q p0 q0 : Vec d) (RHS : RegCoeffField d → ℝ)
    (hφ_int : IntegrableOn φ (cubeSet (originCube d m)) volume)
    (hMean : cubeAverage (originCube d m) φ = 1)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hJ : ∀ R, R ∈ descendantsAtScale (originCube d m) k →
      Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P)
    (hRHS : Integrable RHS P)
    (hBound :
      ∀ᵐ a ∂P,
        |centeredJMinusCutoffWeightedChildAtScale m k φ p q p0 q0 a| ≤ RHS a) :
    Ch04.expectedResponseJCubeSet P (originCube d m) p q -
        (1 / 2 : ℝ) * vecDot p0 q0 ≤
      ∫ a, RHS a ∂P := by
  let : IsProbabilityMeasure P := hP.isProbability
  let X : RegCoeffField d → ℝ :=
    centeredJMinusCutoffWeightedChildAtScale m k φ p q p0 q0
  have hWeightedInt :
      Integrable (cutoffWeightedChildResponseJAtScale m k φ p q) P :=
    integrable_cutoffWeightedChildResponseJAtScale (P := P) hkm φ p q hJ
  have hCenteredInt :
      Integrable (centeredResponseJAtScale m p q p0 q0) P := by
    simpa [centeredResponseJAtScale] using
      Ch04.integrable_restrictionCenteredResponseJObservableCubeSet
        (P := P) (Q := originCube d m) p q p0 q0 hParent
  have hXint : Integrable X P := by
    simpa [X, centeredJMinusCutoffWeightedChildAtScale] using!
      hCenteredInt.sub hWeightedInt
  have hInt_le :
      ∫ a, X a ∂P ≤ ∫ a, RHS a ∂P :=
    integral_le_integral_of_ae_abs_le hXint hRHS (by
      simpa [X] using hBound)
  have hIntegral_eq :
      ∫ a, X a ∂P =
        Ch04.expectedResponseJCubeSet P (originCube d m) p q -
          (1 / 2 : ℝ) * vecDot p0 q0 := by
    simpa [X] using
      integral_centeredJMinusCutoffWeightedChildAtScale_eq_expectedResponseJCubeSet_sub_half_dot
        (P := P) hP hstat hk_nonneg hkm φ p q p0 q0
        hφ_int hMean hParent hJ
  simpa [hIntegral_eq] using hInt_le

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
