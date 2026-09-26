/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourcePartitionAverageFluctuations
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourcePartitionAverageLowMoments
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourcePartitionAverageMoments
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceResponseObservables

/-!
# Exact-source ResponseJ partition averages

This module specializes the one-origin source partition endpoint to the scalar
response observable.  Its locality and translation covariance are derived
from the exact-source response API.
-/

@[expose] public section

namespace Homogenization.Book.Ch04

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

private theorem sourceResponseJ_translation_covariant {d : ℕ} (p q : Vec d) :
    IsSourceTranslationCovariant
      (fun (U : Set (Vec d)) (a : Source.Coarse.Carrier d) => ResponseJ U p q a.1) := by
  apply isSourceTranslationCovariant_comp_toCoeffField
  intro U z a
  simpa [translateByInt] using
    (ResponseJ_translateSet_eq_translateCoeffField (intVecToRealVec z) U p q a)

/-- The exact-source scalar response partition average `J_{n,m}`. -/
noncomputable def sourceResponseJDescendantAverage {d : ℕ} [NeZero d]
    (n m : ℤ) (_hn : 0 ≤ n) (_hnm : n ≤ m) (p q : Vec d) :
    Source.Coarse.Carrier d → ℝ :=
  fun a =>
    ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtScale (originCube d m) n, ResponseJ (cubeSet R) p q a.1

/-- The integrably centered exact-source scalar response partition average. -/
noncomputable def sourceCenteredResponseJDescendantAverage {d : ℕ} [NeZero d]
    (P : SourceCoeffLaw d) (n m : ℤ) (_hn : 0 ≤ n) (_hnm : n ≤ m)
    (p q : Vec d)
    (_hJ_int : Integrable
      (fun a : Source.Coarse.Carrier d =>
        ResponseJ (cubeSet (originCube d n)) p q a.1) P) :
    Source.Coarse.Carrier d → ℝ :=
  fun a =>
    sourceResponseJDescendantAverage n m _hn _hnm p q a -
      ∫ b, ResponseJ (cubeSet (originCube d n)) p q b.1 ∂P

private theorem sourceTranslatedObservable_responseJ_eq
    {d : ℕ} {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m) (p q : Vec d)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d m) n) :
    sourceTranslatedObservable (scaleTranslationShift n R)
      (fun a : Source.Coarse.Carrier d =>
        ResponseJ (cubeSet (originCube d n)) p q a.1) =
      fun a : Source.Coarse.Carrier d => ResponseJ (cubeSet R) p q a.1 := by
  have hcov : IsSourceTranslationCovariant
      (fun (U : Set (Vec d)) (a : Source.Coarse.Carrier d) => ResponseJ U p q a.1) :=
    sourceResponseJ_translation_covariant p q
  funext a
  have hshift :=
    cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
      (d := d) hn hnm hR
  calc
    ResponseJ (cubeSet (originCube d n)) p q
        (Source.Coarse.Carrier.translate (scaleTranslationShift n R) a).1 =
        ResponseJ
          (translateSet (intVecToRealVec (scaleTranslationShift n R))
            (cubeSet (originCube d n))) p q a.1 := by
          symm
          exact hcov (cubeSet (originCube d n)) (scaleTranslationShift n R) a
    _ = ResponseJ (cubeSet R) p q a.1 := by rw [hshift]

private theorem sourceCenteredTranslatedDescendantAverage_responseJ_eq
    {d : ℕ} [NeZero d] {n m : ℤ} (P : SourceCoeffLaw d)
    (hn : 0 ≤ n) (hnm : n ≤ m) (p q : Vec d)
    (hJ_int : Integrable
      (fun a : Source.Coarse.Carrier d =>
        ResponseJ (cubeSet (originCube d n)) p q a.1) P) :
    sourceCenteredTranslatedDescendantAverage P n m hn hnm
      (fun a : Source.Coarse.Carrier d =>
        ResponseJ (cubeSet (originCube d n)) p q a.1) hJ_int =
      sourceCenteredResponseJDescendantAverage P n m hn hnm p q hJ_int := by
  let D : Finset (TriadicCube d) := descendantsAtScale (originCube d m) n
  let μ : ℝ := ∫ b, ResponseJ (cubeSet (originCube d n)) p q b.1 ∂P
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtScale_nonempty (originCube d m) hnm
  have hD_card_ne_zero : ((D.card : ℝ)) ≠ 0 := by
    exact_mod_cast hD_nonempty.card_ne_zero
  have hsum_eq : ∀ a : Source.Coarse.Carrier d,
      (∑ R ∈ D,
        (sourceTranslatedObservable (scaleTranslationShift n R)
          (fun a : Source.Coarse.Carrier d =>
            ResponseJ (cubeSet (originCube d n)) p q a.1) a - μ)) =
        ∑ R ∈ D, (ResponseJ (cubeSet R) p q a.1 - μ) := by
    intro a
    refine Finset.sum_congr rfl ?_
    intro R hR
    rw [sourceTranslatedObservable_responseJ_eq hn hnm p q (by simpa [D] using hR)]
  funext a
  change ((D.card : ℝ)⁻¹ *
      ∑ R ∈ D,
        (sourceTranslatedObservable (scaleTranslationShift n R)
          (fun a : Source.Coarse.Carrier d =>
            ResponseJ (cubeSet (originCube d n)) p q a.1) a - μ)) =
    ((D.card : ℝ)⁻¹ * ∑ R ∈ D, ResponseJ (cubeSet R) p q a.1) - μ
  rw [hsum_eq a, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp [hD_card_ne_zero]

/-- Under source P1, the expectation of `J_{n,m}` is the origin-cube
expectation. -/
theorem integral_sourceResponseJDescendantAverage_eq_origin_of_sourceStationaryLaw
    {d : ℕ} [NeZero d] {n m : ℤ} {P : SourceCoeffLaw d}
    [IsProbabilityMeasure P]
    (hn : 0 ≤ n) (hnm : n ≤ m) (hPstat : SourceStationaryLaw P)
    (p q : Vec d)
    (hJ_int : Integrable
      (fun a : Source.Coarse.Carrier d =>
        ResponseJ (cubeSet (originCube d n)) p q a.1) P) :
    ∫ a, sourceResponseJDescendantAverage n m hn hnm p q a ∂P =
      ∫ a, ResponseJ (cubeSet (originCube d n)) p q a.1 ∂P := by
  let D : Finset (TriadicCube d) := descendantsAtScale (originCube d m) n
  let X : Source.Coarse.Carrier d → ℝ :=
    fun a => ResponseJ (cubeSet (originCube d n)) p q a.1
  have hX_meas : Measurable X :=
    (isSourceLocalRandomVariable_ResponseJ_cubeSet (originCube d n) p q).measurable
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtScale_nonempty (originCube d m) hnm
  have hD_card_ne_zero : ((D.card : ℝ)) ≠ 0 := by
    exact_mod_cast hD_nonempty.card_ne_zero
  have hJ_int_child : ∀ R ∈ D,
      Integrable (fun a : Source.Coarse.Carrier d => ResponseJ (cubeSet R) p q a.1) P := by
    intro R hR
    rw [← sourceTranslatedObservable_responseJ_eq hn hnm p q (by simpa [D] using hR)]
    simpa [X] using!
      (integrable_comp_sourceCarrier_translate_of_sourceStationaryLaw
        (P := P) hPstat (scaleTranslationShift n R) X hJ_int)
  have hJ_expect_child : ∀ R ∈ D,
      ∫ a, ResponseJ (cubeSet R) p q a.1 ∂P = ∫ a, X a ∂P := by
    intro R hR
    rw [← sourceTranslatedObservable_responseJ_eq hn hnm p q (by simpa [D] using hR)]
    exact integral_sourceTranslatedObservable_eq_origin_of_sourceStationaryLaw
      (P := P) hPstat (scaleTranslationShift n R) X hX_meas
  change ∫ a, ((D.card : ℝ)⁻¹ * ∑ R ∈ D, ResponseJ (cubeSet R) p q a.1) ∂P =
    ∫ a, X a ∂P
  rw [integral_const_mul, integral_finsetSum D hJ_int_child]
  calc
    ((D.card : ℝ)⁻¹ * ∑ R ∈ D, ∫ a, ResponseJ (cubeSet R) p q a.1 ∂P) =
        ((D.card : ℝ)⁻¹ * ∑ R ∈ D, ∫ a, X a ∂P) := by
          apply congrArg (fun x : ℝ => (D.card : ℝ)⁻¹ * x)
          exact Finset.sum_congr rfl fun R hR => hJ_expect_child R hR
    _ = ∫ a, X a ∂P := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp [hD_card_ne_zero]

/-- Centered `Gamma_sigma` concentration for partition averages of the exact
source scalar response. -/
theorem isBigO_gammaSigma_sourceCenteredResponseJDescendantAverage
    {d : ℕ} [NeZero d] {n m : ℤ} {P : SourceCoeffLaw d}
    [IsProbabilityMeasure P] {σ K : ℝ}
    (hn : 0 ≤ n) (hnm : n ≤ m)
    (hPstat : SourceStationaryLaw P) (hPdep : SourceUnitRangeDependentLaw P)
    (p q : Vec d)
    (hJ_int : Integrable
      (fun a : Source.Coarse.Carrier d =>
        ResponseJ (cubeSet (originCube d n)) p q a.1) P)
    (hσ₀ : 0 < σ) (hσ₂ : σ ≤ 2) (hK : 0 < K)
    (hJ0 : IsBigO P (gammaSigma σ)
      (sourceCenteredObservable P (fun a : Source.Coarse.Carrier d =>
        ResponseJ (cubeSet (originCube d n)) p q a.1) hJ_int) K) :
    IsBigO P (gammaSigma σ)
      (sourceCenteredResponseJDescendantAverage P n m hn hnm p q hJ_int)
      (gammaSigmaDescendantsAtScaleConst d n σ *
        partitionCardinalityScale (d := d) n m * K) := by
  have hJ_local :
      IsSourceLocalRandomVariable (cubeSet (originCube d n))
        (measurableSet_cubeSet (originCube d n))
        (fun a : Source.Coarse.Carrier d =>
          ResponseJ (cubeSet (originCube d n)) p q a.1) :=
    isSourceLocalRandomVariable_ResponseJ_cubeSet (originCube d n) p q
  have hsource :=
    isBigO_gammaSigma_sourceCenteredTranslatedDescendantAverage_of_sourceUnitRangeDependentLaw
      (P := P) hn hnm hPstat hPdep
      (fun a : Source.Coarse.Carrier d =>
        ResponseJ (cubeSet (originCube d n)) p q a.1)
      hJ_local hJ_int hσ₀ hσ₂ hK hJ0
  rw [sourceCenteredTranslatedDescendantAverage_responseJ_eq P hn hnm p q hJ_int] at hsource
  exact hsource

/-- Centered `Psi_sigma` concentration for partition averages of the exact
source scalar response. -/
theorem isBigO_psiSigma_sourceCenteredResponseJDescendantAverage
    {d : ℕ} [NeZero d] {n m : ℤ} {P : SourceCoeffLaw d}
    [IsProbabilityMeasure P] {σ K : ℝ}
    (hn : 0 ≤ n) (hnm : n ≤ m)
    (hPstat : SourceStationaryLaw P) (hPdep : SourceUnitRangeDependentLaw P)
    (p q : Vec d)
    (hJ_int : Integrable
      (fun a : Source.Coarse.Carrier d =>
        ResponseJ (cubeSet (originCube d n)) p q a.1) P)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (hJ0 : IsBigO P (psiSigma σ)
      (sourceCenteredObservable P (fun a : Source.Coarse.Carrier d =>
        ResponseJ (cubeSet (originCube d n)) p q a.1) hJ_int) K) :
    IsBigO P (psiSigma σ)
      (sourceCenteredResponseJDescendantAverage P n m hn hnm p q hJ_int)
      (psiSigmaDescendantsAtScaleConst d n σ *
        partitionCardinalityScale (d := d) n m * K) := by
  have hJ_local :
      IsSourceLocalRandomVariable (cubeSet (originCube d n))
        (measurableSet_cubeSet (originCube d n))
        (fun a : Source.Coarse.Carrier d =>
          ResponseJ (cubeSet (originCube d n)) p q a.1) :=
    isSourceLocalRandomVariable_ResponseJ_cubeSet (originCube d n) p q
  have hsource :=
    isBigO_psiSigma_sourceCenteredTranslatedDescendantAverage_of_sourceUnitRangeDependentLaw
      (P := P) hn hnm hPstat hPdep
      (fun a : Source.Coarse.Carrier d =>
        ResponseJ (cubeSet (originCube d n)) p q a.1)
      hJ_local hJ_int hσ hK hJ0
  rw [sourceCenteredTranslatedDescendantAverage_responseJ_eq P hn hnm p q hJ_int] at hsource
  exact hsource

/-- The real-exponent moment bound for the centered source `ResponseJ`
partition average, reduced to the one-origin source partition endpoint. -/
theorem integral_abs_sourceCenteredResponseJDescendantAverage_rpow_rpow_inv_le_of_sourceUnitRangeDependentLaw
    {d : ℕ} [NeZero d] {n m : ℤ} {P : SourceCoeffLaw d}
    [IsProbabilityMeasure P] {r : ℝ}
    (hn : 0 ≤ n) (hnm : n ≤ m)
    (hPstat : SourceStationaryLaw P) (hPdep : SourceUnitRangeDependentLaw P)
    (p q : Vec d)
    (hJ_int : Integrable
      (fun a : Source.Coarse.Carrier d =>
        ResponseJ (cubeSet (originCube d n)) p q a.1) P)
    (hr : 2 ≤ r)
    (hJ0r_int : Integrable
      (fun a =>
        |sourceCenteredObservable P
          (fun a : Source.Coarse.Carrier d =>
            ResponseJ (cubeSet (originCube d n)) p q a.1) hJ_int a| ^ r) P) :
    (∫ a,
        |sourceCenteredResponseJDescendantAverage P n m hn hnm p q hJ_int a| ^ r ∂P) ^ r⁻¹ ≤
      ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
        (rosenthalDescendantsAtScaleRpowLpConst d n r *
            ((descendantsAtScale (originCube d m) n).card : ℝ) ^ r⁻¹ +
          rosenthalDescendantsAtScaleRpowSqrtConst d n r *
            Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ)) *
          (∫ a,
            |sourceCenteredObservable P
              (fun a : Source.Coarse.Carrier d =>
                ResponseJ (cubeSet (originCube d n)) p q a.1) hJ_int a| ^ r ∂P) ^ r⁻¹ := by
  have hJ_local :
      IsSourceLocalRandomVariable (cubeSet (originCube d n))
        (measurableSet_cubeSet (originCube d n))
        (fun a : Source.Coarse.Carrier d =>
          ResponseJ (cubeSet (originCube d n)) p q a.1) :=
    isSourceLocalRandomVariable_ResponseJ_cubeSet (originCube d n) p q
  have hsource :=
    integral_abs_sourceCenteredTranslatedDescendantAverage_rpow_rpow_inv_le_of_sourceUnitRangeDependentLaw
      (P := P) (p := r) hn hnm hPstat hPdep
      (fun a : Source.Coarse.Carrier d =>
        ResponseJ (cubeSet (originCube d n)) p q a.1)
      hJ_local hJ_int hr hJ0r_int
  rw [sourceCenteredTranslatedDescendantAverage_responseJ_eq P hn hnm p q hJ_int] at hsource
  exact hsource

/-- A finite source `ξ`-moment of `ResponseJ` controls the `L¹` fluctuation
of its centered partition average. -/
theorem integral_abs_sourceCenteredResponseJDescendantAverage_le_of_sourceUnitRangeDependentLaw
    {d : ℕ} [NeZero d] {n m : ℤ} {P : SourceCoeffLaw d}
    [IsProbabilityMeasure P] {ξ : ℝ}
    (hn : 0 ≤ n) (hnm : n ≤ m)
    (hPstat : SourceStationaryLaw P) (hPdep : SourceUnitRangeDependentLaw P)
    (p q : Vec d) (hξ : 2 ≤ ξ)
    (hJξ_int : Integrable
      (fun a : Source.Coarse.Carrier d =>
        |ResponseJ (cubeSet (originCube d n)) p q a.1| ^ ξ) P) :
    let hJ_int :=
      _root_.Homogenization.IndependentSums.integrable_of_integrable_abs_rpow
        (μ := P)
        (f := fun a : Source.Coarse.Carrier d =>
          ResponseJ (cubeSet (originCube d n)) p q a.1)
        (le_trans (by norm_num) hξ)
        (isSourceLocalRandomVariable_ResponseJ_cubeSet (originCube d n) p q).measurable
        hJξ_int
    ∫ a, |sourceCenteredResponseJDescendantAverage P n m hn hnm p q hJ_int a| ∂P ≤
      ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
        (rosenthalDescendantsAtScaleRpowLpConst d n 2 *
            ((descendantsAtScale (originCube d m) n).card : ℝ) ^ (2 : ℝ)⁻¹ +
          rosenthalDescendantsAtScaleRpowSqrtConst d n 2 *
            Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ)) *
          (∫ a,
            |sourceCenteredObservable P
              (fun a : Source.Coarse.Carrier d =>
                ResponseJ (cubeSet (originCube d n)) p q a.1) hJ_int a| ^ ξ ∂P) ^ ξ⁻¹ := by
  let X : Source.Coarse.Carrier d → ℝ := fun a =>
    ResponseJ (cubeSet (originCube d n)) p q a.1
  have hJ_local :
      IsSourceLocalRandomVariable (cubeSet (originCube d n))
        (measurableSet_cubeSet (originCube d n)) X := by
    simpa [X] using
      (isSourceLocalRandomVariable_ResponseJ_cubeSet (originCube d n) p q)
  have hsource :=
    integral_abs_sourceCenteredTranslatedDescendantAverage_le_of_sourceUnitRangeDependentLaw
      (P := P) hn hnm hPstat hPdep X hJ_local hξ (by simpa [X] using hJξ_int)
  simpa only [X, sourceCenteredTranslatedDescendantAverage_responseJ_eq] using hsource

end

end Homogenization.Book.Ch04
