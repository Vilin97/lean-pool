/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceColorClassIndependence
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceMeasurability
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Concentration

/-!
# Concentration of source-local observables on a scale-color class

These wrappers combine source unit-range dependence with the existing
independent-sum concentration estimates.  Source locality supplies both the
independence input and global measurability of each summand.
-/

namespace Homogenization.Book.Ch04

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- A single scale-color class of descendant cubes inherits `Gamma_sigma`
concentration from uniformly controlled centered source-local summands. -/
theorem isBigO_gammaSigma_finsetSum_descendantsAtScaleScaleColorClass_of_sourceUnitRangeDependentLaw
    {d : ℕ} {Q : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    {P : SourceCoeffLaw d} [IsProbabilityMeasure P] {σ K : ℝ}
    (hP : SourceUnitRangeDependentLaw P)
    (hσ₀ : 0 < σ) (hσ₂ : σ ≤ 2) (hK : 0 < K)
    (X : TriadicCube d → Source.Coarse.Carrier d → ℝ)
    (hX_local :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c,
        IsSourceLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (X R))
    (hX :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c,
        IsBigO P (gammaSigma σ) (X R) K)
    (h_mean :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c, ∫ a, X R a ∂P = 0) :
    IsBigO P (gammaSigma σ)
      (fun a => ∑ R ∈ descendantsAtScaleScaleColorClass Q k c, X R a)
      (gammaSigmaIndependentSumConst σ *
        Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) * K) := by
  let S : Finset (TriadicCube d) := descendantsAtScaleScaleColorClass Q k c
  by_cases hS : S.Nonempty
  · let Y : {R : TriadicCube d // R ∈ S} → Source.Coarse.Carrier d → ℝ :=
      fun R => X R.1
    have h_indep : iIndepFun Y P := by
      exact iIndepFun_descendantsAtScaleScaleColorClass_of_sourceUnitRangeDependentLaw
        (Q := Q) (k := k) (c := c) (P := P) hP
        (fun R => hX_local R.1 R.2)
    have h_meas : ∀ R, Measurable (Y R) := by
      intro R
      exact (hX_local R.1 R.2).measurable
    have hY :
        ∀ R ∈ S.attach, IsBigO P (gammaSigma σ) (Y R) K := by
      intro R _hR
      exact hX R.1 R.2
    have h_meanY : ∀ R ∈ S.attach, ∫ a, Y R a ∂P = 0 := by
      intro R _hR
      exact h_mean R.1 R.2
    have hS_attach : S.attach.Nonempty := by
      simpa using hS
    have hsum_eq :
        (fun a => ∑ R ∈ S.attach, Y R a) =
          fun a => ∑ R ∈ S, X R a := by
      funext a
      simpa [Y] using
        (Finset.sum_attach (s := S) (f := fun R => X R a))
    have hsum :=
      isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
        (μ := P) (X := Y) (s := S.attach) (σ := σ) (K := K)
        h_indep h_meas hS_attach hσ₀ hσ₂ hK hY h_meanY
    simpa [S, hsum_eq, mul_assoc, mul_left_comm, mul_comm] using hsum
  · have hS_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [isBigO_gammaSigma_iff]
    intro t ht
    have htail_empty :
        absTailEvent (fun _ : Source.Coarse.Carrier d => (0 : ℝ)) 0 = ∅ := by
      ext a
      simp [absTailEvent]
    simpa [S, hS_empty, htail_empty, absTailEvent, upperTailEvent] using
      (show (0 : ℝ) ≤ Real.exp (-(t ^ σ)) by positivity)

/-- A single scale-color class of descendant cubes inherits `Psi_sigma`
concentration from uniformly controlled centered source-local summands. -/
theorem isBigO_psiSigma_finsetSum_descendantsAtScaleScaleColorClass_of_sourceUnitRangeDependentLaw
    {d : ℕ} {Q : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    {P : SourceCoeffLaw d} [IsProbabilityMeasure P] {σ K : ℝ}
    (hP : SourceUnitRangeDependentLaw P)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (X : TriadicCube d → Source.Coarse.Carrier d → ℝ)
    (hX_local :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c,
        IsSourceLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (X R))
    (hX_int :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c, Integrable (X R) P)
    (hX :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c,
        IsBigO P (psiSigma σ) (X R) K)
    (h_mean :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c, ∫ a, X R a ∂P = 0) :
    IsBigO P (psiSigma σ)
      (fun a => ∑ R ∈ descendantsAtScaleScaleColorClass Q k c, X R a)
      (psiSigmaIndependentSumConst σ *
        Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) * K) := by
  let S : Finset (TriadicCube d) := descendantsAtScaleScaleColorClass Q k c
  by_cases hS : S.Nonempty
  · let Y : {R : TriadicCube d // R ∈ S} → Source.Coarse.Carrier d → ℝ :=
      fun R => X R.1
    have h_indep : iIndepFun Y P := by
      exact iIndepFun_descendantsAtScaleScaleColorClass_of_sourceUnitRangeDependentLaw
        (Q := Q) (k := k) (c := c) (P := P) hP
        (fun R => hX_local R.1 R.2)
    have h_meas : ∀ R, Measurable (Y R) := by
      intro R
      exact (hX_local R.1 R.2).measurable
    have h_int : ∀ R ∈ S.attach, Integrable (Y R) P := by
      intro R _hR
      exact hX_int R.1 R.2
    have hY :
        ∀ R ∈ S.attach, IsBigO P (psiSigma σ) (Y R) K := by
      intro R _hR
      exact hX R.1 R.2
    have h_meanY : ∀ R ∈ S.attach, ∫ a, Y R a ∂P = 0 := by
      intro R _hR
      exact h_mean R.1 R.2
    have hS_attach : S.attach.Nonempty := by
      simpa using hS
    have hsum_eq :
        (fun a => ∑ R ∈ S.attach, Y R a) =
          fun a => ∑ R ∈ S, X R a := by
      funext a
      simpa [Y] using
        (Finset.sum_attach (s := S) (f := fun R => X R a))
    have hsum :=
      isBigO_psiSigma_finset_sum_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero
        (μ := P) (X := Y) (s := S.attach) (σ := σ) (K := K)
        h_indep h_meas h_int h_meanY hS_attach hσ hK hY
    simpa [S, hsum_eq, mul_assoc, mul_left_comm, mul_comm] using hsum
  · have hS_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [isBigO_psiSigma_iff]
    intro t ht
    have htail_empty :
        absTailEvent (fun _ : Source.Coarse.Carrier d => (0 : ℝ)) 0 = ∅ := by
      ext a
      simp [absTailEvent]
    simpa [S, hS_empty, htail_empty, absTailEvent, upperTailEvent] using
      (show 0 ≤ Real.exp
        (-((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ))) by positivity)

end

end Homogenization.Book.Ch04
