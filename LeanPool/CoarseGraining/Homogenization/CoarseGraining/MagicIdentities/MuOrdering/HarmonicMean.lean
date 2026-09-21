/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Ambient.MatrixOrderBridge
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.HilbertOperator

/-! # Harmonic Mean -/

namespace Homogenization

noncomputable section

open scoped MatrixOrder

/-!
# Harmonic-mean matrix bounds

This file upgrades the inverse-side scalar quadratic estimate
`σ_*^{-1} ≤ average(symmPart(a)^{-1})` to an honest matrix-order statement,
and then inverts it to obtain the note-facing harmonic-mean lower bound for
`σ_*`.
-/

/-- Entrywise volume-average of the pointwise inverse symmetric part. -/
noncomputable def averagedSymmPartInv {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) : Mat d :=
  volumeAverageMat U (fun x => (symmPart (a x))⁻¹)

private theorem integrableOn_symmPartInv_entry_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (i j : Fin d) :
    MeasureTheory.IntegrableOn (fun x => (((symmPart (a x))⁻¹ : Mat d) i j)) U := by
  classical
  let aExt : Vec d → Fin d → Fin d → ℝ := fun x => if x ∈ U then a x else 0
  have haExt : Measurable aExt := by
    refine measurable_pi_iff.2 ?_
    intro i
    refine measurable_pi_iff.2 ?_
    intro j
    have hmeas : Measurable (fun x => if x ∈ U then a x i j else 0) :=
      (measurable_pi_iff.1 (measurable_pi_iff.1 hEll.1 i) j)
    have hEq : (fun x => aExt x i j) = fun x => if x ∈ U then a x i j else 0 := by
      funext x
      by_cases hx : x ∈ U <;> simp [aExt, hx]
    rw [hEq]
    exact hmeas
  let sExt : Vec d → Fin d → Fin d → ℝ := fun x => symmPart (aExt x)
  have hsExt : Measurable sExt := by
    refine measurable_pi_iff.2 ?_
    intro i
    refine measurable_pi_iff.2 ?_
    intro j
    simpa [sExt] using measurable_symmPart_entry haExt i j
  let coeffExt : Vec d → ℝ := fun x => (((sExt x : Mat d)⁻¹ : Mat d) i j)
  have hcoeffExt : Measurable coeffExt := by
    simpa [coeffExt] using measurable_matrix_inv_entry hsExt i j
  have hfinite : MeasureTheory.volume U ≠ ⊤ := by
    simpa [volumeMeasureOn] using
      (MeasureTheory.measure_lt_top (volumeMeasureOn U) Set.univ).ne
  have hIntExt : MeasureTheory.IntegrableOn coeffExt U := by
    refine
      MeasureTheory.Measure.integrableOn_of_bounded
        (μ := MeasureTheory.volume) (M := lam⁻¹) hfinite hcoeffExt.aestronglyMeasurable ?_
    have hmem : ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
      exact
        (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
          (Filter.Eventually.of_forall fun x hx => hx)
    filter_upwards [hmem] with x hx
    have hbound :
        |(((symmPart (a x))⁻¹ : Mat d) i j)| ≤ lam⁻¹ :=
      abs_apply_symmPartInv_le_of_isEllipticFieldOn hEll hx i j
    simpa [coeffExt, sExt, aExt, hx, Real.norm_eq_abs] using hbound
  refine hIntExt.congr_fun ?_ (measurableSet_of_isEllipticFieldOn hEll)
  intro x hx
  simp [coeffExt, sExt, aExt, hx]

theorem vecDot_matVecMul_averagedSymmPartInv_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d) :
    vecDot q (matVecMul (averagedSymmPartInv U a) q) =
      volumeAverage U (fun x => vecDot q (matVecMul ((symmPart (a x))⁻¹) q)) := by
  exact
    vecDot_matVecMul_volumeAverageMat
      (fun i j => integrableOn_symmPartInv_entry_of_isEllipticFieldOn hEll i j) q q

theorem averagedSymmPartInv_posDef_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    (averagedSymmPartInv U a).PosDef := by
  have hSymm : (averagedSymmPartInv U a).IsSymm := by
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    apply congrArg (volumeAverage U)
    funext x
    have hS : Matrix.transpose (symmPart (a x)) = symmPart (a x) := by
      simpa [matTranspose] using (matTranspose_symmPart (a x))
    have hT : Matrix.transpose ((symmPart (a x))⁻¹ : Mat d) = ((symmPart (a x))⁻¹ : Mat d) := by
      simpa [hS] using (Matrix.transpose_nonsing_inv (A := symmPart (a x)))
    simpa [averagedSymmPartInv, volumeAverageMat] using congrArg (fun M => M i j) hT
  have hHerm : (averagedSymmPartInv U a).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hSymm
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hHerm ?_
  intro q hq
  have hvol_ne_zero : MeasureTheory.volume U ≠ 0 := by
    intro hzero
    have : (MeasureTheory.volume U).toReal = 0 := by simp [hzero]
    linarith
  obtain ⟨x0, hx0⟩ :
      U.Nonempty := MeasureTheory.nonempty_of_measure_ne_zero hvol_ne_zero
  rcases hEll.2 x0 hx0 with ⟨hlam_pos, hlamLam, -, -⟩
  have hLam_pos : 0 < Lam := lt_of_lt_of_le hlam_pos hlamLam
  let c : ℝ := lam * (Lam⁻¹ * Lam⁻¹)
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hqNorm_pos : 0 < vecNormSq q := by
    have hqNorm_ne : vecNormSq q ≠ 0 := by
      simpa [vecNormSq_eq_zero_iff] using hq
    exact lt_of_le_of_ne (vecNormSq_nonneg q) (by simpa [eq_comm] using hqNorm_ne)
  have hscalarInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot q (matVecMul ((symmPart (a x))⁻¹) q)) U := by
    exact
      integrableOn_vecDot_matVecMul_of_integrableOn_entries
        (fun i j => integrableOn_symmPartInv_entry_of_isEllipticFieldOn hEll i j) q q
  have hconstInt :
      MeasureTheory.IntegrableOn (fun _ : Vec d => c * vecNormSq q) U := by
    exact MeasureTheory.integrable_const _
  have hnonneg :
      0 ≤
        volumeAverage U
          (fun x => vecDot q (matVecMul ((symmPart (a x))⁻¹) q) - c * vecNormSq q) := by
    apply volumeAverage_nonneg_of_nonneg_on (measurableSet_of_isEllipticFieldOn hEll)
    intro x hx
    have hpoint := lowerBound_symmPartInv_of_isEllipticMatrix (hEll.2 x hx) q
    linarith
  have hsub :
      volumeAverage U
          (fun x => vecDot q (matVecMul ((symmPart (a x))⁻¹) q) - c * vecNormSq q) =
        volumeAverage U (fun x => vecDot q (matVecMul ((symmPart (a x))⁻¹) q)) -
          c * vecNormSq q := by
    rw [show
        (fun x => vecDot q (matVecMul ((symmPart (a x))⁻¹) q) - c * vecNormSq q) =
          (fun x => vecDot q (matVecMul ((symmPart (a x))⁻¹) q)) -
            fun _ : Vec d => c * vecNormSq q by
        funext x
        rfl]
    rw [volumeAverage_sub hscalarInt hconstInt, volumeAverage_const hvol.ne']
  have hLower :
      c * vecNormSq q ≤
        vecDot q (matVecMul (averagedSymmPartInv U a) q) := by
    rw [vecDot_matVecMul_averagedSymmPartInv_of_isEllipticFieldOn hEll q]
    linarith
  have hPos :
      0 < vecDot q (matVecMul (averagedSymmPartInv U a) q) := by
    nlinarith
  simpa [vecDot, matVecMul] using! hPos

theorem sigmaStarInvCoarse_le_averagedSymmPartInv_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U) (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    MatLoewnerLE (sigmaStarInvCoarse U a) (averagedSymmPartInv U a) := by
  intro q
  rw [vecDot_matVecMul_averagedSymmPartInv_of_isEllipticFieldOn hEll q]
  have h :=
    sigmaStarInvCoarse_le_averaged_symmPart_inv_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hU hEll hHodge hvol compat q
  nlinarith

theorem sigmaStarInvCoarse_le_averagedSymmPartInv_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U) (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    MatLoewnerLE (sigmaStarInvCoarse U a) (averagedSymmPartInv U a) := by
  exact
    sigmaStarInvCoarse_le_averagedSymmPartInv_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
      hvol compat

/--
Note-facing harmonic-mean lower bound
`(average(symmPart(a)^{-1}))^{-1} ≤ σ_*(U; a)`.
-/
theorem harmonicMeanSymmPart_le_sigmaStarCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U) (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    MatLoewnerLE ((averagedSymmPartInv U a)⁻¹) (sigmaStarCoarse U a) := by
  have hSigmaInvPos :
      (sigmaStarInvCoarse U a).PosDef :=
    sigmaStarInvCoarse_posDef_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hU hEll hHodge hvol compat
  have hAvgPos :
      (averagedSymmPartInv U a).PosDef :=
    averagedSymmPartInv_posDef_of_isEllipticFieldOn (U := U) (a := a) hEll hvol
  have hOrder :
      MatLoewnerLE (sigmaStarInvCoarse U a) (averagedSymmPartInv U a) :=
    sigmaStarInvCoarse_le_averagedSymmPartInv_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hU hEll hHodge hvol compat
  simpa [sigmaStarCoarse] using matLoewnerLE_inv_of_posDef hSigmaInvPos hAvgPos hOrder

theorem harmonicMeanSymmPart_le_sigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U) (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    MatLoewnerLE ((averagedSymmPartInv U a)⁻¹) (sigmaStarCoarse U a) := by
  exact
    harmonicMeanSymmPart_le_sigmaStarCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
      hvol compat

end
