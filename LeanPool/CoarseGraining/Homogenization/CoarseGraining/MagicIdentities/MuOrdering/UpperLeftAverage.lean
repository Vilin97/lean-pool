/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.HilbertOperator

/-! # Upper Left Average -/

namespace Homogenization

noncomputable section

/-!
# Upper-left averaged matrix bounds

This file upgrades the scalar quadratic upper-left estimate
`b(U; a) ≤ average(symmPart(a) + k(a)ᵀ symmPart(a)⁻¹ k(a))`
to an honest matrix-order theorem.
-/

/-- Entrywise volume-average of the pointwise upper-left block coefficient. -/
noncomputable def averagedSymmPartPlusCorrection {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) : Mat d :=
  volumeAverageMat U (fun x =>
    symmPart (a x) +
      matTranspose (skewPart (a x)) * (symmPart (a x))⁻¹ * skewPart (a x))

private theorem abs_blockMatrixOfCoeff_upperLeft_entry_le_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) {x : Vec d} (hx : x ∈ U) (i j : Fin d) :
    |((blockMatrixOfCoeff (a x)).upperLeft i j)| ≤
      Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam) := by
  let B : BlockMat d := blockMatrixOfCoeff (a x)
  let α : BlockCoord d := Sum.inl i
  let β : BlockCoord d := Sum.inl j
  let eα : BlockVec d := blockBasis α
  let eβ : BlockVec d := blockBasis β
  have hentry :
      blockVecDot eα (blockMatVecMul B eβ) =
        ((blockMatrixOfCoeff (a x)).upperLeft i j) := by
    simpa [B, α, β, eα, eβ, blockMatEntry] using blockBasis_pairing B α β
  have hsingle_i : vecNormSq (Pi.single i 1 : Vec d) = 1 := by
    rw [vecNormSq, vecDot, Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      simp [Pi.single_eq_of_ne hki]
    · simp
  have hsingle_j : vecNormSq (Pi.single j 1 : Vec d) = 1 := by
    rw [vecNormSq, vecDot, Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [Pi.single_eq_of_ne hkj]
    · simp
  have hbasisα : blockVecDot eα eα = 1 := by
    change vecNormSq (Pi.single i 1 : Vec d) + vecNormSq (0 : Vec d) = 1
    rw [hsingle_i]
    simp [vecNormSq, vecDot]
  have hbasisβ : blockVecDot eβ eβ = 1 := by
    change vecNormSq (Pi.single j 1 : Vec d) + vecNormSq (0 : Vec d) = 1
    rw [hsingle_j]
    simp [vecNormSq, vecDot]
  have hsq :
      (((blockMatrixOfCoeff (a x)).upperLeft i j)) ^ 2 ≤
        blockVecDot eα eα * blockVecDot (blockMatVecMul B eβ) (blockMatVecMul B eβ) := by
    calc
      (((blockMatrixOfCoeff (a x)).upperLeft i j)) ^ 2
          = (blockVecDot eα (blockMatVecMul B eβ)) ^ 2 := by rw [hentry]
      _ ≤ blockVecDot eα eα * blockVecDot (blockMatVecMul B eβ) (blockMatVecMul B eβ) :=
        sq_blockVecDot_le_blockVecDot_mul_blockVecDot eα (blockMatVecMul B eβ)
  have himage :
      blockVecDot (blockMatVecMul B eβ) (blockMatVecMul B eβ) ≤
        blockMatrixOfCoeffNormSqBound lam Lam := by
    have h :=
      blockMatrixOfCoeff_image_bound_of_isEllipticMatrix (hEll.2 x hx) eβ
    simpa [B, hbasisβ] using h
  have hsq' :
      (((blockMatrixOfCoeff (a x)).upperLeft i j)) ^ 2 ≤
        blockMatrixOfCoeffNormSqBound lam Lam := by
    rw [hbasisα] at hsq
    nlinarith
  have hbound_nonneg : 0 ≤ blockMatrixOfCoeffNormSqBound lam Lam :=
    blockMatrixOfCoeffNormSqBound_nonneg lam Lam
  have habs_sq :
      |((blockMatrixOfCoeff (a x)).upperLeft i j)| ^ 2 ≤
        blockMatrixOfCoeffNormSqBound lam Lam := by
    simpa [sq_abs] using hsq'
  have hsqrt_nonneg : 0 ≤ Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam) := by
    exact Real.sqrt_nonneg _
  have habs_nonneg : 0 ≤ |((blockMatrixOfCoeff (a x)).upperLeft i j)| := by
    exact abs_nonneg _
  nlinarith [habs_sq, Real.sq_sqrt hbound_nonneg,
    hsqrt_nonneg, habs_nonneg,
    sq_nonneg (Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam) -
      |((blockMatrixOfCoeff (a x)).upperLeft i j)|)]

private theorem integrableOn_blockMatrixOfCoeff_upperLeft_entry_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (i j : Fin d) :
    MeasureTheory.IntegrableOn (fun x => ((blockMatrixOfCoeff (a x)).upperLeft i j)) U := by
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
  let coeffExt : Vec d → ℝ := fun x => ((blockMatrixOfCoeff (aExt x)).upperLeft i j)
  have hcoeffExt : Measurable coeffExt := by
    have hblock :
        Measurable (fun x α β =>
          toFullBlockMat (blockMatrixOfCoeff (aExt x)) α β) :=
      measurable_toFullBlockMat_blockCoeffField haExt
    simpa [coeffExt] using!
      (measurable_pi_iff.1 (measurable_pi_iff.1 hblock (Sum.inl i)) (Sum.inl j))
  have hfinite : MeasureTheory.volume U ≠ ⊤ := by
    simpa [volumeMeasureOn] using
      (MeasureTheory.measure_lt_top (volumeMeasureOn U) Set.univ).ne
  have hIntExt : MeasureTheory.IntegrableOn coeffExt U := by
    refine
      MeasureTheory.Measure.integrableOn_of_bounded
        (μ := MeasureTheory.volume)
        (M := Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam))
        hfinite hcoeffExt.aestronglyMeasurable ?_
    have hmem : ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
      exact
        (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
          (Filter.Eventually.of_forall fun x hx => hx)
    filter_upwards [hmem] with x hx
    have hbound :
        |((blockMatrixOfCoeff (a x)).upperLeft i j)| ≤
          Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam) :=
      abs_blockMatrixOfCoeff_upperLeft_entry_le_of_isEllipticFieldOn hEll hx i j
    simpa [coeffExt, aExt, hx, Real.norm_eq_abs] using hbound
  refine hIntExt.congr_fun ?_ (measurableSet_of_isEllipticFieldOn hEll)
  intro x hx
  simp [coeffExt, aExt, hx]

private theorem integrableOn_symmPartPlusCorrection_entry_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (i j : Fin d) :
    MeasureTheory.IntegrableOn
      (fun x =>
        (symmPart (a x) +
          matTranspose (skewPart (a x)) * (symmPart (a x))⁻¹ * skewPart (a x)) i j) U := by
  refine
    (integrableOn_blockMatrixOfCoeff_upperLeft_entry_of_isEllipticFieldOn hEll i j).congr_fun
      ?_ (measurableSet_of_isEllipticFieldOn hEll)
  intro x hx
  simp [blockMatrixOfCoeff]

theorem vecDot_matVecMul_averagedSymmPartPlusCorrection_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (p : Vec d) :
    vecDot p (matVecMul (averagedSymmPartPlusCorrection U a) p) =
      volumeAverage U
        (fun x =>
          vecDot p
            (matVecMul
              (symmPart (a x) +
                matTranspose (skewPart (a x)) * (symmPart (a x))⁻¹ * skewPart (a x)) p)) := by
  exact
    vecDot_matVecMul_volumeAverageMat
      (fun i j => integrableOn_symmPartPlusCorrection_entry_of_isEllipticFieldOn hEll i j)
      p p

/--
Note-facing upper-left matrix-order bound
`b(U; a) ≤ average(symmPart(a) + k(a)ᵀ symmPart(a)⁻¹ k(a))`.
-/
theorem bCoarse_le_averagedSymmPartPlusCorrection_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U) (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) :
    MatLoewnerLE
      (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a))
      (averagedSymmPartPlusCorrection U a) := by
  intro p
  rw [vecDot_matVecMul_averagedSymmPartPlusCorrection_of_isEllipticFieldOn hEll p]
  have h :=
    bCoarse_le_averaged_symmPart_plus_correction_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hU hEll hHodge hvol compat hA hS hK hSigma p
  nlinarith

theorem bCoarse_le_averagedSymmPartPlusCorrection_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U) (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) :
    MatLoewnerLE
      (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a))
      (averagedSymmPartPlusCorrection U a) := by
  exact
    bCoarse_le_averagedSymmPartPlusCorrection_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
      hvol compat hA hS hK hSigma

end
