/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.PairedWeakNormSquares

/-! # Weak Norm Square Integrability -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

/-!
# Special-vector weak-norm square integrability

This proof-internal file discharges the finite-RHS side conditions inherited
from the first Section 5.3 lemma, in the special-vector regime used by the
coarse-fluctuation lemma.
-/

noncomputable section

namespace Internal

@[irreducible] noncomputable def specialGradientWeakNormSquare
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (e : Vec d) (a : RegCoeffField d) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  (Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e a.toFun) ^ 2

@[irreducible] noncomputable def specialFluxWeakNormSquare
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (e : Vec d) (a : RegCoeffField d) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  let t := hP4.sUpper + 2 * β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e a.toFun) ^ 2

@[irreducible] noncomputable def specialPairedWeakNormSquare
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (e : Vec d) (a : RegCoeffField d) : ℝ :=
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  σ * specialGradientWeakNormSquare hP hStruct hP4 m e a +
    σ⁻¹ * specialFluxWeakNormSquare hP hStruct hP4 m e a

@[irreducible] noncomputable def specialWeakNormComponentSquareSum
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Vec d) (a : RegCoeffField d) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let K := WeakNormsMaximizer.section53WeakNormMaximizerConst d
  let H : RegCoeffField d → ℝ := fun a =>
    σ *
        (WeakNormsMaximizer.gradientAverageTermAtScale
          (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxAverageTermAtScale
          (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2
  let M : RegCoeffField d → ℝ := fun a =>
    σ *
        (WeakNormsMaximizer.gradientMismatchTermAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxMismatchTermAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
  let L : RegCoeffField d → ℝ := fun a =>
    σ *
        (WeakNormsMaximizer.gradientLowScaleTailAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxLowScaleTailAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
  let T : ℝ :=
    σ *
        (WeakNormsMaximizer.gradientConstantTailAtScale
          (m : ℤ) (k : ℤ) s p0_e) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxConstantTailAtScale
          (m : ℤ) (k : ℤ) t q0_e) ^ 2
  16 * (((H a + K ^ 2 * M a) + K ^ 2 * L a) + K ^ 2 * T)

end Internal

private theorem barSigmaStarAtScale_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 < hP.barSigmaStarAtScale hStruct (m : ℤ) := by
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have hInv : 0 < hP.barSigmaStarInvAtScale hStruct (m : ℤ) := by
    simpa [Ch04.RestrictionLawCarrier.barSigmaStarInvAtScale] using
      Ch04.RestrictionLawCarrier.Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube
        hP
        (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw
          hP hStruct (m : ℤ))
        hBlock
  rw [hP.barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale hStruct (m : ℤ)]
  exact inv_pos.mpr hInv

private theorem barSigmaAtScale_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 < hP.barSigmaAtScale hStruct (m : ℤ) := by
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have htheta :=
    Section52.one_le_thetaAtScale_of_integrable_coarseFullBlockMatrixAtCube
      hP hStruct (m : ℤ) hBlock
  have hstar_pos := barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hprod_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) *
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ := by
    exact lt_of_lt_of_le zero_lt_one (by
      simpa [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale] using htheta)
  exact pos_of_mul_pos_left hprod_pos (inv_pos.mpr hstar_pos).le

private theorem sigmaHatAtScale_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 < sigmaHatAtScale hP hStruct (m : ℤ) := by
  dsimp [sigmaHatAtScale]
  exact Real.sqrt_pos_of_pos
    (mul_pos (barSigmaAtScale_pos_of_P4 hP hStruct hP4 m)
      (barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m))

private theorem sq_sum_four_le_const_sum_sq (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤
      4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

private theorem paired_rhsSquares_le_componentSquares
    {σ K AG MG LG CG AF MF LF CF : ℝ} (hσ : 0 ≤ σ) :
    σ * (AG + K * MG + K * LG + K * CG) ^ 2 +
        σ⁻¹ * (AF + K * MF + K * LF + K * CF) ^ 2
      ≤
    4 *
      ((σ * AG ^ 2 + σ⁻¹ * AF ^ 2) +
        K ^ 2 * (σ * MG ^ 2 + σ⁻¹ * MF ^ 2) +
          K ^ 2 * (σ * LG ^ 2 + σ⁻¹ * LF ^ 2) +
            K ^ 2 * (σ * CG ^ 2 + σ⁻¹ * CF ^ 2)) := by
  have hσinv : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ
  have hg := sq_sum_four_le_const_sum_sq AG (K * MG) (K * LG) (K * CG)
  have hf := sq_sum_four_le_const_sum_sq AF (K * MF) (K * LF) (K * CF)
  calc
    σ * (AG + K * MG + K * LG + K * CG) ^ 2 +
        σ⁻¹ * (AF + K * MF + K * LF + K * CF) ^ 2
        ≤
      σ * (4 * (AG ^ 2 + (K * MG) ^ 2 + (K * LG) ^ 2 + (K * CG) ^ 2)) +
        σ⁻¹ * (4 * (AF ^ 2 + (K * MF) ^ 2 + (K * LF) ^ 2 + (K * CF) ^ 2)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hg hσ)
          (mul_le_mul_of_nonneg_left hf hσinv)
    _ =
      4 *
        ((σ * AG ^ 2 + σ⁻¹ * AF ^ 2) +
          K ^ 2 * (σ * MG ^ 2 + σ⁻¹ * MF ^ 2) +
            K ^ 2 * (σ * LG ^ 2 + σ⁻¹ * LF ^ 2) +
              K ^ 2 * (σ * CG ^ 2 + σ⁻¹ * CF ^ 2)) := by ring

private theorem integrable_specialWeakNormComponentSquareSum
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Vec d) (he : vecNormSq e = 1) :
    Integrable (Internal.specialWeakNormComponentSquareSum hP hStruct hP4 k m e) P := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let K := WeakNormsMaximizer.section53WeakNormMaximizerConst d
  let gradWeak :=
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e
  let fluxWeak :=
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e
  let H : RegCoeffField d → ℝ := fun a =>
    σ *
        (WeakNormsMaximizer.gradientAverageTermAtScale
          (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxAverageTermAtScale
          (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2
  let M : RegCoeffField d → ℝ := fun a =>
    σ *
        (WeakNormsMaximizer.gradientMismatchTermAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxMismatchTermAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
  let L : RegCoeffField d → ℝ := fun a =>
    σ *
        (WeakNormsMaximizer.gradientLowScaleTailAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxLowScaleTailAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
  let T : ℝ :=
    σ *
        (WeakNormsMaximizer.gradientConstantTailAtScale
          (m : ℤ) (k : ℤ) s p0_e) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxConstantTailAtScale
          (m : ℤ) (k : ℤ) t q0_e) ^ 2
  let W := Internal.specialPairedWeakNormSquare hP hStruct hP4 m e
  let Z : RegCoeffField d → ℝ := fun a =>
    16 * (((H a + K ^ 2 * M a) + K ^ 2 * L a) + K ^ 2 * T)
  have hHigh :=
    integral_paired_highScaleAverageTerms_special_le_fullBlockSumAtScale
      hP hstat hStruct hP4 hkm e he
  have hHighInt : Integrable H P := by
    simpa [H, β, s, t, p_e, q_e, p0_e, q0_e, σ] using hHigh.1
  rcases integral_paired_mismatchTermSquares_special_le_coarseFluctuationTerms_uniform
      hP4.params with ⟨_Cmis, _hCmis_nonneg, hMis_all⟩
  have hMis := hMis_all hP hstat hStruct hP4 rfl hkm e
  have hMInt : Integrable M P := by
    simpa [M, β, s, s', t, t', p_e, q_e, σ] using hMis.1
  have hLowRaw :=
    integral_paired_lowScaleTailSquares_special_le_rawLowScaleTerms
      hP hstat hStruct hP4 hkm e
  have hLInt : Integrable L P := by
    simpa [L, β, s, s', t, t', p_e, q_e, σ] using hLowRaw.1
  have hinside :
      Integrable (fun a : RegCoeffField d =>
        ((H a + K ^ 2 * M a) + K ^ 2 * L a) + K ^ 2 * T) P :=
    ((hHighInt.add (hMInt.const_mul (K ^ 2))).add
      (hLInt.const_mul (K ^ 2))).add (integrable_const (K ^ 2 * T))
  unfold Internal.specialWeakNormComponentSquareSum
  change
    Integrable
      (fun a : RegCoeffField d =>
        16 * (((H a + K ^ 2 * M a) + K ^ 2 * L a) + K ^ 2 * T)) P
  simpa [mul_assoc] using hinside.const_mul 16

private theorem aemeasurable_specialPairedWeakNormSquares
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {m : ℕ} (e : Vec d) :
    AEMeasurable (Internal.specialPairedWeakNormSquare hP hStruct hP4 m e) P := by
  classical
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let t := hP4.sUpper + 2 * β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let gradWeak :=
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e
  let fluxWeak :=
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e
  have hg :=
    hP.aemeasurable_canonicalScalarResponseGradientWeakNorm_cubeSet Q s p_e q_e p0_e
  have hf :=
    hP.aemeasurable_canonicalScalarResponseFluxWeakNorm_cubeSet Q t p_e q_e q0_e
  unfold Internal.specialPairedWeakNormSquare
  unfold Internal.specialGradientWeakNormSquare
  unfold Internal.specialFluxWeakNormSquare
  simpa [gradWeak, fluxWeak, β, s, t, Q, p_e, q_e, p0_e, q0_e, σ, pow_two] using!
    ((hg.mul hg).const_mul σ).add
      ((hf.mul hf).const_mul σ⁻¹)

private theorem ae_nonneg_specialPairedWeakNormSquares
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {m : ℕ} (e : Vec d) :
    0 ≤ᵐ[P] Internal.specialPairedWeakNormSquare hP hStruct hP4 m e := by
  classical
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let t := hP4.sUpper + 2 * β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let gradWeak :=
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e
  let fluxWeak :=
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e
  have hσ_nonneg : 0 ≤ σ := Real.sqrt_nonneg _
  have hs_pos : 0 < s := by
    dsimp [s, β]
    linarith [hP4.sLower_pos, section53CoarseFluctuationBeta_pos hP4]
  have ht_pos : 0 < t := by
    dsimp [t, β]
    linarith [hP4.sUpper_pos, section53CoarseFluctuationBeta_pos hP4]
  filter_upwards
    [JUpperBoundWeakNorms.canonicalScalarResponseGradientWeakNormCubeSet_nonneg_ae
      hP Q hs_pos p_e q_e p0_e,
     JUpperBoundWeakNorms.canonicalScalarResponseFluxWeakNormCubeSet_nonneg_ae
      hP Q ht_pos p_e q_e q0_e] with a hg hf
  unfold Internal.specialPairedWeakNormSquare
  unfold Internal.specialGradientWeakNormSquare
  unfold Internal.specialFluxWeakNormSquare
  simpa [gradWeak, fluxWeak, β, s, t, Q, p_e, q_e, p0_e, q0_e, σ] using
    add_nonneg
      (mul_nonneg hσ_nonneg (sq_nonneg _))
      (mul_nonneg (inv_nonneg.mpr hσ_nonneg) (sq_nonneg _))

private theorem ae_specialPairedWeakNormSquares_le_componentSquareSum
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Vec d) :
    Internal.specialPairedWeakNormSquare hP hStruct hP4 m e
      ≤ᵐ[P] Internal.specialWeakNormComponentSquareSum hP hStruct hP4 k m e := by
  classical
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let K := WeakNormsMaximizer.section53WeakNormMaximizerConst d
  let gradWeak :=
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e
  let fluxWeak :=
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e
  let H : RegCoeffField d → ℝ := fun a =>
    σ *
        (WeakNormsMaximizer.gradientAverageTermAtScale
          (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxAverageTermAtScale
          (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2
  let M : RegCoeffField d → ℝ := fun a =>
    σ *
        (WeakNormsMaximizer.gradientMismatchTermAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxMismatchTermAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
  let L : RegCoeffField d → ℝ := fun a =>
    σ *
        (WeakNormsMaximizer.gradientLowScaleTailAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxLowScaleTailAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
  let T : ℝ :=
    σ *
        (WeakNormsMaximizer.gradientConstantTailAtScale
          (m : ℤ) (k : ℤ) s p0_e) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxConstantTailAtScale
          (m : ℤ) (k : ℤ) t q0_e) ^ 2
  have hσ_nonneg : 0 ≤ σ := Real.sqrt_nonneg _
  filter_upwards [ae_paired_weakNormSquares_special_le_four_rhsSquares
      hP hStruct hP4 hkm e] with a hweak
  have hAlg :=
    paired_rhsSquares_le_componentSquares
      (σ := σ) (K := K)
      (AG := WeakNormsMaximizer.gradientAverageTermAtScale
        (m : ℤ) (k : ℤ) s p_e q_e p0_e a)
      (MG := WeakNormsMaximizer.gradientMismatchTermAtScale
        (m : ℤ) (k : ℤ) s s' p_e q_e a)
      (LG := WeakNormsMaximizer.gradientLowScaleTailAtScale
        (m : ℤ) (k : ℤ) s s' p_e q_e a)
      (CG := WeakNormsMaximizer.gradientConstantTailAtScale
        (m : ℤ) (k : ℤ) s p0_e)
      (AF := WeakNormsMaximizer.fluxAverageTermAtScale
        (m : ℤ) (k : ℤ) t p_e q_e q0_e a)
      (MF := WeakNormsMaximizer.fluxMismatchTermAtScale
        (m : ℤ) (k : ℤ) t t' p_e q_e a)
      (LF := WeakNormsMaximizer.fluxLowScaleTailAtScale
        (m : ℤ) (k : ℤ) t t' p_e q_e a)
      (CF := WeakNormsMaximizer.fluxConstantTailAtScale
        (m : ℤ) (k : ℤ) t q0_e) hσ_nonneg
  calc
    Internal.specialPairedWeakNormSquare hP hStruct hP4 m e a ≤
        4 *
          (σ *
              (WeakNormsMaximizer.gradientRHSAtScale K
                (m : ℤ) (k : ℤ) s s' p_e q_e p0_e a) ^ 2 +
            σ⁻¹ *
              (WeakNormsMaximizer.fluxRHSAtScale K
                (m : ℤ) (k : ℤ) t t' p_e q_e q0_e a) ^ 2) := by
        simpa [Internal.specialPairedWeakNormSquare, Internal.specialGradientWeakNormSquare,
          Internal.specialFluxWeakNormSquare, gradWeak, fluxWeak, K, Q, β, s, s', t,
          t',
          p_e, q_e, p0_e, q0_e, σ] using hweak
    _ ≤ Internal.specialWeakNormComponentSquareSum hP hStruct hP4 k m e a := by
        have hAlg' :
            4 *
              (σ *
                  (WeakNormsMaximizer.gradientRHSAtScale K
                    (m : ℤ) (k : ℤ) s s' p_e q_e p0_e a) ^ 2 +
                σ⁻¹ *
                  (WeakNormsMaximizer.fluxRHSAtScale K
                    (m : ℤ) (k : ℤ) t t' p_e q_e q0_e a) ^ 2)
              ≤ 16 * (((H a + K ^ 2 * M a) + K ^ 2 * L a) + K ^ 2 * T) := by
          dsimp [H, M, L, T, WeakNormsMaximizer.gradientRHSAtScale,
            WeakNormsMaximizer.fluxRHSAtScale]
          nlinarith [hAlg]
        unfold Internal.specialWeakNormComponentSquareSum
        change
          4 *
            (σ *
                (WeakNormsMaximizer.gradientRHSAtScale K
                  (m : ℤ) (k : ℤ) s s' p_e q_e p0_e a) ^ 2 +
              σ⁻¹ *
                (WeakNormsMaximizer.fluxRHSAtScale K
                  (m : ℤ) (k : ℤ) t t' p_e q_e q0_e a) ^ 2)
            ≤ 16 * (((H a + K ^ 2 * M a) + K ^ 2 * L a) + K ^ 2 * T)
        exact hAlg'

/-- The paired special-vector weak-norm square is integrable.  This is the
non-circular version: the left side is integrated by domination from the
second Section 5.3 weak-norm maximizer estimate and the already proved
component-square integrability facts. -/
theorem integrable_paired_specialWeakNormSquares_from_weakNormMaximizer
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Vec d) (he : vecNormSq e = 1) :
    Integrable (Internal.specialPairedWeakNormSquare hP hStruct hP4 m e) P := by
  classical
  let W := Internal.specialPairedWeakNormSquare hP hStruct hP4 m e
  let Z := Internal.specialWeakNormComponentSquareSum hP hStruct hP4 k m e
  have hZInt : Integrable Z P := by
    simpa [Z] using
      integrable_specialWeakNormComponentSquareSum hP hstat hStruct hP4 hkm e he
  have hWAE : AEMeasurable W P := by
    simpa [W] using
      aemeasurable_specialPairedWeakNormSquares hP hStruct hP4 e
  have hW_nonneg : 0 ≤ᵐ[P] W := by
    simpa [W] using
      ae_nonneg_specialPairedWeakNormSquares hP hStruct hP4 e
  have hPoint : W ≤ᵐ[P] Z := by
    simpa [W, Z] using
      ae_specialPairedWeakNormSquares_le_componentSquareSum
        hP hStruct hP4 hkm e
  refine Integrable.mono' hZInt hWAE.aestronglyMeasurable ?_
  filter_upwards [hPoint, hW_nonneg] with a hle hnonneg
  change ‖W a‖ ≤ Z a
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hle

/-- Special-vector gradient weak-norm square integrability from the second
Section 5.3 weak-norm maximizer lemma. -/
theorem integrable_specialGradientWeakNormSquare_from_weakNormMaximizer
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Vec d) (he : vecNormSq e = 1) :
    Integrable (Internal.specialGradientWeakNormSquare hP hStruct hP4 m e) P := by
  classical
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let t := hP4.sUpper + 2 * β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let gradWeak :=
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e
  let fluxWeak :=
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e
  let W := Internal.specialPairedWeakNormSquare hP hStruct hP4 m e
  have hσ_pos := sigmaHatAtScale_pos_of_P4 hP hStruct hP4 m
  have hσ_ne : σ ≠ 0 := by
    simpa [σ] using hσ_pos.ne'
  have hσ_inv_pos : 0 < σ⁻¹ := inv_pos.mpr hσ_pos
  have hWInt :
      Integrable W P := by
    simpa [W] using
      integrable_paired_specialWeakNormSquares_from_weakNormMaximizer
        hP hstat hStruct hP4 hkm e he
  have hAE :
      AEMeasurable (Internal.specialGradientWeakNormSquare hP hStruct hP4 m e) P := by
    have hg :=
      hP.aemeasurable_canonicalScalarResponseGradientWeakNorm_cubeSet Q s p_e q_e p0_e
    unfold Internal.specialGradientWeakNormSquare
    simpa [β, s, Q, p_e, q_e, p0_e, gradWeak, pow_two] using! hg.mul hg
  refine Integrable.mono' (hWInt.const_mul σ⁻¹) hAE.aestronglyMeasurable ?_
  filter_upwards with a
  have hle :
      Internal.specialGradientWeakNormSquare hP hStruct hP4 m e a ≤ σ⁻¹ * W a := by
    have hflux_nonneg : 0 ≤ σ⁻¹ * (fluxWeak a) ^ 2 :=
      mul_nonneg hσ_inv_pos.le (sq_nonneg _)
    calc
      Internal.specialGradientWeakNormSquare hP hStruct hP4 m e a =
          (gradWeak a) ^ 2 := by
          unfold Internal.specialGradientWeakNormSquare
          simp [β, s, Q, p_e, q_e, p0_e, gradWeak]
      _ = σ⁻¹ * (σ * (gradWeak a) ^ 2) := by
          calc
            (gradWeak a) ^ 2 = (σ⁻¹ * σ) * (gradWeak a) ^ 2 := by
              rw [inv_mul_cancel₀ hσ_ne, one_mul]
            _ = σ⁻¹ * (σ * (gradWeak a) ^ 2) := by ring
      _ ≤ σ⁻¹ * (σ * (gradWeak a) ^ 2 + σ⁻¹ * (fluxWeak a) ^ 2) := by
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hflux_nonneg)
            hσ_inv_pos.le
      _ = σ⁻¹ * W a := by
          have hW_eval :
              W a = σ * (gradWeak a) ^ 2 + σ⁻¹ * (fluxWeak a) ^ 2 := by
            simp [W, Internal.specialPairedWeakNormSquare,
              Internal.specialGradientWeakNormSquare, Internal.specialFluxWeakNormSquare,
              β, s, t, Q, p_e, q_e, p0_e, q0_e, σ, gradWeak, fluxWeak]
          rw [hW_eval]
  have hleft_nonneg :
      0 ≤ Internal.specialGradientWeakNormSquare hP hStruct hP4 m e a := by
    unfold Internal.specialGradientWeakNormSquare
    simpa [β, s, Q, p_e, q_e, p0_e, gradWeak] using sq_nonneg (gradWeak a)
  have hright_nonneg : 0 ≤ σ⁻¹ * W a := hleft_nonneg.trans hle
  simpa [Real.norm_eq_abs, abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using hle

/-- Special-vector flux weak-norm square integrability from the second
Section 5.3 weak-norm maximizer lemma. -/
theorem integrable_specialFluxWeakNormSquare_from_weakNormMaximizer
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Vec d) (he : vecNormSq e = 1) :
    Integrable (Internal.specialFluxWeakNormSquare hP hStruct hP4 m e) P := by
  classical
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let t := hP4.sUpper + 2 * β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let gradWeak :=
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e
  let fluxWeak :=
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e
  let W := Internal.specialPairedWeakNormSquare hP hStruct hP4 m e
  have hσ_pos := sigmaHatAtScale_pos_of_P4 hP hStruct hP4 m
  have hσ_ne : σ ≠ 0 := by
    simpa [σ] using hσ_pos.ne'
  have hWInt :
      Integrable W P := by
    simpa [W] using
      integrable_paired_specialWeakNormSquares_from_weakNormMaximizer
        hP hstat hStruct hP4 hkm e he
  have hAE :
      AEMeasurable (Internal.specialFluxWeakNormSquare hP hStruct hP4 m e) P := by
    have hf :=
      hP.aemeasurable_canonicalScalarResponseFluxWeakNorm_cubeSet Q t p_e q_e q0_e
    unfold Internal.specialFluxWeakNormSquare
    simpa [β, t, Q, p_e, q_e, q0_e, fluxWeak, pow_two] using! hf.mul hf
  refine Integrable.mono' (hWInt.const_mul σ) hAE.aestronglyMeasurable ?_
  filter_upwards with a
  have hgrad_nonneg : 0 ≤ σ * (gradWeak a) ^ 2 :=
    mul_nonneg hσ_pos.le (sq_nonneg _)
  have hle :
      Internal.specialFluxWeakNormSquare hP hStruct hP4 m e a ≤ σ * W a := by
    calc
      Internal.specialFluxWeakNormSquare hP hStruct hP4 m e a =
          (fluxWeak a) ^ 2 := by
          unfold Internal.specialFluxWeakNormSquare
          simp [β, t, Q, p_e, q_e, q0_e, fluxWeak]
      _ = σ * (σ⁻¹ * (fluxWeak a) ^ 2) := by
          calc
            (fluxWeak a) ^ 2 = (σ * σ⁻¹) * (fluxWeak a) ^ 2 := by
              rw [mul_inv_cancel₀ hσ_ne, one_mul]
            _ = σ * (σ⁻¹ * (fluxWeak a) ^ 2) := by ring
      _ ≤ σ * (σ * (gradWeak a) ^ 2 + σ⁻¹ * (fluxWeak a) ^ 2) := by
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hgrad_nonneg)
            hσ_pos.le
      _ = σ * W a := by
          have hW_eval :
              W a = σ * (gradWeak a) ^ 2 + σ⁻¹ * (fluxWeak a) ^ 2 := by
            simp [W, Internal.specialPairedWeakNormSquare,
              Internal.specialGradientWeakNormSquare, Internal.specialFluxWeakNormSquare,
              β, s, t, Q, p_e, q_e, p0_e, q0_e, σ, gradWeak, fluxWeak]
          rw [hW_eval]
  have hleft_nonneg :
      0 ≤ Internal.specialFluxWeakNormSquare hP hStruct hP4 m e a := by
    unfold Internal.specialFluxWeakNormSquare
    simpa [β, t, Q, p_e, q_e, q0_e, fluxWeak] using sq_nonneg (fluxWeak a)
  have hright_nonneg : 0 ≤ σ * W a := hleft_nonneg.trans hle
  simpa [Real.norm_eq_abs, abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using hle

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
