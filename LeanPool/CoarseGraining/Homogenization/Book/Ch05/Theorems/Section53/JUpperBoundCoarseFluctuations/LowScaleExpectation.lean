/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.LowScaleTails
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.RHSConversion

/-! # Low Scale Expectation -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open MeasureTheory
open scoped Matrix.Norms.Elementwise

/-!
# Low-scale expectation estimates

This proof-internal file owns the expectation-level conversion of the
low-scale tails in the third Section 5.3 lemma.  The pointwise low-scale split
stays in `LowScaleTails.lean`.
-/

noncomputable section

private theorem lowScaleTailFactor_le_beta_inv_cube {β n : ℝ}
    (hβ_pos : 0 < β) (hβ_le_one : β ≤ 1) (hn_nonneg : 0 ≤ n) :
    (β ^ 2)⁻¹ * Real.rpow (3 : ℝ) (-2 * β * n) ≤ (β ^ 3)⁻¹ := by
  have hexp_nonpos : -2 * β * n ≤ 0 := by nlinarith
  have hdecay_le_one :
      Real.rpow (3 : ℝ) (-2 * β * n) ≤ 1 := by
    calc
      Real.rpow (3 : ℝ) (-2 * β * n)
          ≤ Real.rpow (1 : ℝ) (-2 * β * n) :=
            Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
              (by norm_num : (1 : ℝ) ≤ 3) hexp_nonpos
      _ = 1 := by simp
  have hsq_inv_nonneg : 0 ≤ (β ^ 2)⁻¹ :=
    inv_nonneg.mpr (sq_nonneg β)
  have hsq_inv_le_cube_inv : (β ^ 2)⁻¹ ≤ (β ^ 3)⁻¹ := by
    have hpow_le : β ^ 3 ≤ β ^ 2 := by
      nlinarith [sq_nonneg β, hβ_le_one]
    exact (inv_le_inv₀ (pow_pos hβ_pos 2) (pow_pos hβ_pos 3)).mpr hpow_le
  calc
    (β ^ 2)⁻¹ * Real.rpow (3 : ℝ) (-2 * β * n)
        ≤ (β ^ 2)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hdecay_le_one hsq_inv_nonneg
    _ ≤ (β ^ 3)⁻¹ := by simpa using hsq_inv_le_cube_inv

/-- Raw expectation-level low-scale reduction: the paired low-scale tails are
bounded by the parent-response baseline plus the shifted positive-excess terms
with the child-response average. -/
theorem integral_paired_lowScaleTailSquares_special_le_rawLowScaleTerms
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Vec d) :
    let β := section53CoarseFluctuationBeta hP4
    let s := hP4.sLower + 2 * β
    let s' := hP4.sLower + β
    let t := hP4.sUpper + 2 * β
    let t' := hP4.sUpper + β
    let Q : TriadicCube d := originCube d (m : ℤ)
    let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let σ := sigmaHatAtScale hP hStruct (m : ℤ)
    let childAvg : RegCoeffField d → ℝ :=
      fun a => descendantsAverage Q j
        (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
    let lowerExcess : RegCoeffField d → ℝ :=
      fun a =>
        max
          ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
            (hP.barSigmaStarAtScale hStruct 0)⁻¹)
          0
    let upperExcess : RegCoeffField d → ℝ :=
      fun a =>
        max
          (Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
            hP.barSigmaAtScale hStruct 0)
          0
    let tailFactor :=
      (β ^ 2)⁻¹ *
        Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
    Integrable
        (fun a : RegCoeffField d =>
          σ *
              (WeakNormsMaximizer.gradientLowScaleTailAtScale
                (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
            σ⁻¹ *
              (WeakNormsMaximizer.fluxLowScaleTailAtScale
                (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) P ∧
      ∫ a,
          (σ *
              (WeakNormsMaximizer.gradientLowScaleTailAtScale
                (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
            σ⁻¹ *
              (WeakNormsMaximizer.fluxLowScaleTailAtScale
                (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P
        ≤
          tailFactor *
            (coarseFluctuationScalarWeightAtScale hP hStruct m *
                Ch04.expectedResponseJCubeSet P Q p_e q_e +
              (σ * (∫ a, lowerExcess a * childAvg a ∂P) +
                σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P))) := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let Jm : RegCoeffField d → ℝ :=
    fun a => Ch04.restrictionResponseJObservableCubeSet Q p_e q_e a
  let childAvg : RegCoeffField d → ℝ :=
    fun a => descendantsAverage Q j
      (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
  let lowerExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct 0)⁻¹)
        0
  let upperExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        (Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct 0)
        0
  let tailFactor :=
    (β ^ 2)⁻¹ *
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
  let X : RegCoeffField d → ℝ :=
    fun a =>
      σ *
          (WeakNormsMaximizer.gradientLowScaleTailAtScale
            (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
        σ⁻¹ *
          (WeakNormsMaximizer.fluxLowScaleTailAtScale
            (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
  let Y : RegCoeffField d → ℝ :=
    fun a =>
      tailFactor *
        (coarseFluctuationScalarWeightAtScale hP hStruct m * Jm a +
          (σ * lowerExcess a + σ⁻¹ * upperExcess a) * childAvg a)
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have htail_nonneg : 0 ≤ tailFactor := by
    dsimp [tailFactor]
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hJInt : Integrable Jm P := by
    have hBlock :
        Integrable (Ch04.coarseFullBlockMatrixAtCube Q) P := by
      simpa [Q] using
        Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
    simpa [Jm] using!
      hP.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
        Q p_e q_e hBlock
  have hs'_pos : 0 < s' := by
    dsimp [s', β]
    linarith [hP4.sLower_pos, hβ_pos]
  have ht'_pos : 0 < t' := by
    dsimp [t', β]
    linarith [hP4.sUpper_pos, hβ_pos]
  have hLowerAE :
      AEMeasurable (fun a : RegCoeffField d =>
        (Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹) P :=
    hP.aemeasurable_lambdaSqCoeffField_finite_one_inv Q hs'_pos
  have hUpperAE :
      AEMeasurable (fun a : RegCoeffField d =>
        Ch04.LambdaSqCoeffField Q t' (.finite 1) a) P :=
    hP.aemeasurable_LambdaSqCoeffField_finite_one Q ht'_pos
  have hJAE : AEMeasurable Jm P := by
    simpa [Jm] using! hP.aemeasurable_restrictionResponseJObservableCubeSet Q p_e q_e
  have hGradAE :
      AEMeasurable
        (fun a : RegCoeffField d =>
          WeakNormsMaximizer.gradientLowScaleTailAtScale
            (m : ℤ) (k : ℤ) s s' p_e q_e a) P := by
    simpa [WeakNormsMaximizer.gradientLowScaleTailAtScale, Q, s, s', Jm] using!
      (((aemeasurable_const.mul aemeasurable_const).mul hLowerAE.sqrt).mul
        hJAE.sqrt)
  have hFluxAE :
      AEMeasurable
        (fun a : RegCoeffField d =>
          WeakNormsMaximizer.fluxLowScaleTailAtScale
            (m : ℤ) (k : ℤ) t t' p_e q_e a) P := by
    simpa [WeakNormsMaximizer.fluxLowScaleTailAtScale, Q, t, t', Jm] using!
      (((aemeasurable_const.mul aemeasurable_const).mul hUpperAE.sqrt).mul
        hJAE.sqrt)
  have hXAEMeas : AEMeasurable X P := by
    simpa [X, pow_two] using!
      (aemeasurable_const.mul (hGradAE.mul hGradAE)).add
        (aemeasurable_const.mul (hFluxAE.mul hFluxAE))
  have hs'_gt : hP4.sLower < s' := by
    dsimp [s', β]
    linarith
  have ht'_gt : hP4.sUpper < t' := by
    dsimp [t', β]
    linarith
  have hs'_lt_one : s' < 1 := by
    have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
    dsimp [s', β]
    nlinarith [hP4.sUpper_pos, hβ_pos]
  have ht'_lt_one : t' < 1 := by
    have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
    dsimp [t', β]
    nlinarith [hP4.sLower_pos, hβ_pos]
  have hLowerExcessAE : AEMeasurable lowerExcess P := by
    simpa [lowerExcess] using
      (hLowerAE.sub aemeasurable_const).max aemeasurable_const
  have hUpperExcessAE : AEMeasurable upperExcess P := by
    simpa [upperExcess] using
      (hUpperAE.sub aemeasurable_const).max aemeasurable_const
  have hLowerExcess_nonneg : ∀ᵐ a ∂P, 0 ≤ lowerExcess a := by
    filter_upwards with a
    exact le_max_right _ _
  have hUpperExcess_nonneg : ∀ᵐ a ∂P, 0 ≤ upperExcess a := by
    filter_upwards with a
    exact le_max_right _ _
  have hLowerPowInt :
      Integrable (fun a : RegCoeffField d => lowerExcess a ^ hP4.xi) P := by
    simpa [lowerExcess, Q, s', β] using
      Section52.lowerPositiveExcessPowIntegrableAtScale_from_P4_twoExponent
        hP hStruct hP4 hs'_gt hs'_lt_one m
  have hUpperPowInt :
      Integrable (fun a : RegCoeffField d => upperExcess a ^ hP4.xi) P := by
    simpa [upperExcess, Q, t', β] using
      Section52.upperPositiveExcessPowIntegrableAtScale_from_P4_twoExponent
        hP hStruct hP4 ht'_gt ht'_lt_one m
  have hLowerMem :
      MemLp lowerExcess (ENNReal.ofReal (hP4.xi : ℝ)) P :=
    memLp_of_integrable_nonneg_nat_pow hP4.xi_pos hLowerExcessAE
      hLowerExcess_nonneg hLowerPowInt
  have hUpperMem :
      MemLp upperExcess (ENNReal.ofReal (hP4.xi : ℝ)) P :=
    memLp_of_integrable_nonneg_nat_pow hP4.xi_pos hUpperExcessAE
      hUpperExcess_nonneg hUpperPowInt
  let ζ := section53CoarseFluctuationZeta hP4
  have hChildMem :
      MemLp childAvg (ENNReal.ofReal ζ) P := by
    have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
    have hkm_int : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm.le
    simpa [childAvg, Q, j, ζ, p_e, q_e] using
      memLp_zeta_descendantsAverage_restrictionResponseJObservableCubeSet_originCube_from_P4_of_stationary
        hP hstat hStruct hP4 hk_nonneg hkm_int p_e q_e
  have hHolderReal : ζ.HolderConjugate (hP4.xi : ℝ) := by
    simpa [ζ] using
      (holderConjugate_xi_section53CoarseFluctuationZeta hP4).symm
  let : ENNReal.HolderTriple (ENNReal.ofReal ζ)
      (ENNReal.ofReal (hP4.xi : ℝ)) 1 := by
    simpa using Real.HolderTriple.ennrealOfReal hHolderReal
  have hLowerChildInt :
      Integrable (fun a : RegCoeffField d => lowerExcess a * childAvg a) P := by
    simpa [mul_comm] using! hChildMem.integrable_mul hLowerMem
  have hUpperChildInt :
      Integrable (fun a : RegCoeffField d => upperExcess a * childAvg a) P := by
    simpa [mul_comm] using! hChildMem.integrable_mul hUpperMem
  have hPosInt :
      Integrable
        (fun a : RegCoeffField d =>
          (σ * lowerExcess a + σ⁻¹ * upperExcess a) * childAvg a) P := by
    have hsum :
        Integrable
          (fun a : RegCoeffField d =>
            σ * (lowerExcess a * childAvg a) +
              σ⁻¹ * (upperExcess a * childAvg a)) P :=
      (hLowerChildInt.const_mul σ).add (hUpperChildInt.const_mul σ⁻¹)
    refine hsum.congr ?_
    filter_upwards with a
    ring
  have hYInt : Integrable Y P := by
    have hInside :
        Integrable
          (fun a : RegCoeffField d =>
            coarseFluctuationScalarWeightAtScale hP hStruct m * Jm a +
              (σ * lowerExcess a + σ⁻¹ * upperExcess a) * childAvg a) P :=
      (hJInt.const_mul (coarseFluctuationScalarWeightAtScale hP hStruct m)).add
        hPosInt
    simpa [Y] using hInside.const_mul tailFactor
  have hParent_le_child : Jm ≤ᵐ[P] childAvg := by
    have hkm_int : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm.le
    simpa [Jm, childAvg, Q, j] using!
      hP.restrictionResponseJObservableCubeSet_le_descendantsAverage_ae
        (n := (k : ℤ)) (m := (m : ℤ)) hkm_int p_e q_e
  have hPointXY : X ≤ᵐ[P] Y := by
    filter_upwards [hParent_le_child] with a hsub
    have hpoint0 :=
      paired_lowScaleTailSquares_special_le_baseline_add_positiveExcess
        hP hStruct hP4 hkm.le e a
    have hpoint0' : X a ≤
        tailFactor *
          (coarseFluctuationScalarWeightAtScale hP hStruct m * Jm a +
            (σ * lowerExcess a + σ⁻¹ * upperExcess a) * Jm a) := by
      simpa [X, tailFactor, lowerExcess, upperExcess, Jm, Q, p_e, q_e,
        σ, s, s', t, t', β] using hpoint0
    have hcoef_nonneg :
        0 ≤ σ * lowerExcess a + σ⁻¹ * upperExcess a := by
      exact add_nonneg
        (mul_nonneg hσ_nonneg (le_max_right _ _))
        (mul_nonneg hσ_inv_nonneg (le_max_right _ _))
    have hpos_le :
        (σ * lowerExcess a + σ⁻¹ * upperExcess a) * Jm a ≤
          (σ * lowerExcess a + σ⁻¹ * upperExcess a) * childAvg a :=
      mul_le_mul_of_nonneg_left hsub hcoef_nonneg
    have hinside_le :
        coarseFluctuationScalarWeightAtScale hP hStruct m * Jm a +
            (σ * lowerExcess a + σ⁻¹ * upperExcess a) * Jm a
          ≤
        coarseFluctuationScalarWeightAtScale hP hStruct m * Jm a +
            (σ * lowerExcess a + σ⁻¹ * upperExcess a) * childAvg a :=
      add_le_add le_rfl hpos_le
    exact hpoint0'.trans (mul_le_mul_of_nonneg_left hinside_le htail_nonneg)
  have hXNonneg : ∀ᵐ a ∂P, 0 ≤ X a := by
    filter_upwards with a
    dsimp [X]
    exact add_nonneg
      (mul_nonneg hσ_nonneg (sq_nonneg _))
      (mul_nonneg hσ_inv_nonneg (sq_nonneg _))
  have hXInt : Integrable X P := by
    refine Integrable.mono' hYInt hXAEMeas.aestronglyMeasurable ?_
    filter_upwards [hPointXY, hXNonneg] with a hle hnonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hIntegralY :
      ∫ a, Y a ∂P =
        tailFactor *
          (coarseFluctuationScalarWeightAtScale hP hStruct m * ∫ a, Jm a ∂P +
            (σ * (∫ a, lowerExcess a * childAvg a ∂P) +
              σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P))) := by
    calc
      ∫ a, Y a ∂P =
          tailFactor *
            ∫ a,
              (coarseFluctuationScalarWeightAtScale hP hStruct m * Jm a +
                (σ * lowerExcess a + σ⁻¹ * upperExcess a) * childAvg a) ∂P := by
            simp [Y, integral_const_mul]
      _ =
          tailFactor *
            (∫ a, coarseFluctuationScalarWeightAtScale hP hStruct m * Jm a ∂P +
              ∫ a, (σ * lowerExcess a + σ⁻¹ * upperExcess a) *
                childAvg a ∂P) := by
            rw [integral_add (hJInt.const_mul _) hPosInt]
      _ =
          tailFactor *
            (coarseFluctuationScalarWeightAtScale hP hStruct m * ∫ a, Jm a ∂P +
              (σ * (∫ a, lowerExcess a * childAvg a ∂P) +
                σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P))) := by
            rw [integral_const_mul]
            congr 1
            have hsplit :
                ∫ a, (σ * lowerExcess a + σ⁻¹ * upperExcess a) * childAvg a ∂P =
                  ∫ a, σ * (lowerExcess a * childAvg a) +
                    σ⁻¹ * (upperExcess a * childAvg a) ∂P := by
                refine integral_congr_ae ?_
                filter_upwards with a
                ring
            rw [hsplit]
            rw [integral_add (hLowerChildInt.const_mul σ)
              (hUpperChildInt.const_mul σ⁻¹)]
            rw [integral_const_mul, integral_const_mul]
  refine ⟨by simpa [X, β, s, s', t, t', p_e, q_e, σ] using hXInt, ?_⟩
  calc
    ∫ a, (σ *
            (WeakNormsMaximizer.gradientLowScaleTailAtScale
              (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
          σ⁻¹ *
            (WeakNormsMaximizer.fluxLowScaleTailAtScale
              (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P
        =
      ∫ a, X a ∂P := by simp [X]
    _ ≤ ∫ a, Y a ∂P :=
      integral_mono_ae hXInt hYInt hPointXY
    _ =
      tailFactor *
        (coarseFluctuationScalarWeightAtScale hP hStruct m *
            Ch04.expectedResponseJCubeSet P Q p_e q_e +
          (σ * (∫ a, lowerExcess a * childAvg a ∂P) +
            σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P))) := by
        simpa [Jm, Ch04.expectedResponseJCubeSet] using hIntegralY

/-- Final low-scale expectation conversion in manuscript form. -/
theorem integral_paired_lowScaleTailSquares_special_le_coarseFluctuationTerms_uniform
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (_hstat : Ch04.RestrictionStationaryLaw P)
      (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ {k m : ℕ}, k < m → ∀ e : Vec d, vecNormSq e = 1 →
        let β := section53CoarseFluctuationBeta hP4
        let s := hP4.sLower + 2 * β
        let s' := hP4.sLower + β
        let t := hP4.sUpper + 2 * β
        let t' := hP4.sUpper + β
        let p_e := specialPAtScale hP hStruct (m : ℤ) e
        let q_e := specialQAtScale hP hStruct (m : ℤ) e
        let σ := sigmaHatAtScale hP hStruct (m : ℤ)
        let θ := thetaAtScale hP hStruct (m : ℤ)
        ∫ a,
            (σ *
                (WeakNormsMaximizer.gradientLowScaleTailAtScale
                  (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
              σ⁻¹ *
                (WeakNormsMaximizer.fluxLowScaleTailAtScale
                  (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P
          ≤
            C *
              ((β ^ 2)⁻¹ *
                  Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) *
                  coarseFluctuationScalarWeightAtScale hP hStruct m * (θ - 1) +
                (hP4.xi : ℝ) * (β ^ 3)⁻¹ *
                  Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
                  coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) := by
  dsimp only
  rcases ellipticityPositiveExcess_childResponseAverage_expectation_le_uniform
      params with ⟨Cpos, hCpos_nonneg, hCpos_all⟩
  let C : ℝ := max 1 Cpos
  refine ⟨C, by dsimp [C]; exact le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro P hP hstat hStruct hP4 hparams k m hkm e he
  subst params
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let childAvg : RegCoeffField d → ℝ :=
    fun a => descendantsAverage Q j
      (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
  let lowerExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct 0)⁻¹)
        0
  let upperExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        (Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct 0)
        0
  let tailFactor :=
    (β ^ 2)⁻¹ *
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
  let lowTerm :=
    (β ^ 2)⁻¹ *
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) *
      coarseFluctuationScalarWeightAtScale hP hStruct m * (θ - 1)
  let posCore :=
    (hP4.xi : ℝ) *
      Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
      coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  let posTerm := (β ^ 3)⁻¹ * posCore
  have hCpos := hCpos_all hP hstat hStruct hP4 rfl hkm e
  have hC_ge_one : 1 ≤ C := le_max_left _ _
  have hC_ge_pos : Cpos ≤ C := le_max_right _ _
  have hraw :=
    integral_paired_lowScaleTailSquares_special_le_rawLowScaleTerms
      hP hstat hStruct hP4 hkm e
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hβ_le_one : β ≤ 1 := by
    have hle := sLower_add_beta_le_one hP4
    dsimp [β] at hle ⊢
    linarith [hP4.sLower_pos]
  have htail_nonneg : 0 ≤ tailFactor := by
    dsimp [tailFactor]
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have htail_le_beta_inv_cube :
      tailFactor ≤ (β ^ 3)⁻¹ := by
    simpa [tailFactor] using
      lowScaleTailFactor_le_beta_inv_cube hβ_pos hβ_le_one
        (show 0 ≤ (((m - k : ℕ) : ℝ)) by positivity)
  have hθ_one : 1 ≤ θ := by
    simpa [θ] using one_le_thetaAtScale_of_P4 hP hStruct hP4 m
  have hθ_sub_nonneg : 0 ≤ θ - 1 := by linarith
  have hscalar_nonneg :
      0 ≤ coarseFluctuationScalarWeightAtScale hP hStruct m :=
    coarseFluctuationScalarWeightAtScale_nonneg hP hStruct hP4 m
  have hunit_nonneg :
      0 ≤ coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m :=
    coarseFluctuationUnitMomentWeightAtScale_nonneg hP hStruct hP4 m
  have hresponse_nonneg :
      0 ≤ coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e :=
    coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4 k m e
  have hposCore_nonneg : 0 ≤ posCore := by
    dsimp [posCore]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by exact_mod_cast Nat.zero_le hP4.xi)
          (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
        hunit_nonneg)
      hresponse_nonneg
  have hposTerm_nonneg : 0 ≤ posTerm := by
    dsimp [posTerm]
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hβ_pos.le 3)) hposCore_nonneg
  have hlowTerm_nonneg : 0 ≤ lowTerm := by
    dsimp [lowTerm]
    exact mul_nonneg (mul_nonneg htail_nonneg hscalar_nonneg) hθ_sub_nonneg
  have hJ_le :
      Ch04.expectedResponseJCubeSet P Q p_e q_e ≤ θ - 1 := by
    simpa [Q, p_e, q_e, θ] using
      expectedResponseJCubeSet_special_le_thetaAtScale_sub_one_of_vecNormSq_eq_one
        hP hStruct hP4 m e he
  have hbaseline_le :
      tailFactor *
          (coarseFluctuationScalarWeightAtScale hP hStruct m *
            Ch04.expectedResponseJCubeSet P Q p_e q_e)
        ≤ C * lowTerm := by
    calc
      tailFactor *
          (coarseFluctuationScalarWeightAtScale hP hStruct m *
            Ch04.expectedResponseJCubeSet P Q p_e q_e)
          ≤
        tailFactor *
          (coarseFluctuationScalarWeightAtScale hP hStruct m * (θ - 1)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hJ_le hscalar_nonneg) htail_nonneg
      _ = 1 * lowTerm := by simp [lowTerm, tailFactor, mul_assoc]
      _ ≤ C * lowTerm :=
          mul_le_mul_of_nonneg_right hC_ge_one hlowTerm_nonneg
  have hpositive_child_le :
      σ * (∫ a, lowerExcess a * childAvg a ∂P) +
          σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P)
        ≤ Cpos * posCore := by
    calc
      σ * (∫ a, lowerExcess a * childAvg a ∂P) +
          σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P)
          ≤
        Cpos * (hP4.xi : ℝ) *
          Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
          coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
            coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
          simpa [β, s', t', Q, j, p_e, q_e, σ, childAvg, lowerExcess,
            upperExcess] using hCpos
      _ = Cpos * posCore := by
          simp [posCore]
          ring
  have hpositive_le :
      tailFactor *
          (σ * (∫ a, lowerExcess a * childAvg a ∂P) +
            σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P))
        ≤ C * posTerm := by
    calc
      tailFactor *
          (σ * (∫ a, lowerExcess a * childAvg a ∂P) +
            σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P))
          ≤ tailFactor * (Cpos * posCore) :=
            mul_le_mul_of_nonneg_left hpositive_child_le htail_nonneg
      _ = Cpos * (tailFactor * posCore) := by ring
      _ ≤ Cpos * ((β ^ 3)⁻¹ * posCore) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right htail_le_beta_inv_cube hposCore_nonneg)
            hCpos_nonneg
      _ ≤ C * ((β ^ 3)⁻¹ * posCore) :=
          mul_le_mul_of_nonneg_right hC_ge_pos hposTerm_nonneg
      _ = C * posTerm := by simp [posTerm]
  have hmain :
      ∫ a,
          (σ *
              (WeakNormsMaximizer.gradientLowScaleTailAtScale
                (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
            σ⁻¹ *
              (WeakNormsMaximizer.fluxLowScaleTailAtScale
                (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P
        ≤ C * (lowTerm + posTerm) := by
    calc
      ∫ a,
          (σ *
              (WeakNormsMaximizer.gradientLowScaleTailAtScale
                (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
            σ⁻¹ *
              (WeakNormsMaximizer.fluxLowScaleTailAtScale
                (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P
          ≤
        tailFactor *
          (coarseFluctuationScalarWeightAtScale hP hStruct m *
              Ch04.expectedResponseJCubeSet P Q p_e q_e +
            (σ * (∫ a, lowerExcess a * childAvg a ∂P) +
              σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P))) := by
          simpa [β, s, s', t, t', Q, j, p_e, q_e, σ, childAvg,
            lowerExcess, upperExcess, tailFactor] using hraw.2
      _ =
        tailFactor *
          (coarseFluctuationScalarWeightAtScale hP hStruct m *
            Ch04.expectedResponseJCubeSet P Q p_e q_e) +
        tailFactor *
          (σ * (∫ a, lowerExcess a * childAvg a ∂P) +
            σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P)) := by ring
      _ ≤ C * lowTerm + C * posTerm :=
        add_le_add hbaseline_le hpositive_le
      _ = C * (lowTerm + posTerm) := by ring
  calc
    ∫ a,
        (σ *
            (WeakNormsMaximizer.gradientLowScaleTailAtScale
              (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
          σ⁻¹ *
            (WeakNormsMaximizer.fluxLowScaleTailAtScale
              (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P
        ≤ C * (lowTerm + posTerm) := hmain
    _ =
        C *
          ((β ^ 2)⁻¹ *
              Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) *
              coarseFluctuationScalarWeightAtScale hP hStruct m * (θ - 1) +
            (hP4.xi : ℝ) * (β ^ 3)⁻¹ *
              Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
              coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
              coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) := by
          dsimp [lowTerm, posTerm, posCore]
          ring

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
