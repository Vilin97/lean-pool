/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Definitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.P4Integrability
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.PositiveExcessLowerAndIntegrability.UnitDescendantSup
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.BlockResponseConcentration

/-! # Quenched Gamma Ellipticity -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped Matrix.Norms.Elementwise

/-!
# Quenched Γσ coarse-grained ellipticity

This file formalizes the strengthened unit-cube ellipticity assumption from
Section 5.7.  The assumption is intentionally kept separate from `(P4)`: the
manuscript says this Γσ condition implies the moment hypothesis, so later files
must prove that implication rather than assume it.
-/

noncomputable section

/-- The parameter-only part of the strengthened Section 5.7 `(P5)` input.

Unlike the Chapter 5 `(P4)` parameter bundle, this record carries no moment
exponent `xi`: a finite `xi` can be chosen internally from the positivity of
`sUpper` and `sLower` whenever the older moment-based API is needed. -/
structure GammaCoarseGrainedEllipticityParams (d : ℕ) : Type where
  sUpper : ℝ
  sLower : ℝ
  two_le_dim : 2 ≤ d
  sUpper_pos : 0 < sUpper
  sUpper_lt_one : sUpper < 1
  sLower_pos : 0 < sLower
  sLower_lt_one : sLower < 1
  sum_lt_one : sUpper + sLower < 1

namespace GammaCoarseGrainedEllipticityParams

theorem sUpper_nonneg {d : ℕ} (params : GammaCoarseGrainedEllipticityParams d) :
    0 ≤ params.sUpper :=
  params.sUpper_pos.le

theorem sLower_nonneg {d : ℕ} (params : GammaCoarseGrainedEllipticityParams d) :
    0 ≤ params.sLower :=
  params.sLower_pos.le

theorem min_pos {d : ℕ} (params : GammaCoarseGrainedEllipticityParams d) :
    0 < min params.sUpper params.sLower :=
  lt_min params.sUpper_pos params.sLower_pos

/-- Choose an internal finite moment exponent compatible with the older `(P4)`
parameter API. -/
theorem exists_internal_xi {d : ℕ}
    (params : GammaCoarseGrainedEllipticityParams d) :
    ∃ ξ : ℕ,
      (2 * d : ℝ) < (ξ : ℝ) ∧
        (d : ℝ) / (ξ : ℝ) < min params.sUpper params.sLower := by
  let smin : ℝ := min params.sUpper params.sLower
  have hsmin_pos : 0 < smin := by
    simpa [smin] using params.min_pos
  obtain ⟨ξ, hξ⟩ :=
    exists_nat_gt (max (2 * (d : ℝ)) ((d : ℝ) / smin + 1))
  refine ⟨ξ, ?_, ?_⟩
  · exact lt_of_le_of_lt (le_max_left _ _) hξ
  · have hξ_gt_div_plus :
        (d : ℝ) / smin + 1 < (ξ : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hξ
    have hξ_gt_div : (d : ℝ) / smin < (ξ : ℝ) := by
      linarith
    have hξ_pos : 0 < (ξ : ℝ) := by
      have htwo_d_nonneg : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
      have htwo_d_lt : 2 * (d : ℝ) < (ξ : ℝ) :=
        lt_of_le_of_lt (le_max_left _ _) hξ
      linarith
    have hd_lt : (d : ℝ) < (ξ : ℝ) * smin :=
      (div_lt_iff₀ hsmin_pos).mp hξ_gt_div
    have : (d : ℝ) < smin * (ξ : ℝ) := by
      nlinarith
    simpa [smin] using (div_lt_iff₀ hξ_pos).mpr this

/-- Convert the Section 5.7 `(P5)` parameters to the older `(P4)` parameter
bundle by choosing an internal finite moment exponent. -/
noncomputable def toQuantitativeParams {d : ℕ}
    (params : GammaCoarseGrainedEllipticityParams d) :
    QuantitativeCoarseGrainedEllipticityParams d where
  sUpper := params.sUpper
  sLower := params.sLower
  xi := Classical.choose params.exists_internal_xi
  two_le_dim := params.two_le_dim
  sUpper_nonneg := params.sUpper_nonneg
  sUpper_lt_one := params.sUpper_lt_one
  sLower_nonneg := params.sLower_nonneg
  sLower_lt_one := params.sLower_lt_one
  xi_gt_two_mul_dim := (Classical.choose_spec params.exists_internal_xi).1
  sum_lt_one := params.sum_lt_one
  dim_div_xi_lt_min := (Classical.choose_spec params.exists_internal_xi).2

@[simp]
theorem toQuantitativeParams_sUpper {d : ℕ}
    (params : GammaCoarseGrainedEllipticityParams d) :
    params.toQuantitativeParams.sUpper = params.sUpper := rfl

@[simp]
theorem toQuantitativeParams_sLower {d : ℕ}
    (params : GammaCoarseGrainedEllipticityParams d) :
    params.toQuantitativeParams.sLower = params.sLower := rfl

end GammaCoarseGrainedEllipticityParams

/-- The unit-cube Γσ ellipticity observable from
`(a.cg.ellipticity.Gamma.sigma)`.

In the manuscript notation this is
`barσ_0^{-1} Λ_{s_1,1}(□_0) + barσ_0 λ_{s_2,1}^{-1}(□_0)`.
-/
noncomputable def gammaSigmaUnitEllipticityObservable
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (sUpper sLower : ℝ) : RegCoeffField d → ℝ :=
  if 0 < hP.barSigmaAtScale hStruct (0 : ℤ) then
    fun a =>
      (hP.barSigmaAtScale hStruct (0 : ℤ))⁻¹ *
          Ch04.LambdaSqCoeffField (originCube d 0) sUpper (.finite 1) a +
        hP.barSigmaAtScale hStruct (0 : ℤ) *
          (Ch04.lambdaSqCoeffField (originCube d 0) sLower (.finite 1) a)⁻¹
  else
    fun a =>
      Ch04.LambdaSqCoeffField (originCube d 0) sUpper (.finite 1) a +
        (Ch04.lambdaSqCoeffField (originCube d 0) sLower (.finite 1) a)⁻¹

/-- The strengthened quenched ellipticity assumption `(P5)` in Section 5.7.

The constant `thetaHat` is the manuscript's `\hat Θ_0`.  No probability law
appears in the choice of the exponents or constants beyond the tail statement
itself; later estimates should quantify their constants before the law.
-/
structure GammaSigmaCoarseGrainedEllipticity
    {d : ℕ} [NeZero d] (P : Ch04.RestrictionCoeffLaw d)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) : Type where
  sigma : ℝ
  sigma_pos : 0 < sigma
  params : QuantitativeCoarseGrainedEllipticityParams d
  thetaHat : ℝ
  thetaHat_pos : 0 < thetaHat
  tail :
    IsBigO P (gammaSigma sigma)
      (gammaSigmaUnitEllipticityObservable hP hStruct
        params.sUpper params.sLower)
      thetaHat

/-- The manuscript-facing finite-`σ` Section 5.7 `(P5)` input, with no exposed
moment exponent `xi`. -/
structure GammaSigmaCoarseGrainedEllipticityNoXi
    {d : ℕ} [NeZero d] (P : Ch04.RestrictionCoeffLaw d)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) : Type where
  sigma : ℝ
  sigma_pos : 0 < sigma
  params : GammaCoarseGrainedEllipticityParams d
  thetaHat : ℝ
  thetaHat_pos : 0 < thetaHat
  tail :
    IsBigO P (gammaSigma sigma)
      (gammaSigmaUnitEllipticityObservable hP hStruct
        params.sUpper params.sLower)
      thetaHat

namespace GammaSigmaCoarseGrainedEllipticityNoXi

variable {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
variable {hP : Ch04.RestrictionLawCarrier P} {hStruct : Ch04.RestrictionStructuralLaw P}

/-- Add the internal finite moment exponent used by the existing Section 5.7
proof infrastructure. -/
noncomputable def withInternalXi
    (hΓ : GammaSigmaCoarseGrainedEllipticityNoXi P hP hStruct) :
    GammaSigmaCoarseGrainedEllipticity P hP hStruct where
  sigma := hΓ.sigma
  sigma_pos := hΓ.sigma_pos
  params := hΓ.params.toQuantitativeParams
  thetaHat := hΓ.thetaHat
  thetaHat_pos := hΓ.thetaHat_pos
  tail := by
    simpa using hΓ.tail

@[simp]
theorem withInternalXi_sigma
    (hΓ : GammaSigmaCoarseGrainedEllipticityNoXi P hP hStruct) :
    hΓ.withInternalXi.sigma = hΓ.sigma := rfl

@[simp]
theorem withInternalXi_thetaHat
    (hΓ : GammaSigmaCoarseGrainedEllipticityNoXi P hP hStruct) :
    hΓ.withInternalXi.thetaHat = hΓ.thetaHat := rfl

end GammaSigmaCoarseGrainedEllipticityNoXi

namespace GammaSigmaCoarseGrainedEllipticity

variable {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
variable {hP : Ch04.RestrictionLawCarrier P} {hStruct : Ch04.RestrictionStructuralLaw P}

theorem sUpper_pos
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    0 < hΓ.params.sUpper :=
  hΓ.params.sUpper_pos

theorem sLower_pos
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    0 < hΓ.params.sLower :=
  hΓ.params.sLower_pos

theorem two_le_xi
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    2 ≤ hΓ.params.xi :=
  hΓ.params.two_le_xi

theorem aemeasurable_unitEllipticityObservable
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    AEMeasurable
      (gammaSigmaUnitEllipticityObservable hP hStruct
        hΓ.params.sUpper hΓ.params.sLower) P := by
  have hUpper :
      AEMeasurable
        (fun a : RegCoeffField d =>
          Ch04.LambdaSqCoeffField (originCube d 0)
            hΓ.params.sUpper (.finite 1) a) P := by
    simpa using
      hP.aemeasurable_LambdaSqCoeffField_finite_one
        (originCube d 0) hΓ.sUpper_pos
  have hLower :
      AEMeasurable
        (fun a : RegCoeffField d =>
          (Ch04.lambdaSqCoeffField (originCube d 0)
            hΓ.params.sLower (.finite 1) a)⁻¹) P := by
    simpa using
      hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
        (originCube d 0) hΓ.sLower_pos
  exact
    if hbar : 0 < hP.barSigmaAtScale hStruct (0 : ℤ) then
      by
        simp [gammaSigmaUnitEllipticityObservable, hbar]
        exact
          (hUpper.const_mul (hP.barSigmaAtScale hStruct (0 : ℤ))⁻¹).add
            (hLower.const_mul (hP.barSigmaAtScale hStruct (0 : ℤ)))
    else
      by
        simp [gammaSigmaUnitEllipticityObservable, hbar]
        exact hUpper.add hLower

/-- The Γσ tail assumption gives finite moments of the normalized unit-cube
ellipticity observable itself.  Splitting this into separate `Λ` and
`λ^{-1}` moments is the next deterministic normalization step. -/
theorem integrable_abs_unitEllipticityObservable_rpow_xi
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    Integrable
      (fun a : RegCoeffField d =>
        |gammaSigmaUnitEllipticityObservable hP hStruct
          hΓ.params.sUpper hΓ.params.sLower a| ^ (hΓ.params.xi : ℝ)) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  have hxi_one : 1 ≤ (hΓ.params.xi : ℝ) := by
    exact_mod_cast
      (le_trans (by norm_num : 1 ≤ 2) hΓ.two_le_xi)
  exact
    integrable_rpow_of_isBigOWith_gammaSigma
      (μ := P)
      (Y := fun a : RegCoeffField d =>
        |gammaSigmaUnitEllipticityObservable hP hStruct
          hΓ.params.sUpper hΓ.params.sLower a|)
      (K := hΓ.thetaHat) (σ := hΓ.sigma) (p := (hΓ.params.xi : ℝ))
      hΓ.sigma_pos hΓ.thetaHat_pos hxi_one
      (fun a => abs_nonneg _)
      (continuous_abs.measurable.comp_aemeasurable
        hΓ.aemeasurable_unitEllipticityObservable)
      hΓ.tail

/-- The Γσ tail makes the unit-scale normalization well-formed: the scalar
`\bar σ_0` is strictly positive.

The guarded definition of `gammaSigmaUnitEllipticityObservable` agrees with the
manuscript expression when this theorem is used.  In the contradictory branch
`\bar σ_0 ≤ 0`, the guard asks for Γσ control of the unnormalized factor sum;
that gives the unit-scale factor integrability needed to recover
`\bar σ_0 > 0` from the Chapter 4 positivity theorem. -/
theorem barSigmaAtScale_zero_pos
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    0 < hP.barSigmaAtScale hStruct (0 : ℤ) := by
  by_cases hbar : 0 < hP.barSigmaAtScale hStruct (0 : ℤ)
  · exact hbar
  · let : IsProbabilityMeasure P := hP.isProbability
    let ξ : ℕ := hΓ.params.xi
    let L : RegCoeffField d → ℝ :=
      fun a => Ch04.LambdaSqCoeffField (originCube d 0)
        hΓ.params.sUpper (.finite 1) a
    let I : RegCoeffField d → ℝ :=
      fun a => (Ch04.lambdaSqCoeffField (originCube d 0)
        hΓ.params.sLower (.finite 1) a)⁻¹
    let X : RegCoeffField d → ℝ :=
      gammaSigmaUnitEllipticityObservable hP hStruct
        hΓ.params.sUpper hΓ.params.sLower
    have hX_abs_rpow_int :
        Integrable (fun a : RegCoeffField d => |X a| ^ (ξ : ℝ)) P := by
      simpa [X, ξ] using
        hΓ.integrable_abs_unitEllipticityObservable_rpow_xi
    have hX_abs_pow_int :
        Integrable (fun a : RegCoeffField d => |X a| ^ ξ) P := by
      refine hX_abs_rpow_int.congr ?_
      filter_upwards with a
      rw [Real.rpow_natCast]
    have hsum_abs_pow_int :
        Integrable (fun a : RegCoeffField d => |L a + I a| ^ ξ) P := by
      simpa [X, L, I, gammaSigmaUnitEllipticityObservable, hbar] using
        hX_abs_pow_int
    have hL_meas : AEMeasurable L P := by
      simpa [L] using
        hP.aemeasurable_LambdaSqCoeffField_finite_one
          (originCube d 0) hΓ.sUpper_pos
    have hI_meas : AEMeasurable I P := by
      simpa [I] using
        hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
          (originCube d 0) hΓ.sLower_pos
    have hL_nonneg : ∀ a, 0 ≤ L a := fun a => by
      dsimp [L]
      exact Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a
        hΓ.sUpper_pos (by norm_num : (1 : ℝ) ≤ 1)
    have hI_nonneg : ∀ a, 0 ≤ I a := fun a => by
      dsimp [I]
      exact inv_nonneg.mpr
        (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a
          hΓ.sLower_pos (by norm_num : (1 : ℝ) ≤ 1))
    have hsum_nonneg : ∀ a, 0 ≤ |L a + I a| := fun a => abs_nonneg _
    have hUpperDom :
        (fun a : RegCoeffField d => |L a|) ≤ᵐ[P]
          fun a => |L a + I a| := by
      filter_upwards with a
      rw [abs_of_nonneg (hL_nonneg a),
        abs_of_nonneg (add_nonneg (hL_nonneg a) (hI_nonneg a))]
      exact le_add_of_nonneg_right (hI_nonneg a)
    have hLowerDom :
        (fun a : RegCoeffField d => |I a|) ≤ᵐ[P]
          fun a => |L a + I a| := by
      filter_upwards with a
      rw [abs_of_nonneg (hI_nonneg a),
        abs_of_nonneg (add_nonneg (hL_nonneg a) (hI_nonneg a))]
      exact le_add_of_nonneg_left (hL_nonneg a)
    have hUpperAbsPowInt :
        Integrable (fun a : RegCoeffField d => |L a| ^ ξ) P :=
      Ch04.RestrictionLawCarrier.integrable_abs_pow_of_ae_abs_le_nonneg hL_meas
        (Filter.Eventually.of_forall hsum_nonneg)
        hUpperDom hsum_abs_pow_int
    have hLowerAbsPowInt :
        Integrable (fun a : RegCoeffField d => |I a| ^ ξ) P :=
      Ch04.RestrictionLawCarrier.integrable_abs_pow_of_ae_abs_le_nonneg hI_meas
        (Filter.Eventually.of_forall hsum_nonneg)
        hLowerDom hsum_abs_pow_int
    have hUpperPowInt :
        Integrable (fun a : RegCoeffField d => L a ^ ξ) P := by
      refine hUpperAbsPowInt.congr ?_
      filter_upwards with a
      simp [abs_of_nonneg (hL_nonneg a)]
    have hLowerPowInt :
        Integrable (fun a : RegCoeffField d => I a ^ ξ) P := by
      refine hLowerAbsPowInt.congr ?_
      filter_upwards with a
      simp [abs_of_nonneg (hI_nonneg a)]
    have hBlock :
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (0 : ℤ))) P :=
      hP.integrable_coarseFullBlockMatrixAtCube_of_integrable_factor_observables
        (originCube d (0 : ℤ))
        hΓ.sUpper_pos hΓ.sLower_pos
        (Nat.succ_le_of_lt hΓ.params.xi_pos)
        (by simpa [L, ξ] using hUpperPowInt)
        (by simpa [I, ξ] using hLowerPowInt)
    exact
      Ch04.RestrictionLawCarrier.barSigmaAtScale_pos_of_integrable_coarseFullBlockMatrixAtCube
        hP hStruct hBlock

theorem barSigmaAtScale_zero_nonneg
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    0 ≤ hP.barSigmaAtScale hStruct (0 : ℤ) :=
  hΓ.barSigmaAtScale_zero_pos.le

/-- Conditional bridge from the Γσ unit-cube assumption to the old `(P4)`
moment hypothesis.

The extra input is exactly the positivity of the normalizing scalar
`\bar σ_0`.  Mathematically this is implicit in the displayed Γσ assumption;
Lean's inverse is total, so the positivity must be supplied or proved before
the two normalized summands can be split. -/
def toQuantitativeCoarseGrainedEllipticity_of_barSigmaAtScale_zero_pos
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (hbar : 0 < hP.barSigmaAtScale hStruct (0 : ℤ)) :
    QuantitativeCoarseGrainedEllipticity P := by
  letI : IsProbabilityMeasure P := hP.isProbability
  let b : ℝ := hP.barSigmaAtScale hStruct (0 : ℤ)
  let ξ : ℕ := hΓ.params.xi
  let L : RegCoeffField d → ℝ :=
    fun a => Ch04.LambdaSqCoeffField (originCube d 0)
      hΓ.params.sUpper (.finite 1) a
  let I : RegCoeffField d → ℝ :=
    fun a => (Ch04.lambdaSqCoeffField (originCube d 0)
      hΓ.params.sLower (.finite 1) a)⁻¹
  let X : RegCoeffField d → ℝ :=
    gammaSigmaUnitEllipticityObservable hP hStruct
      hΓ.params.sUpper hΓ.params.sLower
  have hb : 0 < b := by simpa [b] using hbar
  have hb_nonneg : 0 ≤ b := hb.le
  have hb_inv_nonneg : 0 ≤ b⁻¹ := (inv_pos.mpr hb).le
  have hL_nonneg : ∀ a, 0 ≤ L a := fun a => by
    dsimp [L]
    exact Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a
      hΓ.sUpper_pos (by norm_num : (1 : ℝ) ≤ 1)
  have hI_nonneg : ∀ a, 0 ≤ I a := fun a => by
    dsimp [I]
    exact inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a
        hΓ.sLower_pos (by norm_num : (1 : ℝ) ≤ 1))
  have hX_abs_rpow_int :
      Integrable (fun a : RegCoeffField d => |X a| ^ (ξ : ℝ)) P := by
    simpa [X, ξ] using
      hΓ.integrable_abs_unitEllipticityObservable_rpow_xi
  have hX_abs_pow_int :
      Integrable (fun a : RegCoeffField d => |X a| ^ ξ) P := by
    refine hX_abs_rpow_int.congr ?_
    filter_upwards with a
    rw [Real.rpow_natCast]
  have hL_meas : AEMeasurable L P := by
    simpa [L] using
      hP.aemeasurable_LambdaSqCoeffField_finite_one
        (originCube d 0) hΓ.sUpper_pos
  have hI_meas : AEMeasurable I P := by
    simpa [I] using
      hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
        (originCube d 0) hΓ.sLower_pos
  have hUpperDom :
      (fun a : RegCoeffField d => |L a|) ≤ᵐ[P]
        fun a => b * |X a| := by
    filter_upwards with a
    have hterm : b⁻¹ * L a ≤ X a := by
      simpa [X, gammaSigmaUnitEllipticityObservable, b, L, I, hb] using
        (show b⁻¹ * L a ≤ b⁻¹ * L a + b * I a from
          le_add_of_nonneg_right (mul_nonneg hb_nonneg (hI_nonneg a)))
    have hmul : b * (b⁻¹ * L a) ≤ b * X a :=
      mul_le_mul_of_nonneg_left hterm hb_nonneg
    have hleft : b * (b⁻¹ * L a) = L a := by
      field_simp [hb.ne']
    have hLX : L a ≤ b * |X a| := by
      calc
        L a = b * (b⁻¹ * L a) := hleft.symm
        _ ≤ b * X a := hmul
        _ ≤ b * |X a| := mul_le_mul_of_nonneg_left (le_abs_self (X a)) hb_nonneg
    simpa [abs_of_nonneg (hL_nonneg a)] using hLX
  have hLowerDom :
      (fun a : RegCoeffField d => |I a|) ≤ᵐ[P]
        fun a => b⁻¹ * |X a| := by
    filter_upwards with a
    have hterm : b * I a ≤ X a := by
      simpa [X, gammaSigmaUnitEllipticityObservable, b, L, I, hb] using
        (show b * I a ≤ b⁻¹ * L a + b * I a from
          le_add_of_nonneg_left (mul_nonneg hb_inv_nonneg (hL_nonneg a)))
    have hmul : b⁻¹ * (b * I a) ≤ b⁻¹ * X a :=
      mul_le_mul_of_nonneg_left hterm hb_inv_nonneg
    have hleft : b⁻¹ * (b * I a) = I a := by
      field_simp [hb.ne']
    have hIX : I a ≤ b⁻¹ * |X a| := by
      calc
        I a = b⁻¹ * (b * I a) := hleft.symm
        _ ≤ b⁻¹ * X a := hmul
        _ ≤ b⁻¹ * |X a| := mul_le_mul_of_nonneg_left (le_abs_self (X a)) hb_inv_nonneg
    simpa [abs_of_nonneg (hI_nonneg a)] using hIX
  have hUpperY_pow_int :
      Integrable (fun a : RegCoeffField d => (b * |X a|) ^ ξ) P := by
    refine (hX_abs_pow_int.const_mul (b ^ ξ)).congr ?_
    filter_upwards with a
    rw [mul_pow]
  have hLowerY_pow_int :
      Integrable (fun a : RegCoeffField d => (b⁻¹ * |X a|) ^ ξ) P := by
    refine (hX_abs_pow_int.const_mul (b⁻¹ ^ ξ)).congr ?_
    filter_upwards with a
    rw [mul_pow]
  have hUpperAbsPowInt :
      Integrable (fun a : RegCoeffField d => |L a| ^ ξ) P :=
    Ch04.RestrictionLawCarrier.integrable_abs_pow_of_ae_abs_le_nonneg hL_meas
      (Filter.Eventually.of_forall fun a =>
        mul_nonneg hb_nonneg (abs_nonneg (X a)))
      hUpperDom hUpperY_pow_int
  have hLowerAbsPowInt :
      Integrable (fun a : RegCoeffField d => |I a| ^ ξ) P :=
    Ch04.RestrictionLawCarrier.integrable_abs_pow_of_ae_abs_le_nonneg hI_meas
      (Filter.Eventually.of_forall fun a =>
        mul_nonneg hb_inv_nonneg (abs_nonneg (X a)))
      hLowerDom hLowerY_pow_int
  have hUpperPowInt :
      Integrable (fun a : RegCoeffField d => L a ^ ξ) P := by
    refine hUpperAbsPowInt.congr ?_
    filter_upwards with a
    simp [abs_of_nonneg (hL_nonneg a)]
  have hLowerPowInt :
      Integrable (fun a : RegCoeffField d => I a ^ ξ) P := by
    refine hLowerAbsPowInt.congr ?_
    filter_upwards with a
    simp [abs_of_nonneg (hI_nonneg a)]
  exact
    { sUpper := hΓ.params.sUpper
      sLower := hΓ.params.sLower
      xi := hΓ.params.xi
      two_le_dim := hΓ.params.two_le_dim
      sUpper_nonneg := hΓ.params.sUpper_nonneg
      sUpper_lt_one := hΓ.params.sUpper_lt_one
      sLower_nonneg := hΓ.params.sLower_nonneg
      sLower_lt_one := hΓ.params.sLower_lt_one
      xi_gt_two_mul_dim := hΓ.params.xi_gt_two_mul_dim
      sum_lt_one := hΓ.params.sum_lt_one
      dim_div_xi_lt_min := hΓ.params.dim_div_xi_lt_min
      upper_moment_integrable := by
        simpa [L, ξ] using hUpperPowInt
      lower_inv_moment_integrable := by
        simpa [I, ξ] using hLowerPowInt }

/-- The Γσ unit-cube assumption implies the old `(P4)` moment hypothesis. -/
def toQuantitativeCoarseGrainedEllipticity
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    QuantitativeCoarseGrainedEllipticity P :=
  hΓ.toQuantitativeCoarseGrainedEllipticity_of_barSigmaAtScale_zero_pos
    hΓ.barSigmaAtScale_zero_pos

theorem unitEllipticityObservable_nonneg
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (a : RegCoeffField d) :
    0 ≤ gammaSigmaUnitEllipticityObservable hP hStruct
      hΓ.params.sUpper hΓ.params.sLower a := by
  have hbar := hΓ.barSigmaAtScale_zero_pos
  simpa [gammaSigmaUnitEllipticityObservable, hbar] using add_nonneg
    (mul_nonneg (inv_nonneg.mpr hΓ.barSigmaAtScale_zero_nonneg)
      (Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a
        hΓ.sUpper_pos (by norm_num : (1 : ℝ) ≤ 1)))
    (mul_nonneg hΓ.barSigmaAtScale_zero_nonneg
      (inv_nonneg.mpr
        (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a
          hΓ.sLower_pos (by norm_num : (1 : ℝ) ≤ 1))))

/-- The `L^ξ` root of the normalized unit-cube Γσ ellipticity observable. -/
noncomputable def unitEllipticityMomentRoot
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) : ℝ :=
  Ch04.annealedMomentRoot P hΓ.params.xi
    (gammaSigmaUnitEllipticityObservable hP hStruct
      hΓ.params.sUpper hΓ.params.sLower)

theorem unitEllipticityMomentRoot_nonneg
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    0 ≤ hΓ.unitEllipticityMomentRoot := by
  refine Ch04.annealedMomentRoot_nonneg_of_nonneg P hΓ.params.xi ?_
  exact hΓ.unitEllipticityObservable_nonneg

theorem unitEllipticityMomentRoot_le_gammaMomentScale
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    hΓ.unitEllipticityMomentRoot ≤
      Ch04.gammaMomentConst hΓ.sigma *
        (hΓ.params.xi : ℝ) ^ hΓ.sigma⁻¹ * hΓ.thetaHat := by
  let : IsProbabilityMeasure P := hP.isProbability
  let ξ : ℕ := hΓ.params.xi
  let X : RegCoeffField d → ℝ :=
    gammaSigmaUnitEllipticityObservable hP hStruct
      hΓ.params.sUpper hΓ.params.sLower
  let M : ℝ := Ch04.gammaMomentConst hΓ.sigma *
    (ξ : ℝ) ^ hΓ.sigma⁻¹ * hΓ.thetaHat
  have hξ_one_nat : 1 ≤ ξ := by
    simpa [ξ] using le_trans (by norm_num : 1 ≤ 2) hΓ.two_le_xi
  have hξ_one : 1 ≤ (ξ : ℝ) := by exact_mod_cast hξ_one_nat
  have hξ_ne : ξ ≠ 0 := by omega
  have hExp_nonneg : 0 ≤ 1 / (ξ : ℝ) := by positivity
  have hX_nonneg : ∀ a, 0 ≤ X a := by
    intro a
    simpa [X] using hΓ.unitEllipticityObservable_nonneg a
  have hX_meas : AEMeasurable X P := by
    simpa [X] using hΓ.aemeasurable_unitEllipticityObservable
  have hIntegral_nonneg :
      0 ≤ ∫ a, |X a| ^ (ξ : ℝ) ∂P := by
    exact MeasureTheory.integral_nonneg fun a =>
      Real.rpow_nonneg (abs_nonneg (X a)) _
  have hMomentConst_pos : 0 < Ch04.gammaMomentConst hΓ.sigma := by
    simpa [Ch04.gammaMomentConst] using
      IndependentSums.gammaMomentConst_pos hΓ.sigma_pos
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg
      (mul_nonneg hMomentConst_pos.le
        (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le ξ) _))
      hΓ.thetaHat_pos.le
  have hmoment :
      ∫ a, |X a| ^ (ξ : ℝ) ∂P ≤ M ^ (ξ : ℝ) := by
    simpa [M, ξ] using
      Ch04.integral_abs_rpow_le_of_isBigO_gammaSigma
        (μ := P) (X := X) (K := hΓ.thetaHat) (σ := hΓ.sigma)
        (p := (ξ : ℝ))
        hΓ.sigma_pos hΓ.thetaHat_pos hξ_one hX_meas hΓ.tail
  calc
    hΓ.unitEllipticityMomentRoot =
        (∫ a, |X a| ^ (ξ : ℝ) ∂P) ^ (1 / (ξ : ℝ)) := by
          dsimp [unitEllipticityMomentRoot, Ch04.annealedMomentRoot, X, ξ]
          congr 1
          exact integral_congr_ae (by
            filter_upwards with a
            rw [abs_of_nonneg (hX_nonneg a), Real.rpow_natCast])
    _ ≤ (M ^ (ξ : ℝ)) ^ (1 / (ξ : ℝ)) := by
          exact Real.rpow_le_rpow hIntegral_nonneg hmoment hExp_nonneg
    _ = M := by
          rw [Real.rpow_natCast, one_div]
          exact Real.pow_rpow_inv_natCast hM_nonneg hξ_ne
    _ =
      Ch04.gammaMomentConst hΓ.sigma *
        (hΓ.params.xi : ℝ) ^ hΓ.sigma⁻¹ * hΓ.thetaHat := by
          simp [M, ξ]

theorem LambdaMomentAtScale_zero_le_barSigma_mul_unitEllipticityMomentRoot
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    Ch04.LambdaMomentAtScale P (0 : ℤ) hΓ.params.sUpper hΓ.params.xi ≤
      hP.barSigmaAtScale hStruct (0 : ℤ) * hΓ.unitEllipticityMomentRoot := by
  let ξ : ℕ := hΓ.params.xi
  let b : ℝ := hP.barSigmaAtScale hStruct (0 : ℤ)
  let L : RegCoeffField d → ℝ :=
    fun a => Ch04.LambdaSqCoeffField (originCube d 0)
      hΓ.params.sUpper (.finite 1) a
  let X : RegCoeffField d → ℝ :=
    gammaSigmaUnitEllipticityObservable hP hStruct
      hΓ.params.sUpper hΓ.params.sLower
  have hξ_one : 1 ≤ ξ := by
    simpa [ξ] using le_trans (by norm_num : 1 ≤ 2) hΓ.two_le_xi
  have hb_pos : 0 < b := by simpa [b] using hΓ.barSigmaAtScale_zero_pos
  have hb_ne : b ≠ 0 := hb_pos.ne'
  have hb_nonneg : 0 ≤ b := by simpa [b] using hΓ.barSigmaAtScale_zero_nonneg
  have hL_nonneg : ∀ a, 0 ≤ L a := fun a => by
    dsimp [L]
    exact Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a
      hΓ.sUpper_pos (by norm_num : (1 : ℝ) ≤ 1)
  have hX_nonneg : ∀ a, 0 ≤ X a := fun a => by
    simpa [X, gammaSigmaUnitEllipticityObservable, b, hb_pos] using add_nonneg
      (mul_nonneg (inv_nonneg.mpr hb_nonneg) (hL_nonneg a))
      (mul_nonneg hb_nonneg
        (inv_nonneg.mpr
          (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a
            hΓ.sLower_pos (by norm_num : (1 : ℝ) ≤ 1))))
  have hL_meas : AEMeasurable L P := by
    simpa [L] using
      hP.aemeasurable_LambdaSqCoeffField_finite_one
        (originCube d 0) hΓ.sUpper_pos
  have hX_abs_int : Integrable (fun a : RegCoeffField d => |X a| ^ ξ) P := by
    have h := hΓ.integrable_abs_unitEllipticityObservable_rpow_xi
    refine h.congr ?_
    filter_upwards with a
    simp [X, ξ, Real.rpow_natCast, gammaSigmaUnitEllipticityObservable, b, hb_pos]
  have hdom : L ≤ᵐ[P] fun a => b * X a := by
    filter_upwards with a
    have hterm : b⁻¹ * L a ≤ X a := by
      simpa [X, gammaSigmaUnitEllipticityObservable, b, L, hb_pos] using
        (show b⁻¹ * L a ≤
            b⁻¹ * L a +
              b * (Ch04.lambdaSqCoeffField (originCube d 0)
                hΓ.params.sLower (.finite 1) a)⁻¹ from
          le_add_of_nonneg_right
            (mul_nonneg hb_nonneg
              (inv_nonneg.mpr
                (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a
                  hΓ.sLower_pos (by norm_num : (1 : ℝ) ≤ 1)))))
    have hmul : b * (b⁻¹ * L a) ≤ b * X a :=
      mul_le_mul_of_nonneg_left hterm hb_nonneg
    have hleft : b * (b⁻¹ * L a) = L a := by
      field_simp [hb_ne]
    calc
      L a = b * (b⁻¹ * L a) := hleft.symm
      _ ≤ b * X a := hmul
  have hroot :=
    Section52.section52_annealedMomentRoot_le_const_mul_of_ae_le
      (P := P) (ξ := ξ) (c := b) (X := L) (Y := X)
      hξ_one hb_nonneg hL_nonneg hX_nonneg hL_meas hX_abs_int hdom
  simpa [Ch04.LambdaMomentAtScale, unitEllipticityMomentRoot, L, X, b, ξ]
    using hroot

theorem lambdaInvMomentAtScale_zero_le_inv_barSigma_mul_unitEllipticityMomentRoot
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    Ch04.lambdaInvMomentAtScale P (0 : ℤ) hΓ.params.sLower hΓ.params.xi ≤
      (hP.barSigmaAtScale hStruct (0 : ℤ))⁻¹ * hΓ.unitEllipticityMomentRoot := by
  let ξ : ℕ := hΓ.params.xi
  let b : ℝ := hP.barSigmaAtScale hStruct (0 : ℤ)
  let I : RegCoeffField d → ℝ :=
    fun a => (Ch04.lambdaSqCoeffField (originCube d 0)
      hΓ.params.sLower (.finite 1) a)⁻¹
  let X : RegCoeffField d → ℝ :=
    gammaSigmaUnitEllipticityObservable hP hStruct
      hΓ.params.sUpper hΓ.params.sLower
  have hξ_one : 1 ≤ ξ := by
    simpa [ξ] using le_trans (by norm_num : 1 ≤ 2) hΓ.two_le_xi
  have hb_pos : 0 < b := by simpa [b] using hΓ.barSigmaAtScale_zero_pos
  have hb_ne : b ≠ 0 := hb_pos.ne'
  have hb_nonneg : 0 ≤ b := by simpa [b] using hΓ.barSigmaAtScale_zero_nonneg
  have hb_inv_nonneg : 0 ≤ b⁻¹ := inv_nonneg.mpr hb_nonneg
  have hI_nonneg : ∀ a, 0 ≤ I a := fun a => by
    dsimp [I]
    exact inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a
        hΓ.sLower_pos (by norm_num : (1 : ℝ) ≤ 1))
  have hX_nonneg : ∀ a, 0 ≤ X a := fun a => by
    simpa [X, gammaSigmaUnitEllipticityObservable, b, I, hb_pos] using add_nonneg
      (mul_nonneg hb_inv_nonneg
        (Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a
          hΓ.sUpper_pos (by norm_num : (1 : ℝ) ≤ 1)))
      (mul_nonneg hb_nonneg (hI_nonneg a))
  have hI_meas : AEMeasurable I P := by
    simpa [I] using
      hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
        (originCube d 0) hΓ.sLower_pos
  have hX_abs_int : Integrable (fun a : RegCoeffField d => |X a| ^ ξ) P := by
    have h := hΓ.integrable_abs_unitEllipticityObservable_rpow_xi
    refine h.congr ?_
    filter_upwards with a
    simp [X, ξ, Real.rpow_natCast, gammaSigmaUnitEllipticityObservable, b, hb_pos]
  have hdom : I ≤ᵐ[P] fun a => b⁻¹ * X a := by
    filter_upwards with a
    have hterm : b * I a ≤ X a := by
      simpa [X, gammaSigmaUnitEllipticityObservable, b, I, hb_pos] using
        (show b * I a ≤
            b⁻¹ *
                Ch04.LambdaSqCoeffField (originCube d 0)
                  hΓ.params.sUpper (.finite 1) a +
              b * I a from
          le_add_of_nonneg_left
            (mul_nonneg hb_inv_nonneg
              (Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a
                hΓ.sUpper_pos (by norm_num : (1 : ℝ) ≤ 1))))
    have hmul : b⁻¹ * (b * I a) ≤ b⁻¹ * X a :=
      mul_le_mul_of_nonneg_left hterm hb_inv_nonneg
    have hleft : b⁻¹ * (b * I a) = I a := by
      field_simp [hb_ne]
    calc
      I a = b⁻¹ * (b * I a) := hleft.symm
      _ ≤ b⁻¹ * X a := hmul
  have hroot :=
    Section52.section52_annealedMomentRoot_le_const_mul_of_ae_le
      (P := P) (ξ := ξ) (c := b⁻¹) (X := I) (Y := X)
      hξ_one hb_inv_nonneg hI_nonneg hX_nonneg hI_meas hX_abs_int hdom
  simpa [Ch04.lambdaInvMomentAtScale, unitEllipticityMomentRoot, I, X, b, ξ]
    using hroot

/-- The unit-scale annealed scalar contrast is controlled linearly by the
Γσ moment root. -/
theorem thetaAtScale_zero_le_unitEllipticityMomentRoot
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    thetaAtScale hP hStruct (0 : ℤ) ≤ hΓ.unitEllipticityMomentRoot := by
  let hP4 := hΓ.toQuantitativeCoarseGrainedEllipticity
  let b : ℝ := hP.barSigmaAtScale hStruct (0 : ℤ)
  let R : ℝ := hΓ.unitEllipticityMomentRoot
  have hb_pos : 0 < b := by simpa [b] using hΓ.barSigmaAtScale_zero_pos
  have hb_ne : b ≠ 0 := hb_pos.ne'
  have hb_nonneg : 0 ≤ b := hb_pos.le
  have hLowerCompare :
      (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ ≤
        Ch04.lambdaInvMomentAtScale P (0 : ℤ) hP4.sLower hP4.xi := by
    exact
      hP.barSigmaStarAtScale_inv_le_lambdaInvMomentAtScale_of_integrable_factor_observables
        hStruct hP4.sUpper_pos hP4.sLower_pos (Nat.succ_le_of_lt hP4.xi_pos)
        (fun l => Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 l)
        (fun l =>
          hP.aemeasurable_LambdaSqCoeffField_finite_one
            (originCube d (l : ℤ)) hP4.sUpper_pos)
        (fun l =>
          hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
            (originCube d (l : ℤ)) hP4.sLower_pos)
        (fun l => Section52.upperFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 l)
        (fun l => Section52.lowerFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 l)
        0
  have hLowerRoot :
      Ch04.lambdaInvMomentAtScale P (0 : ℤ) hP4.sLower hP4.xi ≤ b⁻¹ * R := by
    simpa [hP4, b, R,
      GammaSigmaCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity,
      GammaSigmaCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity_of_barSigmaAtScale_zero_pos]
      using
      hΓ.lambdaInvMomentAtScale_zero_le_inv_barSigma_mul_unitEllipticityMomentRoot
  have hStarInv_le : (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ ≤ b⁻¹ * R :=
    hLowerCompare.trans hLowerRoot
  calc
    thetaAtScale hP hStruct (0 : ℤ) =
        b * (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ := by
          simp [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, b]
    _ ≤ b * (b⁻¹ * R) :=
          mul_le_mul_of_nonneg_left hStarInv_le hb_nonneg
    _ = R := by
          field_simp [hb_ne]

/-- The unit-scale annealed scalar contrast is controlled by the deterministic
Γσ moment scale. -/
theorem thetaAtScale_zero_le_gammaMomentScale
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    thetaAtScale hP hStruct (0 : ℤ) ≤
      Ch04.gammaMomentConst hΓ.sigma *
        (hΓ.params.xi : ℝ) ^ hΓ.sigma⁻¹ * hΓ.thetaHat :=
  hΓ.thetaAtScale_zero_le_unitEllipticityMomentRoot.trans
    hΓ.unitEllipticityMomentRoot_le_gammaMomentScale

theorem widetildeThetaAtScale_zero_le_unitEllipticityMomentRoot_sq
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    widetildeThetaAtScale P (0 : ℤ) hΓ.toQuantitativeCoarseGrainedEllipticity ≤
      hΓ.unitEllipticityMomentRoot ^ 2 := by
  let hP4 := hΓ.toQuantitativeCoarseGrainedEllipticity
  let b : ℝ := hP.barSigmaAtScale hStruct (0 : ℤ)
  let R : ℝ := hΓ.unitEllipticityMomentRoot
  have hb_pos : 0 < b := by simpa [b] using hΓ.barSigmaAtScale_zero_pos
  have hb_ne : b ≠ 0 := hb_pos.ne'
  have hΛ :
      Ch04.LambdaMomentAtScale P (0 : ℤ) hP4.sUpper hP4.xi ≤ b * R := by
    simpa [hP4, b, R,
      GammaSigmaCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity,
      GammaSigmaCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity_of_barSigmaAtScale_zero_pos]
      using
      hΓ.LambdaMomentAtScale_zero_le_barSigma_mul_unitEllipticityMomentRoot
  have hI :
      Ch04.lambdaInvMomentAtScale P (0 : ℤ) hP4.sLower hP4.xi ≤ b⁻¹ * R := by
    simpa [hP4, b, R,
      GammaSigmaCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity,
      GammaSigmaCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity_of_barSigmaAtScale_zero_pos]
      using
      hΓ.lambdaInvMomentAtScale_zero_le_inv_barSigma_mul_unitEllipticityMomentRoot
  have hI_nonneg :
      0 ≤ Ch04.lambdaInvMomentAtScale P (0 : ℤ) hP4.sLower hP4.xi := by
    simpa [hP4,
      GammaSigmaCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity,
      GammaSigmaCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity_of_barSigmaAtScale_zero_pos]
      using
      Ch04.lambdaInvMomentAtScale_nonneg P (0 : ℤ)
        (ξ := hΓ.params.xi) hΓ.sLower_pos
  have hUpper_nonneg : 0 ≤ b * R := by
    exact mul_nonneg hΓ.barSigmaAtScale_zero_nonneg hΓ.unitEllipticityMomentRoot_nonneg
  calc
    widetildeThetaAtScale P (0 : ℤ) hP4 =
        Ch04.LambdaMomentAtScale P (0 : ℤ) hP4.sUpper hP4.xi *
          Ch04.lambdaInvMomentAtScale P (0 : ℤ) hP4.sLower hP4.xi := by
          rfl
    _ ≤ (b * R) * (b⁻¹ * R) := by
          exact mul_le_mul hΛ hI hI_nonneg hUpper_nonneg
    _ = R ^ 2 := by
          field_simp [hb_ne]

/-- Quantitative ordering of the old unit-scale moment contrast by the Γσ
scale.  This is the Lean form of the `\widetilde Θ_0` consequence; with the
current definitions the direct bound is quadratic in the Γσ scale. -/
theorem widetildeThetaAtScale_zero_le_gammaMomentScale_sq
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    widetildeThetaAtScale P (0 : ℤ) hΓ.toQuantitativeCoarseGrainedEllipticity ≤
      (Ch04.gammaMomentConst hΓ.sigma *
        (hΓ.params.xi : ℝ) ^ hΓ.sigma⁻¹ * hΓ.thetaHat) ^ 2 := by
  have hroot := hΓ.unitEllipticityMomentRoot_le_gammaMomentScale
  have hroot_nonneg := hΓ.unitEllipticityMomentRoot_nonneg
  calc
    widetildeThetaAtScale P (0 : ℤ) hΓ.toQuantitativeCoarseGrainedEllipticity ≤
        hΓ.unitEllipticityMomentRoot ^ 2 :=
          hΓ.widetildeThetaAtScale_zero_le_unitEllipticityMomentRoot_sq
    _ ≤
        (Ch04.gammaMomentConst hΓ.sigma *
          (hΓ.params.xi : ℝ) ^ hΓ.sigma⁻¹ * hΓ.thetaHat) ^ 2 :=
          pow_le_pow_left₀ hroot_nonneg hroot 2

end GammaSigmaCoarseGrainedEllipticity

end

end Section57
end Ch05
end Book
end Homogenization
