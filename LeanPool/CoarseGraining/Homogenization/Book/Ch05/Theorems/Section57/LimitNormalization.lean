/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AnnealedLimit
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic.Basic

/-! # Limit Normalization -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums

/-!
# Limiting full-block normalization

This file packages the full-block diagonal normalizers associated with the
limiting scalar annealed matrix `\overline A`.  These are the Lean objects
appearing in the first quenched estimate as
`\overline A^{-1/2} e` and `\overline A^{1/2} e`.
-/

noncomputable section

/-- Diagonal full-block matrix representing `\overline A^{-1/2}` in the
scalarized limiting normalization. -/
noncomputable def scalarLimitInvSqrtMatrix
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) :
    FullBlockMat d :=
  Matrix.diagonal
    (Ch04.scalarFullBlockInvSqrtDiag
      (barSigmaLimit hP hStruct) (barSigmaLimit hP hStruct))

/-- Diagonal full-block matrix representing `\overline A^{1/2}` in the
scalarized limiting normalization. -/
noncomputable def scalarLimitSqrtMatrix
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) :
    FullBlockMat d :=
  Matrix.diagonal
    (Section56.scalarFullBlockSqrtDiag
      (barSigmaLimit hP hStruct) (barSigmaLimit hP hStruct))

/-- The first block vector in
`J(Q,\overline A^{-1/2}e,\overline A^{1/2}e)`. -/
noncomputable def scalarLimitInvSqrtBlockVec
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (e : FullBlockVec d) : BlockVec d :=
  ofFullBlockVec (Matrix.mulVec (scalarLimitInvSqrtMatrix hP hStruct) e)

/-- The second block vector in
`J(Q,\overline A^{-1/2}e,\overline A^{1/2}e)`. -/
noncomputable def scalarLimitSqrtBlockVec
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (e : FullBlockVec d) : BlockVec d :=
  ofFullBlockVec (Matrix.mulVec (scalarLimitSqrtMatrix hP hStruct) e)

/-- The Section 5.7 normalized block-response observable with the limiting
annealed normalization. -/
noncomputable def limitNormalizedBlockJObservable
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (Q : TriadicCube d) (e : FullBlockVec d) : RegCoeffField d → ℝ :=
  Ch04.blockJObservableCubeSetBlockVec Q
    (scalarLimitInvSqrtBlockVec hP hStruct e)
    (scalarLimitSqrtBlockVec hP hStruct e)

/-- Unit-cube ellipticity observable with the limiting scalar normalization.
This is the pointwise factor produced after replacing
`\overline A_0` by `\overline A`. -/
noncomputable def limitWeightedUnitEllipticityObservable
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (sUpper sLower : ℝ) : RegCoeffField d → ℝ :=
  fun a =>
    (barSigmaLimit hP hStruct)⁻¹ *
        Ch04.LambdaSqCoeffField (originCube d 0) sUpper (.finite 1) a +
      barSigmaLimit hP hStruct *
        (Ch04.lambdaSqCoeffField (originCube d 0) sLower (.finite 1) a)⁻¹

/-- Unit-cube ellipticity observable on an arbitrary cube, with the limiting
scalar normalization.  The origin version above is the special case used by
the Γσ assumption; this localized version is the one needed for descendant
unit cubes inside a larger cube. -/
noncomputable def limitWeightedUnitEllipticityObservableOnCube
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (Q : TriadicCube d) (sUpper sLower : ℝ) : RegCoeffField d → ℝ :=
  fun a =>
    (barSigmaLimit hP hStruct)⁻¹ *
        Ch04.LambdaSqCoeffField Q sUpper (.finite 1) a +
      barSigmaLimit hP hStruct *
        (Ch04.lambdaSqCoeffField Q sLower (.finite 1) a)⁻¹

@[simp] theorem limitWeightedUnitEllipticityObservableOnCube_originCube_zero
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (sUpper sLower : ℝ) :
    limitWeightedUnitEllipticityObservableOnCube hP hStruct
        (originCube d 0) sUpper sLower =
      limitWeightedUnitEllipticityObservable hP hStruct sUpper sLower :=
  rfl

namespace GammaSigmaCoarseGrainedEllipticity

variable {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
variable {hP : Ch04.RestrictionLawCarrier P} {hStruct : Ch04.RestrictionStructuralLaw P}

/-- The two limiting scalar normalizers are dual: their pairing preserves the
Euclidean square norm of the full-block vector. -/
theorem scalarLimit_normalizers_pairing_eq_dotProduct
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (e : FullBlockVec d) :
    blockVecDot
        (scalarLimitInvSqrtBlockVec hP hStruct e)
        (scalarLimitSqrtBlockVec hP hStruct e) =
      dotProduct e e := by
  classical
  let L : ℝ := barSigmaLimit hP hStruct
  have hL_pos : 0 < L := by
    simpa [L] using hΓ.barSigmaLimit_pos
  have hsqrtL_ne : √(barSigmaLimit hP hStruct) ≠ 0 := by
    simpa [L] using ne_of_gt (Real.sqrt_pos.2 hL_pos)
  rw [← dotProduct_toFullBlockVec]
  simp only [scalarLimitInvSqrtBlockVec, scalarLimitSqrtBlockVec,
    toFullBlockVec_ofFullBlockVec]
  unfold dotProduct
  simp only [Matrix.mulVec]
  refine Finset.sum_congr rfl ?_
  intro α _hα
  cases α with
  | inl i =>
      simp [scalarLimitInvSqrtMatrix, scalarLimitSqrtMatrix,
        Ch04.scalarFullBlockInvSqrtDiag, Section56.scalarFullBlockSqrtDiag]
      field_simp [hsqrtL_ne]
  | inr i =>
      simp [scalarLimitInvSqrtMatrix, scalarLimitSqrtMatrix,
        Ch04.scalarFullBlockInvSqrtDiag, Section56.scalarFullBlockSqrtDiag]
      field_simp [hsqrtL_ne]

/-- Replacing the unit-scale scalar normalizer by the limiting scalar normalizer
costs at most the initial scalar contrast. -/
theorem limitWeightedUnitEllipticityObservable_le_thetaAtScale_zero_mul_unit
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (a : RegCoeffField d) :
    limitWeightedUnitEllipticityObservable hP hStruct
        hΓ.params.sUpper hΓ.params.sLower a ≤
      thetaAtScale hP hStruct (0 : ℤ) *
        gammaSigmaUnitEllipticityObservable hP hStruct
          hΓ.params.sUpper hΓ.params.sLower a := by
  let hP4 := hΓ.toQuantitativeCoarseGrainedEllipticity
  let b0 := hP.barSigmaAtScale hStruct (0 : ℤ)
  let L := barSigmaLimit hP hStruct
  let θ := thetaAtScale hP hStruct (0 : ℤ)
  let Λ :=
    Ch04.LambdaSqCoeffField (originCube d 0)
      hΓ.params.sUpper (.finite 1) a
  let I :=
    (Ch04.lambdaSqCoeffField (originCube d 0)
      hΓ.params.sLower (.finite 1) a)⁻¹
  have hb0_nonneg : 0 ≤ b0 := by
    exact (Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 0).le
  have hθ_one : 1 ≤ θ := by
    simpa [θ] using
      Section54.GoodScale.one_le_thetaAtScale_of_P4 hP hStruct hP4 0
  have hΛ_nonneg : 0 ≤ Λ := by
    exact Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a
      hΓ.sUpper_pos (by norm_num : (1 : ℝ) ≤ 1)
  have hI_nonneg : 0 ≤ I := by
    exact inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a
        hΓ.sLower_pos (by norm_num : (1 : ℝ) ≤ 1))
  have hL_inv :
      L⁻¹ ≤ θ * b0⁻¹ := by
    simpa [L, θ, b0] using
      hΓ.barSigmaLimit_inv_le_thetaAtScale_zero_mul_barSigmaAtScale_zero_inv
  have hL_le_b0 : L ≤ b0 := by
    simpa [L, b0] using hΓ.barSigmaLimit_le_barSigmaAtScale 0
  have hb0_le_theta_b0 : b0 ≤ θ * b0 := by
    calc
      b0 = 1 * b0 := by ring
      _ ≤ θ * b0 := mul_le_mul_of_nonneg_right hθ_one hb0_nonneg
  have hL_le_theta_b0 : L ≤ θ * b0 := hL_le_b0.trans hb0_le_theta_b0
  have hupper : L⁻¹ * Λ ≤ (θ * b0⁻¹) * Λ :=
    mul_le_mul_of_nonneg_right hL_inv hΛ_nonneg
  have hlower : L * I ≤ (θ * b0) * I :=
    mul_le_mul_of_nonneg_right hL_le_theta_b0 hI_nonneg
  calc
    limitWeightedUnitEllipticityObservable hP hStruct
        hΓ.params.sUpper hΓ.params.sLower a
        = L⁻¹ * Λ + L * I := by
            simp [limitWeightedUnitEllipticityObservable, L, Λ, I]
    _ ≤ (θ * b0⁻¹) * Λ + (θ * b0) * I := add_le_add hupper hlower
    _ =
        θ *
          gammaSigmaUnitEllipticityObservable hP hStruct
            hΓ.params.sUpper hΓ.params.sLower a := by
          have hbar : 0 < hP.barSigmaAtScale hStruct (0 : ℤ) :=
            hΓ.barSigmaAtScale_zero_pos
          simp [gammaSigmaUnitEllipticityObservable, θ, b0, Λ, I, hbar]
          ring

/-- Pointwise nonnegativity of the localized limiting-normalized unit
ellipticity observable. -/
theorem limitWeightedUnitEllipticityObservableOnCube_nonneg
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (Q : TriadicCube d) (a : RegCoeffField d) :
    0 ≤ limitWeightedUnitEllipticityObservableOnCube hP hStruct Q
      hΓ.params.sUpper hΓ.params.sLower a := by
  have hL_pos : 0 < barSigmaLimit hP hStruct := hΓ.barSigmaLimit_pos
  have hΛ_nonneg :
      0 ≤ Ch04.LambdaSqCoeffField Q hΓ.params.sUpper (.finite 1) a :=
    Ch04.LambdaSqCoeffField_finite_nonneg Q a
      hΓ.sUpper_pos (by norm_num : (1 : ℝ) ≤ 1)
  have hI_nonneg :
      0 ≤ (Ch04.lambdaSqCoeffField Q hΓ.params.sLower (.finite 1) a)⁻¹ :=
    inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg Q a
        hΓ.sLower_pos (by norm_num : (1 : ℝ) ≤ 1))
  dsimp [limitWeightedUnitEllipticityObservableOnCube]
  exact add_nonneg
    (mul_nonneg (inv_pos.mpr hL_pos).le hΛ_nonneg)
    (mul_nonneg hL_pos.le hI_nonneg)

/-- The limiting-normalized unit ellipticity observable inherits the Γσ tail
from the unit-scale Γσ assumption. -/
theorem limitWeightedUnitEllipticityObservable_isBigO
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    IsBigO P (gammaSigma hΓ.sigma)
      (limitWeightedUnitEllipticityObservable hP hStruct
        hΓ.params.sUpper hΓ.params.sLower)
      (thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat) := by
  let : IsProbabilityMeasure P := hP.isProbability
  let hP4 := hΓ.toQuantitativeCoarseGrainedEllipticity
  let θ := thetaAtScale hP hStruct (0 : ℤ)
  let X : RegCoeffField d → ℝ :=
    gammaSigmaUnitEllipticityObservable hP hStruct
      hΓ.params.sUpper hΓ.params.sLower
  let Y : RegCoeffField d → ℝ :=
    limitWeightedUnitEllipticityObservable hP hStruct
      hΓ.params.sUpper hΓ.params.sLower
  have hθ_nonneg : 0 ≤ θ := by
    exact le_trans zero_le_one
      (by
        simpa [θ] using
          Section54.GoodScale.one_le_thetaAtScale_of_P4 hP hStruct hP4 0)
  have hY_nonneg : ∀ a, 0 ≤ Y a := by
    intro a
    have hL_pos : 0 < barSigmaLimit hP hStruct := hΓ.barSigmaLimit_pos
    have hΛ_nonneg :
        0 ≤ Ch04.LambdaSqCoeffField (originCube d 0)
          hΓ.params.sUpper (.finite 1) a :=
      Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a
        hΓ.sUpper_pos (by norm_num : (1 : ℝ) ≤ 1)
    have hI_nonneg :
        0 ≤ (Ch04.lambdaSqCoeffField (originCube d 0)
          hΓ.params.sLower (.finite 1) a)⁻¹ :=
      inv_nonneg.mpr
        (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a
          hΓ.sLower_pos (by norm_num : (1 : ℝ) ≤ 1))
    dsimp [Y, limitWeightedUnitEllipticityObservable]
    exact add_nonneg
      (mul_nonneg (inv_pos.mpr hL_pos).le hΛ_nonneg)
      (mul_nonneg hL_pos.le hI_nonneg)
  have hθX_nonneg : ∀ a, 0 ≤ θ * X a := by
    intro a
    exact mul_nonneg hθ_nonneg (by
      simpa [X] using hΓ.unitEllipticityObservable_nonneg a)
  have htail : IsBigO P (gammaSigma hΓ.sigma) (fun a => θ * X a)
      (θ * hΓ.thetaHat) := by
    simpa [X, θ] using
      IndependentSums.IsBigO.const_mul
        (μ := P) (Ψ := gammaSigma hΓ.sigma)
        (X := gammaSigmaUnitEllipticityObservable hP hStruct
          hΓ.params.sUpper hΓ.params.sLower)
        (A := hΓ.thetaHat) hθ_nonneg hΓ.tail
  exact htail.of_abs_le fun a => by
    have hle :
        Y a ≤ θ * X a := by
      simpa [Y, X, θ] using
        hΓ.limitWeightedUnitEllipticityObservable_le_thetaAtScale_zero_mul_unit a
    rw [abs_of_nonneg (hY_nonneg a), abs_of_nonneg (hθX_nonneg a)]
    exact hle

end GammaSigmaCoarseGrainedEllipticity

end

end Section57
end Ch05
end Book
end Homogenization
