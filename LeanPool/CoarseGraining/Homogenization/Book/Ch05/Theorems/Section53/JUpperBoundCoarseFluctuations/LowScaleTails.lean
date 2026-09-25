/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.PositiveExcessResponseDefect

/-! # Low Scale Tails -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open MeasureTheory

/-!
# Low-scale tails for the coarse-fluctuation lemma

This proof-internal file owns the low-scale tail route in the final
coarse-fluctuation assembly.  The important point is that the weak-norm
maximizer is instantiated with two buffers, so the ellipticity coefficients in
the low-scale tails are shifted by one buffer.
-/

noncomputable section

private theorem rpow_three_sq (x : ℝ) :
    Real.rpow (3 : ℝ) x ^ 2 = Real.rpow (3 : ℝ) (2 * x) := by
  calc
    Real.rpow (3 : ℝ) x ^ 2 =
        Real.rpow (3 : ℝ) x * Real.rpow (3 : ℝ) x := by ring
    _ = Real.rpow (3 : ℝ) (x + x) := by
        exact (Real.rpow_add (by norm_num : (0 : ℝ) < 3) x x).symm
    _ = Real.rpow (3 : ℝ) (2 * x) := by ring_nf

private theorem inv_sq_eq_inv_sq {x : ℝ} (hx : x ≠ 0) :
    x⁻¹ ^ 2 = (x ^ 2)⁻¹ := by
  field_simp [hx]

private theorem positivePart_split_le (x base : ℝ) :
    x ≤ base + max (x - base) 0 := by
  by_cases h : x ≤ base
  · exact h.trans (le_add_of_nonneg_right (le_max_right _ _))
  · have hx : base ≤ x := le_of_lt (lt_of_not_ge h)
    have hmax : max (x - base) 0 = x - base := max_eq_left (sub_nonneg.mpr hx)
    linarith

private theorem buffered_lowScaleTail_sq (m k : ℕ) {β coefficient Jm : ℝ}
    (hβ_ne : β ≠ 0) (hcoefficient_nonneg : 0 ≤ coefficient) (hJ_nonneg : 0 ≤ Jm) :
    (β⁻¹ * Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - (k : ℤ)) : ℝ)) *
      Real.sqrt coefficient * Real.sqrt Jm) ^ 2 =
      (β ^ 2)⁻¹ * Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) *
        (coefficient * Jm) := by
  have hpow :
      Real.rpow (3 : ℝ)
          (-β * (Int.toNat ((m : ℤ) - (k : ℤ)) : ℝ)) ^ 2 =
        Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) := by
    have hmk :
        (Int.toNat ((m : ℤ) - (k : ℤ)) : ℝ) = ((m - k : ℕ) : ℝ) := by
      have hmk_nat : Int.toNat ((m : ℤ) - (k : ℤ)) = m - k := by
        omega
      exact_mod_cast hmk_nat
    rw [hmk]
    calc
      Real.rpow (3 : ℝ) (-β * ((m - k : ℕ) : ℝ)) ^ 2 =
          Real.rpow (3 : ℝ) (2 * (-β * ((m - k : ℕ) : ℝ))) :=
            rpow_three_sq _
      _ = Real.rpow (3 : ℝ) (-2 * β * ((m - k : ℕ) : ℝ)) := by ring_nf
  change
    (β⁻¹ * Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - (k : ℤ)) : ℝ)) *
        Real.sqrt coefficient * Real.sqrt Jm) ^ 2 =
      (β ^ 2)⁻¹ *
        Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) *
          (coefficient * Jm)
  have hsqrt :
      (Real.sqrt coefficient * Real.sqrt Jm) ^ 2 = coefficient * Jm := by
    rw [mul_pow, Real.sq_sqrt hcoefficient_nonneg, Real.sq_sqrt hJ_nonneg]
  calc
    (β⁻¹ * Real.rpow (3 : ℝ)
        (-β * (Int.toNat ((m : ℤ) - (k : ℤ)) : ℝ)) *
          Real.sqrt coefficient * Real.sqrt Jm) ^ 2
        =
      (β⁻¹) ^ 2 *
        Real.rpow (3 : ℝ)
          (-β * (Int.toNat ((m : ℤ) - (k : ℤ)) : ℝ)) ^ 2 *
        (Real.sqrt coefficient * Real.sqrt Jm) ^ 2 := by ring
    _ =
      (β ^ 2)⁻¹ *
        Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) *
          (coefficient * Jm) := by
        rw [inv_sq_eq_inv_sq hβ_ne, hpow, hsqrt]

/-- Pointwise algebraic reduction of the paired low-scale tails.  The
ellipticity coefficients are the shifted coefficients
`sLower + beta` and `sUpper + beta`, as required for the Section 5.2 moment
input. -/
theorem paired_lowScaleTailSquares_special_le_baseline_add_positiveExcess
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) (e : Vec d) (a : RegCoeffField d) :
    let β := section53CoarseFluctuationBeta hP4
    let s := hP4.sLower + 2 * β
    let s' := hP4.sLower + β
    let t := hP4.sUpper + 2 * β
    let t' := hP4.sUpper + β
    let Q : TriadicCube d := originCube d (m : ℤ)
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let σ := sigmaHatAtScale hP hStruct (m : ℤ)
    let Jm := Ch04.restrictionResponseJObservableCubeSet Q p_e q_e a
    let lowerCoeff := (Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹
    let upperCoeff := Ch04.LambdaSqCoeffField Q t' (.finite 1) a
    let lowerBase := (hP.barSigmaStarAtScale hStruct 0)⁻¹
    let upperBase := hP.barSigmaAtScale hStruct 0
    let lowerExcess := max (lowerCoeff - lowerBase) 0
    let upperExcess := max (upperCoeff - upperBase) 0
    let tailFactor :=
      (β ^ 2)⁻¹ *
        Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
    σ *
        (WeakNormsMaximizer.gradientLowScaleTailAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxLowScaleTailAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
      ≤
        tailFactor *
          (coarseFluctuationScalarWeightAtScale hP hStruct m * Jm +
            (σ * lowerExcess + σ⁻¹ * upperExcess) * Jm) := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let Jm := Ch04.restrictionResponseJObservableCubeSet Q p_e q_e a
  let lowerCoeff := (Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹
  let upperCoeff := Ch04.LambdaSqCoeffField Q t' (.finite 1) a
  let lowerBase := (hP.barSigmaStarAtScale hStruct 0)⁻¹
  let upperBase := hP.barSigmaAtScale hStruct 0
  let lowerExcess := max (lowerCoeff - lowerBase) 0
  let upperExcess := max (upperCoeff - upperBase) 0
  let tailFactor :=
    (β ^ 2)⁻¹ *
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hβ_ne : β ≠ 0 := hβ_pos.ne'
  have hs'_pos : 0 < s' := by
    dsimp [s', β]
    linarith [hP4.sLower_pos, section53CoarseFluctuationBeta_pos hP4]
  have ht'_pos : 0 < t' := by
    dsimp [t', β]
    linarith [hP4.sUpper_pos, section53CoarseFluctuationBeta_pos hP4]
  have hlower_nonneg : 0 ≤ lowerCoeff := by
    dsimp [lowerCoeff]
    exact inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg Q a hs'_pos (by norm_num))
  have hupper_nonneg : 0 ≤ upperCoeff := by
    dsimp [upperCoeff]
    exact Ch04.LambdaSqCoeffField_finite_nonneg Q a ht'_pos (by norm_num)
  have hJ_nonneg : 0 ≤ Jm := by
    dsimp [Jm]
    exact Ch04.restrictionResponseJObservableCubeSet_nonneg Q p_e q_e a
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have htail_nonneg : 0 ≤ tailFactor := by
    dsimp [tailFactor]
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hlower_split : lowerCoeff ≤ lowerBase + lowerExcess := by
    simpa [lowerExcess] using positivePart_split_le lowerCoeff lowerBase
  have hupper_split : upperCoeff ≤ upperBase + upperExcess := by
    simpa [upperExcess] using positivePart_split_le upperCoeff upperBase
  have hgrad_sq :
      (WeakNormsMaximizer.gradientLowScaleTailAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 =
        tailFactor * (lowerCoeff * Jm) := by
    dsimp [WeakNormsMaximizer.gradientLowScaleTailAtScale, tailFactor,
      Q, s, s', β]
    have hgap : hP4.sLower + 2 * β - (hP4.sLower + β) = β := by ring
    rw [hgap]
    exact buffered_lowScaleTail_sq m k hβ_ne hlower_nonneg hJ_nonneg
  have hflux_sq :
      (WeakNormsMaximizer.fluxLowScaleTailAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2 =
        tailFactor * (upperCoeff * Jm) := by
    dsimp [WeakNormsMaximizer.fluxLowScaleTailAtScale, tailFactor,
      Q, t, t', β]
    have hgap : hP4.sUpper + 2 * β - (hP4.sUpper + β) = β := by ring
    rw [hgap]
    exact buffered_lowScaleTail_sq m k hβ_ne hupper_nonneg hJ_nonneg
  have hpoint :
      σ * (tailFactor * (lowerCoeff * Jm)) +
          σ⁻¹ * (tailFactor * (upperCoeff * Jm)) ≤
        tailFactor *
          (coarseFluctuationScalarWeightAtScale hP hStruct m * Jm +
            (σ * lowerExcess + σ⁻¹ * upperExcess) * Jm) := by
    have hlowerJ :
        lowerCoeff * Jm ≤ (lowerBase + lowerExcess) * Jm :=
      mul_le_mul_of_nonneg_right hlower_split hJ_nonneg
    have hupperJ :
        upperCoeff * Jm ≤ (upperBase + upperExcess) * Jm :=
      mul_le_mul_of_nonneg_right hupper_split hJ_nonneg
    calc
      σ * (tailFactor * (lowerCoeff * Jm)) +
          σ⁻¹ * (tailFactor * (upperCoeff * Jm))
          =
        tailFactor * (σ * (lowerCoeff * Jm) + σ⁻¹ * (upperCoeff * Jm)) := by ring
      _ ≤
        tailFactor * (σ * ((lowerBase + lowerExcess) * Jm) +
          σ⁻¹ * ((upperBase + upperExcess) * Jm)) := by
          refine mul_le_mul_of_nonneg_left ?_ htail_nonneg
          exact add_le_add
            (mul_le_mul_of_nonneg_left hlowerJ hσ_nonneg)
            (mul_le_mul_of_nonneg_left hupperJ hσ_inv_nonneg)
      _ =
        tailFactor *
          (coarseFluctuationScalarWeightAtScale hP hStruct m * Jm +
            (σ * lowerExcess + σ⁻¹ * upperExcess) * Jm) := by
          dsimp [coarseFluctuationScalarWeightAtScale, σ, lowerBase,
            upperBase, lowerExcess, upperExcess]
          ring
  calc
    σ *
        (WeakNormsMaximizer.gradientLowScaleTailAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxLowScaleTailAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
        =
      σ * (tailFactor * (lowerCoeff * Jm)) +
        σ⁻¹ * (tailFactor * (upperCoeff * Jm)) := by
          rw [hgrad_sq, hflux_sq]
    _ ≤
      tailFactor *
          (coarseFluctuationScalarWeightAtScale hP hStruct m * Jm +
            (σ * lowerExcess + σ⁻¹ * upperExcess) * Jm) := hpoint

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
