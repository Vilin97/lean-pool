/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyFiniteBlockSmoothIdentity
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyScaleOffsetPointwise
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyZeroPhaseLowControl
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNormalizedBlockRadii

/-!
# Direct comparison of the paper's finite height blocks with high suffixes

The two smooth endpoints are rounded in the original spatial coordinates.
Their common maximal-function error is independent of the modulation. Only
the retained high block is dilated to unit phase.
-/

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson.KrauseLaceyFiniteBlockHighReduction

open KrauseLaceyFiniteBlockSmoothIdentity KrauseLaceyScaleOffsetPointwise
open KrauseLaceySharpSmoothAdapter KrauseLaceySparseDilation
open KrauseLaceyFullDyadicReflection KrauseLaceyFullDyadicSparseTransfer
open KrauseLaceyZeroPhaseLowControl


noncomputable
section

/-- Dilation at a physical radius obtained by dividing a normalized radius. -/
theorem smoothHighPass_square_div (a : ℝ) (ha : 0 < a) (ρ : ℝ)
    (f : L0Infinity) (x : ℝ) :
    smoothQuadraticHighPass (a ^ 2) (ρ / a) f x =
      smoothQuadraticHighPass 1 ρ (L0Infinity.dilate a ha f) (a * x) := by
  have h := smoothQuadraticHighPass_scale 1 a ha (ρ / a) f x
  have hr : a * (ρ / a) = ρ := by field_simp
  rw [one_mul, hr] at h
  exact h

/-- The normalized high finite block is the retained difference of the two
physical smooth cutoffs. -/
theorem normalizedHighBlock_eq_physicalSmoothDifference
    (a : ℝ) (ha : 0 < a) (B : ℕ) (f : L0Infinity) (x : ℝ) :
    finiteQuadraticDyadicBlock 1 1 B (L0Infinity.dilate a ha f) (a * x) =
      smoothQuadraticHighPass (a ^ 2) ((1 / 4 : ℝ) / a) f x -
        smoothQuadraticHighPass (a ^ 2) ((2 : ℝ) ^ ((B : ℤ) - 1) / a) f x := by
  rw [finiteQuadraticDyadicBlock_eq_smoothHighPass_sub 1 1 B
    (L0Infinity.dilate a ha f).integrable]
  have hlo : (2 : ℝ) ^ ((1 : ℤ) - 3) = 1 / 4 := by norm_num
  have hhi : (1 : ℤ) + (B : ℤ) - 2 = (B : ℤ) - 1 := by omega
  rw [hlo, hhi, smoothHighPass_square_div, smoothHighPass_square_div]

/-- Rounding the two physical endpoints has one common maximal-function cost.
The geometric premises are discharged at the paper's oscillatory scale below. -/
theorem enorm_block_sub_normalizedHighBlock_le
    (a : ℝ) (ha : 0 < a) (j : ℤ) (B : ℕ) (f : L0Infinity) (x : ℝ)
    (hlo : (2 : ℝ) ^ (j - 3) ≤ (1 / 4 : ℝ) / a ∧
      (1 / 4 : ℝ) / a ≤ 2 * (2 : ℝ) ^ (j - 3))
    (hhi : (2 : ℝ) ^ (j + (B : ℤ) - 2) ≤ (2 : ℝ) ^ ((B : ℤ) - 1) / a ∧
      (2 : ℝ) ^ ((B : ℤ) - 1) / a ≤ 2 * (2 : ℝ) ^ (j + (B : ℤ) - 2)) :
    ‖finiteQuadraticDyadicBlock (a ^ 2) j B f x -
        finiteQuadraticDyadicBlock 1 1 B (L0Infinity.dilate a ha f) (a * x)‖ₑ ≤
      48 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  rw [finiteQuadraticDyadicBlock_eq_smoothHighPass_sub (a ^ 2) j B f.integrable,
    normalizedHighBlock_eq_physicalSmoothDifference]
  have heq :
      (smoothQuadraticHighPass (a ^ 2) ((2 : ℝ) ^ (j - 3)) f x -
        smoothQuadraticHighPass (a ^ 2) ((2 : ℝ) ^ (j + (B : ℤ) - 2)) f x) -
      (smoothQuadraticHighPass (a ^ 2) ((1 / 4 : ℝ) / a) f x -
        smoothQuadraticHighPass (a ^ 2) ((2 : ℝ) ^ ((B : ℤ) - 1) / a) f x) =
      (smoothQuadraticHighPass (a ^ 2) ((2 : ℝ) ^ (j - 3)) f x -
        smoothQuadraticHighPass (a ^ 2) ((1 / 4 : ℝ) / a) f x) -
      (smoothQuadraticHighPass (a ^ 2) ((2 : ℝ) ^ (j + (B : ℤ) - 2)) f x -
        smoothQuadraticHighPass (a ^ 2) ((2 : ℝ) ^ ((B : ℤ) - 1) / a) f x) := by ring
  rw [heq]
  calc
    _ ≤ _ + _ := enorm_sub_le
    _ ≤ 24 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x +
        24 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x :=
      add_le_add
        (enorm_smoothHighPass_sub_le_maximal (a ^ 2)
          (zpow_pos (by norm_num) _) hlo.1 hlo.2 f.measurable_toFun f.integrable x)
        (enorm_smoothHighPass_sub_le_maximal (a ^ 2)
          (zpow_pos (by norm_num) _) hhi.1 hhi.2 f.measurable_toFun f.integrable x)
    _ = _ := by ring

/-- Every complete finite block is the zero-cutoff member of its suffix maximum. -/
theorem enorm_finiteBlock_le_suffixMaxOperator
    (lam : ℝ) (j : ℤ) (B : ℕ) (f : L0Infinity) (x : ℝ) :
    ‖finiteQuadraticDyadicBlock lam j B f x‖ₑ ≤
      ‖finiteFullDyadicSuffixMaxOperator lam j (B + 1) f x‖ₑ := by
  have hmem : 0 ∈ Finset.range (B + 1 + 1) := by simp
  have hsup := Finset.le_sup
    (f := fun m ↦ ‖finiteFullDyadicSuffix lam j (B + 1) m f x‖₊) hmem
  have hz : finiteFullDyadicSuffix lam j (B + 1) 0 f x =
      finiteQuadraticDyadicBlock lam j B f x := by
    simp only [finiteFullDyadicSuffix, Nat.cast_zero, add_zero, Nat.sub_zero]
    exact finiteFullDyadicTail_succ_eq_finiteQuadraticDyadicBlock lam j B
      (memLp_two_L0Infinity f) x
  rw [hz] at hsup
  simpa only [finiteFullDyadicSuffixMaxOperator, enorm_eq_nnnorm,
    ENNReal.coe_le_coe, Complex.nnnorm_real, NNReal.nnnorm_eq,
    finiteFullDyadicSuffixMaxNNNorm] using hsup

/-- The exact paper block is controlled by a normalized high suffix and one
modulation-independent maximal-function error. No auxiliary scale choice remains. -/
theorem enorm_paperLowDyadicOperator_le_dilatedHighSuffix_add_maximal
    (lam : ℝ) (hlam : 0 < lam) (B : ℕ) (f : L0Infinity) (x : ℝ) :
    ‖paperLowDyadicOperator lam hlam.ne' B f x‖ₑ ≤
      ‖dilatedOperator (Real.sqrt lam) (Real.sqrt_pos.mpr hlam)
        (finiteFullDyadicSuffixMaxOperator 1 1 (B + 1)) f x‖ₑ +
      48 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  let a := Real.sqrt lam
  have ha : 0 < a := Real.sqrt_pos.mpr hlam
  let j := oscillatoryScaleIndex lam 0 hlam.ne'
  have herr := enorm_block_sub_normalizedHighBlock_le a ha j B f x
    (KrauseLaceyNormalizedBlockRadii.paperBlockLowerRadius_bracket lam hlam)
    (KrauseLaceyNormalizedBlockRadii.paperBlockUpperRadius_bracket lam hlam B)
  have hsquare : a ^ 2 = lam := Real.sq_sqrt hlam.le
  rw [hsquare] at herr
  rw [paperLowDyadicOperator_eq_finiteQuadraticDyadicBlock]
  change ‖finiteQuadraticDyadicBlock lam j B f x‖ₑ ≤ _
  calc
    _ = ‖(finiteQuadraticDyadicBlock lam j B f x -
        finiteQuadraticDyadicBlock 1 1 B (L0Infinity.dilate a ha f) (a * x)) +
        finiteQuadraticDyadicBlock 1 1 B (L0Infinity.dilate a ha f) (a * x)‖ₑ :=
      congrArg (fun z : ℂ ↦ ‖z‖ₑ) (sub_add_cancel _ _).symm
    _ ≤ _ + _ := enorm_add_le _ _
    _ ≤ 48 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x +
        ‖finiteFullDyadicSuffixMaxOperator 1 1 (B + 1)
          (L0Infinity.dilate a ha f) (a * x)‖ₑ :=
      add_le_add herr (enorm_finiteBlock_le_suffixMaxOperator 1 1 B
        (L0Infinity.dilate a ha f) (a * x))
    _ = _ := add_comm _ _


end
end QuadraticCarleson.KrauseLaceyFiniteBlockHighReduction
