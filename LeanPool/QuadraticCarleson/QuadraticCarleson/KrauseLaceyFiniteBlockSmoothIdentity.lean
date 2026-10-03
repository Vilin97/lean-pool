/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySharpSmoothAdapter

/-!
# Finite dyadic blocks as exact smooth high-pass differences

The sharp truncation boundary terms cancel in a consecutive smooth dyadic
block. This identity also applies to the paper's modulation-dependent low
block, without a pointwise majorization or any loss in constants.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyFiniteBlockSmoothIdentity

open KrauseLaceySharpSmoothAdapter


noncomputable
section

theorem finiteQuadraticDyadicBlock_eq_smoothHighPass_sub
    (lam : ℝ) (j : ℤ) (B : ℕ) {f : ℝ → ℂ} (hfi : Integrable f) (x : ℝ) :
    finiteQuadraticDyadicBlock lam j B f x =
      smoothQuadraticHighPass lam ((2 : ℝ) ^ (j - 3)) f x -
        smoothQuadraticHighPass lam ((2 : ℝ) ^ (j + (B : ℤ) - 2)) f x := by
  rw [finiteQuadraticDyadicBlock_eq_truncations_add_boundaries lam j B hfi,
    quadraticHilbertTrunc_eq_smoothHighPass_add_boundary lam
      (zpow_pos (by norm_num : (0 : ℝ) < 2) _) hfi,
    quadraticHilbertTrunc_eq_smoothHighPass_add_boundary lam
      (zpow_pos (by norm_num : (0 : ℝ) < 2) _) hfi]
  ring

theorem paperLowDyadicOperator_eq_smoothHighPass_sub
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) (f : L0Infinity) (x : ℝ) :
    paperLowDyadicOperator lam hlam B f x =
      smoothQuadraticHighPass lam
        ((2 : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam - 3)) f x -
      smoothQuadraticHighPass lam
        ((2 : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam + (B : ℤ) - 2)) f x := by
  rw [paperLowDyadicOperator_eq_finiteQuadraticDyadicBlock]
  exact finiteQuadraticDyadicBlock_eq_smoothHighPass_sub
    lam (oscillatoryScaleIndex lam 0 hlam) B f.integrable x


end
end KrauseLaceyFiniteBlockSmoothIdentity
end QuadraticCarleson
