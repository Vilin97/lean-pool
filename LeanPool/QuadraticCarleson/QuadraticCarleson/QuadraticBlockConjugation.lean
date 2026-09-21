/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySparseDilation

/-!
# Conjugation of finite quadratic blocks

Changing the sign of a nonzero modulation leaves its selected spatial scales
unchanged. Since the dyadic cutoff is real, conjugating the input therefore
turns the negative-modulation block exactly into the conjugate of the
positive-modulation block.
-/

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace QuadraticCarleson.QuadraticBlockConjugation


noncomputable
section

/-- The paper's selected spatial scales depend only on absolute modulation. -/
theorem oscillatoryScaleIndex_neg (lam : ℝ) (hlam : lam ≠ 0) (r : ℕ) :
    oscillatoryScaleIndex (-lam) r (neg_ne_zero.mpr hlam) =
      oscillatoryScaleIndex lam r hlam := by
  apply oscillatoryScaleIndex_unique lam r hlam
  simpa only [OscillatoryScaleSpec, abs_neg] using
    oscillatoryScaleIndex_spec (-lam) r (neg_ne_zero.mpr hlam)

theorem lowOscillatoryKernel_neg_eq_conj
    (lam : ℝ) (B : ℕ) (J : ℕ → ℤ) (t : ℝ) :
    lowOscillatoryKernel (-lam) B J t = conj (lowOscillatoryKernel lam B J t) := by
  simp only [lowOscillatoryKernel, map_sum, map_mul, Complex.conj_ofReal,
    ← phase_neg_eq_conj, neg_mul]

/-- Exact conjugation for a finite block, under the total integral convention. -/
theorem finiteQuadraticDyadicBlock_neg_eq_conj
    (lam : ℝ) (j : ℤ) (B : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    finiteQuadraticDyadicBlock (-lam) j B f x =
      conj (finiteQuadraticDyadicBlock lam j B (fun y ↦ conj (f y)) x) := by
  unfold finiteQuadraticDyadicBlock
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with y
  simp [lowOscillatoryKernel_neg_eq_conj]

/-- The actual paper block changes modulation sign by conjugating the input. -/
theorem paperLowDyadicOperator_neg_eq_conj
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) (f : L0Infinity) (x : ℝ) :
    paperLowDyadicOperator (-lam) (neg_ne_zero.mpr hlam) B f x =
      conj (paperLowDyadicOperator lam hlam B (L0Infinity.conjugate f) x) := by
  rw [paperLowDyadicOperator_eq_finiteQuadraticDyadicBlock,
    paperLowDyadicOperator_eq_finiteQuadraticDyadicBlock,
    oscillatoryScaleIndex_neg, finiteQuadraticDyadicBlock_neg_eq_conj]
  rfl

theorem norm_paperLowDyadicOperator_neg
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) (f : L0Infinity) (x : ℝ) :
    ‖paperLowDyadicOperator (-lam) (neg_ne_zero.mpr hlam) B f x‖ =
      ‖paperLowDyadicOperator lam hlam B (L0Infinity.conjugate f) x‖ := by
  rw [paperLowDyadicOperator_neg_eq_conj, Complex.norm_conj]

theorem enorm_paperLowDyadicOperator_neg
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) (f : L0Infinity) (x : ℝ) :
    ‖paperLowDyadicOperator (-lam) (neg_ne_zero.mpr hlam) B f x‖ₑ =
      ‖paperLowDyadicOperator lam hlam B (L0Infinity.conjugate f) x‖ₑ := by
  simpa only [ofReal_norm] using
    congrArg ENNReal.ofReal (norm_paperLowDyadicOperator_neg lam hlam B f x)


end
end QuadraticCarleson.QuadraticBlockConjugation
