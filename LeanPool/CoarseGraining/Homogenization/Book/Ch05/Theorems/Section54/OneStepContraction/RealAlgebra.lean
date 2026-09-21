/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.Basic

/-! # Real Algebra -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace OneStepContraction

noncomputable section

/-!
# Real algebra for the one-step contraction

The final proof chooses `epsilon = delta^(1/4)`.  This file isolates the
elementary estimates for that choice.
-/

/-- The one-step epsilon is positive for positive `delta`. -/
theorem oneStepContractionEpsilon_pos {delta : ℝ} (hdelta_pos : 0 < delta) :
    0 < oneStepContractionEpsilon delta := by
  dsimp [oneStepContractionEpsilon]
  exact Real.rpow_pos_of_pos hdelta_pos _

/-- The one-step epsilon is nonnegative for nonnegative `delta`. -/
theorem oneStepContractionEpsilon_nonneg {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) :
    0 ≤ oneStepContractionEpsilon delta := by
  dsimp [oneStepContractionEpsilon]
  exact Real.rpow_nonneg hdelta_nonneg _

/-- In the manuscript range, the one-step epsilon is at most one. -/
theorem oneStepContractionEpsilon_le_one {delta : ℝ}
    (hdelta_pos : 0 < delta) (hdelta_le_half : delta ≤ 1 / 2) :
    oneStepContractionEpsilon delta ≤ 1 := by
  dsimp [oneStepContractionEpsilon]
  exact Real.rpow_le_one hdelta_pos.le (by linarith) (by norm_num)

/-- The square root dominates `delta` on the manuscript range. -/
theorem delta_le_sqrt_of_pos_of_le_half {delta : ℝ}
    (hdelta_pos : 0 < delta) (hdelta_le_half : delta ≤ 1 / 2) :
    delta ≤ Real.sqrt delta := by
  have hdelta_le_one : delta ≤ 1 := by linarith
  have hsq : delta ^ (2 : ℕ) ≤ (Real.sqrt delta) ^ (2 : ℕ) := by
    rw [Real.sq_sqrt hdelta_pos.le]
    nlinarith
  exact (sq_le_sq₀ hdelta_pos.le (Real.sqrt_nonneg delta)).1 hsq

/-- The quarter power dominates the square root when `0 < delta <= 1`. -/
theorem sqrt_le_oneStepContractionEpsilon {delta : ℝ}
    (hdelta_pos : 0 < delta) (hdelta_le_half : delta ≤ 1 / 2) :
    Real.sqrt delta ≤ oneStepContractionEpsilon delta := by
  have hdelta_le_one : delta ≤ 1 := by linarith
  calc
    Real.sqrt delta = Real.rpow delta (1 / 2 : ℝ) := Real.sqrt_eq_rpow delta
    _ ≤ Real.rpow delta (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one (by norm_num)
    _ = oneStepContractionEpsilon delta := by
      rfl

/-- The quarter power dominates `delta` on the manuscript range. -/
theorem delta_le_oneStepContractionEpsilon {delta : ℝ}
    (hdelta_pos : 0 < delta) (hdelta_le_half : delta ≤ 1 / 2) :
    delta ≤ oneStepContractionEpsilon delta :=
  (delta_le_sqrt_of_pos_of_le_half hdelta_pos hdelta_le_half).trans
    (sqrt_le_oneStepContractionEpsilon hdelta_pos hdelta_le_half)

/-- With `epsilon = delta^(1/4)`, the product `epsilon^{-1} sqrt(delta)`
is again `epsilon`. -/
theorem oneStepContractionEpsilon_inv_mul_sqrt_eq {delta : ℝ}
    (hdelta_pos : 0 < delta) :
    (oneStepContractionEpsilon delta)⁻¹ * Real.sqrt delta =
      oneStepContractionEpsilon delta := by
  have hinv :
      (Real.rpow delta (1 / 4 : ℝ))⁻¹ =
        Real.rpow delta (-(1 / 4 : ℝ)) := by
    simpa using (Real.rpow_neg hdelta_pos.le (1 / 4 : ℝ)).symm
  calc
    (oneStepContractionEpsilon delta)⁻¹ * Real.sqrt delta =
        Real.rpow delta (-(1 / 4 : ℝ)) * Real.rpow delta (1 / 2 : ℝ) := by
          rw [oneStepContractionEpsilon, hinv]
          exact congrArg
            (fun z : ℝ => Real.rpow delta (-(1 / 4 : ℝ)) * z)
            (Real.sqrt_eq_rpow delta)
    _ = Real.rpow delta (-(1 / 4 : ℝ) + 1 / 2) := by
          exact
            (Real.rpow_add hdelta_pos (-(1 / 4 : ℝ)) (1 / 2 : ℝ)).symm
    _ = oneStepContractionEpsilon delta := by
          norm_num [oneStepContractionEpsilon]

/-- The final epsilon absorption used after the Section 5.3 estimate. -/
theorem oneStepContractionEpsilon_add_inv_mul_sqrt_le
    {delta : ℝ} (hdelta_pos : 0 < delta) :
    oneStepContractionEpsilon delta +
        (oneStepContractionEpsilon delta)⁻¹ * Real.sqrt delta ≤
      2 * oneStepContractionEpsilon delta := by
  rw [oneStepContractionEpsilon_inv_mul_sqrt_eq hdelta_pos]
  ring_nf
  exact le_rfl

end

end OneStepContraction
end Section54
end Ch05
end Book
end Homogenization
