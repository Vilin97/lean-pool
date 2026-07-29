/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.SelectedHeightQuadraticGrowth

/-!
# Selected Height Sequence

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter NumberField Set
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A completed zeta selected height used in the Odlyzko-bound argument. -/
noncomputable def completedZetaSelectedHeight (n : ℕ) : ℝ :=
  Classical.choose
    (exists_height_norm_logDeriv_poleClearedCompletedZeta_le_quadratic
      K (A := (n : ℝ) + 6) (by norm_num))

open Classical in
theorem completedZetaSelectedHeight_spec (n : ℕ) :
    (n : ℝ) + 6 < completedZetaSelectedHeight K n ∧
      completedZetaSelectedHeight K n < (n : ℝ) + 7 ∧
      ∀ x ∈ Icc (-1 : ℝ) 5,
        (poleClearedCompletedDedekindZetaContinuation K
            (x + completedZetaSelectedHeight K n * I) ≠ 0 ∧
          ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K)
              (x + completedZetaSelectedHeight K n * I)‖ ≤
            completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K *
              ((n : ℝ) + 7) ^ 2) ∧
        (poleClearedCompletedDedekindZetaContinuation K
            (x - completedZetaSelectedHeight K n * I) ≠ 0 ∧
          ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K)
              (x - completedZetaSelectedHeight K n * I)‖ ≤
            completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K *
              ((n : ℝ) + 7) ^ 2) := by
  simpa [completedZetaSelectedHeight,
    show (n : ℝ) + 6 + 1 = (n : ℝ) + 7 by ring] using
      (Classical.choose_spec
        (exists_height_norm_logDeriv_poleClearedCompletedZeta_le_quadratic
          K (A := (n : ℝ) + 6) (by norm_num)))

open Classical in
theorem completedZetaSelectedHeight_pos (n : ℕ) :
    0 < completedZetaSelectedHeight K n := by
  linarith [(completedZetaSelectedHeight_spec K n).1]

open Classical in
theorem tendsto_completedZetaSelectedHeight_atTop :
    Tendsto (completedZetaSelectedHeight K) atTop atTop := by
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall fun n ↦
      (completedZetaSelectedHeight_spec K n).1.le)
    (tendsto_atTop_add_const_right atTop 6
      (tendsto_natCast_atTop_atTop (R := ℝ)))

end NumberField.Odlyzko
