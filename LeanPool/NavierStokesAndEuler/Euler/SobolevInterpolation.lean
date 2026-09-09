/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevSpace
import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevOperators
import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedWeakDerivative

/-! Strong-derivative interpolation on the actual cylinder Sobolev spaces. -/

@[expose] public section


noncomputable section

namespace EulerSobolevInterpolation

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity EulerLiftedWeakDerivative
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- One genuine derivative is controlled by its parent word and one available higher derivative. -/
theorem word_square_le_parent {s n : ℕ} (h : n + 2 ≤ s) (u : SobolevSpace period s)
    (w : Fin n → Fin 4) (i : Fin 4) :
    ‖word period u (by omega : n+1 ≤ s) (Fin.cons i w)‖^2 ≤
      ‖word period u (by omega : n ≤ s) w‖*‖u‖ := by
  have hp := translation_derivative_pairing period (standardDirection i)
    (word period u (by omega : n ≤ s) w)
    (word period u (by omega : n+1 ≤ s) (Fin.cons i w))
    (word period u (by omega : n+1 ≤ s) (Fin.cons i w))
    (word period u h (Fin.cons i (Fin.cons i w)))
    (word_hasDerivAt period u (by omega : n < s) w i)
    (word_hasDerivAt period u (by omega : n+1 < s) (Fin.cons i w) i)
  rw [real_inner_self_eq_norm_sq] at hp
  calc
    _ = -inner ℝ (word period u (by omega : n ≤ s) w)
        (word period u h (Fin.cons i (Fin.cons i w))) := hp
    _ ≤ |inner ℝ (word period u (by omega : n ≤ s) w)
        (word period u h (Fin.cons i (Fin.cons i w)))| := neg_le_abs _
    _ ≤ ‖word period u (by omega : n ≤ s) w‖*
        ‖word period u h (Fin.cons i (Fin.cons i w))‖ := abs_real_inner_le_norm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (word_norm_le period u ⟨⟨n+2,Nat.lt_succ_of_le h⟩,Fin.cons i (Fin.cons i w)⟩) (norm_nonneg _)

end EulerSobolevInterpolation
