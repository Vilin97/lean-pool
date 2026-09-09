/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
import LeanPool.NavierStokesAndEuler.Euler.FiniteQuadraticCauchy
import LeanPool.NavierStokesAndEuler.Euler.TopBlockTimeNorm

/-! Actual strong L²-time completion from finitely many closed derivative blocks. -/

@[expose] public section


noncomputable section

namespace EulerTopBlockTimeNorm

open MeasureTheory Set EulerTimeLp EulerVolterraConvolution
open scoped Topology

variable {X Y Z I : Type*} [Fintype I]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Bounded spatial observation and actual time embedding preserve subtraction together. -/
theorem mapped_pathLp_sub (T : ℝ) (hT : 0 ≤ T) (A : X →L[ℝ] Y)
    (u v : C(Icc (0 : ℝ) T, X)) :
    pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) (u-v)) =
      pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) u) -
      pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) v) :=
  (congrArg (pathLp T hT) (map_sub (A.compLeftContinuous ℝ (Icc (0 : ℝ) T)) u v)).trans
    (pathLp_sub T hT _ _)

/-- The integrated genuine spatial block bound also controls time-space differences. -/
theorem pathLp_quadratic_difference (A : X →L[ℝ] Y) (B : I → X →L[ℝ] Z)
    (hb : ∀ x, ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 + ∑ i, ‖B i x‖ ^ 2)
    (T : ℝ) (hT : 0 ≤ T) (u v : C(Icc (0 : ℝ) T, X)) :
    ‖pathLp T hT u-pathLp T hT v‖^2 ≤
      ‖pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) u) -
        pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) v)‖^2 +
      ∑ i, ‖pathLp T hT ((B i).compLeftContinuous ℝ (Icc (0 : ℝ) T) u) -
        pathLp T hT ((B i).compLeftContinuous ℝ (Icc (0 : ℝ) T) v)‖^2 := by
  have h := pathLp_quadratic_bound A B hb T hT (u-v)
  simp only [pathLp_sub, mapped_pathLp_sub] at h
  exact h

/-- Genuine finite block convergence and lower-order convergence construct strong convergence in the
full Bochner Sobolev space. -/
theorem cauchy_pathLp_of_blocks (A : X →L[ℝ] Y) (B : I → X →L[ℝ] Z)
    (hb : ∀ x, ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 + ∑ i, ‖B i x‖ ^ 2)
    (T : ℝ) (hT : 0 ≤ T) (u : ℕ → C(Icc (0 : ℝ) T, X))
    (hu : CauchySeq (fun n => pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) (u n))))
    (hf : ∀ i, CauchySeq (fun n => pathLp T hT ((B i).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u n))))
        :
    CauchySeq (fun n => pathLp T hT (u n)) := by
  exact EulerQuadraticCauchy.cauchy_of_finite_quadratic_bound _ _ _ hu hf
    (fun n m => pathLp_quadratic_difference A B hb T hT (u n) (u m))

end EulerTopBlockTimeNorm
