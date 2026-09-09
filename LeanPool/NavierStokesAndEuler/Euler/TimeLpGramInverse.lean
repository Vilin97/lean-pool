/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramPath
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientGevrey

@[expose] public section

/-!
# The actual Gram inverse on Bochner L²

The multiplier Gram operator inherits the pointwise lower frame bound.
Its coercive inverse equals multiplication by the previously constructed
matrix/Hilbert Gram inverse. This identifies the strong-equation inverse
with the same operator to which the genuine parameter estimates apply.
-/

noncomputable section

open scoped ContDiff

namespace EulerTimeLpGramInverse

open Set MeasureTheory InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerVolterraConvolution EulerTransverseGramInverse
  EulerTransverseGramPath EulerCoerciveProjection EulerTimeLpCoefficientMap
  EulerTimeLpCoefficientGevrey EulerOperatorGevreyCalculus EulerGevrey

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The genuine Bochner Gram operator, formed from the actual frame multiplier. -/
def gramOperator (T : ℝ) (hT : 0 ≤ T) (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E)) :
    TimeLp T U →L[ℝ] TimeLp T U :=
  (timeMultiplier T hT Q).adjoint.comp (timeMultiplier T hT Q)

/-- The pointwise lower frame bound gives coercivity on the actual time-L² space. -/
theorem gramOperator_coercive (T : ℝ) (hT : 0 ≤ T)
    (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (c : ℝ)
    (hQ : ∀ t v, c*‖v‖^2 ≤ ‖Q t v‖^2) (u : TimeLp T U) :
    c*‖u‖^2 ≤ ⟪gramOperator T hT Q u, u⟫_ℝ := by
  calc
    c*‖u‖^2 = c*⟪u,u⟫_ℝ := by rw [real_inner_self_eq_norm_sq]
    _ ≤ ⟪timeMultiplier T hT Q u, timeMultiplier T hT Q u⟫_ℝ := by
      rw [L2.inner_def, L2.inner_def, ← integral_const_mul]
      apply integral_mono_ae ((L2.integrable_inner u u).const_mul c)
        (L2.integrable_inner (timeMultiplier T hT Q u) (timeMultiplier T hT Q u))
      filter_upwards [timeMultiplier_ae T hT Q u] with t ht
      rw [ht, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      exact hQ (projIcc 0 T hT t) (u t)
    _ = ⟪gramOperator T hT Q u,u⟫_ℝ := by
      simp only [gramOperator, comp_apply, adjoint_inner_left]

/-- The actual coercive inverse of the time Gram operator. -/
def gramSolver (T : ℝ) (hT : 0 ≤ T)
    (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ t v, c*‖v‖^2 ≤ ‖Q t v‖^2) : TimeLp T U →L[ℝ] TimeLp T U :=
  coerciveInverse (gramOperator T hT Q) c hc (gramOperator_coercive T hT Q c hQ)

/-- The Gram operator is pointwise `Q*Q`, with genuine Bochner representatives. -/
theorem gramOperator_ae (T : ℝ) (hT : 0 ≤ T)
    (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (u : TimeLp T U) :
    ∀ᵐ t ∂timeMeasure T, gramOperator T hT Q u t =
      (Q (projIcc 0 T hT t)).adjoint (Q (projIcc 0 T hT t) (u t)) := by
  simp only [gramOperator, comp_apply, timeMultiplier_adjoint]
  filter_upwards [timeMultiplier_ae T hT (adjointPath T Q) (timeMultiplier T hT Q u),
    timeMultiplier_ae T hT Q u] with t hA hQ
  rw [hA, hQ]
  rfl

/-- The actual coercive inverse equals the pointwise inverse used in the strong equation. -/
theorem gramSolver_eq_multiplier (T : ℝ) (hT : 0 ≤ T)
    (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ t v, c*‖v‖^2 ≤ ‖Q t v‖^2) :
    gramSolver T hT Q c hc hQ = timeMultiplier T hT (gramInversePath T Q c hc hQ) := by
  apply ContinuousLinearMap.ext
  intro f
  have he : gramOperator T hT Q (timeMultiplier T hT (gramInversePath T Q c hc hQ) f) = f := by
    apply Lp.ext
    filter_upwards [gramOperator_ae T hT Q (timeMultiplier T hT (gramInversePath T Q c hc hQ) f),
      timeMultiplier_ae T hT (gramInversePath T Q c hc hQ) f] with t hg hb
    rw [hg, hb]
    exact gram_inverse_apply (Q (projIcc 0 T hT t)) c hc (hQ _) (f t)
  have hi := inverse_operator_apply (gramOperator T hT Q) c hc
    (gramOperator_coercive T hT Q c hQ) (timeMultiplier T hT (gramInversePath T Q c hc hQ) f)
  rw [he] at hi
  exact hi

/-- The lower frame bound controls the true operator inverse. -/
theorem gramSolver_norm (T : ℝ) (hT : 0 ≤ T)
    (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ t v, c*‖v‖^2 ≤ ‖Q t v‖^2) :
    ‖gramSolver T hT Q c hc hQ‖ ≤ c⁻¹ :=
  coerciveInverse_norm_le (gramOperator T hT Q) c hc (gramOperator_coercive T hT Q c hQ)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Actual smoothness of the time Gram operator follows from the coefficient path. -/
theorem gramOperator_contDiff (T : ℝ) (hT : 0 ≤ T)
    (Q : P → C(Icc (0 : ℝ) T, U →L[ℝ] E)) {n : ℕ∞ω} (hQ : ContDiff ℝ n Q) :
    ContDiff ℝ n (fun x => gramOperator T hT (Q x)) := by
  have hM := contDiff_timeMultiplier T hT Q hQ
  exact ((realAdjoint (U := TimeLp T U) (E := TimeLp T E)).contDiff.comp hM).clm_comp hM

/-- The actual Gram coefficient jets have a polynomial factorial multiplier constant. -/
theorem gramOperator_bound (T : ℝ) (hT : 0 ≤ T)
    (Q : P → C(Icc (0 : ℝ) T, U →L[ℝ] E)) (hQ : ContDiff ℝ ∞ Q)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C*majorant R 0 n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => gramOperator T hT (Q y)) x‖ ≤
      (3*C^2)*majorant R 0 n := by
  let M := fun y => timeMultiplier T hT (Q y)
  have hM : ContDiff ℝ ∞ M := contDiff_timeMultiplier T hT Q hQ
  have hb := timeMultiplier_bound T hT Q hQ R C hR hC 0 hbQ
  have h := clm_comp_bound (fun y => (M y).adjoint) M
    ((realAdjoint (U := TimeLp T U) (E := TimeLp T E)).contDiff.comp hM) hM
    R C C hR hC hC 0 0 (adjoint_bound M hM R C hR hC 0 hb) hb n x
  have he : 3*C*C = 3*C^2 := by ring
  simp only [Nat.add_zero, he] at h
  convert h using 1
  rfl

end EulerTimeLpGramInverse
