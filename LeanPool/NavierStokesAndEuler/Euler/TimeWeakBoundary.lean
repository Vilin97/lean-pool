/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeWeakDerivative

@[expose] public section

/-!
# Recovering the actual initial trace from a full time weak identity

The terminal primitive and its exact integration-by-parts identity identify
both an absolutely continuous representative and its initial trace.  The
boundary value is a conclusion of testing against all terminal-zero H¹ paths.
-/

noncomputable section

namespace EulerTimeWeakBoundary

open MeasureTheory Set InnerProductSpace EulerTimeLp EulerTerminalTimePrimitive
  EulerTimeWeakDerivative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The full weak identity determines the integration constant explicitly. -/
theorem weak_boundary_eq_primitive_add_constant (T : ℝ) (hT : 0 ≤ T)
    (p h : TimeLp T E) (b : E)
    (hweak : ∀ v : TimeLp T E,
      ⟪p, v⟫_ℝ + ⟪h, primitiveTimeLp T hT v⟫_ℝ + ⟪b, initialTrace T hT v⟫_ℝ = 0) :
    p = primitiveTimeLp T hT h + constantField T hT (b-initialTrace T hT h) := by
  apply ext_inner_right ℝ
  intro v
  have hp := hweak v
  have hj := primitive_inner_identity T hT h v
  rw [inner_add_left, constantField_inner, inner_sub_left]
  linarith only [hp, hj]

/-- The actual AC representative with the boundary value forced by the weak form. -/
def boundaryRepresentative (T : ℝ) (hT : 0 ≤ T) (h : TimeLp T E) (b : E) : ℝ → E :=
  fun t => realPrimitive T h t + (b-initialTrace T hT h)

omit [CompleteSpace E] in
/-- This representative has precisely the initial value appearing in the weak form. -/
@[simp] theorem boundaryRepresentative_initial (T : ℝ) (hT : 0 ≤ T) (h : TimeLp T E) (b : E) :
    boundaryRepresentative T hT h b 0 = b := by
  change initialTrace T hT h + (b-initialTrace T hT h) = b
  abel

omit [CompleteSpace E] in
/-- The explicitly reconstructed representative is genuinely absolutely continuous. -/
theorem boundaryRepresentative_absolutelyContinuous (T : ℝ) (hT : 0 ≤ T)
    (h : TimeLp T E) (b : E) :
    AbsolutelyContinuousOnInterval (boundaryRepresentative T hT h b) 0 T :=
  (realPrimitive_absolutelyContinuous T h).add
    ((LipschitzWith.const (b-initialTrace T hT h)).lipschitzOnWith.absolutelyContinuousOnInterval)

/-- Its a.e. derivative is the actual L² field in the weak identity. -/
theorem boundaryRepresentative_hasDerivAt_ae (T : ℝ) (hT : 0 ≤ T) (h : TimeLp T E) (b : E) :
    ∀ᵐ t ∂timeMeasure T, HasDerivAt (boundaryRepresentative T hT h b) (h t) t := by
  filter_upwards [realPrimitive_hasDerivAt_ae T h] with t ht
  exact ht.add_const (b-initialTrace T hT h)

/-- The full weak identity identifies its original L² field with this actual
representative, not merely with a formal boundary functional. -/
theorem weak_boundary_representation (T : ℝ) (hT : 0 ≤ T) (p h : TimeLp T E) (b : E)
    (hweak : ∀ v : TimeLp T E,
      ⟪p, v⟫_ℝ + ⟪h, primitiveTimeLp T hT v⟫_ℝ + ⟪b, initialTrace T hT v⟫_ℝ = 0) :
    (p : ℝ → E) =ᵐ[timeMeasure T] boundaryRepresentative T hT h b := by
  rw [weak_boundary_eq_primitive_add_constant T hT p h b hweak]
  filter_upwards [Lp.coeFn_add (primitiveTimeLp T hT h)
      (constantField T hT (b-initialTrace T hT h)),
    primitiveTimeLp_ae T hT h, constantField_ae T hT (b-initialTrace T hT h)]
    with t hadd hj hc
  simpa only [Pi.add_apply, boundaryRepresentative, hj, hc] using hadd

/-- Existence of a genuine AC representative with the derived initial trace and
prescribed a.e. derivative; this also covers the degenerate zero-length interval. -/
theorem exists_ac_representative_with_initial (T : ℝ) (hT : 0 ≤ T)
    (p h : TimeLp T E) (b : E)
    (hweak : ∀ v : TimeLp T E,
      ⟪p, v⟫_ℝ + ⟪h, primitiveTimeLp T hT v⟫_ℝ + ⟪b, initialTrace T hT v⟫_ℝ = 0) :
    ∃ η : ℝ → E, AbsolutelyContinuousOnInterval η 0 T ∧ η 0 = b ∧
      (p : ℝ → E) =ᵐ[timeMeasure T] η ∧
      ∀ᵐ t ∂timeMeasure T, HasDerivAt η (h t) t :=
  ⟨boundaryRepresentative T hT h b, boundaryRepresentative_absolutelyContinuous T hT h b,
    boundaryRepresentative_initial T hT h b, weak_boundary_representation T hT p h b hweak,
    boundaryRepresentative_hasDerivAt_ae T hT h b⟩

end EulerTimeWeakBoundary
