/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.InitialTimePrimitive
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1FieldProduct
public import LeanPool.NavierStokesAndEuler.Euler.TimeWeakDerivative

@[expose] public section

/-!
Initial-zero versions of the actual H¹ product and reconstruction lemmas.
These permit nonzero terminal values and hence explicit affine coordinate
lifts in the fixed-space endpoint problem.
-/

noncomputable section

namespace EulerInitialTimePrimitive

open MeasureTheory Set ContinuousLinearMap EulerTimeLp EulerTerminalTimePrimitive
  EulerVolterraConvolution EulerTimeH1OperatorProduct EulerTimeH1FieldProduct
  EulerTimeWeakDerivative

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem eq_initialRealPrimitive_of_ac_hasDerivAt_ae
    (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E) (η : ℝ → E)
    (hη : AbsolutelyContinuousOnInterval η 0 T)
    (hder : ∀ᵐ t ∂timeMeasure T, HasDerivAt η (u t) t)
    (hzero : η 0 = 0) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    η t = initialRealPrimitive T u t := by
  have hd : ∀ᵐ s ∂timeMeasure T, HasDerivAt (fun r => η r - η T) (u s) s := by
    filter_upwards [hder] with s hs
    exact hs.sub_const _
  have he := eq_realPrimitive_of_ac_hasDerivAt_ae T hT u (fun r => η r - η T)
    (hη.sub ((LipschitzWith.const (η T)).lipschitzOnWith.absolutelyContinuousOnInterval))
    hd (sub_self _)
  have h₀ := he 0 ⟨le_rfl, hT⟩
  change η t = realPrimitive T u t - realPrimitive T u 0
  rw [← he t ht, ← h₀, hzero]
  abel

omit [CompleteSpace E] in
theorem initialPrimitiveTimeLp_eq_primitive_of_trace_zero
    (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E) (hu : initialTrace T hT u = 0) :
    initialPrimitiveTimeLp T hT u = primitiveTimeLp T hT u := by
  have h₀ : realPrimitive T u 0 = 0 := hu
  apply Lp.ext
  filter_upwards [initialPrimitiveTimeLp_ae T hT u, primitiveTimeLp_ae T hT u]
    with t hi ht
  rw [hi, ht, initialRealPrimitive, h₀, sub_zero]

variable (T : ℝ) (hT : 0 ≤ T) (A A₁ : C(Icc (0 : ℝ) T, E →L[ℝ] F))

def initialProductDerivative : TimeLp T E →L[ℝ] TimeLp T F :=
  (timeMultiplier T hT A₁).comp (initialPrimitiveTimeLp T hT) + timeMultiplier T hT A

def initialProductPrimitive (u : TimeLp T E) (t : ℝ) : F :=
  extendPath T hT A t (initialRealPrimitive T u t)

omit [CompleteSpace E] [CompleteSpace F] in
theorem initialProductDerivative_ae (u : TimeLp T E) :
    (initialProductDerivative T hT A A₁ u : ℝ → F) =ᵐ[timeMeasure T]
      fun t => extendPath T hT A₁ t (initialRealPrimitive T u t) + extendPath T hT A t (u t) := by
  filter_upwards [fieldProductDerivative_ae T hT A A₁ (initialPrimitiveTimeLp T hT u) u,
    initialPrimitiveTimeLp_ae T hT u] with t hd hu
  change fieldProductDerivative T hT A A₁ (initialPrimitiveTimeLp T hT u) u t = _
  rw [hd, hu]

variable (hd : ∀ t : Icc (0 : ℝ) T,
  HasDerivWithinAt (extendPath T hT A) (A₁ t) (Icc (0 : ℝ) T) t)

include hd in
omit [CompleteSpace E] [CompleteSpace F] in
theorem initialProductPrimitive_absolutelyContinuous (u : TimeLp T E) :
    AbsolutelyContinuousOnInterval (initialProductPrimitive T hT A u) 0 T :=
  clm_apply_absolutelyContinuous (operatorPath_absolutelyContinuous T hT A A₁ hd)
    (initialRealPrimitive_absolutelyContinuous T u)

include hd in
omit [CompleteSpace F] in
theorem initialProductPrimitive_hasDerivAt_ae (u : TimeLp T E) :
    ∀ᵐ t ∂timeMeasure T,
      HasDerivAt (initialProductPrimitive T hT A u) (initialProductDerivative T hT A A₁ u t) t :=
  fieldProduct_hasDerivAt_ae T hT A A₁ hd (initialPrimitiveTimeLp T hT u) u
    (initialRealPrimitive T u) (initialPrimitiveTimeLp_ae T hT u)
    (initialRealPrimitive_hasDerivAt_ae T u)

include hd in
theorem initialPrimitive_initialProductDerivative (u : TimeLp T E) (t : Icc (0 : ℝ) T) :
    initialPrimitive T hT (initialProductDerivative T hT A A₁ u) t =
      A t (initialPrimitive T hT u t) := by
  have he := eq_initialRealPrimitive_of_ac_hasDerivAt_ae T hT
    (initialProductDerivative T hT A A₁ u) (initialProductPrimitive T hT A u)
    (initialProductPrimitive_absolutelyContinuous T hT A A₁ hd u)
    (initialProductPrimitive_hasDerivAt_ae T hT A A₁ hd u)
    (by simp only [initialProductPrimitive, initialRealPrimitive_initial, map_zero]) t t.property
  simpa only [initialProductPrimitive, extendPath, projIcc_of_mem hT t.property,
    initialPrimitive_apply] using he.symm

omit [CompleteSpace E] [CompleteSpace F] in
theorem initialProductDerivative_eq_product_of_trace_zero (u : TimeLp T E)
    (hu : initialTrace T hT u = 0) :
    initialProductDerivative T hT A A₁ u = productDerivative T hT A A₁ u := by
  change timeMultiplier T hT A₁ (initialPrimitiveTimeLp T hT u) + timeMultiplier T hT A u = _
  rw [initialPrimitiveTimeLp_eq_primitive_of_trace_zero T hT u hu]
  rfl

/-- Constants embedded as a genuine bounded operator into time L². -/
def constantFieldOperator : E →L[ℝ] TimeLp T E :=
  (pathLpOperator T hT).comp (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T))

omit [CompleteSpace E] in
theorem constantFieldOperator_ae (x : E) :
    (constantFieldOperator T hT x : ℝ → E) =ᵐ[timeMeasure T] fun _ => x :=
  pathLp_ae T hT (ContinuousMap.const (Icc (0 : ℝ) T) x)

theorem initialPrimitive_constantFieldOperator (x : E) (t : Icc (0 : ℝ) T) :
    initialPrimitive T hT (constantFieldOperator T hT x) t = (t : ℝ) • x := by
  have hlin : AbsolutelyContinuousOnInterval (fun s : ℝ => s • x) 0 T :=
    (toSpanSingleton ℝ x).lipschitzWith.lipschitzOnWith.absolutelyContinuousOnInterval
  apply Eq.symm
  apply eq_initialRealPrimitive_of_ac_hasDerivAt_ae T hT (constantFieldOperator T hT x)
    (fun s : ℝ => s • x) hlin _ (zero_smul ℝ x) t t.property
  filter_upwards [constantFieldOperator_ae T hT x] with s hs
  rw [hs]
  simpa only [id_eq, one_smul] using (hasDerivAt_id s).smul_const x

end EulerInitialTimePrimitive
