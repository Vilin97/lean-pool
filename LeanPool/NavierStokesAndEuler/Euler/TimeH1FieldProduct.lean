/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeH1OperatorProduct

@[expose] public section

/-!
# Operator products of genuine H¹ fields with arbitrary terminal trace

Unlike a terminal primitive, a momentum field need not vanish at the final time.
This file constructs the derivative of a C¹ coefficient times any actual AC
representative with Bochner L² value and derivative classes.
-/

noncomputable section

namespace EulerTimeH1FieldProduct

open MeasureTheory Set Filter EulerTimeLp EulerTerminalTimePrimitive
  EulerVolterraConvolution EulerTimeH1OperatorProduct

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (T : ℝ) (hT : 0 ≤ T)
  (A A' : C(Icc (0 : ℝ) T, E →L[ℝ] F))

/-- The product derivative is constructed in the actual L² space. -/
def fieldProductDerivative (p q : TimeLp T E) : TimeLp T F :=
  timeMultiplier T hT A' p + timeMultiplier T hT A q

/-- The constructed derivative is the pointwise Leibniz expression a.e. -/
theorem fieldProductDerivative_ae (p q : TimeLp T E) :
    (fieldProductDerivative T hT A A' p q : ℝ → F) =ᵐ[timeMeasure T]
      fun t => extendPath T hT A' t (p t) + extendPath T hT A t (q t) := by
  filter_upwards [Lp.coeFn_add (timeMultiplier T hT A' p) (timeMultiplier T hT A q),
    timeMultiplier_ae T hT A' p, timeMultiplier_ae T hT A q] with t hadd hp hq
  simp only [Pi.add_apply] at hadd
  change (timeMultiplier T hT A' p + timeMultiplier T hT A q) t = _
  rw [hadd, hp, hq]

/-- The actual Bochner product has the given continuous product representative. -/
theorem fieldProduct_ae (p : TimeLp T E) (η : ℝ → E)
    (hp : (p : ℝ → E) =ᵐ[timeMeasure T] η) :
    (timeMultiplier T hT A p : ℝ → F) =ᵐ[timeMeasure T]
      fun t => extendPath T hT A t (η t) := by
  filter_upwards [timeMultiplier_ae T hT A p, hp] with t hmul hp'
  exact hmul.trans (congrArg (fun z : E => extendPath T hT A t z) hp')

variable (hA : ∀ t : Icc (0 : ℝ) T,
  HasDerivWithinAt (extendPath T hT A) (A' t) (Icc (0 : ℝ) T) t)

include hA in
/-- Within-interval coefficient derivatives give genuine derivatives almost
everywhere; endpoints have zero time measure. -/
theorem operatorPath_hasDerivAt_ae :
    ∀ᵐ t ∂timeMeasure T,
      HasDerivAt (extendPath T hT A) (extendPath T hT A' t) t := by
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo (0 : ℝ) T := by
    change ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), t ∈ Ioo (0 : ℝ) T
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem] with t ht
  have hAt := (hA ⟨t, ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  simpa only [extendPath, projIcc_of_mem hT ⟨ht.1.le, ht.2.le⟩] using hAt

include hA in
/-- C¹ operator application preserves actual absolute continuity. -/
theorem fieldProduct_absolutelyContinuous (η : ℝ → E)
    (hη : AbsolutelyContinuousOnInterval η 0 T) :
    AbsolutelyContinuousOnInterval (fun t => extendPath T hT A t (η t)) 0 T :=
  clm_apply_absolutelyContinuous (operatorPath_absolutelyContinuous T hT A A' hA) hη

include hA in
/-- The L² product derivative is the derivative of the actual product representative.
No vanishing terminal trace is assumed. -/
theorem fieldProduct_hasDerivAt_ae (p q : TimeLp T E) (η : ℝ → E)
    (hp : (p : ℝ → E) =ᵐ[timeMeasure T] η)
    (hηder : ∀ᵐ t ∂timeMeasure T, HasDerivAt η (q t) t) :
    ∀ᵐ t ∂timeMeasure T,
      HasDerivAt (fun r => extendPath T hT A r (η r))
        (fieldProductDerivative T hT A A' p q t) t := by
  filter_upwards [operatorPath_hasDerivAt_ae T hT A A' hA, hp, hηder,
    fieldProductDerivative_ae T hT A A' p q] with t hAt hp' hη' hprod
  rw [hprod, hp']
  exact hAt.clm_apply hη'

include hA in
/-- A complete H¹ product conclusion, with actual value and derivative classes. -/
theorem fieldProduct_h1 (p q : TimeLp T E) (η : ℝ → E)
    (hη : AbsolutelyContinuousOnInterval η 0 T)
    (hp : (p : ℝ → E) =ᵐ[timeMeasure T] η)
    (hηder : ∀ᵐ t ∂timeMeasure T, HasDerivAt η (q t) t) :
    AbsolutelyContinuousOnInterval (fun t => extendPath T hT A t (η t)) 0 T ∧
      (timeMultiplier T hT A p : ℝ → F) =ᵐ[timeMeasure T]
        (fun t => extendPath T hT A t (η t)) ∧
      ∀ᵐ t ∂timeMeasure T,
        HasDerivAt (fun r => extendPath T hT A r (η r))
          (fieldProductDerivative T hT A A' p q t) t :=
  ⟨fieldProduct_absolutelyContinuous T hT A A' hA η hη,
    fieldProduct_ae T hT A p η hp,
    fieldProduct_hasDerivAt_ae T hT A A' hA p q η hp hηder⟩

/-- The constructed derivative has the expected operator-norm bound. -/
theorem fieldProductDerivative_norm_le (p q : TimeLp T E) :
    ‖fieldProductDerivative T hT A A' p q‖ ≤ ‖A'‖*‖p‖+‖A‖*‖q‖ :=
  (norm_add_le _ _).trans (add_le_add (timeApply_bound T hT A' p) (timeApply_bound T hT A q))

end EulerTimeH1FieldProduct
