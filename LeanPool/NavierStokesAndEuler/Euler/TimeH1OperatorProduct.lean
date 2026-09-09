/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TerminalTimePrimitive
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpMultiplier
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# Products of genuine time-H¹ paths and differentiable operator paths

The product derivative is constructed in the actual Bochner L² space from the
coefficient multiplier and terminal primitive. Its integral is identified with
the literal pointwise product by absolute continuity and uniqueness of primitives.
-/

noncomputable section


namespace EulerTimeH1OperatorProduct

open MeasureTheory Set Filter EulerTimeLp EulerTerminalTimePrimitive EulerVolterraConvolution
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pointwise application of two absolutely continuous operator/vector paths is
absolutely continuous. The estimate uses their actual compact-interval bounds. -/
theorem clm_apply_absolutelyContinuous {a b : ℝ} {A : ℝ → E →L[ℝ] F} {u : ℝ → E}
    (hA : AbsolutelyContinuousOnInterval A a b)
    (hu : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun t => A t (u t)) a b := by
  obtain ⟨C, hC⟩ := hA.exists_bound
  obtain ⟨D, hD⟩ := hu.exists_bound
  unfold AbsolutelyContinuousOnInterval at hA hu
  apply squeeze_zero' ?_ ?_ (by simpa using (hu.const_mul C).add (hA.const_mul D))
  · exact Eventually.of_forall fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg)
  rw [eventually_inf_principal]
  filter_upwards with (n, I) hnI
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  gcongr with i hi
  have hs := (show ∀ i ∈ Finset.range n, (I i).1 ∈ uIcc a b ∧ (I i).2 ∈ uIcc a b from
    hnI.left) i hi
  calc
    dist (A (I i).1 (u (I i).1)) (A (I i).2 (u (I i).2)) ≤
        dist (A (I i).1 (u (I i).1)) (A (I i).1 (u (I i).2)) +
        dist (A (I i).1 (u (I i).2)) (A (I i).2 (u (I i).2)) := dist_triangle _ _ _
    _ ≤ C * dist (u (I i).1) (u (I i).2) + D * dist (A (I i).1) (A (I i).2) := by
      apply add_le_add
      · rw [dist_eq_norm, ← map_sub, dist_eq_norm]
        exact ((A (I i).1).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hC _ hs.1) (norm_nonneg _))
      · rw [dist_eq_norm, ← sub_apply, dist_eq_norm]
        exact ((A (I i).1-A (I i).2).le_opNorm _).trans (by
          calc
            _ ≤ ‖A (I i).1-A (I i).2‖ * D :=
              mul_le_mul_of_nonneg_left (hD _ hs.2) (norm_nonneg _)
            _ = _ := mul_comm _ _)

variable (T : ℝ) (hT : 0 ≤ T)
  (A A' : C(Icc (0 : ℝ) T, E →L[ℝ] F))

/-- A genuine differentiable extension supplies the within-interval derivative
hypothesis for its clamped continuous path, including both endpoints. -/
theorem operatorPath_hasDerivWithinAt_of_extension (a : ℝ → E →L[ℝ] F)
    (ha : ∀ t : Icc (0 : ℝ) T, A t = a t)
    (hader : ∀ t : Icc (0 : ℝ) T, HasDerivAt a (A' t) t) :
    ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT A) (A' t) (Icc (0 : ℝ) T) t := by
  intro t
  apply (hader t).hasDerivWithinAt.congr_of_mem _ t.property
  intro x hx
  simpa only [extendPath, projIcc_of_mem hT hx] using ha ⟨x, hx⟩

/-- Within-interval differentiability with a continuous derivative implies actual
absolute continuity of the clamped coefficient path. -/
theorem operatorPath_absolutelyContinuous
    (hA : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT A) (A' t) (Icc (0 : ℝ) T) t) :
    AbsolutelyContinuousOnInterval (extendPath T hT A) 0 T := by
  have hl : LipschitzOnWith ‖A'‖₊ (extendPath T hT A) (Icc (0 : ℝ) T) := by
    apply (convex_Icc (0 : ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := extendPath T hT A')
    · intro t ht
      simpa only [extendPath, projIcc_of_mem hT ht] using hA ⟨t, ht⟩
    · intro t ht
      exact A'.norm_coe_le_norm (projIcc 0 T hT t)
  have hl' : LipschitzOnWith ‖A'‖₊ (extendPath T hT A) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT] using hl
  exact hl'.absolutelyContinuousOnInterval

/-- The derivative of `A(t) Ju(t)`, constructed as an actual bounded L² operator. -/
def productDerivative : TimeLp T E →L[ℝ] TimeLp T F :=
  (timeMultiplier T hT A').comp (primitiveTimeLp T hT) + timeMultiplier T hT A

/-- The product derivative has its literal Leibniz-rule representative. -/
theorem productDerivative_ae (u : TimeLp T E) :
    (productDerivative T hT A A' u : ℝ → F) =ᵐ[timeMeasure T]
      fun t => extendPath T hT A' t (realPrimitive T u t) + extendPath T hT A t (u t) := by
  filter_upwards [Lp.coeFn_add (timeMultiplier T hT A' (primitiveTimeLp T hT u))
      (timeMultiplier T hT A u),
    timeMultiplier_ae T hT A' (primitiveTimeLp T hT u), timeMultiplier_ae T hT A u,
    primitiveTimeLp_ae T hT u] with t hadd ha' ha hu
  change (timeMultiplier T hT A' (primitiveTimeLp T hT u) + timeMultiplier T hT A u) t = _
  change _ = (timeMultiplier T hT A' (primitiveTimeLp T hT u)) t +
    (timeMultiplier T hT A u) t at hadd
  rw [hadd, ha', ha, hu]

/-- The actual pointwise coefficient-times-primitive path. -/
def productPrimitive (u : TimeLp T E) : ℝ → F :=
  fun t => extendPath T hT A t (realPrimitive T u t)

/-- Every such product has zero terminal trace. -/
@[simp] theorem productPrimitive_terminal (u : TimeLp T E) : productPrimitive T hT A u T = 0 := by
  simp only [productPrimitive, realPrimitive_terminal, map_zero]

/-- The product path is genuinely absolutely continuous. -/
theorem productPrimitive_absolutelyContinuous
    (hA : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT A) (A' t) (Icc (0 : ℝ) T) t)
    (u : TimeLp T E) : AbsolutelyContinuousOnInterval (productPrimitive T hT A u) 0 T :=
  clm_apply_absolutelyContinuous (operatorPath_absolutelyContinuous T hT A A' hA)
    (realPrimitive_absolutelyContinuous T u)

/-- The constructed L² field is the actual a.e. derivative of the pointwise product. -/
theorem productPrimitive_hasDerivAt_ae [CompleteSpace E]
    (hA : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT A) (A' t) (Icc (0 : ℝ) T) t)
    (u : TimeLp T E) :
    ∀ᵐ t ∂timeMeasure T,
      HasDerivAt (productPrimitive T hT A u) (productDerivative T hT A A' u t) t := by
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo (0 : ℝ) T := by
    change ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), t ∈ Ioo (0 : ℝ) T
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem, realPrimitive_hasDerivAt_ae T u,
    productDerivative_ae T hT A A' u] with t ht hu hprod
  rw [hprod]
  have hAt := (hA ⟨t, ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hAt' : HasDerivAt (extendPath T hT A) (extendPath T hT A' t) t := by
    simpa only [extendPath, projIcc_of_mem hT ⟨ht.1.le, ht.2.le⟩] using hAt
  exact hAt'.clm_apply hu

/-- The literal product is the terminal primitive of the derivative constructed
in L². This identifies the product as a genuine terminal-zero H¹ path. -/
theorem productPrimitive_eq_realPrimitive [CompleteSpace E] [CompleteSpace F]
    (hA : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT A) (A' t) (Icc (0 : ℝ) T) t)
    (u : TimeLp T E) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    productPrimitive T hT A u t = realPrimitive T (productDerivative T hT A A' u) t :=
  eq_realPrimitive_of_ac_hasDerivAt_ae T hT (productDerivative T hT A A' u)
    (productPrimitive T hT A u) (productPrimitive_absolutelyContinuous T hT A A' hA u)
    (productPrimitive_hasDerivAt_ae T hT A A' hA u) (productPrimitive_terminal T hT A u) t ht

/-- Integrating the product derivative recovers the literal pointwise product
at every time, including both endpoints. -/
theorem terminalPrimitive_productDerivative [CompleteSpace E] [CompleteSpace F]
    (hA : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT A) (A' t) (Icc (0 : ℝ) T) t)
    (u : TimeLp T E) (t : Icc (0 : ℝ) T) :
    terminalPrimitive T hT (productDerivative T hT A A' u) t =
      A t (terminalPrimitive T hT u t) := by
  change realPrimitive T (productDerivative T hT A A' u) t = A t (realPrimitive T u t)
  simpa only [productPrimitive, extendPath, projIcc_of_mem hT t.property] using
    (productPrimitive_eq_realPrimitive T hT A A' hA u t t.property).symm

/-- The same product rule is an exact identity of actual Bochner L² fields. -/
theorem primitiveTimeLp_productDerivative [CompleteSpace E] [CompleteSpace F]
    (hA : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT A) (A' t) (Icc (0 : ℝ) T) t)
    (u : TimeLp T E) :
    primitiveTimeLp T hT (productDerivative T hT A A' u) =
      timeMultiplier T hT A (primitiveTimeLp T hT u) := by
  apply Lp.ext
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Icc (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [hmem, primitiveTimeLp_ae T hT (productDerivative T hT A A' u),
    timeMultiplier_ae T hT A (primitiveTimeLp T hT u), primitiveTimeLp_ae T hT u]
    with t ht hp ha hu
  calc
    primitiveTimeLp T hT (productDerivative T hT A A' u) t =
        realPrimitive T (productDerivative T hT A A' u) t := hp
    _ = extendPath T hT A t (realPrimitive T u t) :=
      (productPrimitive_eq_realPrimitive T hT A A' hA u t ht).symm
    _ = extendPath T hT A t (primitiveTimeLp T hT u t) :=
      congrArg (fun z : E => extendPath T hT A t z) hu.symm
    _ = timeMultiplier T hT A (primitiveTimeLp T hT u) t := ha.symm

/-- The actual initial trace transforms by the coefficient's initial value. -/
theorem initialTrace_productDerivative [CompleteSpace E] [CompleteSpace F]
    (hA : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT A) (A' t) (Icc (0 : ℝ) T) t)
    (u : TimeLp T E) :
    initialTrace T hT (productDerivative T hT A A' u) =
      A ⟨0, le_rfl, hT⟩ (initialTrace T hT u) :=
  terminalPrimitive_productDerivative T hT A A' hA u ⟨0, le_rfl, hT⟩

/-- A uniform bound on the actual derivative in terms of the coefficient and
its derivative; the time primitive retains its sharp square-root bound. -/
theorem productDerivative_norm_le (u : TimeLp T E) :
    ‖productDerivative T hT A A' u‖ ≤
      (‖A'‖ * Real.sqrt (T^2/2) + ‖A‖) * ‖u‖ := by
  have hp : ‖primitiveTimeLp T hT u‖ ≤ Real.sqrt (T^2/2) * ‖u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact primitiveTimeLp_norm_sq_le T hT u
  change ‖timeMultiplier T hT A' (primitiveTimeLp T hT u) + timeMultiplier T hT A u‖ ≤ _
  calc
    _ ≤ ‖timeMultiplier T hT A' (primitiveTimeLp T hT u)‖ + ‖timeMultiplier T hT A u‖ :=
      norm_add_le _ _
    _ ≤ ‖A'‖ * ‖primitiveTimeLp T hT u‖ + ‖A‖ * ‖u‖ :=
      add_le_add (timeApply_bound T hT A' _) (timeApply_bound T hT A u)
    _ ≤ ‖A'‖ * (Real.sqrt (T^2/2) * ‖u‖) + ‖A‖ * ‖u‖ := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg A')
      exact hp
    _ = _ := by ring

end EulerTimeH1OperatorProduct
