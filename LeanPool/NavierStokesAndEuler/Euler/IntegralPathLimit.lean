/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import LeanPool.NavierStokesAndEuler.Euler.VolterraConvolution
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.Positivity.Finset

/-! Passing genuine Banach-valued evolution equations through uniform time-path limits. -/

@[expose] public section


noncomputable section

namespace EulerIntegralPathLimit

open MeasureTheory Set EulerVolterraConvolution
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integration of the actual clamped time path is a bounded linear operator. -/
def pathIntegralOperator (T : ℝ) (hT : 0 ≤ T) (a b : ℝ) : C(Icc (0 : ℝ) T,E) →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ t in a..b, extendPath T hT f t
      map_add' := by
        intro f g
        exact intervalIntegral.integral_add ((extendPath_continuous T hT f).intervalIntegrable a b)
          ((extendPath_continuous T hT g).intervalIntegrable a b)
      map_smul' := by
        intro c f
        exact intervalIntegral.integral_smul c (extendPath T hT f) }
    |b-a| (fun f => by
      change ‖∫ t in a..b, extendPath T hT f t‖ ≤ _
      have h : ‖∫ t in a..b, extendPath T hT f t‖ ≤ ‖f‖*|b-a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => extendPath_norm_le T hT f t)
      exact h.trans_eq (mul_comm _ _))

/-- The time-integral operator is the literal Bochner interval integral. -/
theorem pathIntegralOperator_apply (T : ℝ) (hT : 0 ≤ T) (a b : ℝ) (f : C(Icc (0 : ℝ) T, E)) :
    pathIntegralOperator T hT a b f = ∫ t in a..b, extendPath T hT f t := rfl

variable [CompleteSpace E]

/-- Interior time derivatives with continuous endpoint traces give the exact integral evolution
formula. -/
theorem integral_equation_of_hasDerivAt (T : ℝ) (hT : 0 ≤ T)
    (u f : C(Icc (0 : ℝ) T, E))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt (extendPath T hT u) (extendPath T hT f t) t)
    (t : Icc (0 : ℝ) T) :
    u t = u ⟨0,le_rfl,hT⟩ + pathIntegralOperator T hT 0 t.val f := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
    (extendPath_continuous T hT u).continuousOn
    (fun r hr => hd r ⟨hr.1,hr.2.trans_le t.property.2⟩)
    ((extendPath_continuous T hT f).intervalIntegrable 0 t.val)
  change pathIntegralOperator T hT 0 t.val f =
    u (projIcc 0 T hT t.val)-u (projIcc 0 T hT 0) at h
  rw [projIcc_of_mem hT t.property,projIcc_of_mem hT ⟨le_rfl,hT⟩] at h
  exact (eq_add_of_sub_eq h.symm).trans (add_comm _ _)

omit [CompleteSpace E] in
/-- Actual integral evolution equations pass to uniform limits of the solution and derivative paths.
-/
theorem integral_equation_limit (T : ℝ) (hT : 0 ≤ T)
    (u f : ℕ → C(Icc (0 : ℝ) T, E)) (v g : C(Icc (0 : ℝ) T, E))
    (hu : Filter.Tendsto u Filter.atTop (𝓝 v)) (hf : Filter.Tendsto f Filter.atTop (𝓝 g))
    (heq : ∀ n t, u n t = u n ⟨0, le_rfl, hT⟩ + pathIntegralOperator T hT 0 t.val (f n))
    (t : Icc (0 : ℝ) T) :
    v t = v ⟨0,le_rfl,hT⟩ + pathIntegralOperator T hT 0 t.val g := by
  have hv := ((ContinuousMap.evalCLM ℝ t).continuous.tendsto v).comp hu
  have hz := ((ContinuousMap.evalCLM ℝ ⟨0,le_rfl,hT⟩).continuous.tendsto v).comp hu
  have hi := ((pathIntegralOperator T hT 0 t.val).continuous.tendsto g).comp hf
  exact tendsto_nhds_unique hv ((hz.add hi).congr (fun n => (heq n t).symm))

/-- A continuous path satisfying the actual integral equation has the prescribed interior
derivative. -/
theorem hasDerivAt_of_integral_equation (T : ℝ) (hT : 0 ≤ T)
    (u f : C(Icc (0 : ℝ) T, E))
    (heq : ∀ t, u t = u ⟨0, le_rfl, hT⟩ + pathIntegralOperator T hT 0 t.val f)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT u) (extendPath T hT f t) t := by
  have hd := ((extendPath_continuous T hT f).integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (u
      ⟨0,le_rfl,hT⟩)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  change u (projIcc 0 T hT r) = _
  rw [projIcc_of_mem hT ⟨hr.1.le,hr.2.le⟩]
  exact heq ⟨r,hr.1.le,hr.2.le⟩

end EulerIntegralPathLimit
