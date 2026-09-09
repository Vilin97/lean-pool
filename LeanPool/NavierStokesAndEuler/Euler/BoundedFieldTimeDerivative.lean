/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import LeanPool.NavierStokesAndEuler.Euler.VolterraConvolution
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Actual time derivatives of uniformly continuous bounded fields

Pointwise derivatives identify a derivative in the bounded-field norm when
both the field and prescribed derivative are continuous in that norm. The
proof uses the Bochner fundamental theorem of calculus and bounded evaluation.
-/

@[expose] public section


noncomputable section

namespace EulerBoundedFieldTimeDerivative

open Set MeasureTheory ContinuousLinearMap EulerVolterraConvolution
open scoped BoundedContinuousFunction

variable {X W : Type*} [TopologicalSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W]
variable (T : ℝ) (hT : 0 ≤ T) (A A' : C(Icc (0 : ℝ) T, X →ᵇ W))

/-- Pointwise derivatives imply the exact integral identity in the bounded-field space. -/
theorem integral_eq_sub
    (hpoint : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : X,
      HasDerivWithinAt (fun s => extendPath T hT A s x)
        (extendPath T hT A' t x) (Icc (0 : ℝ) T) t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    (∫ s in (0 : ℝ)..t, extendPath T hT A' s) =
      extendPath T hT A t - extendPath T hT A 0 := by
  apply BoundedContinuousFunction.ext
  intro x
  let ev : (X →ᵇ W) →L[ℝ] W := BoundedContinuousFunction.evalCLM ℝ x
  have hcA := ev.continuous.comp (extendPath_continuous T hT A)
  have hcA' := ev.continuous.comp (extendPath_continuous T hT A')
  calc
    (∫ s in (0 : ℝ)..t, extendPath T hT A' s) x =
        ∫ s in (0 : ℝ)..t, extendPath T hT A' s x := by
      exact (ev.intervalIntegral_comp_comm ((extendPath_continuous T hT A').intervalIntegrable 0
          t)).symm
    _ = extendPath T hT A t x - extendPath T hT A 0 x := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcA.continuousOn
        ?_ (hcA'.intervalIntegrable 0 t)
      intro s hs
      have hsT : s < T := hs.2.trans_le ht.2
      exact (hpoint s ⟨hs.1.le, hsT.le⟩ x).hasDerivAt (Icc_mem_nhds hs.1 hsT)

/-- This is a genuine derivative in the uniform bounded-field norm. -/
theorem hasDerivWithinAt
    (hpoint : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : X,
      HasDerivWithinAt (fun s => extendPath T hT A s x)
        (extendPath T hT A' t x) (Icc (0 : ℝ) T) t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT A) (extendPath T hT A' t) (Icc (0 : ℝ) T) t := by
  have hc := extendPath_continuous T hT A'
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  apply (hd.const_add (extendPath T hT A 0)).hasDerivWithinAt.congr_of_mem ?_ ht
  intro s hs
  rw [integral_eq_sub T hT A A' hpoint s hs]
  abel

end EulerBoundedFieldTimeDerivative
