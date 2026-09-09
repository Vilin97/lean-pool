/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowJets
public import LeanPool.NavierStokesAndEuler.Euler.GevreyFlowFinite

@[expose] public section

/-! Source-scale Gevrey bounds for the actual globally constructed Picard
flow.  Only bounds on the given velocity jets and the small product BRT
are hypotheses; smoothness and all time-jet identities of the flow come
from its construction. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff BoundedContinuousFunction Interval

namespace EulerSmoothFlowGevrey

open EulerSmoothBanachFlow EulerGevreyFlowFinite EulerGevreyGeneratingDerivatives
  EulerVolterraConvolution

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A : SmoothTimeField (Icc (0 : ℝ) T) E E)

private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] E) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] E) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] E)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] E)) := inferInstance

def velocityExtension (t : ℝ) (x : E) : E := A.field (projIcc 0 T hT t) x

omit [FiniteDimensional ℝ E] in
@[simp] theorem velocityExtension_apply (t : Icc (0 : ℝ) T) (x : E) :
    velocityExtension T hT A t x = A.field t x := by
  simp only [velocityExtension, projIcc_of_mem hT t.property]

omit [FiniteDimensional ℝ E] in
theorem velocityExtension_contDiff (t : ℝ) :
    ContDiff ℝ ∞ (velocityExtension T hT A t) := A.smooth _

omit [FiniteDimensional ℝ E] in
theorem velocityExtension_jet_bound (B R : ℝ)
    (hb : ∀ n, ‖A.jet n‖ ≤ B*R^n*(n.factorial : ℝ)^2)
    (n : ℕ) (t : ℝ) (x : E) :
    ‖iteratedFDeriv ℝ n (velocityExtension T hT A t) x‖ ≤ B*R^n*(n.factorial : ℝ)^2 := by
  change ‖iteratedFDeriv ℝ n (A.field (projIcc 0 T hT t) : E → E) x‖ ≤ _
  rw [← A.jet_eq]
  exact ((A.jet n (projIcc 0 T hT t)).norm_coe_le_norm x).trans
    (((A.jet n).norm_coe_le_norm _).trans (hb n))

theorem composition_jet_hasDerivWithinAt (n : ℕ) (x : E) (t : ℝ) (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun s => iteratedFDeriv ℝ n (displacement T hT A s) x)
      (iteratedFDeriv ℝ n (velocityExtension T hT A t ∘ (id+displacement T hT A t)) x)
      (Icc 0 T) t := by
  have he : velocityExtension T hT A t ∘ (id+displacement T hT A t) =
      fun y => A.field ⟨t,ht⟩ (y+displacement T hT A t y) := by
    funext y
    exact velocityExtension_apply T hT A ⟨t,ht⟩ _
  rw [he]
  exact displacement_jet_hasDerivWithinAt T hT A n x ⟨t,ht⟩

theorem composition_jet_continuous (n : ℕ) (x : E) :
    ContinuousOn (fun t => iteratedFDeriv ℝ n
      (velocityExtension T hT A t ∘ (id+displacement T hT A t)) x) (Icc 0 T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun t : Icc (0 : ℝ) T => iteratedFDeriv ℝ n
    (velocityExtension T hT A t ∘ (id+displacement T hT A t)) x)
  have he : (fun t : Icc (0 : ℝ) T => iteratedFDeriv ℝ n
      (velocityExtension T hT A t ∘ (id+displacement T hT A t)) x) =
      fun t : Icc (0 : ℝ) T => iteratedFDeriv ℝ n
        (fun y => A.field t (y+displacement T hT A t y)) x := by
    funext t
    congr 1
    funext y
    exact velocityExtension_apply T hT A t _
  rw [he]
  exact velocity_jet_continuous T hT A n x

/-- A finite generating sum for the actual constructed flow, with a
cutoff-independent radius and coefficient. -/
theorem constructed_generating_sum_bound (B R : ℝ)
    (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B*R*T ≤ 1/8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B*R^n*(n.factorial : ℝ)^2)
    (N : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) :
    derivativeSum (displacement T hT A t) N ((4*R)⁻¹) x ≤ B*t := by
  apply flow_generating_sum_bound_of_jet_derivative
    (displacement T hT A) (velocityExtension T hT A) N T B R hT hB hR hsmall
    (fun s _ => (displacement_contDiff T hT A s).of_le (by simp))
    (fun s _ => (velocityExtension_contDiff T hT A s).of_le (by simp))
    (displacement_zero T hT A) _ _ _ t ht x
  · exact fun s _ y n _ => velocityExtension_jet_bound T hT A B R hb n s y
  · exact fun n _ s hs y => composition_jet_hasDerivWithinAt T hT A n y s hs
  · exact fun n _ y => composition_jet_continuous T hT A n y

theorem displacement_positive_bound (B R : ℝ)
    (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B*R*T ≤ 1/8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B*R^n*(n.factorial : ℝ)^2)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) :
    ‖iteratedFDeriv ℝ n (displacement T hT A t) x‖ ≤
      B*t*(4*R)^n*(n.factorial : ℝ)^2 := by
  exact derivative_bound_of_generating_sum (displacement T hT A t) n n R (B*t) x hR
    (Finset.mem_Icc.mpr ⟨hn,le_rfl⟩)
    (constructed_generating_sum_bound T hT A B R hB hR hsmall hb n t ht x)

/-- Order zero uses direct integration of the actual velocity. -/
theorem displacement_zero_bound (B R : ℝ)
    (hb : ∀ n, ‖A.jet n‖ ≤ B*R^n*(n.factorial : ℝ)^2)
    (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) :
    ‖iteratedFDeriv ℝ 0 (displacement T hT A t) x‖ ≤ B*t := by
  let v := fun s => velocityExtension T hT A s ∘ (id+displacement T hT A s)
  have he := jet_integral_of_hasDerivWithinAt (displacement T hT A) v 0 T
    (displacement_zero T hT A)
    (fun s hs y => composition_jet_hasDerivWithinAt T hT A 0 y s hs)
    (composition_jet_continuous T hT A 0) t ht x
  rw [he]
  apply (intervalIntegral.norm_integral_le_integral_norm ht.1).trans
  have hc := ((composition_jet_continuous T hT A 0 x).mono
    (Icc_subset_Icc_right ht.2)).norm
  have hi := intervalIntegral.integral_mono_on (μ := volume) ht.1
    (hc.intervalIntegrable_of_Icc ht.1) intervalIntegrable_const
    (g := fun _ : ℝ => B) (fun s _ => by
      change ‖iteratedFDeriv ℝ 0 (v s) x‖ ≤ B
      rw [norm_iteratedFDeriv_zero]
      change ‖velocityExtension T hT A s (x+displacement T hT A s x)‖ ≤ B
      have hz := velocityExtension_jet_bound T hT A B R hb 0 s
        (x+displacement T hT A s x)
      simpa only [norm_iteratedFDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
        one_pow, mul_one] using hz)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using hi

/-- Source-only all-order spatial estimate for the actual Picard flow
displacement.  It includes order zero and is linear in B*t. -/
theorem displacement_bound (B R : ℝ)
    (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B*R*T ≤ 1/8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B*R^n*(n.factorial : ℝ)^2)
    (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) :
    ‖iteratedFDeriv ℝ n (displacement T hT A t) x‖ ≤
      B*t*(4*R)^n*(n.factorial : ℝ)^2 := by
  by_cases hn : n = 0
  · subst n
    simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one] using
      displacement_zero_bound T hT A B R hb t ht x
  · exact displacement_positive_bound T hT A B R hB hR hsmall hb n (Nat.pos_of_ne_zero hn) t ht x

end EulerSmoothFlowGevrey
