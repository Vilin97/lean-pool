/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowJets
public import LeanPool.NavierStokesAndEuler.Euler.GevreyGeneratingDerivatives
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Source-scale Gevrey bounds for the actual globally constructed Picard
flow.  Only bounds on the given velocity jets and the small product BRT
are hypotheses; smoothness and all time-jet identities of the flow come
from its construction. -/

section

/-! Finite-order small-flow estimates.  The only evolution input is the
literal integral (or, in the final theorem, differential) equation for
the actual spatial derivatives.  The nonlinear majorant is derived here
from Faà di Bruno; no bound on the flow derivatives is assumed. -/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff Interval

namespace EulerGevreyFlowFinite

open EulerGevreyGeneratingComposition EulerGevreyGeneratingDerivatives
  EulerGevreyFlowBootstrap

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem derivativeSum_continuousOn (f : ℝ → E → F) (N : ℕ) (z T : ℝ) (x : E)
    (hc : ∀ n ∈ Finset.Icc 1 N,
      ContinuousOn (fun t => iteratedFDeriv ℝ n (f t) x) (Icc 0 T)) :
    ContinuousOn (fun t => derivativeSum (f t) N z x) (Icc 0 T) := by
  unfold derivativeSum generatingSum normalizedJet ftaylorSeries
  exact continuousOn_finsetSum _ fun n hn => ((hc n hn).norm.div_const _).mul_const _

theorem derivativeSum_zero (N : ℕ) (z : ℝ) (x : E) :
    derivativeSum (0 : E → F) N z x = 0 := by
  simp [derivativeSum, generatingSum, normalizedJet, ftaylorSeries, iteratedFDeriv_zero]

theorem derivative_term_le_sum (f : E → F) (N n : ℕ) (z : ℝ) (x : E)
    (hn : n ∈ Finset.Icc 1 N) (hz : 0 ≤ z) :
    ‖iteratedFDeriv ℝ n f x‖/(n.factorial : ℝ)^2*z^n ≤ derivativeSum f N z x := by
  unfold derivativeSum generatingSum normalizedJet ftaylorSeries
  exact Finset.single_le_sum
    (fun j _ => mul_nonneg
      (div_nonneg (norm_nonneg (iteratedFDeriv ℝ j f x)) (sq_nonneg (j.factorial : ℝ)))
      (pow_nonneg hz j)) hn

theorem derivativeSum_le_integral
    (f : E → F) (v : ℝ → E → F) (N : ℕ) (z t : ℝ) (x : E)
    (ht : 0 ≤ t) (hz : 0 ≤ z)
    (hc : ∀ n ∈ Finset.Icc 1 N,
      ContinuousOn (fun s => iteratedFDeriv ℝ n (v s) x) (Icc 0 t))
    (heq : ∀ n ∈ Finset.Icc 1 N,
      iteratedFDeriv ℝ n f x = ∫ s in 0..t, iteratedFDeriv ℝ n (v s) x) :
    derivativeSum f N z x ≤ ∫ s in 0..t, derivativeSum (v s) N z x := by
  unfold derivativeSum generatingSum normalizedJet ftaylorSeries
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_le_sum
    intro n hn
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div, heq n hn]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hz n)
    exact div_le_div_of_nonneg_right (intervalIntegral.norm_integral_le_integral_norm ht)
      (sq_nonneg _)
  · intro n hn
    exact (((hc n hn).norm.div_const _).mul_const _).intervalIntegrable_of_Icc ht

/-- Uniform finite-order bound for a genuine flow displacement, from its
actual differentiated integral equation.  The smallness condition and the
resulting radius are independent of N. -/
theorem flow_generating_sum_bound
    (ψ b : ℝ → E → E) (N : ℕ) (T B R : ℝ)
    (hT : 0 ≤ T) (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B * R * T ≤ 1 / 8)
    (hψ : ∀ t ∈ Icc 0 T, ContDiff ℝ N (ψ t))
    (hb : ∀ t ∈ Icc 0 T, ContDiff ℝ N (b t)) (hψ0 : ψ 0 = 0)
    (hbjet : ∀ t ∈ Icc 0 T, ∀ y, ∀ n ∈ Finset.Icc 1 N,
      ‖iteratedFDeriv ℝ n (b t) y‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (hcψ : ∀ n ∈ Finset.Icc 1 N, ∀ x,
      ContinuousOn (fun t => iteratedFDeriv ℝ n (ψ t) x) (Icc 0 T))
    (hcv : ∀ n ∈ Finset.Icc 1 N, ∀ x,
      ContinuousOn (fun t => iteratedFDeriv ℝ n (b t ∘ (id + ψ t)) x) (Icc 0 T))
    (heq : ∀ n ∈ Finset.Icc 1 N, ∀ t ∈ Icc 0 T, ∀ x,
      iteratedFDeriv ℝ n (ψ t) x =
        ∫ s in 0..t, iteratedFDeriv ℝ n (b s ∘ (id + ψ s)) x) :
    ∀ t ∈ Icc 0 T, ∀ x,
      derivativeSum (ψ t) N ((4*R)⁻¹) x ≤ B*t := by
  intro t ht x
  have hz : 0 ≤ (4*R)⁻¹ := by positivity
  have hfc := derivativeSum_continuousOn ψ N ((4*R)⁻¹) T x (fun n hn => hcψ n hn x)
  have hf0 : derivativeSum (ψ 0) N ((4*R)⁻¹) x = 0 := by
    rw [hψ0, derivativeSum_zero]
  apply (rational_integral_bootstrap
    (fun s => derivativeSum (ψ s) N ((4*R)⁻¹) x) T B R hT hB hR hsmall hfc hf0 ?_ t ht).1
  intro s hs hbefore
  have hbase := derivativeSum_le_integral (ψ s) (fun r => b r ∘ (id+ψ r))
    N ((4*R)⁻¹) s x hs.1 hz
    (fun n hn => (hcv n hn x).mono (Icc_subset_Icc_right hs.2))
    (fun n hn => heq n hn s hs x)
  have hcontV := derivativeSum_continuousOn (fun r => b r ∘ (id+ψ r))
    N ((4*R)⁻¹) s x (fun n hn => (hcv n hn x).mono (Icc_subset_Icc_right hs.2))
  have hcontF := hfc.mono (Icc_subset_Icc_right hs.2)
  have hden : ∀ r ∈ Icc 0 s,
      1-R*((4*R)⁻¹+derivativeSum (ψ r) N ((4*R)⁻¹) x) ≠ 0 := by
    intro r hr
    have hh := hbefore r hr
    linarith
  have hrate : ContinuousOn
      (fun r => rationalRate B R ((4*R)⁻¹) (derivativeSum (ψ r) N ((4*R)⁻¹) x))
      (Icc 0 s) := by
    unfold rationalRate
    exact (continuousOn_const.mul (continuousOn_const.mul (continuousOn_const.add hcontF))).div
      (continuousOn_const.sub (continuousOn_const.mul (continuousOn_const.add hcontF))) hden
  apply hbase.trans
  apply intervalIntegral.integral_mono_on hs.1
    (hcontV.intervalIntegrable_of_Icc hs.1) (hrate.intervalIntegrable_of_Icc hs.1)
  intro r hr
  have hrT : r ∈ Icc 0 T := ⟨hr.1,hr.2.trans hs.2⟩
  exact derivativeSum_comp_id_add_le (ψ r) (b r) N ((4*R)⁻¹) B R x hz hB hR.le
    (hψ r hrT).contDiffAt (hb r hrT).contDiffAt
    (hbjet r hrT _) (lt_of_le_of_lt (hbefore r hr) (by norm_num))

/-- Extracting one term from the same finite sum gives a single fixed
Gevrey radius, rather than a radius enlarged at each derivative order. -/
theorem derivative_bound_of_generating_sum (f : E → F) (N n : ℕ) (R A : ℝ)
    (x : E) (hR : 0 < R) (hn : n ∈ Finset.Icc 1 N)
    (hbound : derivativeSum f N ((4 * R)⁻¹) x ≤ A) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ A*(4*R)^n*(n.factorial : ℝ)^2 := by
  have hw := (derivative_term_le_sum f N n ((4*R)⁻¹) x hn (by positivity)).trans hbound
  have hm := mul_le_mul_of_nonneg_right hw (pow_nonneg (show 0 ≤ 4*R by positivity) n)
  have hid : ((4*R)⁻¹)^n*(4*R)^n = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (show 4*R ≠ 0 by positivity), one_pow]
  rw [mul_assoc, hid, mul_one] at hm
  exact (div_le_iff₀ (by positivity : 0 < (n.factorial : ℝ)^2)).mp hm

variable [CompleteSpace E]

/-- The integral equation used above follows from the actual within-time
derivative identity on the closed interval, including a degenerate end. -/
theorem jet_integral_of_hasDerivWithinAt
    (ψ v : ℝ → E → E) (n : ℕ) (T : ℝ) (hψ0 : ψ 0 = 0)
    (hd : ∀ t ∈ Icc 0 T, ∀ x,
      HasDerivWithinAt (fun s => iteratedFDeriv ℝ n (ψ s) x)
        (iteratedFDeriv ℝ n (v t) x) (Icc 0 T) t)
    (hc : ∀ x, ContinuousOn (fun t => iteratedFDeriv ℝ n (v t) x) (Icc 0 T))
    (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) :
    iteratedFDeriv ℝ n (ψ t) x = ∫ s in 0..t, iteratedFDeriv ℝ n (v s) x := by
  have hcp : ContinuousOn (fun s => iteratedFDeriv ℝ n (ψ s) x) (Icc 0 t) :=
    fun s hs => (hd s ⟨hs.1,hs.2.trans ht.2⟩ x).continuousWithinAt.mono
      (Icc_subset_Icc_right ht.2)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcp
    (fun s hs => (hd s ⟨hs.1.le,(hs.2.trans_le ht.2).le⟩ x).hasDerivAt
      (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2)))
    (((hc x).mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1)
  simpa only [hψ0, iteratedFDeriv_zero, Pi.zero_apply, sub_zero] using he.symm

/-- The finite flow bound using genuine time derivatives of the spatial
jets, with no independent integral-equation assumption. -/
theorem flow_generating_sum_bound_of_jet_derivative
    (ψ b : ℝ → E → E) (N : ℕ) (T B R : ℝ)
    (hT : 0 ≤ T) (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B * R * T ≤ 1 / 8)
    (hψ : ∀ t ∈ Icc 0 T, ContDiff ℝ N (ψ t))
    (hb : ∀ t ∈ Icc 0 T, ContDiff ℝ N (b t)) (hψ0 : ψ 0 = 0)
    (hbjet : ∀ t ∈ Icc 0 T, ∀ y, ∀ n ∈ Finset.Icc 1 N,
      ‖iteratedFDeriv ℝ n (b t) y‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (hd : ∀ n ∈ Finset.Icc 1 N, ∀ t ∈ Icc 0 T, ∀ x,
      HasDerivWithinAt (fun s => iteratedFDeriv ℝ n (ψ s) x)
        (iteratedFDeriv ℝ n (b t ∘ (id + ψ t)) x) (Icc 0 T) t)
    (hcv : ∀ n ∈ Finset.Icc 1 N, ∀ x,
      ContinuousOn (fun t => iteratedFDeriv ℝ n (b t ∘ (id + ψ t)) x) (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, ∀ x, derivativeSum (ψ t) N ((4*R)⁻¹) x ≤ B*t := by
  apply flow_generating_sum_bound ψ b N T B R hT hB hR hsmall hψ hb hψ0 hbjet
  · exact fun n hn x t ht => (hd n hn t ht x).continuousWithinAt
  · exact hcv
  · intro n hn t ht x
    exact jet_integral_of_hasDerivWithinAt ψ (fun s => b s ∘ (id+ψ s))
      n T hψ0 (hd n hn) (hcv n hn) t ht x

/-- All positive spatial orders have the same radius 4R and the same
linear amplitude B*t.  Smoothness and the jet equation are qualitative
inputs; the derivative estimates are conclusions. -/
theorem flow_positive_derivative_bound
    (ψ b : ℝ → E → E) (T B R : ℝ)
    (hT : 0 ≤ T) (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B * R * T ≤ 1 / 8)
    (hψ : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (ψ t))
    (hb : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (b t)) (hψ0 : ψ 0 = 0)
    (hbjet : ∀ t ∈ Icc 0 T, ∀ y, ∀ n, 0 < n →
      ‖iteratedFDeriv ℝ n (b t) y‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (hd : ∀ n, 0 < n → ∀ t ∈ Icc 0 T, ∀ x,
      HasDerivWithinAt (fun s => iteratedFDeriv ℝ n (ψ s) x)
        (iteratedFDeriv ℝ n (b t ∘ (id + ψ t)) x) (Icc 0 T) t)
    (hcv : ∀ n, 0 < n → ∀ x,
      ContinuousOn (fun t => iteratedFDeriv ℝ n (b t ∘ (id + ψ t)) x) (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, ∀ x, ∀ n, 0 < n →
      ‖iteratedFDeriv ℝ n (ψ t) x‖ ≤ B*t*(4*R)^n*(n.factorial : ℝ)^2 := by
  intro t ht x n hn
  apply derivative_bound_of_generating_sum (ψ t) n n R (B*t) x hR
    (Finset.mem_Icc.mpr ⟨hn,le_rfl⟩)
  exact flow_generating_sum_bound_of_jet_derivative ψ b n T B R hT hB hR hsmall
    (fun s hs => (hψ s hs).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _))
    (fun s hs => (hb s hs).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)) hψ0
    (fun s hs y j hj => hbjet s hs y j (Finset.mem_Icc.mp hj).1)
    (fun j hj => hd j (Finset.mem_Icc.mp hj).1)
    (fun j hj => hcv j (Finset.mem_Icc.mp hj).1) t ht x

end EulerGevreyFlowFinite

end
end

end

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff BoundedContinuousFunction Interval

namespace EulerSmoothFlowGevrey

open EulerSmoothBanachFlow EulerGevreyFlowFinite EulerGevreyGeneratingDerivatives
  EulerVolterraConvolution

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A : SmoothTimeField (Icc (0 : ℝ) T) E E)

/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowGevrey1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instSmoothFlowGevrey2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowGevrey3 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] E)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowGevrey4 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] E)) := inferInstance

/-- Velocity extension, given by `A.field (projIcc 0 T hT t) x`. -/
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
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
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
    (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B * R * T ≤ 1 / 8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
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
    (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B * R * T ≤ 1 / 8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) :
    ‖iteratedFDeriv ℝ n (displacement T hT A t) x‖ ≤
      B*t*(4*R)^n*(n.factorial : ℝ)^2 := by
  exact derivative_bound_of_generating_sum (displacement T hT A t) n n R (B*t) x hR
    (Finset.mem_Icc.mpr ⟨hn,le_rfl⟩)
    (constructed_generating_sum_bound T hT A B R hB hR hsmall hb n t ht x)

/-- Order zero uses direct integration of the actual velocity. -/
theorem displacement_zero_bound (B R : ℝ)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
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
    (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B * R * T ≤ 1 / 8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) :
    ‖iteratedFDeriv ℝ n (displacement T hT A t) x‖ ≤
      B*t*(4*R)^n*(n.factorial : ℝ)^2 := by
  by_cases hn : n = 0
  · subst n
    simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one] using
      displacement_zero_bound T hT A B R hb t ht x
  · exact displacement_positive_bound T hT A B R hB hR hsmall hb n (Nat.pos_of_ne_zero hn) t ht x

end EulerSmoothFlowGevrey
