/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyGeneratingDerivatives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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
