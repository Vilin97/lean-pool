/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

@[expose] public section

/-! The finite generating-sum bootstrap used for the small lifted flow in
source (21).  A first-hitting argument proves the bound from an integral
inequality valid only inside its radius of convergence.  No global
smallness of the unknown path or exponential flow bound is assumed. -/

noncomputable section

namespace EulerGevreyFlowBootstrap

open Set MeasureTheory
open scoped Interval

/-- A continuous path cannot first hit a barrier if its bound up to that
first hit lies strictly below the barrier. -/
theorem continuous_barrier (f : ℝ → ℝ) (T B a : ℝ)
    (_hT : 0 ≤ T) (hB : 0 ≤ B) (ha : 0 < a) (hBa : B * T < a)
    (hf : ContinuousOn f (Icc 0 T)) (hf0 : f 0 = 0)
    (hstep : ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, f s ≤ a) → f t ≤ B * t) :
    ∀ t ∈ Icc 0 T, f t ≤ B*t := by
  have hstrict : ∀ t ∈ Icc 0 T, f t < a := by
    intro t ht
    by_contra hfail
    let S := Icc (0 : ℝ) T ∩ f ⁻¹' Ici a
    have hSc : IsCompact S := isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici) inter_subset_left
    have hSn : S.Nonempty := ⟨t,ht,le_of_not_gt hfail⟩
    obtain ⟨m,hm⟩ := hSc.exists_isLeast hSn
    have hmI : m ∈ Icc (0 : ℝ) T := hm.1.1
    have hmhigh : a ≤ f m := hm.1.2
    have hfm : f m = a := by
      have hc : ContinuousOn f (Icc 0 m) := hf.mono (Icc_subset_Icc_right hmI.2)
      obtain ⟨r,hr,her⟩ := intermediate_value_Icc hmI.1 hc
        (show a ∈ Icc (f 0) (f m) from ⟨by rw [hf0]; exact ha.le,hmhigh⟩)
      have hmr : m ≤ r := hm.2 ⟨⟨hr.1,hr.2.trans hmI.2⟩,her.ge⟩
      have hrm : r = m := le_antisymm hr.2 hmr
      simpa only [hrm] using her
    have hbefore : ∀ s ∈ Icc 0 m, f s ≤ a := by
      intro s hs
      by_cases hsm : s = m
      · simp only [hsm,hfm,le_refl]
      · have hlt : s < m := lt_of_le_of_ne hs.2 hsm
        by_contra hhigh
        have hms : m ≤ s := hm.2 ⟨⟨hs.1,hs.2.trans hmI.2⟩,(lt_of_not_ge hhigh).le⟩
        exact (not_le_of_gt hlt) hms
    have hh := hstep m hmI hbefore
    have hmB : B*m ≤ B*T := mul_le_mul_of_nonneg_left hmI.2 hB
    rw [hfm] at hh
    linarith
  intro t ht
  exact hstep t ht (fun s hs => (hstrict s ⟨hs.1,hs.2.trans ht.2⟩).le)

def rationalRate (B R a u : ℝ) : ℝ := B*(R*(a+u))/(1-R*(a+u))

theorem rationalRate_le (B R a u : ℝ) (hB : 0 ≤ B)
    (hu : R * (a + u) ≤ 1 / 2) : rationalRate B R a u ≤ B := by
  have hd : 0 < 1-R*(a+u) := by linarith
  unfold rationalRate
  apply (div_le_iff₀ hd).2
  nlinarith [mul_le_mul_of_nonneg_left hu hB]

/-- The nonlinear generating-sum inequality closes at BRT≤1/8.  The bound
is linear in the velocity size B and time, with no exponential factor. -/
theorem rational_integral_bootstrap (f : ℝ → ℝ) (T B R : ℝ)
    (hT : 0 ≤ T) (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B * R*T ≤ 1 / 8)
    (hf : ContinuousOn f (Icc 0 T)) (hf0 : f 0 = 0)
    (hineq : ∀ t ∈ Icc 0 T,
      (∀ s ∈ Icc 0 t, R * ((4 * R)⁻¹ + f s) ≤ 1 / 2) →
      f t ≤ ∫ s in 0..t, rationalRate B R ((4 * R)⁻¹) (f s)) :
    ∀ t ∈ Icc 0 T, f t ≤ B*t ∧ R*((4*R)⁻¹+f t) ≤ 3/8 := by
  have ha : 0 < (4*R)⁻¹ := inv_pos.mpr (by positivity)
  have hRa : R*(4*R)⁻¹ = 1/4 := by field_simp
  have hBT : B*T < (4*R)⁻¹ := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt h) hR.le
    rw [hRa] at hm
    nlinarith
  have hb : ∀ t ∈ Icc 0 T, f t ≤ B*t := by
    apply continuous_barrier f T B ((4*R)⁻¹) hT hB ha hBT hf hf0
    intro t ht hbefore
    have hhalf : ∀ s ∈ Icc 0 t, R*((4*R)⁻¹+f s) ≤ 1/2 := by
      intro s hs
      have hm := mul_le_mul_of_nonneg_left (hbefore s hs) hR.le
      nlinarith
    have hden : ∀ s ∈ Icc 0 t, 1-R*((4*R)⁻¹+f s) ≠ 0 := by
      intro s hs
      have hh := hhalf s hs
      linarith
    have hrate : ContinuousOn (fun s => rationalRate B R ((4*R)⁻¹) (f s)) (Icc 0 t) := by
      have hf' := hf.mono (Icc_subset_Icc_right ht.2)
      unfold rationalRate
      exact (continuousOn_const.mul (continuousOn_const.mul (continuousOn_const.add hf'))).div
        (continuousOn_const.sub (continuousOn_const.mul (continuousOn_const.add hf'))) hden
    have hi : IntervalIntegrable (fun s => rationalRate B R ((4*R)⁻¹) (f s)) volume 0 t :=
      hrate.intervalIntegrable_of_Icc ht.1
    have hm := intervalIntegral.integral_mono_on ht.1 hi intervalIntegrable_const
      (fun s hs => rationalRate_le B R ((4*R)⁻¹) (f s) hB (hhalf s hs))
    have hc : (∫ s in (0 : ℝ)..t, B) = B*t := by simp [mul_comm]
    exact (hineq t ht hhalf).trans (hm.trans_eq hc)
  intro t ht
  refine ⟨hb t ht,?_⟩
  have hm := mul_le_mul_of_nonneg_left (hb t ht) hR.le
  have htB := mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hB hR.le)
  nlinarith

end EulerGevreyFlowBootstrap
