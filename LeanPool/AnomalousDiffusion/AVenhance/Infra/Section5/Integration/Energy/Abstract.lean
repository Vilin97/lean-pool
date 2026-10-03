/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # An integrated differential inequality (pure real analysis)

If `E` is continuous on `[0,1]`, differentiable on `(0,∞)` with continuous derivative `D`, and
`D ≤ h` almost everywhere on `(0,1)` for an integrable `h`, then
`E t - E 0 ≤ ∫₀ᵗ h` for every `t ∈ [0,1]`. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace AVenhance.Infra.Section5.Integration.Energy

/-- On a compact subinterval of `(0,1]` the fundamental theorem gives the integrated inequality. -/
theorem sub_le_integral_of_deriv_le {E D h : ℝ → ℝ} {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (ht : t ≤ 1)
    (hEd : ∀ x, 0 < x → HasDerivAt E (D x) x)
    (hDc : ContinuousOn D (Ioi 0))
    (hh : IntegrableOn h (Ioo 0 1))
    (hineq : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1), D x ≤ h x) :
    E t - E s ≤ ∫ x in s..t, h x := by
  have hsub : uIcc s t ⊆ Ioi 0 := by
    rw [uIcc_of_le hst]
    intro x hx
    exact lt_of_lt_of_le hs hx.1
  have hDint : IntervalIntegrable D volume s t :=
    (hDc.mono hsub).intervalIntegrable
  have hftc : ∫ x in s..t, D x = E t - E s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hEd x (hsub hx)) hDint
  have hhIoc : IntegrableOn h (Ioc 0 1) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).2 hh
  have hhint : IntervalIntegrable h volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact hhIoc.mono_set (Ioc_subset_Ioc hs.le ht)
  have hae : ∀ᵐ x ∂volume.restrict (Icc 0 1), D x ≤ h x := by
    rwa [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  have hae' : ∀ᵐ x ∂volume.restrict (Icc s t), D x ≤ h x :=
    ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hs.le ht) hae
  rw [← hftc]
  exact intervalIntegral.integral_mono_ae_restrict hst hDint hhint hae'

/-- The integrated differential inequality on `[0,1]`. -/
theorem sub_le_integral_of_deriv_le_ae {E D h : ℝ → ℝ}
    (hEc : ContinuousOn E (Icc 0 1))
    (hEd : ∀ x, 0 < x → HasDerivAt E (D x) x)
    (hDc : ContinuousOn D (Ioi 0))
    (hh : IntegrableOn h (Ioo 0 1))
    (hineq : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1), D x ≤ h x) :
    ∀ t ∈ Icc (0 : ℝ) 1, E t - E 0 ≤ ∫ x in (0 : ℝ)..t, h x := by
  intro t ht
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    simp
  have hhIcc : IntegrableOn h (Icc 0 1) := (integrableOn_Icc_iff_integrableOn_Ioo).2 hh
  have hhI : IntegrableOn h (uIcc 0 1) := by rwa [uIcc_of_le zero_le_one]
  have hP : ContinuousOn (fun x => ∫ y in (0 : ℝ)..x, h y) (uIcc 0 1) :=
    intervalIntegral.continuousOn_primitive_interval hhI
  rw [uIcc_of_le zero_le_one] at hP
  have hint0 : ∀ x ∈ Icc (0 : ℝ) 1, IntervalIntegrable h volume 0 x := by
    intro x hx
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx.1]
    exact hhIcc.mono_set (Icc_subset_Icc le_rfl hx.2)
  have hmono : Ioo 0 t ⊆ Icc (0 : ℝ) 1 := fun x hx => ⟨hx.1.le, hx.2.le.trans ht.2⟩
  have hl : Tendsto (fun x => E x - ∫ y in (0 : ℝ)..x, h y) (𝓝[Ioo 0 t] 0)
      (𝓝 (E 0 - ∫ y in (0 : ℝ)..0, h y)) := by
    have hE0 : ContinuousWithinAt E (Ioo 0 t) 0 :=
      (hEc 0 ⟨le_rfl, zero_le_one⟩).mono hmono
    have hP0 : ContinuousWithinAt (fun x => ∫ y in (0 : ℝ)..x, h y) (Ioo 0 t) 0 :=
      (hP 0 ⟨le_rfl, zero_le_one⟩).mono hmono
    exact hE0.sub hP0
  have hne : (𝓝[Ioo 0 t] (0 : ℝ)).NeBot := by
    have : (0 : ℝ) ∈ closure (Ioo 0 t) := by
      rw [closure_Ioo hpos.ne]
      exact ⟨le_rfl, hpos.le⟩
    exact mem_closure_iff_nhdsWithin_neBot.1 this
  have hev : ∀ᶠ x in 𝓝[Ioo 0 t] (0 : ℝ),
      E t - ∫ y in (0 : ℝ)..t, h y ≤ E x - ∫ y in (0 : ℝ)..x, h y := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have h1 := sub_le_integral_of_deriv_le hx.1 hx.2.le ht.2 hEd hDc hh hineq
    have hxI := hint0 x (hmono hx)
    have htI := hint0 t ht
    have h2 : ∫ y in x..t, h y = (∫ y in (0 : ℝ)..t, h y) - ∫ y in (0 : ℝ)..x, h y :=
      (intervalIntegral.integral_interval_sub_left htI hxI).symm
    linarith
  have := ge_of_tendsto hl hev
  simp only [intervalIntegral.integral_same, sub_zero] at this
  linarith

end AVenhance.Infra.Section5.Integration.Energy

end
