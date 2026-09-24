/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedCutoff
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform derivatives of fixed and domain-adapted cutoffs

A fixed smooth compactly supported function has one numerical bound for its
value, time derivative, spatial first derivatives, and spatial Laplacian.
Equality of germs transports these bounds without imposing smoothness or
support assumptions on the second function. In particular the negative-time
bounds of a domain-adapted cutoff retain the fixed function's constants.
-/

@[expose] public section

open Set Filter
open scoped Topology BigOperators
open CKN.Foundation.Parabolic CKN.Core.Step3


noncomputable section

namespace CKN.Core.Endgame

private theorem spatial_partial_eq_of_eventuallyEq
    {φ ψ : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (h : φ =ᶠ[𝓝 z] ψ) (i : Fin 3) : spatialPartial φ i z = spatialPartial ψ i z := by
  have hmap : Continuous (fun x : Vec3 => (x, z.2)) := continuous_id.prodMk continuous_const
  have hslice : (fun x : Vec3 => φ (x, z.2)) =ᶠ[𝓝 z.1]
      (fun x => ψ (x, z.2)) := hmap.continuousAt.preimage_mem_nhds h
  exact congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) hslice.fderiv_eq

private theorem laplacian_eq_sum_second (ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) :
    spatialLaplacian (fun x => ψ (x, z.2)) z.1 = ∑ i, spatialSecondPartial ψ i i z := rfl

/-- Equality near a space-time point preserves all derivatives entering
the localized heat equation, including the spatial Laplacian. -/
theorem cutoff_derivatives_eq_of_eventuallyEq
    {φ ψ : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ} (h : φ =ᶠ[𝓝 z] ψ) :
    φ z = ψ z ∧ timePartial φ z = timePartial ψ z ∧
      (∀ i, spatialPartial φ i z = spatialPartial ψ i z) ∧
      spatialLaplacian (fun x => φ (x, z.2)) z.1 =
        spatialLaplacian (fun x => ψ (x, z.2)) z.1 := by
  refine ⟨h.eq_of_nhds, ?_, spatial_partial_eq_of_eventuallyEq h, ?_⟩
  · have hmap : Continuous (fun t : ℝ => (z.1, t)) := continuous_const.prodMk continuous_id
    have hslice : (fun t : ℝ => φ (z.1, t)) =ᶠ[𝓝 z.2]
        (fun t => ψ (z.1, t)) := hmap.continuousAt.preimage_mem_nhds h
    exact congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hslice.fderiv_eq
  · rw [laplacian_eq_sum_second, laplacian_eq_sum_second]
    apply Finset.sum_congr rfl
    intro i _
    have hi : (fun w : Vec3 × ℝ => spatialPartial φ i w) =ᶠ[𝓝 z]
        (fun w : Vec3 × ℝ => spatialPartial ψ i w) := by
      filter_upwards [h.eventuallyEq_nhds] with w hw
      exact spatial_partial_eq_of_eventuallyEq hw i
    exact spatial_partial_eq_of_eventuallyEq hi i

private theorem exists_abs_bound_of_compact_zero
    {ψ g : Vec3 × ℝ → ℝ} (hc : HasCompactSupport ψ) (hg : Continuous g)
    (hzero : ∀ z ∉ tsupport ψ, g z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |g z| ≤ C := by
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro z
  by_cases hz : z ∈ tsupport ψ
  · exact (show |g z| ≤ B by simpa only [Real.norm_eq_abs] using hB z hz).trans
      (le_max_left _ _)
  · rw [hzero z hz, abs_zero]
    exact le_max_right _ _

/-- A smooth compactly supported cutoff has a single finite numerical
bound for all scalar coefficients in the localized equation. -/
theorem exists_cutoff_derivative_bound
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Vec3 × ℝ,
      |ψ z| ≤ C ∧ |timePartial ψ z| ≤ C ∧
      (∀ i, |spatialPartial ψ i z| ≤ C) ∧
      |spatialLaplacian (fun x => ψ (x, z.2)) z.1| ≤ C := by
  obtain ⟨C₀, hC₀, hb₀⟩ := exists_abs_bound_of_compact_zero hc hψ.continuous
    (fun _ hz => image_eq_zero_of_notMem_tsupport hz)
  obtain ⟨Ct, hCt, hbt⟩ := exists_abs_bound_of_compact_zero hc
    (timePartial_contDiff_full hψ).continuous
    (fun _ hz => timePartial_zero_of_not_mem_tsupport_public hψ hz)
  have hx : ∀ i : Fin 3, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : Vec3 × ℝ, |spatialPartial ψ i z| ≤ C := fun i =>
    exists_abs_bound_of_compact_zero hc (spatialPartial_contDiff hψ i).continuous
      (fun _ hz => spatialPartial_zero_of_not_mem_tsupport_public hψ hz i)
  choose Cx hCx hbx using hx
  have hΔ : Continuous (fun z : Vec3 × ℝ => spatialLaplacian (fun x => ψ (x, z.2)) z.1) := by
    simp only [laplacian_eq_sum_second]
    exact continuous_finsetSum _ fun i _ => (spatialSecondPartial_contDiff_full hψ i i).continuous
  have hΔzero : ∀ z ∉ tsupport ψ, spatialLaplacian (fun x => ψ (x, z.2)) z.1 = 0 := by
    intro z hz
    rw [laplacian_eq_sum_second]
    exact Finset.sum_eq_zero fun i _ => spatialSecondPartial_zero_of_not_mem_tsupport_public hψ hz i i
  obtain ⟨CΔ, hCΔ, hbΔ⟩ := exists_abs_bound_of_compact_zero hc hΔ hΔzero
  have hsum : 0 ≤ ∑ i, Cx i := Finset.sum_nonneg fun i _ => hCx i
  refine ⟨1 + C₀ + Ct + (∑ i, Cx i) + CΔ, by linarith only [hC₀, hCt, hsum, hCΔ], ?_⟩
  intro z
  refine ⟨(hb₀ z).trans ?_, (hbt z).trans ?_, ?_, (hbΔ z).trans ?_⟩
  · linarith only [hCt, hsum, hCΔ]
  · linarith only [hC₀, hsum, hCΔ]
  · intro i
    have hi : Cx i ≤ ∑ j, Cx j := Finset.single_le_sum (fun j _ => hCx j) (Finset.mem_univ i)
    exact (hbx i z).trans (hi.trans (by linarith only [hC₀, hCt, hCΔ]))
  · linarith only [hC₀, hCt, hsum]

/-- Negative-time germ agreement transfers a fixed numerical derivative
bound, with no dependence on the domain of the adapted cutoff. -/
theorem cutoff_derivative_bound_on_past_of_eventuallyEq
    {φ ψ : Vec3 × ℝ → ℝ} {C : ℝ}
    (hbound : ∀ z : Vec3 × ℝ,
      |ψ z| ≤ C ∧ |timePartial ψ z| ≤ C ∧
      (∀ i, |spatialPartial ψ i z| ≤ C) ∧
      |spatialLaplacian (fun x => ψ (x, z.2)) z.1| ≤ C)
    (hagree : ∀ z : Vec3 × ℝ, z.2 ≤ 0 → φ =ᶠ[𝓝 z] ψ) :
    ∀ z : Vec3 × ℝ, z.2 ≤ 0 →
      |φ z| ≤ C ∧ |timePartial φ z| ≤ C ∧
      (∀ i, |spatialPartial φ i z| ≤ C) ∧
      |spatialLaplacian (fun x => φ (x, z.2)) z.1| ≤ C := by
  intro z ht
  obtain ⟨heq, htime, hspace, hlap⟩ := cutoff_derivatives_eq_of_eventuallyEq (hagree z ht)
  simpa only [heq, htime, hspace, hlap] using hbound z


end CKN.Core.Endgame
