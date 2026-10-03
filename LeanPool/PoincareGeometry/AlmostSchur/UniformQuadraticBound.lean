/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.Order.Compact

/-! # Uniform lower bounds for positive quadratic families

Compactness of the parameter set and unit sphere turns pointwise positivity
and degree-two homogeneity into a uniform norm-squared lower bound.
-/

@[expose] public noncomputable section
open Set Metric

namespace AlmostSchur

/-- A continuous positive homogeneous quadratic family is uniformly positive
over compact parameter sets, including empty sets and zero-dimensional spaces. -/
theorem exists_uniform_quadratic_lower_bound
    {X V : Type*} [TopologicalSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {K : Set X} (hK : IsCompact K)
    (q : X → V → ℝ)
    (hc : ContinuousOn (fun p : X × V => q p.1 p.2) (K ×ˢ sphere (0 : V) 1))
    (hp : ∀ x ∈ K, ∀ v : V, v ≠ 0 → 0 < q x v)
    (hs : ∀ x ∈ K, ∀ (a : ℝ) (v : V), q x (a • v) = a ^ 2 * q x v) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ v : V, C * ‖v‖ ^ 2 ≤ q x v := by
  have hz (x : X) (hx : x ∈ K) : q x 0 = 0 := by
    simpa using hs x hx 0 0
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨1, zero_lt_one, fun x hx v => ?_⟩
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv, hz x hx]
  rcases K.eq_empty_or_nonempty with hKe | hKn
  · subst K
    exact ⟨1, zero_lt_one, by simp⟩
  have hSn : (sphere (0 : V) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨p, hpK, hmin⟩ := (hK.prod (isCompact_sphere (0 : V) 1)).exists_isMinOn
    (hKn.prod hSn) hc
  have hpv : p.2 ≠ 0 := by
    have hn : ‖p.2‖ = 1 := mem_sphere_zero_iff_norm.mp hpK.2
    intro he
    simp [he] at hn
  refine ⟨q p.1 p.2, hp p.1 hpK.1 p.2 hpv, fun x hx v => ?_⟩
  by_cases hv : v = 0
  · simp [hv, hz x hx]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hunit : ‖v‖⁻¹ • v ∈ sphere (0 : V) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have hb := hmin (show (x, ‖v‖⁻¹ • v) ∈ K ×ˢ sphere (0 : V) 1 from ⟨hx, hunit⟩)
  change q p.1 p.2 ≤ q x (‖v‖⁻¹ • v) at hb
  rw [hs x hx] at hb
  have hb' := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖v‖)
  have he : (‖v‖⁻¹ ^ 2 * q x v) * ‖v‖ ^ 2 = q x v := by
    field_simp
  rwa [he] at hb'

/-- Every continuous degree-two homogeneous family has a compact uniform absolute bound. -/
theorem exists_uniform_quadratic_upper_bound
    {X V : Type*} [TopologicalSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {K : Set X} (hK : IsCompact K)
    (q : X → V → ℝ)
    (hc : ContinuousOn (fun p : X × V => q p.1 p.2) (K ×ˢ sphere (0 : V) 1))
    (hs : ∀ x ∈ K, ∀ (a : ℝ) (v : V), q x (a • v) = a ^ 2 * q x v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ v : V, |q x v| ≤ C * ‖v‖ ^ 2 := by
  have hz (x : X) (hx : x ∈ K) : q x 0 = 0 := by
    simpa using hs x hx 0 0
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_sphere (0 : V) 1)).exists_bound_of_continuousOn hc
  refine ⟨max B 0, le_max_right _ _, fun x hx v => ?_⟩
  by_cases hv : v = 0
  · simp [hv, hz x hx]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hunit : ‖v‖⁻¹ • v ∈ sphere (0 : V) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have hb := (hB (x, ‖v‖⁻¹ • v) ⟨hx, hunit⟩).trans (le_max_left B 0)
  change ‖q x (‖v‖⁻¹ • v)‖ ≤ max B 0 at hb
  rw [hs x hx, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)] at hb
  have hb' := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖v‖)
  have he : (‖v‖⁻¹ ^ 2 * |q x v|) * ‖v‖ ^ 2 = |q x v| := by field_simp
  rwa [he] at hb'

end AlmostSchur
