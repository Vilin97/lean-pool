/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonCutoffs
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicUniqueness
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactTimeIntegral
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Constants supplied by the compactly supported comparison solution

These bounds are consequences of joint smoothness and one fixed compact
spatial support. They impose no condition on the competing solution.
-/

@[expose] public section



noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace NavierStokesR3.CompactComparisonBounds

open ProblemStatement Comparison
open NavierStokes.ProblemStatement (spatialDerivative)

/-- The shared compact support contains the support of every spatial slice. -/
theorem hasCompactSupport_slice {T : ℝ} {u : VelocityField} {K : Set Space}
    (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x : Space => u (t, x)) ⊆ K)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasCompactSupport (fun x : Space => u (t, x)) :=
  hK.of_isClosed_subset isClosed_closure (hsupp t ht)

/-- The candidate's first spatial derivative is bounded on all of space and
uniformly over the closed comparison interval. -/
theorem exists_gradient_bound {T : ℝ} (hT : 0 < T) {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab 0 T)) {K : Set Space} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x : Space => u (t, x)) ⊆ K) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
      ‖spatialDerivative u t x‖ ≤ G := by
  obtain ⟨G, hG, hbound⟩ := NavierStokes.PeriodicUniqueness.exists_gradient_bound hT hu hK
  refine ⟨G, hG.le, ?_⟩
  intro t ht x
  by_cases hx : x ∈ K
  · exact hbound t ht x hx
  · have hzero : spatialDerivative u t x = 0 :=
      fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hx (hsupp t ht h))
    rw [hzero, norm_zero]
    exact hG.le

/-- Compact support and continuity place every candidate slice in `L³`. -/
theorem memLp_three_slice {T : ℝ} {u : VelocityField}
    (hu : ContinuousOn u (slab 0 T)) {K : Set Space} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x : Space => u (t, x)) ⊆ K)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    MemLp (fun x : Space => u (t, x)) 3 volume :=
  (CompactTimeIntegral.continuous_slice hu ht).memLp_of_hasCompactSupport
    (hasCompactSupport_slice hK hsupp ht)

/-- The ordinary cube-norm integral varies continuously with time. -/
theorem continuousOn_integral_norm_cube {T : ℝ} {u : VelocityField}
    (hu : ContinuousOn u (slab 0 T)) {K : Set Space} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x : Space => u (t, x)) ⊆ K) :
    ContinuousOn (fun t => ∫ x : Space, ‖u (t, x)‖ ^ 3) (Icc (0 : ℝ) T) := by
  apply CompactTimeIntegral.continuousOn_integral
    (F := fun z : SpaceTime => ‖u z‖ ^ 3) hK (hu.norm.pow 3)
  intro t ht x hx
  have hzero : u (t, x) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y : Space => u (t, y))
      (fun h => hx (hsupp t ht h))
  simp only [hzero, norm_zero, zero_pow (by decide : (3 : ℕ) ≠ 0)]

/-- The finite `L³` norm has its ordinary integral formula. -/
theorem lpNorm_three_eq_integral_norm_cube_rpow {f : Space → Space}
    (hf : MemLp f 3 volume) :
    comparisonLpNorm 3 f = (∫ x : Space, ‖f x‖ ^ 3) ^ (3 : ℝ)⁻¹ := by
  have heq := MemLp.eLpNorm_eq_integral_rpow_norm
    (p := (3 : ℝ≥0∞)) (by norm_num) (by norm_num) hf
  norm_num only [ENNReal.toReal_ofNat] at heq
  rw [comparisonLpNorm, heq, ENNReal.toReal_ofReal]
  · rw [one_div]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun x => Real.rpow_natCast (‖f x‖) 3)
  · positivity

/-- One finite `L³` bound works at every time in the comparison interval. -/
theorem exists_lpNorm_three_bound {T : ℝ} {u : VelocityField}
    (hu : ContinuousOn u (slab 0 T)) {K : Set Space} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x : Space => u (t, x)) ⊆ K) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ t ∈ Icc (0 : ℝ) T,
      MemLp (fun x : Space => u (t, x)) 3 volume ∧
        comparisonLpNorm 3 (fun x => u (t, x)) ≤ U := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_integral_norm_cube hu hK hsupp)
  refine ⟨(max C 0) ^ (3 : ℝ)⁻¹, by positivity, ?_⟩
  intro t ht
  have hLp := memLp_three_slice hu hK hsupp ht
  refine ⟨hLp, ?_⟩
  rw [lpNorm_three_eq_integral_norm_cube_rpow hLp]
  apply Real.rpow_le_rpow (integral_nonneg (fun x => by positivity)) _ (by positivity)
  exact (le_abs_self _).trans ((hC t ht).trans (le_max_left _ _))

/-- The cutoff weight is locally constant throughout its strict plateau. -/
theorem weight_fderiv_eq_zero_of_norm_lt {R : ℝ} (hR : 0 < R)
    {x : Space} (hx : ‖x‖ < R) :
    fderiv ℝ (ComparisonCutoffs.weight R) x = 0 := by
  have heq : ComparisonCutoffs.weight R =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact ComparisonCutoffs.weight_eq_one hR hy.le
  rw [heq.fderiv_eq, fderiv_const_apply]

/-- Sufficiently large cutoffs have exactly zero derivative in the direction
of the compactly supported candidate, at every spatial point. -/
theorem exists_radius_weight_derivative_zero {T : ℝ} {u : VelocityField}
    {K : Set Space} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x : Space => u (t, x)) ⊆ K) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R ≥ R₀, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
      fderiv ℝ (ComparisonCutoffs.weight R) x (u (t, x)) = 0 := by
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  refine ⟨max 1 (C + 1), le_max_left _ _, ?_⟩
  intro R hR t ht x
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
  by_cases hx : x ∈ K
  · have hxR : ‖x‖ < R :=
      lt_of_le_of_lt (hC x hx) ((lt_add_one C).trans_le ((le_max_right _ _).trans hR))
    rw [weight_fderiv_eq_zero_of_norm_lt hRpos hxR]
    rfl
  · have hzero : u (t, x) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y : Space => u (t, y))
        (fun h => hx (hsupp t ht h))
    rw [hzero, map_zero]

/-- On a compact time interval, smoothness and one fixed compact spatial
support already imply the target's uniform finite-energy condition. -/
theorem uniformFiniteEnergy_of_compact_slab {T : ℝ} {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab 0 T)) {K : Set Space} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x : Space => u (t, x)) ⊆ K) :
    UniformFiniteEnergy (Icc (0 : ℝ) T) u := by
  have hcont : ContinuousOn (fun t => ∫ x : Space, ‖u (t, x)‖ ^ 2)
      (Icc (0 : ℝ) T) := by
    apply CompactTimeIntegral.continuousOn_integral
      (F := fun z : SpaceTime => ‖u z‖ ^ 2) hK (hu.continuousOn.norm.pow 2)
    intro t ht x hx
    have hzero : u (t, x) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y : Space => u (t, y))
        (fun h => hx (hsupp t ht h))
    simp only [hzero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨(1 / 2 : ℝ) * max C 0, by positivity, ?_⟩
  intro t ht
  have hLp : MemLp (fun x : Space => u (t, x)) 2 volume :=
    (CompactTimeIntegral.continuous_slice hu.continuousOn ht).memLp_of_hasCompactSupport
      (hasCompactSupport_slice hK hsupp ht)
  refine ⟨(memLp_two_iff_integrable_sq_norm hLp.1).1 hLp, ?_⟩
  have hbound : (∫ x : Space, ‖u (t, x)‖ ^ 2) ≤ max C 0 :=
    (le_abs_self _).trans ((hC t ht).trans (le_max_left _ _))
  exact mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 1 / 2)

end NavierStokesR3.CompactComparisonBounds
