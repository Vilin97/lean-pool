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

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Tactic

/-! # Schur Constancy -/

@[expose] public noncomputable section

/-!
# Constancy for the global step of Schur's argument

This file proves only constancy from a vanishing manifold differential, not
Schur's curvature theorem. The local argument uses the convex range of a
model with corners, so boundary and corners are allowed. In fact, neither
finite dimensionality nor smoothness beyond differentiability is needed.
-/

open Set Filter Manifold
open scoped Topology ContDiff

namespace SchurConstancy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- A differentiable real function with zero manifold differential is locally constant. -/
theorem isLocallyConstant_of_mfderiv_eq_zero {f : M → ℝ}
    (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hzero : ∀ x, mfderiv I 𝓘(ℝ, ℝ) f x = 0) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp
    (extChartAt_target_mem_nhdsWithin (I := I) x)
  let s := Metric.ball (extChartAt I x x) r ∩ range I
  have hd : ∀ z ∈ s, HasFDerivWithinAt
      (f ∘ (extChartAt I x).symm) (0 : E →L[ℝ] ℝ) s z := by
    intro z hz
    have hfz := (hf ((extChartAt I x).symm z)).hasMFDerivAt
    rw [hzero] at hfz
    have hc := hfz.comp_hasMFDerivWithinAt z
      (mdifferentiableWithinAt_extChartAt_symm (hball hz)).hasMFDerivWithinAt
    have hc' : HasFDerivWithinAt (f ∘ (extChartAt I x).symm)
        (0 : E →L[ℝ] ℝ) (range I) z := by
      simpa only [ContinuousLinearMap.zero_comp,
        hasMFDerivWithinAt_iff_hasFDerivWithinAt] using! hc
    exact hc'.mono inter_subset_right
  have hx : extChartAt I x x ∈ s :=
    ⟨Metric.mem_ball_self hr, ⟨_, rfl⟩⟩
  have hs : Convex ℝ s := (convex_ball _ _).inter I.convex_range
  have heq : ∀ z ∈ s, (f ∘ (extChartAt I x).symm) z = f x := by
    intro z hz
    have hh := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le (C := 0) hd
      (fun z hz => by simp) hz hx
    have he : (f ∘ (extChartAt I x).symm) (extChartAt I x x) =
        (f ∘ (extChartAt I x).symm) z := by
      simpa only [norm_le_zero_iff, zero_mul, sub_eq_zero] using hh
    simpa using he.symm
  have hb := (continuousAt_extChartAt (I := I) x).preimage_mem_nhds
    (Metric.ball_mem_nhds _ hr)
  filter_upwards [hb, (isOpen_extChartAt_source (I := I) x).mem_nhds
    (mem_extChartAt_source (I := I) x)] with y hy hys
  have hh := heq (extChartAt I x y) ⟨hy, ⟨_, rfl⟩⟩
  simpa only [Function.comp_apply, (extChartAt I x).left_inv hys] using hh

/-- Connectedness globalizes the vanishing-differential condition. -/
theorem eq_of_mfderiv_eq_zero [PreconnectedSpace M] {f : M → ℝ}
    (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hzero : ∀ x, mfderiv I 𝓘(ℝ, ℝ) f x = 0) (x y : M) : f x = f y :=
  (isLocallyConstant_of_mfderiv_eq_zero I hf hzero).apply_eq_of_preconnectedSpace x y

/-- A smooth real function on a connected manifold whose differential vanishes
is a constant function. This applies in particular to every finite-dimensional
smooth real manifold, with any model with corners. -/
theorem exists_const_of_contMDiff_mfderiv_eq_zero [ConnectedSpace M] {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hzero : ∀ x, mfderiv I 𝓘(ℝ, ℝ) f x = 0) :
    ∃ c : ℝ, ∀ x, f x = c := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  exact ⟨f x₀, fun x => eq_of_mfderiv_eq_zero I
    (hf.mdifferentiable (by simp)) hzero x x₀⟩

/-- Scalar cancellation of the dimension factor appearing in Schur's argument.
The subtraction is in `ℝ`, not truncated natural subtraction. -/
theorem scalar_eq_zero_of_dimension_factor {n : ℕ} (hn : 3 ≤ n) {d : ℝ}
    (h : ((n : ℝ) - 2) * d = 0) : d = 0 := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  exact (mul_eq_zero.mp h).resolve_left (by linarith)

/-- The same cancellation for a differential, or any real module element. -/
theorem eq_zero_of_dimension_factor_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (hn : 3 ≤ n) {d : V} (h : ((n : ℝ) - 2) • d = 0) : d = 0 := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  exact (smul_eq_zero.mp h).resolve_left (by linarith)

end SchurConstancy
