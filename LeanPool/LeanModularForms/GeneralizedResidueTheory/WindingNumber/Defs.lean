/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Basic
import LeanPool.LeanModularForms.GeneralizedResidueTheory.PrincipalValue
import LeanPool.LeanModularForms.GeneralizedResidueTheory.WindingNumber.Proposition22
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Homotopy.Integrality
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Winding Number: Definitions and Simple Results

Definitions for generalized winding numbers of piecewise C¹ curves,
including the Hungerbühler-Wasem angle-based approach.

## Main Definitions

* `angleAtCrossing` — angle at a crossing point where γ passes through z₀
* `windingNumberWithAngles'` — winding number via explicit angle sum
* `PiecewiseC1Immersion.translate` — translate an immersion
* `externalWindingContribution` — winding from the curve's global topology

## Main Results

* `windingNumber_smooth_crossing` — smooth crossing contributes 1/2
* `windingNumber_corner_crossing` — corner with angle α contributes α/(2π)
* `angleAtCrossing_translate` — translation invariance of crossing angle
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section


/-- The angle at a crossing point where γ passes through z₀.
`arg(L_out) - arg(-L_in)` where L_in and L_out are one-sided derivative
limits. At smooth points (not in partition), returns π. -/
def angleAtCrossing (γ : PiecewiseC1Immersion) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) : ℝ :=
  if h : t₀ ∈ γ.toPiecewiseC1Curve.partition then
    let L_left :=
      Classical.choose (γ.left_deriv_limit t₀ h ht₀.1)
    let L_right :=
      Classical.choose (γ.right_deriv_limit t₀ h ht₀.2)
    arg L_right - arg (-L_left)
  else Real.pi

theorem angleAtCrossing_smooth (γ : PiecewiseC1Immersion)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hsmooth : t₀ ∉ γ.toPiecewiseC1Curve.partition) :
    angleAtCrossing γ t₀ ht₀ = Real.pi := by simp only [angleAtCrossing, hsmooth, ↓reduceDIte]

/-- Winding number via explicit angle sum at crossings. -/
def windingNumberWithAngles'
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (crossings : Finset ℝ)
    (hcrossings_in : ∀ t ∈ crossings, t ∈ Ioo γ.a γ.b)
    (hcrossings_at : ∀ t ∈ crossings, γ.toFun t = z₀) :
    ℂ :=
  -- `hcrossings_at` (and hence `z₀`) records that the listed parameters are the
  -- crossings of `γ` through `z₀`; it is consumed here so the definition carries
  -- this provenance even though the angle sum itself does not reference `z₀`.
  let _ := hcrossings_at
  ∑ t : crossings,
    (angleAtCrossing γ t
      (hcrossings_in t t.prop)) / (2 * Real.pi)

theorem singleton_mem_Ioo (t₀ : ℝ) (a b : ℝ)
    (ht₀ : t₀ ∈ Ioo a b) :
    ∀ t ∈ ({t₀} : Finset ℝ), t ∈ Ioo a b := by
  simp_all [Finset.mem_singleton]

theorem singleton_at_crossing (γ : PiecewiseC1Immersion)
    (t₀ : ℝ) (z₀ : ℂ) (hcross : γ.toFun t₀ = z₀) :
    ∀ t ∈ ({t₀} : Finset ℝ), γ.toFun t = z₀ := by
  simp_all [Finset.mem_singleton]

/-- A single smooth crossing contributes 1/2 to the winding number. -/
theorem windingNumber_smooth_crossing
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀)
    (hsmooth : t₀ ∉ γ.toPiecewiseC1Curve.partition) :
    windingNumberWithAngles' γ z₀ {t₀}
      (singleton_mem_Ioo t₀ γ.a γ.b ht₀)
      (singleton_at_crossing γ t₀ z₀ hcross) = 1/2 := by
  simp only [windingNumberWithAngles']
  rw [Fintype.sum_unique]
  simp only [Finset.default_singleton]
  rw [angleAtCrossing_smooth γ t₀ ht₀ hsmooth]
  field_simp [Real.pi_ne_zero]

/-- A corner crossing with angle α contributes α/(2π). -/
theorem windingNumber_corner_crossing
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (α : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀)
    (hangle : angleAtCrossing γ t₀ ht₀ = α) :
    windingNumberWithAngles' γ z₀ {t₀}
      (singleton_mem_Ioo t₀ γ.a γ.b ht₀)
      (singleton_at_crossing γ t₀ z₀ hcross) =
    α / (2 * Real.pi) := by
  simp only [windingNumberWithAngles']
  rw [Fintype.sum_unique]
  simp only [Finset.default_singleton]
  rw [hangle]

/-- When γ avoids z₀, the PV cutoff is trivial below minimum distance. -/
theorem cauchyPrincipalValue_eq_classical_off_curve'
    (γ : PiecewiseC1Curve) (z₀ : ℂ)
    (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z₀) :
    ∃ δ > 0, ∀ ε < δ, ∀ t ∈ Icc γ.a γ.b,
      ‖γ.toFun t - z₀‖ > ε := by
  have h_dist_pos :
      0 < Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b) := by
    rw [← Metric.infDist_pos_iff_notMem_closure
      ⟨γ.toFun γ.a, mem_image_of_mem _ (left_mem_Icc.mpr γ.hab.le)⟩,
      (isCompact_Icc.image_of_continuousOn γ.continuous_toFun).isClosed.closure_eq]
    rw [mem_image]; push Not; intro t ht; exact hoff t ht
  exact ⟨_, h_dist_pos, fun ε hε t ht => by
    calc ‖γ.toFun t - z₀‖
        = dist (γ.toFun t) z₀ := (dist_eq_norm _ _).symm
      _ = dist z₀ (γ.toFun t) := dist_comm _ _
      _ ≥ Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b) :=
          Metric.infDist_le_dist_of_mem (mem_image_of_mem _ ht)
      _ > ε := hε⟩

theorem integral_inv_real_axis (r ε : ℝ) (hr : 0 < r)
    (hε : 0 < ε) :
    ∫ t in ε..r, (t : ℂ)⁻¹ =
    Complex.log r - Complex.log ε := by
  simp_rw [← Complex.ofReal_inv]
  have h_real : ∫ t in ε..r, (t : ℝ)⁻¹ = Real.log r - Real.log ε := by
    rw [integral_inv_of_pos hε hr, Real.log_div hr.ne' hε.ne']
  rw [intervalIntegral.integral_ofReal, h_real]
  simp only [Complex.ofReal_sub,
    Complex.ofReal_log hr.le, Complex.ofReal_log hε.le]

/-- Translate a piecewise C¹ immersion by a constant. -/
def PiecewiseC1Immersion.translate
    (γ : PiecewiseC1Immersion) (c : ℂ) :
    PiecewiseC1Immersion where
  toFun := fun t => γ.toFun t + c
  a := γ.a
  b := γ.b
  hab := γ.hab
  partition := γ.partition
  partition_subset := γ.partition_subset
  endpoints_in_partition := γ.endpoints_in_partition
  continuous_toFun := γ.continuous_toFun.add continuousOn_const
  smooth_off_partition := fun t ht ht' =>
    (γ.smooth_off_partition t ht ht').add
      (differentiableAt_const _)
  deriv_continuous_off_partition := by
    intro t ht hnp
    have := γ.deriv_continuous_off_partition t ht hnp
    convert this using 1
    exact funext fun x => by rw [deriv_add_const]
  deriv_ne_zero := by
    intro t ht ht'
    rw [deriv_add_const]
    exact γ.deriv_ne_zero t ht ht'
  left_deriv_limit := by
    intro p hp hp'
    obtain ⟨L, hL_ne, hL⟩ := γ.left_deriv_limit p hp hp'
    exact ⟨L, hL_ne, by
      have h : deriv (fun t => γ.toFun t + c) =
          deriv γ.toFun := funext fun _ => deriv_add_const c
      rwa [h]⟩
  right_deriv_limit := by
    intro p hp hp'
    obtain ⟨L, hL_ne, hL⟩ := γ.right_deriv_limit p hp hp'
    exact ⟨L, hL_ne, by
      have h : deriv (fun t => γ.toFun t + c) =
          deriv γ.toFun := funext fun _ => deriv_add_const c
      rwa [h]⟩

/-- The angle at a crossing is invariant under translation. -/
theorem angleAtCrossing_translate
    (γ : PiecewiseC1Immersion) (c : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) :
    angleAtCrossing (γ.translate c) t₀ ht₀ =
    angleAtCrossing γ t₀ ht₀ := by
  unfold angleAtCrossing
  generalize_proofs at *
  unfold PiecewiseC1Immersion.translate; aesop

/-- The external winding contribution at a single crossing point.
For a closed piecewise C¹ immersion passing through z₀ exactly once,
this measures the winding of the curve around z₀ apart from the local
crossing angle. Mathematically, this is the classical winding number
of the modified curve Λ that detours around z₀ (H-W Proposition 2.2).

The decomposition is `n_{z₀}(γ) = N - α/(2π)`, so `N = n_{z₀}(γ) + α/(2π)`.
When `N = 0`, the generalized winding number equals `-α/(2π)`. -/
def externalWindingContribution (γ : PiecewiseC1Immersion)
    (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) : ℂ :=
  generalizedWindingNumber' γ.toFun γ.a γ.b z₀ +
    (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * Real.pi)


end
