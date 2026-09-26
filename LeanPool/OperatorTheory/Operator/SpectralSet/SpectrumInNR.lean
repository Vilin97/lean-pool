/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.Normed.Operator.Banach
public import LeanPool.OperatorTheory.Operator.NumericalRange.Helpers

/-!
# Spectrum inside the closure of the numerical range (L2.2)

`σ(A) ⊆ closure W(A)` for a continuous linear operator `A` on a complex Hilbert space.

Route (task-spec L2.2): if `λ ∉ closure W(A)`, there is `d > 0` with `d ≤ ‖⟪x, A x⟫_ℂ - λ‖` for
every unit vector `x`, i.e. `d ≤ ‖⟪x, B x⟫_ℂ‖` for `B = A - λ • 1`. By homogeneity and
Cauchy–Schwarz this gives `d * ‖x‖ ≤ ‖B x‖` for all `x` (`norm_apply_ge_of_forall_unit`), and
likewise for `B†`, since `⟪x, B† x⟫_ℂ = conj ⟪x, B x⟫_ℂ`. An operator bounded below is injective
with closed range, and its adjoint being bounded below makes the range dense; so `B` is bijective,
hence a unit (`isUnit_of_forall_norm_le`), i.e. `λ ∉ σ(A)`.

## Main declarations

* `norm_apply_ge_of_forall_unit` — a lower bound `d ≤ ‖⟪x, B x⟫_ℂ‖` on unit vectors gives
  `d * ‖x‖ ≤ ‖B x‖` for all `x`.
* `isUnit_of_forall_norm_le` — an operator bounded below whose adjoint is bounded below is a unit.
* `spectrum_subset_closure_numericalRange` — `σ(A) ⊆ closure W(A)`.

The proof was written by agent-alpha (`.sessions/agent-alpha/SpikeL22.lean`) and moved to
production, with one rewrite direction fixed, by agent-alpha-2.

Requires `[CompleteSpace E]` (adjoints and the spectrum of `E →L[ℂ] E`).
-/

@[expose] public section

open scoped InnerProductSpace
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A lower bound `d ≤ ‖⟪x, B x⟫_ℂ‖` on unit vectors gives `d * ‖x‖ ≤ ‖B x‖` for all `x`
(homogeneity of the quadratic form, then Cauchy–Schwarz). -/
theorem norm_apply_ge_of_forall_unit (B : E →L[ℂ] E) {d : ℝ}
    (h : ∀ x : E, ‖x‖ = 1 → d ≤ ‖⟪x, B x⟫_ℂ‖) (x : E) : d * ‖x‖ ≤ ‖B x‖ := by
  by_cases hx : x = 0
  · subst x
    simp only [norm_zero, mul_zero, map_zero, le_refl]
  · let y : E := ((‖x‖ : ℂ)⁻¹) • x
    have hy : ‖y‖ = 1 := norm_inv_norm_smul hx
    have hBy : d ≤ ‖B y‖ := calc
      d ≤ ‖⟪y, B y⟫_ℂ‖ := h y hy
      _ ≤ ‖y‖ * ‖B y‖ := norm_inner_le_norm y (B y)
      _ = ‖B y‖ := by rw [hy, one_mul]
    have hscaled : d ≤ ‖x‖⁻¹ * ‖B x‖ := by
      dsimp only [y] at hBy
      simpa only [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg x)] using hBy
    rw [← div_eq_inv_mul] at hscaled
    exact (le_div_iff₀ (norm_pos_iff.mpr hx)).mp hscaled

variable [CompleteSpace E]

/-- An operator bounded below (`d * ‖x‖ ≤ ‖B x‖`, `d > 0`) whose adjoint is bounded below is a
unit: it is injective with closed range, and the range is dense because its orthogonal complement
is the kernel of the adjoint. -/
theorem isUnit_of_forall_norm_le (B : E →L[ℂ] E) {d : ℝ} (hd : 0 < d)
    (hB : ∀ x, d * ‖x‖ ≤ ‖B x‖) (hB' : ∀ x, d * ‖x‖ ≤ ‖(adjoint B) x‖) : IsUnit B := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have hanti : AntilipschitzWith ⟨d⁻¹, inv_nonneg.mpr hd.le⟩ B := by
    refine B.antilipschitz_of_bound fun x => ?_
    calc ‖x‖ = d⁻¹ * (d * ‖x‖) := by field_simp
      _ ≤ d⁻¹ * ‖B x‖ := mul_le_mul_of_nonneg_left (hB x) (inv_nonneg.mpr hd.le)
  refine ⟨hanti.injective, ?_⟩
  have hclosed : IsClosed (Set.range B) := hanti.isClosed_range B.uniformContinuous
  have hdense : (LinearMap.range (B : E →ₗ[ℂ] E)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_orthogonal'] at hy
    have h0 : (adjoint B) y = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℂ), adjoint_inner_left]
      exact hy _ (LinearMap.mem_range_self (B : E →ₗ[ℂ] E) _)
    have h1 : d * ‖y‖ ≤ d * 0 := by
      rw [mul_zero]
      simpa only [h0, norm_zero] using hB' y
    exact norm_le_zero_iff.mp (le_of_mul_le_mul_left h1 hd)
  have hclosed' : IsClosed ((LinearMap.range (B : E →ₗ[ℂ] E) : Submodule ℂ E) : Set E) := hclosed
  have hrange : LinearMap.range (B : E →ₗ[ℂ] E) = ⊤ := by
    rw [← hclosed'.submodule_topologicalClosure_eq]; exact hdense
  exact LinearMap.range_eq_top.mp hrange

/-- The spectrum of `A` is contained in the closure of its numerical range. -/
theorem spectrum_subset_closure_numericalRange (A : E →L[ℂ] E) :
    spectrum ℂ (A : E →L[ℂ] E) ⊆ closure (numericalRange A) := by
  intro l hl
  by_contra hl'
  obtain ⟨d, hd, hfar⟩ : ∃ d > 0, ∀ z ∈ numericalRange A, d ≤ ‖z - l‖ := by
    rw [Metric.mem_closure_iff] at hl'
    push Not at hl'
    obtain ⟨d, hd, h⟩ := hl'
    exact ⟨d, hd, fun z hz => by simpa only [dist_eq_norm, norm_sub_rev] using h z hz⟩
  have hunit : ∀ x : E, ‖x‖ = 1 → d ≤ ‖⟪x, (A - l • 1) x⟫_ℂ‖ := fun x hx => by
    rw [inner_sub_smul_one_apply_self A l hx]
    exact hfar _ ⟨x, hx, rfl⟩
  have hunit' : ∀ x : E, ‖x‖ = 1 → d ≤ ‖⟪x, (adjoint (A - l • 1)) x⟫_ℂ‖ := fun x hx => by
    rw [adjoint_inner_right, ← inner_conj_symm ((A - l • 1) x) x, RCLike.norm_conj]
    exact hunit x hx
  have hU : IsUnit (A - l • 1) :=
    isUnit_of_forall_norm_le (A - l • 1) hd (norm_apply_ge_of_forall_unit _ hunit)
      (norm_apply_ge_of_forall_unit _ hunit')
  apply spectrum.mem_iff.mp hl
  rw [Algebra.algebraMap_eq_smul_one, ← neg_sub]
  exact hU.neg

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
