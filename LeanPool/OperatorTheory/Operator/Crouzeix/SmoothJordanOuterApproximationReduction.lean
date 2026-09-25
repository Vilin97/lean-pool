/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothJordanOuterApproximation

/-!
# Reducing smooth outer approximation to the full-dimensional case

For a nonempty compact convex planar set, it is enough to construct smooth
Jordan outer approximations when the set has nonempty interior.  Before
invoking that case, replace the target by its closed half-scale thickening.
This thickening is still compact and convex, has nonempty interior, and a
second half-scale thickening fits inside the requested original scale.
-/

@[expose] public section

open Complex Metric Set
open scoped InnerProductSpace

/-- Smooth outer approximation for compact convex sets with nonempty interior
implies the same statement for every nonempty compact convex set. -/
theorem hasSmoothJordanOuterApproximation_of_nonemptyInterior_case
    {K : Set ℂ} (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hKconvex : Convex ℝ K)
    (hfull : ∀ L : Set ℂ, IsCompact L → Convex ℝ L →
      (interior L).Nonempty → HasSmoothJordanOuterApproximation L) :
    HasSmoothJordanOuterApproximation K := by
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith
  let L : Set ℂ := Metric.cthickening δ K
  have hLcompact : IsCompact L := by
    exact hKcompact.cthickening
  have hLconvex : Convex ℝ L := by
    exact hKconvex.cthickening δ
  have hLinterior : (interior L).Nonempty := by
    obtain ⟨z, hz⟩ := hKnonempty
    refine ⟨z, Metric.thickening_subset_interior_cthickening δ K ?_⟩
    exact Metric.self_subset_thickening hδ K hz
  obtain ⟨Omega, hLOmega, hOmegaL⟩ :=
    hfull L hLcompact hLconvex hLinterior δ hδ
  refine ⟨Omega, ?_, ?_⟩
  · exact (Metric.self_subset_cthickening K).trans hLOmega
  · have hsum : δ + δ = ε := by
      dsimp only [δ]
      ring
    simpa only [L, thickening_cthickening hδ hδ.le, hsum] using hOmegaL

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]

/-- To obtain the exact Crouzeix--Palencia bound, the remaining planar
geometry theorem may be restricted to compact convex sets with nonempty
interior. -/
theorem crouzeix_palencia_of_smoothJordanOuterApproximation_nonemptyInterior_case
    (A : E →L[ℂ] E)
    (hfull : ∀ K : Set ℂ, IsCompact K → Convex ℝ K →
      (interior K).Nonempty → HasSmoothJordanOuterApproximation K) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  have hcompact : IsCompact (closure (numericalRange A)) := by
    have hbounded : Bornology.IsBounded (numericalRange A) :=
      Metric.isBounded_closedBall.subset (fun z hz => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_le_of_mem_numericalRange A hz)
    exact hbounded.isCompact_closure
  have hnonempty : (closure (numericalRange A)).Nonempty := by
    obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hxnorm : ‖x‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at hx
      exact hx
    exact ⟨⟪x, A x⟫_ℂ,
      subset_closure ((mem_numericalRange A _).mpr ⟨x, hxnorm, rfl⟩)⟩
  apply crouzeix_palencia_of_smoothJordanOuterApproximation A
  exact hasSmoothJordanOuterApproximation_of_nonemptyInterior_case
    hcompact hnonempty (convex_numericalRange A).closure hfull

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
