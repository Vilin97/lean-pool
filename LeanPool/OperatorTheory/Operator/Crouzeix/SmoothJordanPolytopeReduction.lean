/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Reducing smooth outer approximation to convex polytopes

Every compact convex subset of a finite-dimensional real normed space can be
sandwiched between itself and any prescribed neighborhood by the convex hull
of finitely many points, with the original set contained in the interior of
that hull.  Applying this theorem in the complex plane reduces the remaining
smooth outer-approximation problem to full-dimensional convex polytopes.

The two half-scale thickenings in the proof compose to the originally
requested scale.  Consequently the same finite-convex-hull hypothesis reaches
the exact Crouzeix--Palencia operator bound.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothJordanOuterApproximationReduction
import Mathlib.Analysis.Normed.Affine.Convex

open Complex Metric Set
open scoped InnerProductSpace

/-- Smooth Jordan outer approximation holds for every full-dimensional
convex polytope in the complex plane, where a polytope is presented as the
convex hull of a finite set of points. -/
def HasSmoothJordanOuterApproximationForPolytopes : Prop :=
  ∀ u : Finset ℂ,
    (interior (convexHull ℝ (u : Set ℂ))).Nonempty →
      HasSmoothJordanOuterApproximation (convexHull ℝ (u : Set ℂ))

/-- The full smooth outer-approximation theorem reduces to the
full-dimensional convex-polytope case. -/
theorem hasSmoothJordanOuterApproximation_of_polytope_case
    {K : Set ℂ} (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hKconvex : Convex ℝ K)
    (hpoly : HasSmoothJordanOuterApproximationForPolytopes) :
    HasSmoothJordanOuterApproximation K := by
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith
  obtain ⟨u, hKinterior, hpolyTarget⟩ :=
    hKconvex.exists_subset_interior_convexHull_finset_of_isCompact
      hKcompact (Metric.thickening_mem_nhdsSet K hδ)
  let P : Set ℂ := convexHull ℝ (u : Set ℂ)
  have hKP : K ⊆ P := by
    exact hKinterior.trans interior_subset
  have hPinterior : (interior P).Nonempty := by
    exact hKnonempty.mono hKinterior
  obtain ⟨Omega, hPOmega, hOmegaP⟩ := hpoly u hPinterior δ hδ
  refine ⟨Omega, hKP.trans hPOmega, hOmegaP.trans ?_⟩
  have hsum : δ + δ = ε := by
    dsimp only [δ]
    ring
  calc
    Metric.thickening δ P ⊆
        Metric.thickening δ (Metric.thickening δ K) :=
      Metric.thickening_subset_of_subset δ hpolyTarget
    _ = Metric.thickening ε K := by
      rw [thickening_thickening hδ hδ, hsum]

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]

/-- It is enough to solve smooth outer approximation for full-dimensional
finite convex hulls in order to obtain the exact Crouzeix--Palencia bound. -/
theorem crouzeix_palencia_of_smoothJordanOuterApproximation_polytope_case
    (A : E →L[ℂ] E)
    (hpoly : HasSmoothJordanOuterApproximationForPolytopes) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_smoothJordanOuterApproximation_nonemptyInterior_case A
  intro K hKcompact hKconvex hKinterior
  exact hasSmoothJordanOuterApproximation_of_polytope_case
    hKcompact (hKinterior.mono interior_subset) hKconvex hpoly

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
