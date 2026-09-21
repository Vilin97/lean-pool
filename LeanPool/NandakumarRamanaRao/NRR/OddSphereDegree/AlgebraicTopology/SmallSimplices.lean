/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricBoundaryCancellation

/-!
# Open-cover-small singular simplices

This file introduces the notion that a singular simplex of a space `X` is
*small with respect to an open cover* of `X`: its image is contained in one of
the open sets of the cover.

We work with the library's existing singular simplex API
(`SphereOddDegree.singularSimplices`), whose underlying continuous map out of
the topological standard simplex `Delta n` is recovered by
`SphereOddDegree.AffineBarycentricSubdivision.singularSimplexAsContinuousMap`.
No parallel singular-simplex type is introduced.

## Main definitions

* `SphereOddDegree.OpenCoverData X` — a family of open subsets of `X` that
 covers `X`.
* `SphereOddDegree.IsSmallSimplex 𝒰 σ` — the predicate that the image (range) of
 the singular simplex `σ` is contained in some member of the cover `𝒰`.

## Main results

* `SphereOddDegree.IsSmallSimplex.of_range_subset` — smallness is inherited
 along any range inclusion of the underlying continuous maps.
* `SphereOddDegree.IsSmallSimplex.comp_of_range_subset` — if `τ = σ ∘ φ` for a
 continuous map `φ : Delta m → Delta n`, then smallness of `σ` implies
 smallness of `τ`.
* `SphereOddDegree.IsSmallSimplex.face` — every boundary face of a small simplex
 is small.

This file deliberately does **not** prove smallness of barycentric subdivision;
that belongs to downstream modules.
-/

open CategoryTheory AlgebraicTopology
open SphereOddDegree.AffineBarycentricSubdivision

namespace SphereOddDegree

/-! ## 1. Open cover data -/

/-- An open cover of a topological space `X`: a family of open subsets whose
union is all of `X`. -/
structure OpenCoverData (X : TopCat.{0}) where
  /-- The underlying family of subsets of `X`. -/
  sets : Set (Set X)
  /-- Each member of the family is open. -/
  isOpen_mem : ∀ U ∈ sets, IsOpen U
  /-- The family covers `X`. -/
  covers : ∀ x : X, ∃ U ∈ sets, x ∈ U

/-- The underlying continuous map `Delta n → X` of a singular simplex `σ`.
This is a thin alias for the library's `singularSimplexAsContinuousMap`, matching
the schematic `mvSimplexMap` accessor. -/
noncomputable abbrev mvSimplexMap {X : TopCat.{0}} {n : ℕ} (σ : singularSimplices X n) :
    C(Delta n, X) :=
  singularSimplexAsContinuousMap X n σ

/-! ## 2. Smallness with respect to a cover -/

/-- A singular `n`-simplex `σ` is **small** with respect to an open cover `𝒰` if
its image is contained in one of the open sets of the cover. -/
def IsSmallSimplex {X : TopCat.{0}} (𝒰 : OpenCoverData X) {n : ℕ}
    (σ : singularSimplices X n) : Prop :=
  ∃ U ∈ 𝒰.sets, Set.range (mvSimplexMap σ) ⊆ U

/-- Smallness is inherited along any inclusion of ranges of the underlying
continuous maps. -/
theorem IsSmallSimplex.of_range_subset {X : TopCat.{0}} {𝒰 : OpenCoverData X}
    {m n : ℕ} {σ : singularSimplices X n} {τ : singularSimplices X m}
    (hσ : IsSmallSimplex 𝒰 σ)
    (h : Set.range (mvSimplexMap τ) ⊆ Set.range (mvSimplexMap σ)) :
    IsSmallSimplex 𝒰 τ := by
  obtain ⟨U, hU, hsub⟩ := hσ
  exact ⟨U, hU, h.trans hsub⟩

/-- If `τ` factors as `σ ∘ φ` for a continuous map `φ : Delta m → Delta n`
(at the level of underlying continuous maps), then smallness of `σ` implies
smallness of `τ`. -/
theorem IsSmallSimplex.comp_of_range_subset {X : TopCat.{0}} {𝒰 : OpenCoverData X}
    {m n : ℕ} {σ : singularSimplices X n} {τ : singularSimplices X m}
    (φ : C(Delta m, Delta n))
    (hcomp : mvSimplexMap τ = (mvSimplexMap σ).comp φ)
    (hσ : IsSmallSimplex 𝒰 σ) :
    IsSmallSimplex 𝒰 τ := by
  refine hσ.of_range_subset ?_
  rw [hcomp]
  rintro _ ⟨y, rfl⟩
  exact ⟨φ y, rfl⟩

/-- **Face stability.** Every boundary face of a small simplex is small: a face
has image contained in the image of the original simplex. -/
theorem IsSmallSimplex.face {X : TopCat.{0}} {𝒰 : OpenCoverData X} {n : ℕ}
    {σ : singularSimplices X (n + 1)} (hσ : IsSmallSimplex 𝒰 σ) (i : Fin (n + 2)) :
    IsSmallSimplex 𝒰 (AlexanderWhitney.faceSimplex X n i σ) :=
  hσ.comp_of_range_subset (cofaceTop n i) (faceSimplex_continuousMap X n i σ)

end SphereOddDegree
