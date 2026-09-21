/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Strict filtered endomorphisms

A strict surjective endomorphism of a filtered module is surjective on every
subquotient of the filtration.  The formulation here uses only submodules and
their quotients; it does not introduce a separate associated-graded framework.
-/

namespace AlgebraicAnalysis.FilteredStrictness

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- An endomorphism is strict for `F` when its image of every filtration piece
is the intersection of that piece with its global range. -/
def IsStrict (F : ℕ → Submodule R M) (f : M →ₗ[R] M) : Prop :=
  ∀ n, (F n).map f = F n ⊓ LinearMap.range f

/-- The filtration subquotient `F upper / F lower`, represented inside
`F upper`. The monotonicity assumption identifies the denominator with the
expected copy of `F lower`. -/
abbrev GradedQuotient (F : ℕ → Submodule R M) (hF : Monotone F)
    (lower upper : ℕ) (h : lower ≤ upper) : Type _ :=
  F upper ⧸ LinearMap.range (Submodule.inclusion (hF h))

/-- The endomorphism induced on a filtration subquotient. -/
def gradedQuotientMap (F : ℕ → Submodule R M) (hF : Monotone F)
    (f : M →ₗ[R] M)
    (hpres : ∀ n, ∀ x ∈ F n, f x ∈ F n)
    (lower upper : ℕ) (h : lower ≤ upper) :
    GradedQuotient F hF lower upper h →ₗ[R]
      GradedQuotient F hF lower upper h := by
  let fUpper : F upper →ₗ[R] F upper :=
    LinearMap.codRestrict (F upper) (f.domRestrict (F upper))
      (fun x ↦ hpres upper x x.property)
  let lowerInUpper : Submodule R (F upper) :=
    LinearMap.range (Submodule.inclusion (hF h))
  exact lowerInUpper.mapQ lowerInUpper fUpper (by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨⟨f y, hpres lower y y.property⟩, rfl⟩)

/-- A globally surjective filtration-preserving strict endomorphism induces a
surjection on every filtration subquotient, hence on each graded piece. -/
theorem gradedQuotientMap_surjective
    (F : ℕ → Submodule R M) (hF : Monotone F)
    (f : M →ₗ[R] M)
    (hpres : ∀ n, ∀ x ∈ F n, f x ∈ F n)
    (hstrict : IsStrict F f)
    (hsurj : Function.Surjective f)
    (lower upper : ℕ) (h : lower ≤ upper) :
    Function.Surjective (gradedQuotientMap F hF f hpres lower upper h) := by
  have hmap : ∀ n, (F n).map f = F n := by
    intro n
    calc
      (F n).map f = F n ⊓ LinearMap.range f := hstrict n
      _ = F n := by rw [LinearMap.range_eq_top.mpr hsurj]; simp
  have hUpper : Function.Surjective
      (LinearMap.codRestrict (F upper) (f.domRestrict (F upper))
        (fun x ↦ hpres upper x x.property)) := by
    intro y
    have hy : (y : M) ∈ (F upper).map f := by
      rw [hmap upper]
      exact y.property
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  intro y
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨x, hx⟩ := hUpper y
  refine ⟨Submodule.Quotient.mk x, ?_⟩
  rw [gradedQuotientMap, Submodule.mapQ_apply, hx]


end AlgebraicAnalysis.FilteredStrictness
