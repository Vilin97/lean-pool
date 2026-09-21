/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.Basic
import Mathlib.Analysis.Normed.Module.Ball.Action

/-!
# Antipodal map API

This file packages the antipodal involution on the concrete sphere model as a
bundled continuous self-map and proves the basic lemmas about composition of
odd maps.

This file is part of the point-set foundation layer; it depends only on the
sphere model in `Basic.lean` and the normed-ball action API. The
orientation/determinant facts about the ambient linear map `x ↦ -x` (which
belong to the topological-degree support layer, not the point-set foundation)
live in `Degree.lean`.
-/

noncomputable section

namespace SphereOddDegree

/-- The antipodal map on `S^n`, bundled as a continuous self-map. -/
def antipodal (n : ℕ) : C(Sphere n, Sphere n) where
  toFun := fun x => -x
  continuous_toFun := continuous_neg

@[simp]
theorem antipodal_apply {n : ℕ} (x : Sphere n) :
    antipodal n x = -x :=
  rfl

/-- The antipodal map is fixed-point free on the sphere: `-x ≠ x`.

This is the canonical fixed-point-free fact and the sphere-level API (it does
not mention the projective quotient), so it lives here next to the antipodal map
rather than in the covering-space file. The reversed orientation `x ≠ -x` is
`ne_neg_self`. -/
theorem antipodal_ne_self {n : ℕ} (x : Sphere n) : -x ≠ x :=
  (ne_neg_of_mem_unit_sphere ℝ x).symm

/-- The antipodal map is fixed-point free on the sphere, reversed orientation:
`x ≠ -x`. This is the `.symm` of the canonical `antipodal_ne_self`; it is the
orientation consumed by `Set.ncard_pair`/`Set.encard_pair` on the fibers of the
double cover. -/
theorem ne_neg_self {n : ℕ} (x : Sphere n) : x ≠ -x :=
  (antipodal_ne_self x).symm

/-- The antipodal map is an involution, pointwise. -/
theorem antipodal_involutive (n : ℕ) :
    Function.Involutive (antipodal n : Sphere n → Sphere n) := by
  intro x
  simp [antipodal]

/-- The antipodal map composed with itself is the identity. -/
@[simp]
theorem antipodal_comp_antipodal (n : ℕ) :
    (antipodal n).comp (antipodal n) = ContinuousMap.id (Sphere n) := by
  ext x
  simp [antipodal]

/-- The antipodal map as a self-homeomorphism of the sphere. It is its own
inverse, since the antipodal map is an involution. -/
def antipodalHomeomorph (n : ℕ) : Sphere n ≃ₜ Sphere n where
  toFun := antipodal n
  invFun := antipodal n
  left_inv := antipodal_involutive n
  right_inv := antipodal_involutive n
  continuous_toFun := (antipodal n).continuous
  continuous_invFun := (antipodal n).continuous

@[simp]
theorem antipodalHomeomorph_apply {n : ℕ} (x : Sphere n) :
    antipodalHomeomorph n x = -x :=
  rfl

@[simp]
theorem antipodalHomeomorph_symm (n : ℕ) :
    (antipodalHomeomorph n).symm = antipodalHomeomorph n :=
  rfl

/-- The antipodal map is bijective. -/
theorem antipodal_bijective (n : ℕ) :
    Function.Bijective (antipodal n : Sphere n → Sphere n) :=
  (antipodalHomeomorph n).bijective

/-- The antipodal map is injective. -/
theorem antipodal_injective (n : ℕ) :
    Function.Injective (antipodal n : Sphere n → Sphere n) :=
  (antipodal_bijective n).injective

/-- The antipodal map is surjective. -/
theorem antipodal_surjective (n : ℕ) :
    Function.Surjective (antipodal n : Sphere n → Sphere n) :=
  (antipodal_bijective n).surjective

/-- The antipodal map is a homeomorphism. -/
theorem antipodal_isHomeomorph (n : ℕ) :
    IsHomeomorph (antipodal n : Sphere n → Sphere n) :=
  (antipodalHomeomorph n).isHomeomorph

/-- The identity map is odd. -/
theorem isOddMap_id (n : ℕ) :
    IsOddMap (ContinuousMap.id (Sphere n)) := by
  intro x
  rfl

/-- The antipodal map itself is odd. -/
theorem isOddMap_antipodal (n : ℕ) :
    IsOddMap (antipodal n) := by
  intro x
  simp [antipodal]

/-- Pointwise rewrite for an odd map on a negated argument: `f (-x) = - f x`.
This is the defining property `IsOddMap`, repackaged for dot notation so that
`rw [hf.apply_neg]` is available at use sites. -/
theorem IsOddMap.apply_neg
    {n : ℕ} {f : C(Sphere n, Sphere n)} (hf : IsOddMap f) (x : Sphere n) :
    f (-x) = - f x :=
  hf x

/-- Composition of odd maps is odd. -/
theorem IsOddMap.comp
  {n : ℕ}
  {f g : C(Sphere n, Sphere n)}
  (hg : IsOddMap g)
  (hf : IsOddMap f) :
    IsOddMap (g.comp f) := by
  intro x
  change g (f (-x)) = -g (f x)
  rw [hf x]
  exact hg (f x)

/-- Oddness is equivalent to commuting with the bundled antipodal map. -/
theorem isOddMap_iff_comp_antipodal
  {n : ℕ}
  {f : C(Sphere n, Sphere n)} :
    IsOddMap f ↔ f.comp (antipodal n) = (antipodal n).comp f := by
  constructor
  · intro hf
    apply ContinuousMap.ext
    intro x
    simpa [antipodal] using hf x
  · intro h x
    have hfun := congrArg (fun h' : C(Sphere n, Sphere n) => h' x) h
    simpa [antipodal] using hfun

/-- Pointwise commutation of an odd map with the bundled antipodal map:
`f (antipodal n x) = antipodal n (f x)`. This is the definition `IsOddMap`
restated through the bundled `antipodal n` map, convenient for `rw`/`simp` when
the surrounding context is phrased with `antipodal n` rather than raw negation. -/
theorem IsOddMap.map_antipodal
    {n : ℕ} {f : C(Sphere n, Sphere n)} (hf : IsOddMap f) (x : Sphere n) :
    f (antipodal n x) = antipodal n (f x) :=
  hf x

/-- Forward direction of `isOddMap_iff_comp_antipodal`, packaged for dot
notation: an odd map commutes with the bundled antipodal map. Using
`hf.comp_antipodal_eq` is more convenient than
`isOddMap_iff_comp_antipodal.mp hf` at use sites. -/
theorem IsOddMap.comp_antipodal_eq
    {n : ℕ} {f : C(Sphere n, Sphere n)} (hf : IsOddMap f) :
    f.comp (antipodal n) = (antipodal n).comp f :=
  isOddMap_iff_comp_antipodal.mp hf

end SphereOddDegree
