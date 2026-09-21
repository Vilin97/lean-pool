/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Core.Action

/-!
# The Markoff surface on commutative semirings

The usual polynomial presentation by subtraction only makes sense over rings.  For strong
approximation from natural-number solutions, the equation itself is the more fundamental
definition:

`x₁² + x₂² + x₃² = 3 * x₁ * x₂ * x₃`.

This file defines that solution type over every commutative semiring and its covariant map along
semiring homomorphisms.  It also records the canonical reduction from `ℕ` to `ZMod p` and compares
the semiring definition with the existing ring-level `MarkoffSurface`.
-/

open CategoryTheory

namespace BGS

/-- The Markoff surface, functorially evaluated on commutative semirings. -/
def Markoff : CommSemiRingCat ⥤ Type where
  obj R := {⟨x, y, z⟩ : R × R × R | x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z}
  map f := ↾fun ⟨⟨x, y, z⟩, h⟩ ↦ ⟨⟨f.hom x, f.hom y, f.hom z⟩, by
    simpa only [Set.mem_setOf_eq, map_add, map_pow, map_mul, map_ofNat] using congrArg f.hom h⟩

end BGS

namespace BGS.Markoff

universe u v w

open CategoryTheory

/-- Strong approximation at modulus `p`: every Markoff solution modulo `p` is the
reduction of a natural-number solution. -/
def StrongApproximationAt (p : ℕ) : Prop :=
  Function.Surjective
    (BGS.Markoff.map (CommSemiRingCat.ofHom (Nat.castRingHom (ZMod p))))

/-- A point satisfies the Markoff equation over a commutative semiring. -/
def IsSemiringMarkoff {R : Type u} [CommSemiring R] (x : Point R) : Prop :=
  x.x1 ^ 2 + x.x2 ^ 2 + x.x3 ^ 2 = 3 * x.x1 * x.x2 * x.x3

/-- Markoff solutions over a commutative semiring. -/
abbrev SemiringMarkoffSurface (R : Type u) [CommSemiring R] :=
  {x : Point R // IsSemiringMarkoff x}

/-- A concise name for the semiring-valued solution type of the Markoff equation. -/
abbrev MarkoffSolutions (R : Type u) [CommSemiring R] := SemiringMarkoffSurface R

/-- Apply a semiring homomorphism coordinatewise to a point of affine three-space. -/
def semiringPointMap {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (x : Point R) : Point S :=
  ⟨f x.x1, f x.x2, f x.x3⟩

@[simp]
theorem semiringPointMap_x1 {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (x : Point R) : (semiringPointMap f x).x1 = f x.x1 :=
  rfl

@[simp]
theorem semiringPointMap_x2 {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (x : Point R) : (semiringPointMap f x).x2 = f x.x2 :=
  rfl

@[simp]
theorem semiringPointMap_x3 {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (x : Point R) : (semiringPointMap f x).x3 = f x.x3 :=
  rfl

theorem isSemiringMarkoff_semiringPointMap
    {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) {x : Point R} (hx : IsSemiringMarkoff x) :
    IsSemiringMarkoff (semiringPointMap f x) := by
  simpa only [IsSemiringMarkoff, semiringPointMap, map_add, map_mul, map_pow, map_ofNat] using
    congrArg f hx

namespace SemiringMarkoffSurface

/-- Map a Markoff solution along a homomorphism of commutative semirings. -/
def map {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (x : SemiringMarkoffSurface R) : SemiringMarkoffSurface S :=
  ⟨semiringPointMap f x.1, isSemiringMarkoff_semiringPointMap f x.2⟩

@[simp]
theorem map_coe {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (x : SemiringMarkoffSurface R) :
    (map f x : Point S) = semiringPointMap f x.1 :=
  rfl

@[simp]
theorem map_x1 {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (x : SemiringMarkoffSurface R) :
    (map f x).1.x1 = f x.1.x1 :=
  rfl

@[simp]
theorem map_x2 {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (x : SemiringMarkoffSurface R) :
    (map f x).1.x2 = f x.1.x2 :=
  rfl

@[simp]
theorem map_x3 {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (x : SemiringMarkoffSurface R) :
    (map f x).1.x3 = f x.1.x3 :=
  rfl

@[simp]
theorem map_id {R : Type u} [CommSemiring R] (x : SemiringMarkoffSurface R) :
    map (RingHom.id R) x = x := by
  apply Subtype.ext
  ext <;> rfl

@[simp]
theorem map_comp {R : Type u} {S : Type v} {T : Type w}
    [CommSemiring R] [CommSemiring S] [CommSemiring T]
    (g : S →+* T) (f : R →+* S) (x : SemiringMarkoffSurface R) :
    map (g.comp f) x = map g (map f x) := by
  apply Subtype.ext
  ext <;> rfl

end SemiringMarkoffSurface

/-- The covariant functor of Markoff solutions on commutative semirings. -/
def markoffFunctor : CommSemiRingCat.{u} ⥤ Type u where
  obj R := SemiringMarkoffSurface R
  map f := ↾SemiringMarkoffSurface.map f.hom
  map_id R := by
    apply ConcreteCategory.hom_ext
    intro x
    exact SemiringMarkoffSurface.map_id x
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact SemiringMarkoffSurface.map_comp g.hom f.hom x

/-- The public triple presentation of `Markoff` agrees with the structured presentation used
internally by the dynamical development. -/
def markoffEquivSemiringMarkoffSurface (R : Type) [CommSemiring R] :
    BGS.Markoff.obj (CommSemiRingCat.of R) ≃ SemiringMarkoffSurface R where
  toFun x := ⟨⟨x.1.1, x.1.2.1, x.1.2.2⟩, x.2⟩
  invFun x := ⟨⟨x.1.x1, x.1.x2, x.1.x3⟩, x.2⟩
  left_inv x := Subtype.ext rfl
  right_inv x := by
    apply Subtype.ext
    cases x.1
    rfl

@[simp]
theorem markoffEquivSemiringMarkoffSurface_map
    {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (x : BGS.Markoff.obj (CommSemiRingCat.of R)) :
    markoffEquivSemiringMarkoffSurface S
        (BGS.Markoff.map (CommSemiRingCat.ofHom f) x) =
      SemiringMarkoffSurface.map f (markoffEquivSemiringMarkoffSurface R x) := by
  apply Subtype.ext
  ext <;> rfl

@[simp]
theorem markoffFunctor_obj (R : CommSemiRingCat.{u}) :
    markoffFunctor.obj R = SemiringMarkoffSurface R :=
  rfl

@[simp]
theorem markoffFunctor_map {R S : CommSemiRingCat.{u}} (f : R ⟶ S)
    (x : SemiringMarkoffSurface R) :
    markoffFunctor.map f x = SemiringMarkoffSurface.map f.hom x :=
  rfl

/-- The origin as a Markoff solution over a commutative semiring. -/
def semiringSurfaceOrigin (R : Type u) [CommSemiring R] : SemiringMarkoffSurface R :=
  ⟨origin, by simp [IsSemiringMarkoff, origin]⟩

/-- The distinguished positive Markoff solution `(1, 1, 1)`. -/
def semiringSurfaceRoot (R : Type u) [CommSemiring R] : SemiringMarkoffSurface R :=
  ⟨⟨1, 1, 1⟩, by norm_num [IsSemiringMarkoff]⟩

@[simp]
theorem SemiringMarkoffSurface.map_origin
    {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    SemiringMarkoffSurface.map f (semiringSurfaceOrigin R) = semiringSurfaceOrigin S := by
  apply Subtype.ext
  ext <;> simp [SemiringMarkoffSurface.map, semiringPointMap, semiringSurfaceOrigin, origin]

@[simp]
theorem SemiringMarkoffSurface.map_root
    {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    SemiringMarkoffSurface.map f (semiringSurfaceRoot R) = semiringSurfaceRoot S := by
  apply Subtype.ext
  ext <;> simp [SemiringMarkoffSurface.map, semiringPointMap, semiringSurfaceRoot]

/-- Coordinatewise reduction of natural-number Markoff solutions modulo `p`. -/
def markoffReduction (p : ℕ) :
    SemiringMarkoffSurface ℕ → SemiringMarkoffSurface (ZMod p) :=
  SemiringMarkoffSurface.map (Nat.castRingHom (ZMod p))

/-- The public functor formulation of strong approximation agrees with the structured
reduction map used internally. -/
theorem strongApproximationAt_iff_markoffReduction_surjective (p : ℕ) :
    StrongApproximationAt p ↔ Function.Surjective (markoffReduction p) := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h ((markoffEquivSemiringMarkoffSurface (ZMod p)).symm y)
    refine ⟨markoffEquivSemiringMarkoffSurface ℕ x, ?_⟩
    simpa [markoffReduction] using
      congrArg (markoffEquivSemiringMarkoffSurface (ZMod p)) hx
  · intro h y
    obtain ⟨x, hx⟩ := h (markoffEquivSemiringMarkoffSurface (ZMod p) y)
    refine ⟨(markoffEquivSemiringMarkoffSurface ℕ).symm x, ?_⟩
    apply (markoffEquivSemiringMarkoffSurface (ZMod p)).injective
    simpa [markoffReduction] using hx

@[simp]
theorem markoffReduction_eq_markoffFunctor_map (p : ℕ) (x : SemiringMarkoffSurface ℕ) :
    markoffReduction p x =
      markoffFunctor.map (CommSemiRingCat.ofHom (Nat.castRingHom (ZMod p))) x :=
  rfl

@[simp]
theorem markoffReduction_x1 (p : ℕ) (x : SemiringMarkoffSurface ℕ) :
    (markoffReduction p x).1.x1 = (x.1.x1 : ZMod p) :=
  rfl

@[simp]
theorem markoffReduction_x2 (p : ℕ) (x : SemiringMarkoffSurface ℕ) :
    (markoffReduction p x).1.x2 = (x.1.x2 : ZMod p) :=
  rfl

@[simp]
theorem markoffReduction_x3 (p : ℕ) (x : SemiringMarkoffSurface ℕ) :
    (markoffReduction p x).1.x3 = (x.1.x3 : ZMod p) :=
  rfl

@[simp]
theorem markoffReduction_origin (p : ℕ) :
    markoffReduction p (semiringSurfaceOrigin ℕ) = semiringSurfaceOrigin (ZMod p) :=
  SemiringMarkoffSurface.map_origin _

@[simp]
theorem markoffReduction_root (p : ℕ) :
    markoffReduction p (semiringSurfaceRoot ℕ) = semiringSurfaceRoot (ZMod p) :=
  SemiringMarkoffSurface.map_root _

/-- Over a commutative ring, the equation-based semiring surface agrees with the existing
zero-locus definition using `markoffPolynomial`. -/
def semiringMarkoffSurfaceEquiv (R : Type u) [CommRing R] :
    SemiringMarkoffSurface R ≃ MarkoffSurface R where
  toFun x :=
    ⟨x.1, by
      change x.1.x1 ^ 2 + x.1.x2 ^ 2 + x.1.x3 ^ 2 -
          3 * x.1.x1 * x.1.x2 * x.1.x3 = 0
      exact sub_eq_zero.mpr x.2⟩
  invFun x :=
    ⟨x.1, by
      apply sub_eq_zero.mp
      exact x.2⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl

@[simp]
theorem semiringMarkoffSurfaceEquiv_apply_coe
    {R : Type u} [CommRing R] (x : SemiringMarkoffSurface R) :
    ((semiringMarkoffSurfaceEquiv R x : MarkoffSurface R) : Point R) = x.1 :=
  rfl

@[simp]
theorem semiringMarkoffSurfaceEquiv_symm_apply_coe
    {R : Type u} [CommRing R] (x : MarkoffSurface R) :
    ((semiringMarkoffSurfaceEquiv R).symm x : Point R) = x.1 :=
  rfl

/-- The distinguished solution `(1, 1, 1)` on the existing ring-level Markoff surface. -/
def surfaceRoot (R : Type u) [CommRing R] : MarkoffSurface R :=
  ⟨⟨1, 1, 1⟩, by norm_num [IsMarkoff, markoffPolynomial]⟩

@[simp]
theorem surfaceRoot_coe (R : Type u) [CommRing R] :
    ((surfaceRoot R : MarkoffSurface R) : Point R) = ⟨1, 1, 1⟩ :=
  rfl

@[simp]
theorem semiringMarkoffSurfaceEquiv_origin (R : Type u) [CommRing R] :
    semiringMarkoffSurfaceEquiv R (semiringSurfaceOrigin R) = surfaceOrigin R := by
  apply Subtype.ext
  rfl

@[simp]
theorem semiringMarkoffSurfaceEquiv_root (R : Type u) [CommRing R] :
    semiringMarkoffSurfaceEquiv R (semiringSurfaceRoot R) = surfaceRoot R := by
  apply Subtype.ext
  rfl

end BGS.Markoff
