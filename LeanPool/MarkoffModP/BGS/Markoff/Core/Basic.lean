/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib

/-!
# The elementary Markoff surface

This file fixes the unscaled coordinates used in the introduction of
Bourgain--Gamburd--Sarnak, arXiv:1607.01530v1. Later parts of the paper use
trace coordinates obtained by multiplying each coordinate by three; that
normalization is deliberately kept separate.
-/

namespace BGS.Markoff

universe u

/-- A point of affine three-space over a type `R`. -/
@[ext]
structure Point (R : Type u) where
  /-- The first coordinate. -/
  x1 : R
  /-- The second coordinate. -/
  x2 : R
  /-- The third coordinate. -/
  x3 : R
deriving DecidableEq, Repr, Fintype

/-- The origin in affine three-space. -/
def origin {R : Type u} [Zero R] : Point R := ⟨0, 0, 0⟩

/-- The polynomial whose zero locus is the Markoff surface. -/
def markoffPolynomial {R : Type u} [CommRing R] (x : Point R) : R :=
  x.x1 ^ 2 + x.x2 ^ 2 + x.x3 ^ 2 - 3 * x.x1 * x.x2 * x.x3

/-- The predicate that a point lies on the Markoff surface. -/
def IsMarkoff {R : Type u} [CommRing R] (x : Point R) : Prop :=
  markoffPolynomial x = 0

/-- The Markoff surface as a set. -/
def surface (R : Type u) [CommRing R] : Set (Point R) :=
  {x | IsMarkoff x}

/-- The punctured Markoff surface, with the origin removed. -/
def puncturedSurface (R : Type u) [CommRing R] : Set (Point R) :=
  surface R \ {origin}

/-- The first Vieta involution. -/
def vieta1 {R : Type u} [CommRing R] (x : Point R) : Point R :=
  ⟨3 * x.x2 * x.x3 - x.x1, x.x2, x.x3⟩

/-- The second Vieta involution. -/
def vieta2 {R : Type u} [CommRing R] (x : Point R) : Point R :=
  ⟨x.x1, 3 * x.x1 * x.x3 - x.x2, x.x3⟩

/-- The third Vieta involution. -/
def vieta3 {R : Type u} [CommRing R] (x : Point R) : Point R :=
  ⟨x.x1, x.x2, 3 * x.x1 * x.x2 - x.x3⟩

/-- Exchange the first two coordinates. -/
def swap12 {R : Type u} (x : Point R) : Point R :=
  ⟨x.x2, x.x1, x.x3⟩

/-- Exchange the last two coordinates. -/
def swap23 {R : Type u} (x : Point R) : Point R :=
  ⟨x.x1, x.x3, x.x2⟩

/-- The fundamental rotation fixing the first coordinate. -/
def rotate1 {R : Type u} [CommRing R] (x : Point R) : Point R :=
  ⟨x.x1, x.x3, 3 * x.x1 * x.x3 - x.x2⟩

@[simp]
theorem markoffPolynomial_origin {R : Type u} [CommRing R] :
    markoffPolynomial (origin : Point R) = 0 := by
  simp [markoffPolynomial, origin]

@[simp]
theorem isMarkoff_origin {R : Type u} [CommRing R] :
    IsMarkoff (origin : Point R) := by
  simp [IsMarkoff]

theorem markoffPolynomial_vieta1 {R : Type u} [CommRing R] (x : Point R) :
    markoffPolynomial (vieta1 x) = markoffPolynomial x := by
  simp [markoffPolynomial, vieta1]
  ring

theorem markoffPolynomial_vieta2 {R : Type u} [CommRing R] (x : Point R) :
    markoffPolynomial (vieta2 x) = markoffPolynomial x := by
  simp [markoffPolynomial, vieta2]
  ring

theorem markoffPolynomial_vieta3 {R : Type u} [CommRing R] (x : Point R) :
    markoffPolynomial (vieta3 x) = markoffPolynomial x := by
  simp [markoffPolynomial, vieta3]
  ring

theorem markoffPolynomial_swap12 {R : Type u} [CommRing R] (x : Point R) :
    markoffPolynomial (swap12 x) = markoffPolynomial x := by
  simp [markoffPolynomial, swap12]
  ring

theorem markoffPolynomial_swap23 {R : Type u} [CommRing R] (x : Point R) :
    markoffPolynomial (swap23 x) = markoffPolynomial x := by
  simp [markoffPolynomial, swap23]
  ring

theorem markoffPolynomial_rotate1 {R : Type u} [CommRing R] (x : Point R) :
    markoffPolynomial (rotate1 x) = markoffPolynomial x := by
  simp [markoffPolynomial, rotate1]
  ring

@[simp]
theorem isMarkoff_vieta1 {R : Type u} [CommRing R] (x : Point R) :
    IsMarkoff (vieta1 x) ↔ IsMarkoff x := by
  simp only [IsMarkoff, markoffPolynomial_vieta1]

@[simp]
theorem isMarkoff_vieta2 {R : Type u} [CommRing R] (x : Point R) :
    IsMarkoff (vieta2 x) ↔ IsMarkoff x := by
  simp only [IsMarkoff, markoffPolynomial_vieta2]

@[simp]
theorem isMarkoff_vieta3 {R : Type u} [CommRing R] (x : Point R) :
    IsMarkoff (vieta3 x) ↔ IsMarkoff x := by
  simp only [IsMarkoff, markoffPolynomial_vieta3]

@[simp]
theorem isMarkoff_rotate1 {R : Type u} [CommRing R] (x : Point R) :
    IsMarkoff (rotate1 x) ↔ IsMarkoff x := by
  simp only [IsMarkoff, markoffPolynomial_rotate1]

@[simp]
theorem vieta1_involutive {R : Type u} [CommRing R] (x : Point R) :
    vieta1 (vieta1 x) = x := by
  ext <;> simp [vieta1]

@[simp]
theorem vieta2_involutive {R : Type u} [CommRing R] (x : Point R) :
    vieta2 (vieta2 x) = x := by
  ext <;> simp [vieta2]

@[simp]
theorem vieta3_involutive {R : Type u} [CommRing R] (x : Point R) :
    vieta3 (vieta3 x) = x := by
  ext <;> simp [vieta3]

@[simp]
theorem swap12_involutive {R : Type u} (x : Point R) :
    swap12 (swap12 x) = x := by
  rfl

@[simp]
theorem swap23_involutive {R : Type u} (x : Point R) :
    swap23 (swap23 x) = x := by
  rfl

/-- The first Vieta move as a permutation of affine three-space. -/
def vieta1Equiv (R : Type u) [CommRing R] : Equiv.Perm (Point R) where
  toFun := vieta1
  invFun := vieta1
  left_inv := vieta1_involutive
  right_inv := vieta1_involutive

/-- The second Vieta move as a permutation of affine three-space. -/
def vieta2Equiv (R : Type u) [CommRing R] : Equiv.Perm (Point R) where
  toFun := vieta2
  invFun := vieta2
  left_inv := vieta2_involutive
  right_inv := vieta2_involutive

/-- The third Vieta move as a permutation of affine three-space. -/
def vieta3Equiv (R : Type u) [CommRing R] : Equiv.Perm (Point R) where
  toFun := vieta3
  invFun := vieta3
  left_inv := vieta3_involutive
  right_inv := vieta3_involutive

/-- The transposition of the first two coordinates as a permutation. -/
def swap12Equiv (R : Type u) : Equiv.Perm (Point R) where
  toFun := swap12
  invFun := swap12
  left_inv := swap12_involutive
  right_inv := swap12_involutive

/-- The transposition of the last two coordinates as a permutation. -/
def swap23Equiv (R : Type u) : Equiv.Perm (Point R) where
  toFun := swap23
  invFun := swap23
  left_inv := swap23_involutive
  right_inv := swap23_involutive

end BGS.Markoff
