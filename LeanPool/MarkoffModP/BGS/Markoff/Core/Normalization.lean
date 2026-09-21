/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Core.Basic

/-!
# Normalized coordinates on the Markoff surface

The paper silently passes from the original coordinates `x` to trace coordinates `u = 3x`.
This file gives the normalized affine space a distinct type, defines its Markoff equation and
Vieta moves, and proves that coordinatewise scaling by three identifies the two theories whenever
three is invertible.
-/

namespace BGS.Markoff

universe u

/-- A point in normalized trace coordinates. This is intentionally not definitionally equal to
the original-coordinate type `Point R`. -/
@[ext]
structure NormalizedPoint (R : Type u) where
  /-- The first normalized trace coordinate. -/
  u1 : R
  /-- The second normalized trace coordinate. -/
  u2 : R
  /-- The third normalized trace coordinate. -/
  u3 : R
deriving DecidableEq, Repr, Fintype

/-- The origin in normalized trace coordinates. -/
def normalizedOrigin {R : Type u} [Zero R] : NormalizedPoint R := ⟨0, 0, 0⟩

/-- The normalized Markoff polynomial `u₁² + u₂² + u₃² - u₁u₂u₃`. -/
def normalizedPolynomial {R : Type u} [CommRing R] (x : NormalizedPoint R) : R :=
  x.u1 ^ 2 + x.u2 ^ 2 + x.u3 ^ 2 - x.u1 * x.u2 * x.u3

/-- The predicate that a normalized point lies on the normalized Markoff surface. -/
def IsNormalizedMarkoff {R : Type u} [CommRing R] (x : NormalizedPoint R) : Prop :=
  normalizedPolynomial x = 0

/-- The normalized Markoff surface. -/
def normalizedSurface (R : Type u) [CommRing R] : Set (NormalizedPoint R) :=
  {x | IsNormalizedMarkoff x}

/-- The normalized Markoff surface with the origin removed. -/
def normalizedPuncturedSurface (R : Type u) [CommRing R] : Set (NormalizedPoint R) :=
  normalizedSurface R \ {normalizedOrigin}

/-- The normalized Markoff fiber obtained by fixing the first coordinate. -/
def normalizedFiber1 {R : Type u} [CommRing R] (a : R) : Set (NormalizedPoint R) :=
  {x | IsNormalizedMarkoff x ∧ x.u1 = a}

/-- The normalized Markoff fiber obtained by fixing the second coordinate. -/
def normalizedFiber2 {R : Type u} [CommRing R] (a : R) : Set (NormalizedPoint R) :=
  {x | IsNormalizedMarkoff x ∧ x.u2 = a}

/-- The normalized Markoff fiber obtained by fixing the third coordinate. -/
def normalizedFiber3 {R : Type u} [CommRing R] (a : R) : Set (NormalizedPoint R) :=
  {x | IsNormalizedMarkoff x ∧ x.u3 = a}

/-- The first Vieta involution in normalized coordinates. -/
def normalizedVieta1 {R : Type u} [CommRing R] (x : NormalizedPoint R) :
    NormalizedPoint R :=
  ⟨x.u2 * x.u3 - x.u1, x.u2, x.u3⟩

/-- The second Vieta involution in normalized coordinates. -/
def normalizedVieta2 {R : Type u} [CommRing R] (x : NormalizedPoint R) :
    NormalizedPoint R :=
  ⟨x.u1, x.u1 * x.u3 - x.u2, x.u3⟩

/-- The third Vieta involution in normalized coordinates. -/
def normalizedVieta3 {R : Type u} [CommRing R] (x : NormalizedPoint R) :
    NormalizedPoint R :=
  ⟨x.u1, x.u2, x.u1 * x.u2 - x.u3⟩

/-- Exchange the first two normalized coordinates. -/
def normalizedSwap12 {R : Type u} (x : NormalizedPoint R) : NormalizedPoint R :=
  ⟨x.u2, x.u1, x.u3⟩

/-- Exchange the last two normalized coordinates. -/
def normalizedSwap23 {R : Type u} (x : NormalizedPoint R) : NormalizedPoint R :=
  ⟨x.u1, x.u3, x.u2⟩

/-- The fundamental rotation fixing the first normalized coordinate. -/
def normalizedRotate1 {R : Type u} [CommRing R] (x : NormalizedPoint R) :
    NormalizedPoint R :=
  ⟨x.u1, x.u3, x.u1 * x.u3 - x.u2⟩

@[simp]
theorem normalizedPolynomial_origin {R : Type u} [CommRing R] :
    normalizedPolynomial (normalizedOrigin : NormalizedPoint R) = 0 := by
  simp [normalizedPolynomial, normalizedOrigin]

@[simp]
theorem isNormalizedMarkoff_origin {R : Type u} [CommRing R] :
    IsNormalizedMarkoff (normalizedOrigin : NormalizedPoint R) := by
  simp [IsNormalizedMarkoff]

theorem normalizedPolynomial_vieta1 {R : Type u} [CommRing R] (x : NormalizedPoint R) :
    normalizedPolynomial (normalizedVieta1 x) = normalizedPolynomial x := by
  simp [normalizedPolynomial, normalizedVieta1]
  ring

theorem normalizedPolynomial_vieta2 {R : Type u} [CommRing R] (x : NormalizedPoint R) :
    normalizedPolynomial (normalizedVieta2 x) = normalizedPolynomial x := by
  simp [normalizedPolynomial, normalizedVieta2]
  ring

theorem normalizedPolynomial_vieta3 {R : Type u} [CommRing R] (x : NormalizedPoint R) :
    normalizedPolynomial (normalizedVieta3 x) = normalizedPolynomial x := by
  simp [normalizedPolynomial, normalizedVieta3]
  ring

theorem normalizedPolynomial_swap12 {R : Type u} [CommRing R] (x : NormalizedPoint R) :
    normalizedPolynomial (normalizedSwap12 x) = normalizedPolynomial x := by
  simp [normalizedPolynomial, normalizedSwap12]
  ring

theorem normalizedPolynomial_swap23 {R : Type u} [CommRing R] (x : NormalizedPoint R) :
    normalizedPolynomial (normalizedSwap23 x) = normalizedPolynomial x := by
  simp [normalizedPolynomial, normalizedSwap23]
  ring

theorem normalizedPolynomial_rotate1 {R : Type u} [CommRing R] (x : NormalizedPoint R) :
    normalizedPolynomial (normalizedRotate1 x) = normalizedPolynomial x := by
  simp [normalizedPolynomial, normalizedRotate1]
  ring

@[simp]
theorem isNormalizedMarkoff_vieta1 {R : Type u} [CommRing R] (x : NormalizedPoint R) :
    IsNormalizedMarkoff (normalizedVieta1 x) ↔ IsNormalizedMarkoff x := by
  simp only [IsNormalizedMarkoff, normalizedPolynomial_vieta1]

@[simp]
theorem isNormalizedMarkoff_vieta2 {R : Type u} [CommRing R] (x : NormalizedPoint R) :
    IsNormalizedMarkoff (normalizedVieta2 x) ↔ IsNormalizedMarkoff x := by
  simp only [IsNormalizedMarkoff, normalizedPolynomial_vieta2]

@[simp]
theorem isNormalizedMarkoff_vieta3 {R : Type u} [CommRing R] (x : NormalizedPoint R) :
    IsNormalizedMarkoff (normalizedVieta3 x) ↔ IsNormalizedMarkoff x := by
  simp only [IsNormalizedMarkoff, normalizedPolynomial_vieta3]

@[simp]
theorem isNormalizedMarkoff_rotate1 {R : Type u} [CommRing R] (x : NormalizedPoint R) :
    IsNormalizedMarkoff (normalizedRotate1 x) ↔ IsNormalizedMarkoff x := by
  simp only [IsNormalizedMarkoff, normalizedPolynomial_rotate1]

/-- The normalized rotation fixes, and therefore preserves, its first-coordinate fiber. -/
theorem normalizedRotate1_mem_fiber1_iff
    {R : Type u} [CommRing R] (a : R) (x : NormalizedPoint R) :
    normalizedRotate1 x ∈ normalizedFiber1 a ↔ x ∈ normalizedFiber1 a := by
  change (IsNormalizedMarkoff (normalizedRotate1 x) ∧ x.u1 = a) ↔
    IsNormalizedMarkoff x ∧ x.u1 = a
  rw [isNormalizedMarkoff_rotate1]

@[simp]
theorem normalizedVieta1_involutive {R : Type u} [CommRing R] (x : NormalizedPoint R) :
    normalizedVieta1 (normalizedVieta1 x) = x := by
  ext <;> simp [normalizedVieta1]

@[simp]
theorem normalizedVieta2_involutive {R : Type u} [CommRing R] (x : NormalizedPoint R) :
    normalizedVieta2 (normalizedVieta2 x) = x := by
  ext <;> simp [normalizedVieta2]

@[simp]
theorem normalizedVieta3_involutive {R : Type u} [CommRing R] (x : NormalizedPoint R) :
    normalizedVieta3 (normalizedVieta3 x) = x := by
  ext <;> simp [normalizedVieta3]

/-- Coordinatewise multiplication by three, from original to normalized coordinates. -/
def toNormalized {R : Type u} [CommRing R] (x : Point R) : NormalizedPoint R :=
  ⟨3 * x.x1, 3 * x.x2, 3 * x.x3⟩

/-- Coordinatewise multiplication by the specified inverse of three. -/
def fromNormalized {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x : NormalizedPoint R) : Point R :=
  ⟨⅟(3 : R) * x.u1, ⅟(3 : R) * x.u2, ⅟(3 : R) * x.u3⟩

@[simp]
theorem toNormalized_origin {R : Type u} [CommRing R] :
    toNormalized (origin : Point R) = normalizedOrigin := by
  simp [toNormalized, origin, normalizedOrigin]

@[simp]
theorem fromNormalized_origin {R : Type u} [CommRing R] [Invertible (3 : R)] :
    fromNormalized (normalizedOrigin : NormalizedPoint R) = origin := by
  simp [fromNormalized, normalizedOrigin, origin]

/-- Scaling multiplies the Markoff polynomial by `3²`. This identity itself does not need three
to be invertible. -/
theorem normalizedPolynomial_toNormalized {R : Type u} [CommRing R] (x : Point R) :
    normalizedPolynomial (toNormalized x) = (3 : R) ^ 2 * markoffPolynomial x := by
  simp [normalizedPolynomial, toNormalized, markoffPolynomial]
  ring

/-- When three is invertible, scaling takes the original Markoff equation to the normalized one
and reflects it. -/
@[simp]
theorem isNormalizedMarkoff_toNormalized_iff {R : Type u} [CommRing R]
    [Invertible (3 : R)] (x : Point R) :
    IsNormalizedMarkoff (toNormalized x) ↔ IsMarkoff x := by
  rw [IsNormalizedMarkoff, normalizedPolynomial_toNormalized, IsMarkoff]
  exact ((isUnit_of_invertible (3 : R)).pow 2).mul_right_eq_zero

/-- Coordinatewise scaling by three as an equivalence of the two ambient affine spaces. -/
def normalizationEquiv (R : Type u) [CommRing R] [Invertible (3 : R)] :
    Point R ≃ NormalizedPoint R where
  toFun := toNormalized
  invFun := fromNormalized
  left_inv x := by
    ext <;> simp [toNormalized, fromNormalized, ← mul_assoc]
  right_inv x := by
    ext <;> simp [toNormalized, fromNormalized, ← mul_assoc]

/-- Scaling by three restricts to an equivalence of the original and normalized Markoff
surfaces. -/
def normalizationSurfaceEquiv (R : Type u) [CommRing R] [Invertible (3 : R)] :
    {x : Point R // IsMarkoff x} ≃ {x : NormalizedPoint R // IsNormalizedMarkoff x} :=
  (normalizationEquiv R).subtypeEquiv fun x => by
    change IsMarkoff x ↔ IsNormalizedMarkoff (toNormalized x)
    exact (isNormalizedMarkoff_toNormalized_iff x).symm

@[simp]
theorem toNormalized_vieta1 {R : Type u} [CommRing R] (x : Point R) :
    toNormalized (vieta1 x) = normalizedVieta1 (toNormalized x) := by
  ext <;> simp [toNormalized, vieta1, normalizedVieta1]
  ring

@[simp]
theorem toNormalized_vieta2 {R : Type u} [CommRing R] (x : Point R) :
    toNormalized (vieta2 x) = normalizedVieta2 (toNormalized x) := by
  ext <;> simp [toNormalized, vieta2, normalizedVieta2]
  ring

@[simp]
theorem toNormalized_vieta3 {R : Type u} [CommRing R] (x : Point R) :
    toNormalized (vieta3 x) = normalizedVieta3 (toNormalized x) := by
  ext <;> simp [toNormalized, vieta3, normalizedVieta3]
  ring

@[simp]
theorem toNormalized_swap12 {R : Type u} [CommRing R] (x : Point R) :
    toNormalized (swap12 x) = normalizedSwap12 (toNormalized x) := by
  rfl

@[simp]
theorem toNormalized_swap23 {R : Type u} [CommRing R] (x : Point R) :
    toNormalized (swap23 x) = normalizedSwap23 (toNormalized x) := by
  rfl

@[simp]
theorem toNormalized_rotate1 {R : Type u} [CommRing R] (x : Point R) :
    toNormalized (rotate1 x) = normalizedRotate1 (toNormalized x) := by
  ext <;> simp [toNormalized, rotate1, normalizedRotate1]
  ring

end BGS.Markoff
