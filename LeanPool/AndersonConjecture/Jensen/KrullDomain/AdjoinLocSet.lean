/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.NSubring

/-!
# Intersection subring definitions

Defines the subrings A_i = R[x_i, y_j^{-1}] of a Noetherian
local domain T and their intersection, used in the Krull domain
construction of Anderson--Jensen.
-/

noncomputable section

open Cardinal Ideal Polynomial Set Pointwise

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

section IntersectionDefs

/-- The set A = R[x, y⁻¹] inside T: elements t such that t·yⁿ = f(x)
for some f ∈ R[X] and n ∈ ℕ. This is the image of the localization
of R[x] at the powers of y, embedded in T via evaluation. -/
def adjoinLocSetY (R : NSubring T) (x : T) (y : R.carrier) : Set T :=
  {t : T | ∃ (f : Polynomial R.carrier) (n : ℕ), t * (↑y : T) ^ n = aeval x f}

/-- R ⊆ R[x, y⁻¹]. -/
theorem R_le_adjoinLocSetY (R : NSubring T) (x : T) (y : R.carrier) :
    ∀ r : R.carrier, (↑r : T) ∈ adjoinLocSetY R x y :=
  fun r => ⟨C r, 0, by simp [show algebraMap R.carrier T = R.carrier.subtype from rfl]⟩

/-- x ∈ R[x, y⁻¹]. -/
theorem x_mem_adjoinLocSetY (R : NSubring T) (x : T) (y : R.carrier) :
    x ∈ adjoinLocSetY R x y :=
  ⟨X, 0, by simp⟩

/-- The intersection Rbar = A₁ ∩ A₂ as a set in T. -/
def intersectionSet (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier) : Set T :=
  adjoinLocSetY R x₁ y₂ ∩ adjoinLocSetY R x₂ y₁

/-- R ⊆ Rbar. -/
theorem R_le_intersectionSet (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier) :
    ∀ r : R.carrier, (↑r : T) ∈ intersectionSet R x₁ x₂ y₁ y₂ :=
  fun r => ⟨R_le_adjoinLocSetY R x₁ y₂ r, R_le_adjoinLocSetY R x₂ y₁ r⟩

end IntersectionDefs

end
