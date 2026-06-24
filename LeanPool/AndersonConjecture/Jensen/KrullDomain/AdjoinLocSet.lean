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

/-- 0 ∈ R[x, y⁻¹]. -/
theorem zero_mem_adjoinLocSetY (R : NSubring T) (x : T) (y : R.carrier) :
    (0 : T) ∈ adjoinLocSetY R x y :=
  ⟨0, 0, by simp⟩

/-- 1 ∈ R[x, y⁻¹]. -/
theorem one_mem_adjoinLocSetY (R : NSubring T) (x : T) (y : R.carrier) :
    (1 : T) ∈ adjoinLocSetY R x y :=
  ⟨C 1, 0, by simp⟩

/-- R[x, y⁻¹] is closed under negation. -/
theorem neg_mem_adjoinLocSetY (R : NSubring T) (x : T) (y : R.carrier) {t : T}
    (ht : t ∈ adjoinLocSetY R x y) : -t ∈ adjoinLocSetY R x y := by
  obtain ⟨f, n, hf⟩ := ht
  exact ⟨-f, n, by rw [map_neg, ← hf, neg_mul]⟩

/-- R[x, y⁻¹] is closed under multiplication. -/
theorem mul_mem_adjoinLocSetY (R : NSubring T) (x : T) (y : R.carrier) {t₁ t₂ : T}
    (h₁ : t₁ ∈ adjoinLocSetY R x y) (h₂ : t₂ ∈ adjoinLocSetY R x y) :
    t₁ * t₂ ∈ adjoinLocSetY R x y := by
  obtain ⟨f₁, n₁, hf₁⟩ := h₁
  obtain ⟨f₂, n₂, hf₂⟩ := h₂
  refine ⟨f₁ * f₂, n₁ + n₂, ?_⟩
  rw [map_mul, ← hf₁, ← hf₂, pow_add]
  ring

/-- R[x, y⁻¹] is closed under addition. -/
theorem add_mem_adjoinLocSetY (R : NSubring T) (x : T) (y : R.carrier) {t₁ t₂ : T}
    (h₁ : t₁ ∈ adjoinLocSetY R x y) (h₂ : t₂ ∈ adjoinLocSetY R x y) :
    t₁ + t₂ ∈ adjoinLocSetY R x y := by
  obtain ⟨f₁, n₁, hf₁⟩ := h₁
  obtain ⟨f₂, n₂, hf₂⟩ := h₂
  refine ⟨f₁ * C (y ^ n₂) + f₂ * C (y ^ n₁), n₁ + n₂, ?_⟩
  have key : (t₁ + t₂) * (↑y : T) ^ (n₁ + n₂) =
      t₁ * (↑y : T) ^ n₁ * (↑y : T) ^ n₂ +
      t₂ * (↑y : T) ^ n₂ * (↑y : T) ^ n₁ := by
    rw [pow_add]
    ring
  rw [key, hf₁, hf₂, map_add, map_mul, map_mul, aeval_C, aeval_C]
  simp only [show algebraMap R.carrier T = R.carrier.subtype from rfl,
    Subring.coe_subtype, map_pow]

/-- The intersection Rbar = A₁ ∩ A₂ as a set in T. -/
def intersectionSet (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier) : Set T :=
  adjoinLocSetY R x₁ y₂ ∩ adjoinLocSetY R x₂ y₁

/-- R ⊆ Rbar. -/
theorem R_le_intersectionSet (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier) :
    ∀ r : R.carrier, (↑r : T) ∈ intersectionSet R x₁ x₂ y₁ y₂ :=
  fun r => ⟨R_le_adjoinLocSetY R x₁ y₂ r, R_le_adjoinLocSetY R x₂ y₁ r⟩

/-- 0 ∈ Rbar. -/
theorem zero_mem_intersectionSet (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier) :
    (0 : T) ∈ intersectionSet R x₁ x₂ y₁ y₂ :=
  ⟨zero_mem_adjoinLocSetY R x₁ y₂, zero_mem_adjoinLocSetY R x₂ y₁⟩

/-- 1 ∈ Rbar. -/
theorem one_mem_intersectionSet (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier) :
    (1 : T) ∈ intersectionSet R x₁ x₂ y₁ y₂ :=
  ⟨one_mem_adjoinLocSetY R x₁ y₂, one_mem_adjoinLocSetY R x₂ y₁⟩

/-- Rbar is closed under negation. -/
theorem neg_mem_intersectionSet (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier) {t : T}
    (ht : t ∈ intersectionSet R x₁ x₂ y₁ y₂) : -t ∈ intersectionSet R x₁ x₂ y₁ y₂ :=
  ⟨neg_mem_adjoinLocSetY R x₁ y₂ ht.1, neg_mem_adjoinLocSetY R x₂ y₁ ht.2⟩

/-- Rbar is closed under multiplication. -/
theorem mul_mem_intersectionSet (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier) {t₁ t₂ : T}
    (h₁ : t₁ ∈ intersectionSet R x₁ x₂ y₁ y₂) (h₂ : t₂ ∈ intersectionSet R x₁ x₂ y₁ y₂) :
    t₁ * t₂ ∈ intersectionSet R x₁ x₂ y₁ y₂ :=
  ⟨mul_mem_adjoinLocSetY R x₁ y₂ h₁.1 h₂.1, mul_mem_adjoinLocSetY R x₂ y₁ h₁.2 h₂.2⟩

/-- Rbar is closed under addition. -/
theorem add_mem_intersectionSet (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier) {t₁ t₂ : T}
    (h₁ : t₁ ∈ intersectionSet R x₁ x₂ y₁ y₂) (h₂ : t₂ ∈ intersectionSet R x₁ x₂ y₁ y₂) :
    t₁ + t₂ ∈ intersectionSet R x₁ x₂ y₁ y₂ :=
  ⟨add_mem_adjoinLocSetY R x₁ y₂ h₁.1 h₂.1, add_mem_adjoinLocSetY R x₂ y₁ h₁.2 h₂.2⟩

end IntersectionDefs

end
