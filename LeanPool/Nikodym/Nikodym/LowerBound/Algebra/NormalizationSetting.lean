/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.LinearNormalization

/-!
# The shared setting of nodes A06′, A07′, A08, A04′

Nodes A06′ (`Algebra/FreeFiber.lean`), A07′ (`Algebra/GradedNorm.lean`), A08
(`Hilbert/DegreeUpper.lean`) and A04′ (`Algebra/Degree.lean`) of the algebra backend
(`docs/algebra_backend_design.md`) all work in the following setting, which we fix here
as a convention so that the files can be developed independently:

* `Q := MvPolynomial (Fin n) K`, `J : Ideal Q` a **homogeneous prime** (in the application,
  `n = d + 1` and `J = homogenization I` for a prime `I` of `MvPolynomial (Fin d) K`);
* `R := Q ⧸ J`, a domain;
* `y : Fin s → Q` linear forms (`∀ i, (y i).IsHomogeneous 1`) produced by linear Noether
  normalization (`exists_linear_normalization`, node A02) with
  `idealOfVars (Fin n) K ^ N ≤ J ⊔ Ideal.span (Set.range y)` and
  `aeval (fun i ↦ Ideal.Quotient.mk J (y i)) : MvPolynomial (Fin s) K →ₐ[K] R` injective;
* `S := MvPolynomial (Fin s) K`, and `R` is an `S`-algebra through an instance `[Algebra S R]`
  together with the hypothesis
  `halg : algebraMap S R = (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom`
  (the pattern already used by `finite_of_pow_idealOfVars_le'`; a consumer discharges `halg` by
  `RingHom.algebraMap_toAlgebra _` after `letI := (aeval …).toRingHom.toAlgebra`).

This file only provides the notion of a *homogeneous element* of `R` used by A06′ and A07′.
-/

namespace Nikodym.LowerBound

variable {K : Type*} [Field K] {n : ℕ}

/-- An element of `MvPolynomial (Fin n) K ⧸ J` is *homogeneous of degree `e`* if it is the class
of a form of degree `e`. -/
def IsHomogeneousElem (J : Ideal (MvPolynomial (Fin n) K)) (r : MvPolynomial (Fin n) K ⧸ J)
    (e : ℕ) : Prop :=
  ∃ G : MvPolynomial (Fin n) K, G.IsHomogeneous e ∧ Ideal.Quotient.mk J G = r

theorem isHomogeneousElem_mk (J : Ideal (MvPolynomial (Fin n) K)) {G : MvPolynomial (Fin n) K}
    {e : ℕ} (hG : G.IsHomogeneous e) : IsHomogeneousElem J (Ideal.Quotient.mk J G) e :=
  ⟨G, hG, rfl⟩

theorem isHomogeneousElem_zero (J : Ideal (MvPolynomial (Fin n) K)) (e : ℕ) :
    IsHomogeneousElem J 0 e :=
  ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, map_zero _⟩

theorem IsHomogeneousElem.mul {J : Ideal (MvPolynomial (Fin n) K)}
    {r₁ r₂ : MvPolynomial (Fin n) K ⧸ J} {e₁ e₂ : ℕ} (h₁ : IsHomogeneousElem J r₁ e₁)
    (h₂ : IsHomogeneousElem J r₂ e₂) : IsHomogeneousElem J (r₁ * r₂) (e₁ + e₂) := by
  obtain ⟨G₁, hG₁, rfl⟩ := h₁
  obtain ⟨G₂, hG₂, rfl⟩ := h₂
  exact ⟨G₁ * G₂, hG₁.mul hG₂, map_mul _ _ _⟩

theorem IsHomogeneousElem.add {J : Ideal (MvPolynomial (Fin n) K)}
    {r₁ r₂ : MvPolynomial (Fin n) K ⧸ J} {e : ℕ} (h₁ : IsHomogeneousElem J r₁ e)
    (h₂ : IsHomogeneousElem J r₂ e) : IsHomogeneousElem J (r₁ + r₂) e := by
  obtain ⟨G₁, hG₁, rfl⟩ := h₁
  obtain ⟨G₂, hG₂, rfl⟩ := h₂
  exact ⟨G₁ + G₂, hG₁.add hG₂, map_add _ _ _⟩

theorem IsHomogeneousElem.smul {J : Ideal (MvPolynomial (Fin n) K)}
    {r : MvPolynomial (Fin n) K ⧸ J} {e : ℕ} (a : K) (h : IsHomogeneousElem J r e) :
    IsHomogeneousElem J (a • r) e := by
  obtain ⟨G, hG, rfl⟩ := h
  exact ⟨a • G, by rw [MvPolynomial.smul_eq_C_mul]; exact hG.C_mul a, by
    rw [← Ideal.Quotient.mkₐ_eq_mk K, map_smul]⟩

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
