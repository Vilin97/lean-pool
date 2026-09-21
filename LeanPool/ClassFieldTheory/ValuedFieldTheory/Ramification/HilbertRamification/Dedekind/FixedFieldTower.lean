/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.FixedFields
/-!
# Hilbert ramification theory: decomposition and inertia tower

This file contains the group-theoretic fixed-field part of the tower
`Z_P ⊆ T_P ⊆ L` in prime-decomposition theory.
-/

noncomputable section

namespace HilbertRamification
namespace Dedekind

open Algebra Module

variable {A B K L : Type*}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Field K] [Field L] [Algebra K L]
variable (G : Type*) [Group G] [MulSemiringAction G L] [SMulCommClass G K L]

/-- prime-decomposition theory:
the inertia field, viewed as an intermediate field over the decomposition
field. -/
abbrev inertiaFieldOverDecompositionField
    (P : Ideal B) [MulSemiringAction G B] :
    IntermediateField (decompositionField (K := K) (L := L) G P) L :=
  IntermediateField.extendScalars
    (decompositionField_le_inertiaField (K := K) (L := L) G P)

variable {G}

/-- Elementwise membership in the inertia field viewed over the decomposition
field. -/
@[simp]
theorem mem_inertiaFieldOverDecompositionField_iff
    {P : Ideal B} [MulSemiringAction G B] {x : L} :
    x ∈ inertiaFieldOverDecompositionField (K := K) (L := L) G P ↔
      ∀ σ ∈ inertiaGroup P G, σ • x = x := by
  rw [inertiaFieldOverDecompositionField, IntermediateField.mem_extendScalars,
    mem_inertiaField_iff]

variable (G)

/-- Restricting the inertia field over the decomposition field back to `K`
recovers the inertia field over `K`. -/
@[simp]
theorem inertiaFieldOverDecompositionField_restrictScalars
    (P : Ideal B) [MulSemiringAction G B] :
    (inertiaFieldOverDecompositionField (K := K) (L := L) G P).restrictScalars K =
      inertiaField (K := K) (L := L) G P :=
  rfl

/-- The prime-decomposition tower identity:
identify the decomposition group with `Gal(L/Z_P)`. -/
def dedekindTower_decompositionGroupEquivGalDecompositionField
    (P : Ideal B) [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] :
    decompositionGroup P G ≃*
      (L ≃ₐ[decompositionField (K := K) (L := L) G P] L) :=
  haveI : Finite (decompositionGroup P G) := inferInstance
  IsGaloisGroup.mulEquivAlgEquiv
    (decompositionGroup P G)
    (decompositionField (K := K) (L := L) G P) L

/-- The equivalence `G_P ≃ Gal(L/Z_P)` acts by the original group action on
elements of `L`. -/
@[simp]
theorem dedekindTower_decompositionGroupEquivGalDecompositionField_apply
    (P : Ideal B) [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L]
    (σ : decompositionGroup P G) (x : L) :
    dedekindTower_decompositionGroupEquivGalDecompositionField
        (K := K) (L := L) G P σ x =
      (σ : G) • x :=
  rfl

/-- Source fact for the tower `Z_P ⊆ L`: `L` is finite-dimensional over the
decomposition field. -/
theorem dedekindTower_decompositionField_finiteDimensional
    (P : Ideal B) [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] :
    FiniteDimensional (decompositionField (K := K) (L := L) G P) L := by
  have : Finite (decompositionGroup P G) := inferInstance
  exact
    IsGaloisGroup.finiteDimensional
      (decompositionGroup P G)
      (decompositionField (K := K) (L := L) G P) L

/-- Source fact for the tower `Z_P ⊆ L`: `L/Z_P` is Galois. -/
theorem dedekindTower_decompositionField_isGalois
    (P : Ideal B) [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] :
    IsGalois (decompositionField (K := K) (L := L) G P) L := by
  have : Finite (decompositionGroup P G) := inferInstance
  exact
    IsGaloisGroup.isGalois
      (decompositionGroup P G)
      (decompositionField (K := K) (L := L) G P) L

/-- prime-decomposition theory:
the inertia subgroup transported to `Gal(L/Z_P)`. -/
abbrev inertiaGroupOverDecompositionField
    (P : Ideal B) [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] :
    Subgroup (L ≃ₐ[decompositionField (K := K) (L := L) G P] L) :=
  Subgroup.map
    (dedekindTower_decompositionGroupEquivGalDecompositionField
      (K := K) (L := L) G P).toMonoidHom
    ((inertiaGroup P G).subgroupOf (decompositionGroup P G))

variable {G}

/-- Membership in the transported inertia subgroup over the decomposition field. -/
@[simp]
theorem mem_inertiaGroupOverDecompositionField_iff
    {P : Ideal B} [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L]
    {σ : L ≃ₐ[decompositionField (K := K) (L := L) G P] L} :
    σ ∈ inertiaGroupOverDecompositionField (K := K) (L := L) G P ↔
      ∃ τ : (inertiaGroup P G).subgroupOf (decompositionGroup P G),
        dedekindTower_decompositionGroupEquivGalDecompositionField
          (K := K) (L := L) G P (τ : decompositionGroup P G) = σ := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨⟨τ, hτ⟩, rfl⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨(τ : decompositionGroup P G), τ.property, rfl⟩

variable (G)

/-- The transported inertia subgroup is normal in `Gal(L/Z_P)`. -/
instance inertiaGroupOverDecompositionField_normal
    (P : Ideal B) [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] :
    (inertiaGroupOverDecompositionField (K := K) (L := L) G P).Normal := by
  let e :=
    dedekindTower_decompositionGroupEquivGalDecompositionField
      (K := K) (L := L) G P
  simpa [inertiaGroupOverDecompositionField, e] using
    (Subgroup.Normal.map
      (inertiaSubgroupOfDecomposition_normal P G)
      e.toMonoidHom e.surjective)

/-- A prime-decomposition consequence:
the fixed field of the transported inertia subgroup over `Z_P` is `T_P`. -/
theorem dedekindRamification_inertiaFieldOverDecompositionField_fixedField_eq
    (P : Ideal B) [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] :
    IntermediateField.fixedField
        (inertiaGroupOverDecompositionField (K := K) (L := L) G P) =
      inertiaFieldOverDecompositionField (K := K) (L := L) G P := by
  ext x
  rw [IntermediateField.mem_fixedField_iff,
    mem_inertiaFieldOverDecompositionField_iff]
  constructor
  · intro hx σ hσ
    let τ : decompositionGroup P G :=
      ⟨σ, Ideal.inertia_le_stabilizer (M := G) P hσ⟩
    have hτ :
        τ ∈ (inertiaGroup P G).subgroupOf (decompositionGroup P G) :=
      hσ
    have hτmap :
        dedekindTower_decompositionGroupEquivGalDecompositionField
            (K := K) (L := L) G P τ ∈
          inertiaGroupOverDecompositionField (K := K) (L := L) G P := by
      exact ⟨τ, hτ, rfl⟩
    simpa [τ] using hx
      (dedekindTower_decompositionGroupEquivGalDecompositionField
        (K := K) (L := L) G P τ) hτmap
  · intro hx σ hσ
    rcases
      (mem_inertiaGroupOverDecompositionField_iff
        (K := K) (L := L) (G := G) (P := P) (σ := σ)).mp hσ with
      ⟨τ, rfl⟩
    simpa using hx ((τ : decompositionGroup P G) : G) τ.property

/-- A prime-decomposition consequence:
`G(L/T_P)` over the decomposition field is the transported inertia subgroup.
-/
theorem dedekindRamification_inertiaFieldOverDecompositionField_fixingSubgroup_eq
    (P : Ideal B) [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] :
    (inertiaFieldOverDecompositionField (K := K) (L := L) G P).fixingSubgroup =
      inertiaGroupOverDecompositionField (K := K) (L := L) G P := by
  have := dedekindTower_decompositionField_finiteDimensional (K := K) (L := L) G P
  rw [← dedekindRamification_inertiaFieldOverDecompositionField_fixedField_eq
    (K := K) (L := L) G P]
  exact
    IntermediateField.fixingSubgroup_fixedField
      (inertiaGroupOverDecompositionField (K := K) (L := L) G P)

/-- The localization and decomposition comparison:
`T_P/Z_P` is normal, at the fixed-field source level. -/
instance inertiaFieldOverDecompositionField_isGalois
    (P : Ideal B) [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] :
    IsGalois (decompositionField (K := K) (L := L) G P)
      (inertiaFieldOverDecompositionField (K := K) (L := L) G P) := by
  have := dedekindTower_decompositionField_finiteDimensional (K := K) (L := L) G P
  have := dedekindTower_decompositionField_isGalois (K := K) (L := L) G P
  rw [← dedekindRamification_inertiaFieldOverDecompositionField_fixedField_eq
    (K := K) (L := L) G P]
  infer_instance

/-- The localization and decomposition comparison gives:
`G_P/I_P ≃ Gal(T_P/Z_P)`, the fixed-field quotient form. -/
def dedekindRamification_decompositionQuotientInertiaEquivGalInertiaFieldOverDecomposition
    (P : Ideal B) [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] :
    decompositionGroup P G ⧸
        (inertiaGroup P G).subgroupOf (decompositionGroup P G) ≃*
      (inertiaFieldOverDecompositionField (K := K) (L := L) G P ≃ₐ[
        decompositionField (K := K) (L := L) G P]
        inertiaFieldOverDecompositionField (K := K) (L := L) G P) := by
  haveI := dedekindTower_decompositionField_finiteDimensional (K := K) (L := L) G P
  haveI := dedekindTower_decompositionField_isGalois (K := K) (L := L) G P
  exact
    (QuotientGroup.congr
      ((inertiaGroup P G).subgroupOf (decompositionGroup P G))
      (inertiaGroupOverDecompositionField (K := K) (L := L) G P)
      (dedekindTower_decompositionGroupEquivGalDecompositionField
        (K := K) (L := L) G P)
      rfl).trans
      (by
        rw [← dedekindRamification_inertiaFieldOverDecompositionField_fixedField_eq
          (K := K) (L := L) G P]
        exact
          IsGalois.normalAutEquivQuotient
            (inertiaGroupOverDecompositionField (K := K) (L := L) G P))

/-- A prime-decomposition consequence:
`[T_P : Z_P] = #(G_P / I_P)`. -/
theorem dedekindRamification_inertiaFieldOverDecompositionField_finrank_eq_quotient_card
    (P : Ideal B) [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] :
    Module.finrank (decompositionField (K := K) (L := L) G P)
        (inertiaFieldOverDecompositionField (K := K) (L := L) G P) =
      Nat.card
        (decompositionGroup P G ⧸
          (inertiaGroup P G).subgroupOf (decompositionGroup P G)) := by
  have := dedekindTower_decompositionField_finiteDimensional (K := K) (L := L) G P
  calc
    Module.finrank (decompositionField (K := K) (L := L) G P)
        (inertiaFieldOverDecompositionField (K := K) (L := L) G P) =
        Nat.card
          (inertiaFieldOverDecompositionField (K := K) (L := L) G P ≃ₐ[
            decompositionField (K := K) (L := L) G P]
            inertiaFieldOverDecompositionField (K := K) (L := L) G P) := by
      rw [← IsGalois.card_aut_eq_finrank]
    _ =
        Nat.card
          (decompositionGroup P G ⧸
            (inertiaGroup P G).subgroupOf (decompositionGroup P G)) := by
      exact
        Nat.card_congr
          (dedekindRamification_decompositionQuotientInertiaEquivGalInertiaFieldOverDecomposition
            (K := K) (L := L) G P).symm.toEquiv

/-- The localization and decomposition comparison:
`Gal(T_P/Z_P) ≃ Gal(kappa(P)/kappa(p))`, obtained by composing the
fixed-field quotient identification with the residue exact sequence. -/
def dedekindRamification_galInertiaFieldOverDecompositionEquivResidueGalois
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    [MulSemiringAction G B] [SMulCommClass G A B]
    [Finite G] [IsGaloisGroup G K L] [Algebra.IsInvariant A B G] :
    (inertiaFieldOverDecompositionField (K := K) (L := L) G P ≃ₐ[
        decompositionField (K := K) (L := L) G P]
        inertiaFieldOverDecompositionField (K := K) (L := L) G P) ≃*
      (B ⧸ P) ≃ₐ[A ⧸ p] B ⧸ P :=
  (dedekindRamification_decompositionQuotientInertiaEquivGalInertiaFieldOverDecomposition
    (K := K) (L := L) G P).symm.trans
    (dedekindRamification_decompositionQuotientInertiaEquivResidueGalois
      (A := A) (B := B) p P G)

/-- The localization and decomposition comparison:
the inertia field proposition, bundled in the field-theoretic form: `T_P/Z_P` is
normal, `Gal(T_P/Z_P)` is the residue Galois group, and `G(L/T_P)=I_P`. -/
theorem dedekindInertiaField_inertiaField_properties
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    [MulSemiringAction G B] [SMulCommClass G A B]
    [Finite G] [IsGaloisGroup G K L] [Algebra.IsInvariant A B G] :
    IsGalois (decompositionField (K := K) (L := L) G P)
        (inertiaFieldOverDecompositionField (K := K) (L := L) G P) ∧
      Nonempty
        ((inertiaFieldOverDecompositionField (K := K) (L := L) G P ≃ₐ[
            decompositionField (K := K) (L := L) G P]
            inertiaFieldOverDecompositionField (K := K) (L := L) G P) ≃*
          (B ⧸ P) ≃ₐ[A ⧸ p] B ⧸ P) ∧
      fixingSubgroup G
          ((inertiaField (K := K) (L := L) G P : IntermediateField K L) :
            Set L) =
        inertiaGroup P G := by
  exact
    ⟨inferInstance,
      ⟨dedekindRamification_galInertiaFieldOverDecompositionEquivResidueGalois
        (A := A) (B := B) (K := K) (L := L) G p P⟩,
      dedekindRamification_inertiaField_fixingSubgroup_eq (K := K) (L := L) G P⟩

end Dedekind
end HilbertRamification
