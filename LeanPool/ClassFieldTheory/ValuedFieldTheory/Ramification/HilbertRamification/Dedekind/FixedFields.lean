/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
/-!
# Hilbert ramification theory: decomposition and inertia fields

This file contains the fixed-field layer of prime-decomposition theory.  The
Dedekind-domain file defines the decomposition and inertia groups attached to
a prime ideal; here we view those groups as subgroups of a finite Galois group
acting on the fraction field and use mathlib's Galois correspondence.
-/

@[expose] public section

noncomputable section

namespace HilbertRamification
namespace Dedekind

open Algebra Module

variable {A B K L : Type*}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Field K] [Field L] [Algebra K L]
variable (G : Type*) [Group G] [MulSemiringAction G L] [SMulCommClass G K L]

/-- The fixed field of a subgroup of a finite Galois group, in the
`IsGaloisGroup` formulation used by the Dedekind ramification API. -/
abbrev fixedFieldOfSubgroup (H : Subgroup G) : IntermediateField K L :=
  FixedPoints.intermediateField H

variable {G}

/-- Elementwise membership in the fixed field of a subgroup. -/
theorem mem_fixedFieldOfSubgroup_iff
    {H : Subgroup G} {x : L} :
    x ∈ fixedFieldOfSubgroup (K := K) (L := L) G H ↔
      ∀ σ : H, (σ : G) • x = x := by
  rfl

/-- Membership in a subgroup fixed field, written with subgroup membership
rather than subtype elements. -/
theorem mem_fixedFieldOfSubgroup_iff_forall_mem
    {H : Subgroup G} {x : L} :
    x ∈ fixedFieldOfSubgroup (K := K) (L := L) G H ↔
      ∀ σ ∈ H, σ • x = x := by
  rw [mem_fixedFieldOfSubgroup_iff]
  exact ⟨fun h σ hσ => h ⟨σ, hσ⟩, fun h σ => h σ σ.property⟩

variable (G)

/-- The subgroup fixing the fixed field of a subgroup is the subgroup itself. -/
theorem fixedFieldOfSubgroup_fixingSubgroup_eq
    (H : Subgroup G) [Finite G] [IsGaloisGroup G K L] :
    fixingSubgroup G
        ((fixedFieldOfSubgroup (K := K) (L := L) G H : IntermediateField K L) :
          Set L) =
      H := by
  simp [fixedFieldOfSubgroup,
    (IsGaloisGroup.fixingSubgroup_fixedPoints
      (G := G) (K := K) (L := L) (H := H))]

variable {G}

/-- A subgroup has full fixed field exactly when it is trivial. -/
theorem fixedFieldOfSubgroup_eq_top_iff_subgroup_eq_bot
    {H : Subgroup G} [Finite G] [IsGaloisGroup G K L] :
    fixedFieldOfSubgroup (K := K) (L := L) G H = ⊤ ↔ H = ⊥ := by
  constructor
  · intro hF
    calc
      H =
          fixingSubgroup G
            ((fixedFieldOfSubgroup (K := K) (L := L) G H :
              IntermediateField K L) : Set L) :=
        (fixedFieldOfSubgroup_fixingSubgroup_eq (K := K) (L := L) G H).symm
      _ =
          fixingSubgroup G ((⊤ : IntermediateField K L) : Set L) := by
        rw [hF]
      _ = ⊥ := IsGaloisGroup.fixingSubgroup_top (G := G) (K := K) (L := L)
  · intro hH
    rw [hH]
    exact IsGaloisGroup.fixedPoints_bot (G := G) (K := K) (L := L)

/-- A subgroup has base fixed field exactly when it is all of the Galois group. -/
theorem fixedFieldOfSubgroup_eq_bot_iff_subgroup_eq_top
    {H : Subgroup G} [Finite G] [IsGaloisGroup G K L] :
    fixedFieldOfSubgroup (K := K) (L := L) G H = ⊥ ↔ H = ⊤ := by
  constructor
  · intro hF
    calc
      H =
          fixingSubgroup G
            ((fixedFieldOfSubgroup (K := K) (L := L) G H :
              IntermediateField K L) : Set L) :=
        (fixedFieldOfSubgroup_fixingSubgroup_eq (K := K) (L := L) G H).symm
      _ =
          fixingSubgroup G ((⊥ : IntermediateField K L) : Set L) := by
        rw [hF]
      _ = ⊤ := IsGaloisGroup.fixingSubgroup_bot (G := G) (K := K) (L := L)
  · intro hH
    rw [hH]
    exact IsGaloisGroup.fixedPoints_top (G := G) (K := K) (L := L)

variable (G)

/-- The decomposition and inertia definition:
the decomposition field `Z_P`, as the fixed field of the decomposition group.
-/
abbrev decompositionField
    (P : Ideal B) [MulSemiringAction G B] : IntermediateField K L :=
  fixedFieldOfSubgroup (K := K) (L := L) G (decompositionGroup P G)

variable {G}

/-- Elementwise membership in the decomposition field. -/
theorem mem_decompositionField_iff
    {P : Ideal B} [MulSemiringAction G B] {x : L} :
    x ∈ decompositionField (K := K) (L := L) G P ↔
      ∀ σ ∈ decompositionGroup P G, σ • x = x := by
  simp [decompositionField]

variable (G)

/-- Decomposition and inertia groups satisfy:
the subgroup fixing the decomposition field is the decomposition group. -/
theorem dedekindDecomposition_decompositionField_fixingSubgroup_eq
    (P : Ideal B) [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] :
    fixingSubgroup G
        ((decompositionField (K := K) (L := L) G P : IntermediateField K L) :
          Set L) =
      decompositionGroup P G := by
  simp [decompositionField]

variable {G}

/-- Decomposition and inertia groups satisfy:
`G_P = 1` if and only if `Z_P = L`. -/
theorem dedekindDecomposition_decompositionField_eq_top_iff_decompositionGroup_eq_bot
    {P : Ideal B} [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] :
    decompositionField (K := K) (L := L) G P = ⊤ ↔
      decompositionGroup P G = ⊥ := by
  simpa [decompositionField] using
    fixedFieldOfSubgroup_eq_top_iff_subgroup_eq_bot
      (K := K) (L := L) (G := G) (H := decompositionGroup P G)

/-- Decomposition and inertia groups satisfy:
`G_P = G` if and only if `Z_P = K`. -/
theorem dedekindDecomposition_decompositionField_eq_bot_iff_decompositionGroup_eq_top
    {P : Ideal B} [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] :
    decompositionField (K := K) (L := L) G P = ⊥ ↔
      decompositionGroup P G = ⊤ := by
  simpa [decompositionField] using
    fixedFieldOfSubgroup_eq_bot_iff_subgroup_eq_top
      (K := K) (L := L) (G := G) (H := decompositionGroup P G)

/-- Decomposition and inertia groups satisfy:
the fixed-field form of total splitting, `Z_P = L` iff the number of primes
above `p` is `#G`. -/
theorem dedekindDecomposition_decompositionField_eq_top_iff_primesOver_ncard_eq_card
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] [IsGaloisGroup G A B] :
    decompositionField (K := K) (L := L) G P = ⊤ ↔
      (p.primesOver B).ncard = Nat.card G :=
  (dedekindDecomposition_decompositionField_eq_top_iff_decompositionGroup_eq_bot
    (K := K) (L := L) (G := G) (P := P)).trans
    (dedekindDecomposition_decompositionGroup_eq_bot_iff_primesOver_ncard_eq_card
      (A := A) (B := B) (G := G) p P)

/-- Decomposition and inertia groups satisfy:
the fixed-field form of nonsplitting, `Z_P = K` iff `P` is the only prime
above `p`. -/
theorem dedekindDecomposition_decompositionField_eq_bot_iff_primesOver_ncard_eq_one
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] [IsGaloisGroup G A B] :
    decompositionField (K := K) (L := L) G P = ⊥ ↔
      (p.primesOver B).ncard = 1 :=
  (dedekindDecomposition_decompositionField_eq_bot_iff_decompositionGroup_eq_top
    (K := K) (L := L) (G := G) (P := P)).trans
    (dedekindDecomposition_decompositionGroup_eq_top_iff_primesOver_ncard_eq_one
      (A := A) (B := B) p P G)

variable (G)

/-- The prime-decomposition tower identity:
`[L : Z_P] = #G_P`. -/
theorem dedekindTower_decompositionField_finrank_eq_decomposition_card
    (P : Ideal B) [MulSemiringAction G B] [IsGaloisGroup G K L] :
    Module.finrank (decompositionField (K := K) (L := L) G P) L =
      Nat.card (decompositionGroup P G) := by
  simp [decompositionField, fixedFieldOfSubgroup,
    (IsGaloisGroup.finrank_fixedPoints_eq_card_subgroup
      (G := G) (K := K) (L := L) (H := decompositionGroup P G))]

/-- The prime-decomposition tower identity:
the decomposition group is the Galois group of `L/Z_P`. -/
instance decompositionGroup_isGaloisGroup
    (P : Ideal B) [MulSemiringAction G B] [IsGaloisGroup G K L] :
    IsGaloisGroup (decompositionGroup P G)
      (decompositionField (K := K) (L := L) G P) L := by
  dsimp [decompositionField, fixedFieldOfSubgroup]
  infer_instance

/-- The inertia-field definition:
the inertia field `T_P`, as the fixed field of the inertia group. -/
abbrev inertiaField
    (P : Ideal B) [MulSemiringAction G B] : IntermediateField K L :=
  fixedFieldOfSubgroup (K := K) (L := L) G (inertiaGroup P G)

variable {G}

/-- Elementwise membership in the inertia field. -/
theorem mem_inertiaField_iff
    {P : Ideal B} [MulSemiringAction G B] {x : L} :
    x ∈ inertiaField (K := K) (L := L) G P ↔
      ∀ σ ∈ inertiaGroup P G, σ • x = x := by
  simp [inertiaField]

variable (G)

/-- Prime-decomposition statement:
the decomposition field is contained in the inertia field. -/
theorem decompositionField_le_inertiaField
    (P : Ideal B) [MulSemiringAction G B] :
    decompositionField (K := K) (L := L) G P ≤
      inertiaField (K := K) (L := L) G P :=
  by
    simpa [decompositionField, inertiaField, fixedFieldOfSubgroup, inertiaGroup,
      decompositionGroup] using
      (IsGaloisGroup.fixedPoints_le_of_le
        (G := G) (K := K) (L := L)
        (H := inertiaGroup P G) (H' := decompositionGroup P G)
        (by
          simpa [inertiaGroup, decompositionGroup] using
            (Ideal.inertia_le_stabilizer (M := G) P)))

/-- Prime-decomposition statement:
the subgroup fixing the inertia field is the inertia group. -/
theorem dedekindRamification_inertiaField_fixingSubgroup_eq
    (P : Ideal B) [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] :
    fixingSubgroup G
        ((inertiaField (K := K) (L := L) G P : IntermediateField K L) :
          Set L) =
      inertiaGroup P G := by
  simp [inertiaField]

variable {G}

/-- A fixed-field special case:
`I_P = 1` if and only if `T_P = L`. -/
theorem dedekindRamification_inertiaField_eq_top_iff_inertiaGroup_eq_bot
    {P : Ideal B} [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] :
    inertiaField (K := K) (L := L) G P = ⊤ ↔
      inertiaGroup P G = ⊥ := by
  simpa [inertiaField] using
    fixedFieldOfSubgroup_eq_top_iff_subgroup_eq_bot
      (K := K) (L := L) (G := G) (H := inertiaGroup P G)

/-- Fixed-field source for the opposite extreme of the inertia field:
`I_P = G` if and only if `T_P = K`. -/
theorem dedekindRamification_inertiaField_eq_bot_iff_inertiaGroup_eq_top
    {P : Ideal B} [MulSemiringAction G B]
    [Finite G] [IsGaloisGroup G K L] :
    inertiaField (K := K) (L := L) G P = ⊥ ↔
      inertiaGroup P G = ⊤ := by
  simpa [inertiaField] using
    fixedFieldOfSubgroup_eq_bot_iff_subgroup_eq_top
      (K := K) (L := L) (G := G) (H := inertiaGroup P G)

variable (G)

/-- A prime-decomposition consequence:
`[L : T_P] = #I_P`. -/
theorem dedekindRamification_inertiaField_finrank_eq_inertia_card
    (P : Ideal B) [MulSemiringAction G B] [IsGaloisGroup G K L] :
    Module.finrank (inertiaField (K := K) (L := L) G P) L =
      Nat.card (inertiaGroup P G) := by
  simp [inertiaField, fixedFieldOfSubgroup,
    (IsGaloisGroup.finrank_fixedPoints_eq_card_subgroup
      (G := G) (K := K) (L := L) (H := inertiaGroup P G))]

/-- A prime-decomposition consequence:
the inertia group is the Galois group of `L/T_P`. -/
instance inertiaGroup_isGaloisGroup
    (P : Ideal B) [MulSemiringAction G B] [IsGaloisGroup G K L] :
    IsGaloisGroup (inertiaGroup P G)
      (inertiaField (K := K) (L := L) G P) L := by
  dsimp [inertiaField, fixedFieldOfSubgroup]
  infer_instance

end Dedekind
end HilbertRamification
