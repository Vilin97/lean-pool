/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
/-!
# Unbounded finite Galois degrees inside an infinite Galois extension

A finite-dimensional extension has only finitely many automorphisms. An
infinite Galois group therefore supplies arbitrarily large linearly
independent finite families. Their finite Galois closures give the required
actual intermediate fields.
-/

@[expose] public section

namespace AlgebraicNumberTheory

universe u v

/-- An extension with infinitely many base-field automorphisms contains
finite Galois intermediate fields of arbitrarily large degree. -/
theorem exists_finiteGaloisIntermediateField_finrank_ge_of_infinite_aut
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [Infinite (L ≃ₐ[K] L)] (N : ℕ) :
    ∃ M : FiniteGaloisIntermediateField K L, N ≤ Module.finrank K M := by
  classical
  have hRank : Cardinal.aleph0 ≤ Module.rank K L := by
    apply le_of_not_gt
    intro h
    let : Module.Finite K L := Module.rank_lt_aleph0_iff.mp h
    exact not_finite (L ≃ₐ[K] L)
  have hN : (N : Cardinal) ≤ Module.rank K L :=
    Cardinal.natCast_lt_aleph0.le.trans hRank
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_rank (R := K) (M := L) hN
  let M : FiniteGaloisIntermediateField K L :=
    FiniteGaloisIntermediateField.adjoin K (Set.range f)
  have hmem : ∀ i, f i ∈ M.toIntermediateField := by
    intro i
    exact FiniteGaloisIntermediateField.subset_adjoin K (Set.range f) ⟨i, rfl⟩
  let g : Fin N → M := fun i ↦ ⟨f i, hmem i⟩
  have hg : LinearIndependent K g :=
    LinearIndependent.of_comp M.toIntermediateField.val.toLinearMap hf
  exact ⟨M, by simpa using hg.fintype_card_le_finrank⟩

/-- An infinite Galois intermediate extension contains ambient finite
Galois intermediate fields of arbitrarily large degree. The actual lift
keeps the field inclusion available to arithmetic consumers. -/
theorem exists_finiteGaloisIntermediateField_le_finrank_ge_of_infinite_aut
    (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω) [IsGalois K L] [Infinite (L ≃ₐ[K] L)]
    (N : ℕ) :
    ∃ E : FiniteGaloisIntermediateField K Ω,
      E.toIntermediateField ≤ L ∧ N ≤ Module.finrank K E := by
  obtain ⟨M, hM⟩ :=
    exists_finiteGaloisIntermediateField_finrank_ge_of_infinite_aut K L N
  let e : M.toIntermediateField ≃ₐ[K]
      IntermediateField.lift M.toIntermediateField :=
    IntermediateField.liftAlgEquiv M.toIntermediateField
  let : IsGalois K M.toIntermediateField := M.isGalois
  let E : FiniteGaloisIntermediateField K Ω :=
    { toIntermediateField := IntermediateField.lift M.toIntermediateField
      finiteDimensional := e.toLinearEquiv.finiteDimensional
      isGalois := IsGalois.of_algEquiv e }
  refine ⟨E, IntermediateField.lift_le M.toIntermediateField, ?_⟩
  change N ≤ Module.finrank K (IntermediateField.lift M.toIntermediateField)
  rw [← e.toLinearEquiv.finrank_eq]
  exact hM

end AlgebraicNumberTheory
