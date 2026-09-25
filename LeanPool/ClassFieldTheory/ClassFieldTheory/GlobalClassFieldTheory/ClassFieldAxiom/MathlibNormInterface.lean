/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.IsFieldNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.NormTheorems.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.HasseNormPrinciple
/-!
# Mathlib-facing Hasse norm theorem

This module translates the idele-theoretic implementation of the cyclic
Hasse norm theorem into the implementation-independent predicates in
`ClassFieldTheory.Definitions.NormTheorems`.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable
section

namespace GlobalClassFieldTheory.ClassFieldAxiom

private theorem isFieldNorm_iff_mem_globalFieldNormSubgroup
    (K L : Type)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (x : Kˣ) :
    ClassFieldTheory.IsFieldNorm K L x ↔
      x ∈ GlobalClassFieldTheory.ClassFieldAxiom.globalFieldNormSubgroup K L := by
  change x ∈ (ClassFieldTheory.fieldNormHom K L).range ↔
    x ∈ (Units.map (Algebra.norm K)).range
  rfl

private theorem isNormAtFinitePlace_iff
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (w : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    ClassFieldTheory.IsNormAtFinitePlace K L w x ↔
      IdeleGroup.finiteComponent w (IdeleGroup.principalIdele K x) ∈
        chosenFinitePlaceLocalNormSubgroup (K := K) (L := L) w := by
  rw [← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
    (K := K) (L := L) w]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply Units.ext
    calc
      Algebra.norm (w.adicCompletion K)
          (y : w.adicCompletion K ⊗[K] L) =
          algebraMap K (w.adicCompletion K) (x : K) := hy
      _ = (IdeleGroup.finiteComponent w
          (IdeleGroup.principalIdele K x) : w.adicCompletion K) :=
        (IdeleGroup.finiteComponent_principalIdele x w).symm
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    calc
      Algebra.norm (w.adicCompletion K)
          (y : w.adicCompletion K ⊗[K] L) =
          (IdeleGroup.finiteComponent w
            (IdeleGroup.principalIdele K x) : w.adicCompletion K) :=
        congrArg Units.val hy
      _ = algebraMap K (w.adicCompletion K) (x : K) :=
        IdeleGroup.finiteComponent_principalIdele x w

private theorem isNormAtInfinitePlace_iff
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (w : InfinitePlace K) (x : Kˣ) :
    ClassFieldTheory.IsNormAtInfinitePlace K L w x ↔
      IdeleGroup.infiniteComponent w (IdeleGroup.principalIdele K x) ∈
        (Units.map
          (Algebra.norm w.Completion :
            (w.Completion ⊗[K] L) →* w.Completion)).range := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply Units.ext
    calc
      Algebra.norm w.Completion (y : w.Completion ⊗[K] L) =
          algebraMap K w.Completion (x : K) := hy
      _ = (IdeleGroup.infiniteComponent w
          (IdeleGroup.principalIdele K x) : w.Completion) :=
        (IdeleGroup.infiniteComponent_principalIdele x w).symm
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    calc
      Algebra.norm w.Completion (y : w.Completion ⊗[K] L) =
          (IdeleGroup.infiniteComponent w
            (IdeleGroup.principalIdele K x) : w.Completion) :=
        congrArg Units.val hy
      _ = algebraMap K w.Completion (x : K) :=
        IdeleGroup.infiniteComponent_principalIdele x w

private theorem isEverywhereLocalNorm_iff_mem_everywhereLocalFieldNormSubgroup
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (x : Kˣ) :
    ClassFieldTheory.IsEverywhereLocalNorm K L x ↔
      x ∈ GlobalClassFieldTheory.ClassFieldAxiom.everywhereLocalFieldNormSubgroup K L := by
  constructor
  · rintro ⟨hfinite, hinfinite⟩
    change IdeleGroup.principalIdele K x ∈
      GlobalClassFieldTheory.ClassFieldAxiom.allPlaceLocalNormCondition
        (K := K) (L := L)
    constructor
    · rw [GlobalClassFieldTheory.ClassFieldAxiom.allFinitePlaceLocalNormCondition]
      apply Subgroup.mem_iInf.mpr
      intro w
      exact (isNormAtFinitePlace_iff K L w x).mp (hfinite w)
    · rw [GlobalClassFieldTheory.ClassFieldAxiom.allInfinitePlaceLocalNormCondition]
      apply Subgroup.mem_iInf.mpr
      intro w
      exact (isNormAtInfinitePlace_iff K L w x).mp (hinfinite w)
  · intro hx
    change IdeleGroup.principalIdele K x ∈
      GlobalClassFieldTheory.ClassFieldAxiom.allPlaceLocalNormCondition
        (K := K) (L := L) at hx
    constructor
    · intro w
      apply (isNormAtFinitePlace_iff K L w x).mpr
      exact Subgroup.mem_iInf.mp
        (show IdeleGroup.principalIdele K x ∈
          GlobalClassFieldTheory.ClassFieldAxiom.allFinitePlaceLocalNormCondition
            (K := K) (L := L) from hx.1) w
    · intro w
      apply (isNormAtInfinitePlace_iff K L w x).mpr
      exact Subgroup.mem_iInf.mp
        (show IdeleGroup.principalIdele K x ∈
          GlobalClassFieldTheory.ClassFieldAxiom.allInfinitePlaceLocalNormCondition
            (K := K) (L := L) from hx.2) w

private theorem norm_includeRight
    (K L A : Type)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommRing A] [Algebra K A]
    (y : L) :
    Algebra.norm A
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := L) y) =
      algebraMap K A (Algebra.norm K y) := by
  classical
  let b := Module.Free.chooseBasis K L
  let bA := b.baseChange A
  rw [Algebra.norm_eq_matrix_det bA,
    Algebra.norm_eq_matrix_det b, (algebraMap K A).map_det]
  congr 1
  ext i j
  simp [bA, b, Algebra.TensorProduct.includeRight,
    Algebra.smul_def, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- A global determinant norm remains a determinant norm after scalar
extension to any completion.  No Galois hypothesis is needed. -/
theorem globalNorm_isEverywhereLocalNorm
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (x : Kˣ) :
    ClassFieldTheory.IsFieldNorm K L x →
      ClassFieldTheory.IsEverywhereLocalNorm K L x := by
  rintro ⟨y, rfl⟩
  constructor
  · intro w
    refine ⟨Units.map
      (Algebra.TensorProduct.includeRight
        (R := K) (A := w.adicCompletion K) (B := L)).toRingHom y, ?_⟩
    change Algebra.norm (w.adicCompletion K)
      (Algebra.TensorProduct.includeRight
        (R := K) (A := w.adicCompletion K) (B := L) (y : L)) =
        algebraMap K (w.adicCompletion K) (Algebra.norm K (y : L))
    exact norm_includeRight K L (w.adicCompletion K) y
  · intro w
    refine ⟨Units.map
      (Algebra.TensorProduct.includeRight
        (R := K) (A := w.Completion) (B := L)).toRingHom y, ?_⟩
    change Algebra.norm w.Completion
      (Algebra.TensorProduct.includeRight
        (R := K) (A := w.Completion) (B := L) (y : L)) =
        algebraMap K w.Completion (Algebra.norm K (y : L))
    exact norm_includeRight K L w.Completion y

/-- Implementation bridge for Hasse's norm theorem for finite cyclic
extensions. -/
theorem cyclicHasseNormTheorem
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (x : Kˣ) :
    ClassFieldTheory.IsFieldNorm K L x ↔
      ClassFieldTheory.IsEverywhereLocalNorm K L x := by
  rw [isFieldNorm_iff_mem_globalFieldNormSubgroup,
    isEverywhereLocalNorm_iff_mem_everywhereLocalFieldNormSubgroup,
    GlobalClassFieldTheory.ClassFieldAxiom.hasseNormPrinciple_cyclic K L]

end GlobalClassFieldTheory.ClassFieldAxiom
