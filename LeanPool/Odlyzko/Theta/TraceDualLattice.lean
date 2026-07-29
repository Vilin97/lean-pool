/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Theta.ScaledEmbedding

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Module NumberField NumberField.InfinitePlace Submodule
open scoped nonZeroDivisors RealInnerProductSpace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- A trace ideal real basis used in the Odlyzko-bound argument. -/
noncomputable def traceIdealRealBasis
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Basis (Free.ChooseBasisIndex ℤ I) ℝ
      (mixedEmbedding.euclidean.mixedSpace K) :=
  (mixedEmbedding.fractionalIdealLatticeBasis K I).map
    (traceToMixed K).symm.toLinearEquiv

open Classical in
@[simp]
theorem traceIdealRealBasis_apply
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (i : Free.ChooseBasisIndex ℤ I) :
    traceIdealRealBasis K I i =
      traceEmbedding K (basisOfFractionalIdeal K I i) := by
  rw [traceIdealRealBasis, Basis.map_apply,
    mixedEmbedding.fractionalIdealLatticeBasis_apply]
  rfl

open Classical in
theorem span_traceIdealRealBasis
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    span ℤ (Set.range (traceIdealRealBasis K I)) =
      traceIdealLattice K I := by
  rw [traceIdealLattice]
  let eZ :
      mixedEmbedding.euclidean.mixedSpace K ≃ₗ[ℤ]
        mixedEmbedding.mixedSpace K :=
    (traceToMixed K).toLinearEquiv.restrictScalars ℤ
  have hrange :
      Set.range (traceIdealRealBasis K I) =
        eZ.symm '' Set.range
          (mixedEmbedding.fractionalIdealLatticeBasis K I) := by
    ext x
    simp [eZ, traceIdealRealBasis]
  calc
    span ℤ (Set.range (traceIdealRealBasis K I)) =
        (span ℤ
          (Set.range (mixedEmbedding.fractionalIdealLatticeBasis K I))).map
            eZ.symm.toLinearMap := by simp_all
    _ = (mixedEmbedding.idealLattice K I).map
          eZ.symm.toLinearMap := by
      rw [mixedEmbedding.span_idealLatticeBasis]
    _ = ZLattice.comap ℝ (mixedEmbedding.idealLattice K I)
          (traceToMixed K).toLinearMap := by
      change (mixedEmbedding.idealLattice K I).map eZ.symm.toLinearMap =
        (mixedEmbedding.idealLattice K I).comap eZ.toLinearMap
      exact Submodule.map_equiv_eq_comap_symm eZ.symm _

open Classical in
theorem innerDualBasis_traceIdealRealBasis_apply
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (i : Free.ChooseBasisIndex ℤ I) :
    LinearMap.BilinForm.dualBasis
        (innerₗ (mixedEmbedding.euclidean.mixedSpace K))
        innerBilin_nondegenerate (traceIdealRealBasis K I) i =
      traceConjugation K
        (traceEmbedding K
          ((basisOfFractionalIdeal K I).traceDual i)) := by
  have h :
      LinearMap.BilinForm.dualBasis
          (innerₗ (mixedEmbedding.euclidean.mixedSpace K))
          innerBilin_nondegenerate (traceIdealRealBasis K I) =
        fun i ↦ traceConjugation K
          (traceEmbedding K
            ((basisOfFractionalIdeal K I).traceDual i)) := by
    rw [LinearMap.BilinForm.dualBasis_eq_iff]
    intro a b
    rw [traceIdealRealBasis_apply]
    change inner ℝ
      (traceConjugation K
        (traceEmbedding K
          ((basisOfFractionalIdeal K I).traceDual a)))
      (traceEmbedding K (basisOfFractionalIdeal K I b)) = _
    rw [real_inner_comm,
      inner_traceEmbedding_traceConjugation K]
    rw [Module.Basis.trace_mul_traceDual]
    split_ifs <;> norm_num
  exact congrFun h i

open Classical in
theorem span_traceDual_basisOfFractionalIdeal
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    span ℤ (Set.range
        (basisOfFractionalIdeal K I).traceDual) =
      ((traceDualIdealUnit K I :
          FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K).restrictScalars ℤ := by
  rw [coe_traceDualIdealUnit,
    FractionalIdeal.coe_dual (A := ℤ) (K := ℚ)
      (Units.ne_zero I)]
  symm
  apply Submodule.traceDual_span_of_basis ℤ
  ext x
  exact (mem_span_basisOfFractionalIdeal K).symm

open Classical in
/-- A trace embedding int linear map used in the Odlyzko-bound argument. -/
noncomputable def traceEmbeddingIntLinearMap :
    K →ₗ[ℤ] mixedEmbedding.euclidean.mixedSpace K :=
  ((traceToMixed K).symm.toLinearEquiv.toLinearMap.restrictScalars ℤ).comp
    (mixedEmbedding K).toIntAlgHom.toLinearMap

open Classical in
@[simp]
theorem traceEmbeddingIntLinearMap_apply (x : K) :
    traceEmbeddingIntLinearMap K x = traceEmbedding K x :=
  rfl

open Classical in
/-- A conjugate trace ideal lattice used in the Odlyzko-bound argument. -/
noncomputable def conjugateTraceIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (mixedEmbedding.euclidean.mixedSpace K) :=
  (traceIdealLattice K I).map
    ((traceConjugation K).toLinearEquiv.restrictScalars ℤ).toLinearMap

open Classical in
theorem map_traceEmbeddingIntLinearMap_fractionalIdeal
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((I : Submodule (𝓞 K) K).restrictScalars ℤ).map
        (traceEmbeddingIntLinearMap K) =
      traceIdealLattice K I := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (traceEmbedding_mem_traceIdealLattice K I).2 hx
  · intro hv
    obtain ⟨x, hx, hxv⟩ :=
      exists_traceEmbedding_eq_of_mem_traceIdealLattice K I hv
    exact ⟨x, hx, by simpa using hxv⟩

open Classical in
theorem span_conjugate_traceDual_basisOfFractionalIdeal
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    span ℤ (Set.range fun i : Free.ChooseBasisIndex ℤ I ↦
        traceConjugation K
          (traceEmbedding K
            ((basisOfFractionalIdeal K I).traceDual i))) =
      conjugateTraceIdealLattice K (traceDualIdealUnit K I) := by
  let cZ :
      mixedEmbedding.euclidean.mixedSpace K ≃ₗ[ℤ]
      mixedEmbedding.euclidean.mixedSpace K :=
    (traceConjugation K).toLinearEquiv.restrictScalars ℤ
  have hrange :
      Set.range (fun i : Free.ChooseBasisIndex ℤ I ↦
        traceConjugation K
          (traceEmbedding K
            ((basisOfFractionalIdeal K I).traceDual i))) =
        (cZ.toLinearMap.comp (traceEmbeddingIntLinearMap K)) ''
          Set.range (basisOfFractionalIdeal K I).traceDual := by
    ext x
    simp [cZ]
  calc
    span ℤ (Set.range fun i : Free.ChooseBasisIndex ℤ I ↦
        traceConjugation K
          (traceEmbedding K
            ((basisOfFractionalIdeal K I).traceDual i))) =
        (span ℤ (Set.range
          (basisOfFractionalIdeal K I).traceDual)).map
            (cZ.toLinearMap.comp (traceEmbeddingIntLinearMap K)) := by
      rw [hrange, Submodule.map_span]
    _ = (((traceDualIdealUnit K I :
          FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K).restrictScalars ℤ).map
            (cZ.toLinearMap.comp (traceEmbeddingIntLinearMap K)) := by
      rw [span_traceDual_basisOfFractionalIdeal]
    _ = conjugateTraceIdealLattice K (traceDualIdealUnit K I) := by
      rw [Submodule.map_comp, map_traceEmbeddingIntLinearMap_fractionalIdeal]
      rfl

open Classical in
theorem dualLattice_traceIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualLattice (traceIdealLattice K I) =
      conjugateTraceIdealLattice K (traceDualIdealUnit K I) := by
  rw [dualLattice, ← span_traceIdealRealBasis K I]
  rw [LinearMap.BilinForm.dualSubmodule_span_of_basis
    (innerₗ (mixedEmbedding.euclidean.mixedSpace K))
    innerBilin_nondegenerate (traceIdealRealBasis K I)]
  rw [show Set.range
      (LinearMap.BilinForm.dualBasis
        (innerₗ (mixedEmbedding.euclidean.mixedSpace K))
        innerBilin_nondegenerate (traceIdealRealBasis K I)) =
      Set.range (fun i : Free.ChooseBasisIndex ℤ I ↦
        traceConjugation K
          (traceEmbedding K
            ((basisOfFractionalIdeal K I).traceDual i))) by
    congr 1
    funext i
    exact innerDualBasis_traceIdealRealBasis_apply K I i]
  exact span_conjugate_traceDual_basisOfFractionalIdeal K I

end NumberField.Odlyzko
