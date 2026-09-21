/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
/-!
# Subgroup data of coherent finite local reciprocity families

At a fixed finite abelian stage, every Galois subgroup is the fixing subgroup
of an intermediate field. Transporting that field into the chosen separable
closure lets the common norm-kernel and tower conditions compare two Artin
families on every Galois subgroup.
-/

noncomputable section

namespace LocalClassFieldTheory

open ClassFieldTheory

/-- If two coherent families have the same norm kernels, membership in any
Galois subgroup for one family implies membership for the other. Applying
the result with the two families swapped gives equality of preimages. -/
theorem finiteAbelianArtinFamilies_subgroup_preimage_le
    (K : Type) [Field K] [TopologicalSpace K]
    (f g : (E : FiniteAbelianLocalExtension K) →
      Kˣ →ₜ* (E.1 ≃ₐ[K] E.1))
    (hfker : ∀ E : FiniteAbelianLocalExtension K,
      (f E).toMonoidHom.ker = E.normSubgroup)
    (hgker : ∀ E : FiniteAbelianLocalExtension K,
      (g E).toMonoidHom.ker = E.normSubgroup)
    (hfcoh : ∀ (E F : FiniteAbelianLocalExtension K)
      (hEF : E.1 ≤ F.1) (x : Kˣ) (y : E.1),
      IntermediateField.inclusion hEF ((f E x) y) =
        (f F x) (IntermediateField.inclusion hEF y))
    (hgcoh : ∀ (E F : FiniteAbelianLocalExtension K)
      (hEF : E.1 ≤ F.1) (x : Kˣ) (y : E.1),
      IntermediateField.inclusion hEF ((g E x) y) =
        (g F x) (IntermediateField.inclusion hEF y))
    (F : FiniteAbelianLocalExtension K)
    (S : Subgroup (F.1 ≃ₐ[K] F.1)) (x : Kˣ) :
    f F x ∈ S → g F x ∈ S := by
  let M₀ : IntermediateField K F.1 := IntermediateField.fixedField S
  let M : IntermediateField K (SeparableClosure K) := M₀.map F.1.val
  let e : M₀ ≃ₐ[K] M := IntermediateField.equivMap M₀ F.1.val
  let : FiniteDimensional K M :=
    LinearEquiv.finiteDimensional e.toLinearEquiv
  let : IsAbelianGalois K M :=
    IsAbelianGalois.of_algHom e.symm.toAlgHom
  let Mpack : FiniteAbelianLocalExtension K :=
    ⟨M, inferInstance, inferInstance⟩
  have hMF : M ≤ F.1 := by
    intro z hz
    obtain ⟨y, _, rfl⟩ := (IntermediateField.mem_map M₀).mp hz
    exact y.property
  have heIncl (y : M₀) :
      IntermediateField.inclusion hMF (e y) = (y : F.1) := by
    apply Subtype.ext
    exact IntermediateField.coe_equivMap_apply M₀ F.1.val y
  have hFix (σ : F.1 ≃ₐ[K] F.1) :
      σ ∈ S ↔
        ∀ z : M, σ (IntermediateField.inclusion hMF z) =
          IntermediateField.inclusion hMF z := by
    rw [← IntermediateField.fixingSubgroup_fixedField S]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro hσ z
      obtain ⟨y, rfl⟩ := e.surjective z
      rw [heIncl]
      exact hσ y y.property
    · intro hσ y hy
      let z : M₀ := ⟨y, hy⟩
      have hz := hσ (e z)
      rw [heIncl] at hz
      exact hz
  intro hσS
  have hfM : f Mpack x = 1 := by
    apply AlgEquiv.ext
    intro z
    change (f Mpack x) z = z
    apply (IntermediateField.inclusion hMF).injective
    calc
      IntermediateField.inclusion hMF ((f Mpack x) z) =
          (f F x) (IntermediateField.inclusion hMF z) :=
            hfcoh Mpack F hMF x z
      _ = IntermediateField.inclusion hMF z := (hFix (f F x)).mp hσS z
  have hnorm : x ∈ Mpack.normSubgroup := by
    rw [← hfker Mpack]
    exact hfM
  have hgM : g Mpack x = 1 := by
    have hmem : x ∈ (g Mpack).toMonoidHom.ker := by
      rw [hgker Mpack]
      exact hnorm
    exact hmem
  apply (hFix (g F x)).mpr
  intro z
  calc
    (g F x) (IntermediateField.inclusion hMF z) =
        IntermediateField.inclusion hMF ((g Mpack x) z) :=
          (hgcoh Mpack F hMF x z).symm
    _ = IntermediateField.inclusion hMF z := by rw [hgM]; rfl

end LocalClassFieldTheory
