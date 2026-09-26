/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.Basis
/-!
# Coprime tensor-product base change of a Galois extension

The roots-of-unity descent uses the following concrete fact. If finite field
extensions `M / K` and `L / K` have
coprime degrees, then `M ⊗[K] L` is a field.  If `L / K` is Galois,
the resulting extension over `M` is Galois of the same degree.

The proof constructs the field structure from linear disjointness.
For Galoisness, every automorphism of `L / K` is extended by
`id_M ⊗ σ`; these distinct automorphisms already account for the full
dimension of the tensor product.
-/

@[expose] public section

open scoped TensorProduct

noncomputable
section

universe u

variable
    (K M L : Type u)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra K L]
    [hKM : FiniteDimensional K M]
    [hKL : FiniteDimensional K L]

/-- Coprime finite field extensions are linearly disjoint, hence their
tensor product is a field. -/
theorem tensorProduct_isField_of_finrank_coprime
    (hcoprime :
      (Module.finrank K M).Coprime
        (Module.finrank K L)) :
    IsField (M ⊗[K] L) := by
  let Ω := AlgebraicClosure K
  let iM : M →ₐ[K] Ω := IsAlgClosed.lift
  let iL : L →ₐ[K] Ω := IsAlgClosed.lift
  let eM : M ≃ₐ[K] iM.fieldRange :=
    AlgEquiv.ofInjectiveField iM
  let eL : L ≃ₐ[K] iL.fieldRange :=
    AlgEquiv.ofInjectiveField iL
  have hdegrees :
      (Module.finrank K iM.fieldRange).Coprime
        (Module.finrank K iL.fieldRange) := by
    rw [← eM.toLinearEquiv.finrank_eq,
      ← eL.toLinearEquiv.finrank_eq]
    exact hcoprime
  have hdisjoint :
      iM.fieldRange.LinearDisjoint iL.fieldRange :=
    IntermediateField.LinearDisjoint.of_finrank_coprime
      hdegrees
  exact
    IntermediateField.LinearDisjoint.isField_of_isAlgebraic'
      hdisjoint
      (Or.inl (Algebra.IsAlgebraic.of_finite K M))

section TensorAutomorphisms

variable [hGalois : IsGalois K L]

/-- Extend a `K`-automorphism of `L` to the coprime tensor base
change, fixing the left factor `M`. -/
def tensorBaseChangeAut
    (σ : L ≃ₐ[K] L) :
    (M ⊗[K] L) ≃ₐ[M] (M ⊗[K] L) :=
  { (Algebra.TensorProduct.congr
      (AlgEquiv.refl : M ≃ₐ[K] M) σ).toRingEquiv with
    commutes' := by
      intro m
      simp [Algebra.TensorProduct.algebraMap_apply] }

omit hKM hKL hGalois in
@[simp]
theorem tensorBaseChangeAut_tmul
    (σ : L ≃ₐ[K] L)
    (m : M) (x : L) :
    tensorBaseChangeAut K M L σ (m ⊗ₜ[K] x) =
      m ⊗ₜ[K] σ x := by
  simp [tensorBaseChangeAut]

omit hKM hKL hGalois in
/-- Distinct automorphisms remain distinct after tensor base change. -/
theorem tensorBaseChangeAut_injective :
    Function.Injective (tensorBaseChangeAut K M L) := by
  intro σ τ hστ
  apply AlgEquiv.ext
  intro x
  have hx :=
    DFunLike.congr_fun hστ
      ((1 : M) ⊗ₜ[K] x)
  have htensor :
      (1 : M) ⊗ₜ[K] σ x =
        (1 : M) ⊗ₜ[K] τ x := by
    simpa using hx
  exact
    (Algebra.TensorProduct.includeRight
      (R := K) (A := M) (B := L)).injective
      htensor

/-- Galoisness survives the coprime tensor-product base change. -/
theorem tensorProduct_isGalois_of_finrank_coprime
    (hcoprime :
      (Module.finrank K M).Coprime
        (Module.finrank K L)) :
    letI : Field (M ⊗[K] L) :=
      (tensorProduct_isField_of_finrank_coprime
        K M L hcoprime).toField
    IsGalois M (M ⊗[K] L) := by
  let N := M ⊗[K] L
  let : Field N :=
    (tensorProduct_isField_of_finrank_coprime
      K M L hcoprime).toField
  have hfinite : FiniteDimensional M N := by
    exact Module.Finite.of_restrictScalars_finite K M N
  let : FiniteDimensional M N := hfinite
  have hlow :
      Nat.card (L ≃ₐ[K] L) ≤
        Nat.card (N ≃ₐ[M] N) :=
    Nat.card_le_card_of_injective
      (tensorBaseChangeAut K M L)
      (tensorBaseChangeAut_injective K M L)
  have hdim :
      Module.finrank M N = Module.finrank K L := by
    exact Module.finrank_baseChange
  have hlow' :
      Module.finrank M N ≤
        Nat.card (N ≃ₐ[M] N) := by
    rw [hdim, ← IsGalois.card_aut_eq_finrank K L]
    exact hlow
  have hupp :
      Nat.card (N ≃ₐ[M] N) ≤
        Module.finrank M N := by
    rw [Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  exact
    IsGalois.of_card_aut_eq_finrank M N
      (Nat.le_antisymm hupp hlow')

end TensorAutomorphisms
