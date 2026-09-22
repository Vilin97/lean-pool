/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.FiniteAbelianCompositum
/-!
# Embedding a finite Galois compositum into a common field

Two finite normal extensions embedded in a common field generate the same
compositum as their chosen realizations in the separable closure.  This
normality argument is the field-theoretic mechanism used to place the local
inertia-field compositum in one cyclotomic target.
-/

noncomputable section

namespace AlgebraicNumberTheory

open Polynomial

/-- Divisibility of cyclotomic orders gives an embedding of the smaller
concrete cyclotomic field into the larger one. -/
noncomputable def cyclotomicFieldEmbeddingOfDvd
    (K : Type*) [Field K] [CharZero K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n) :
    CyclotomicField m K →ₐ[K] CyclotomicField n K := by
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsCyclotomicExtension {m} K (CyclotomicField m K) :=
    CyclotomicField.isCyclotomicExtension m K
  letI : IsSplittingField K (CyclotomicField m K)
      (Polynomial.cyclotomic m K) :=
    IsCyclotomicExtension.splitting_field_cyclotomic
      m K (CyclotomicField m K)
  let C := CyclotomicField n K
  letI hC : IsCyclotomicExtension {n} K C :=
    CyclotomicField.isCyclotomicExtension n K
  letI : IsCyclotomicExtension ({n} ∪ {m}) K C :=
    IsCyclotomicExtension.of_union_of_dvd K C
      ⟨n, Set.mem_singleton n, hn.ne', hmn⟩
  exact IsSplittingField.lift (CyclotomicField m K)
    (Polynomial.cyclotomic m K)
    (IsCyclotomicExtension.splits_cyclotomic K C
      (Set.mem_union_right {n} (Set.mem_singleton m)))

/-- Base extension and divisibility of cyclotomic orders together give an
embedding into the larger cyclotomic field over the enlarged base. -/
noncomputable def cyclotomicFieldEmbeddingOfBaseAndDvd
    (K K' : Type*) [Field K] [Field K'] [CharZero K] [CharZero K']
    [Algebra K K']
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n) :
    CyclotomicField m K →ₐ[K] CyclotomicField n K' := by
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsCyclotomicExtension {m} K (CyclotomicField m K) :=
    CyclotomicField.isCyclotomicExtension m K
  letI : IsSplittingField K (CyclotomicField m K)
      (Polynomial.cyclotomic m K) :=
    IsCyclotomicExtension.splitting_field_cyclotomic
      m K (CyclotomicField m K)
  let C := CyclotomicField n K'
  letI : IsScalarTower K K' C := inferInstance
  letI hC : IsCyclotomicExtension {n} K' C :=
    CyclotomicField.isCyclotomicExtension n K'
  letI : IsCyclotomicExtension ({n} ∪ {m}) K' C :=
    IsCyclotomicExtension.of_union_of_dvd K' C
      ⟨n, Set.mem_singleton n, hn.ne', hmn⟩
  have hs' : ((Polynomial.cyclotomic m K').map
      (algebraMap K' C)).Splits :=
    IsCyclotomicExtension.splits_cyclotomic K' C
      (Set.mem_union_right {n} (Set.mem_singleton m))
  have hs : ((Polynomial.cyclotomic m K).map
      (algebraMap K C)).Splits := by
    simpa only [← Polynomial.map_cyclotomic m (algebraMap K K'),
      Polynomial.map_map, IsScalarTower.algebraMap_eq K K' C] using hs'
  exact IsSplittingField.lift (CyclotomicField m K)
    (Polynomial.cyclotomic m K) hs

variable (K L E T : Type)
variable [Field K] [Field L] [Field E] [Field T]
variable [Algebra K L] [Algebra K E] [Algebra K T]
variable [FiniteDimensional K L] [FiniteDimensional K E]
variable [IsAbelianGalois K L] [IsAbelianGalois K E]

/-- If two finite Galois extensions embed in one field, their concrete
compositum in the chosen separable closure embeds in that field as well. -/
noncomputable def finiteGaloisCompositumEmbeddingOfEmbeddings
    (i : L →ₐ[K] T) (j : E →ₐ[K] T) :
    finiteAbelianCompositumField K L E →ₐ[K] T := by
  let A : IntermediateField K T := i.fieldRange
  let B : IntermediateField K T := j.fieldRange
  let R : IntermediateField K T := A ⊔ B
  let eA : L ≃ₐ[K] A := AlgEquiv.ofInjectiveField i
  let eB : E ≃ₐ[K] B := AlgEquiv.ofInjectiveField j
  letI : FiniteDimensional K A := eA.toLinearEquiv.finiteDimensional
  letI : FiniteDimensional K B := eB.toLinearEquiv.finiteDimensional
  letI : IsGalois K A := IsGalois.of_algEquiv eA
  letI : IsGalois K B := IsGalois.of_algEquiv eB
  letI : FiniteDimensional K R :=
    IntermediateField.finiteDimensional_sup A B
  letI : IsGalois K R := inferInstance
  let r : R →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let A₀ : IntermediateField K (SeparableClosure K) :=
    finiteGaloisFieldRange K L
  let B₀ : IntermediateField K (SeparableClosure K) :=
    finiteGaloisFieldRange K E
  let M₀ : IntermediateField K (SeparableClosure K) := A₀ ⊔ B₀
  let aR : A →ₐ[K] R := IntermediateField.inclusion le_sup_left
  let bR : B →ₐ[K] R := IntermediateField.inclusion le_sup_right
  let eA₀ : L ≃ₐ[K] A₀ := finiteGaloisFieldRangeEquiv K L
  let eB₀ : E ≃ₐ[K] B₀ := finiteGaloisFieldRangeEquiv K E
  let fA : A₀ →ₐ[K] SeparableClosure K :=
    r.comp (aR.comp (eA.toAlgHom.comp eA₀.symm.toAlgHom))
  let fB : B₀ →ₐ[K] SeparableClosure K :=
    r.comp (bR.comp (eB.toAlgHom.comp eB₀.symm.toAlgHom))
  have hA : A₀ ≤ r.fieldRange := by
    rw [← AlgHom.fieldRange_of_normal fA]
    rintro x ⟨y, rfl⟩
    exact ⟨aR (eA (eA₀.symm y)), rfl⟩
  have hB : B₀ ≤ r.fieldRange := by
    rw [← AlgHom.fieldRange_of_normal fB]
    rintro x ⟨y, rfl⟩
    exact ⟨bR (eB (eB₀.symm y)), rfl⟩
  have hM : M₀ ≤ r.fieldRange := sup_le hA hB
  let intoRange : M₀ →ₐ[K] r.fieldRange :=
    IntermediateField.inclusion hM
  let rangeEquiv : R ≃ₐ[K] r.fieldRange := AlgEquiv.ofInjectiveField r
  exact R.val.comp (rangeEquiv.symm.toAlgHom.comp intoRange)

/-- The common-target embedding can be chosen to agree with the prescribed
embedding of the left factor.  Normality first identifies the two copies of
the left field; the correcting automorphism then extends to the whole
Galois compositum. -/
theorem exists_finiteGaloisCompositumEmbeddingOfEmbeddings_left_eq
    (i : L →ₐ[K] T) (j : E →ₐ[K] T) :
    ∃ g : finiteAbelianCompositumField K L E →ₐ[K] T,
      ∀ x : L, g (finiteAbelianCompositumEmbeddingLeft K L E x) = i x := by
  let M := finiteAbelianCompositumField K L E
  let i₀ : L →ₐ[K] M := finiteAbelianCompositumEmbeddingLeft K L E
  let g₀ : M →ₐ[K] T :=
    finiteGaloisCompositumEmbeddingOfEmbeddings K L E T i j
  let f : L →ₐ[K] T := g₀.comp i₀
  let A : IntermediateField K T := f.fieldRange
  let B : IntermediateField K T := i.fieldRange
  let eF : L ≃ₐ[K] A := AlgEquiv.ofInjectiveField f
  let eI : L ≃ₐ[K] B := AlgEquiv.ofInjectiveField i
  let : FiniteDimensional K A := eF.toLinearEquiv.finiteDimensional
  let : IsGalois K A := IsGalois.of_algEquiv eF
  let gA : A →ₐ[K] T := i.comp eF.symm.toAlgHom
  have hgA_range : gA.fieldRange = B := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      exact ⟨eF.symm x, rfl⟩
    · rintro y ⟨x, rfl⟩
      refine ⟨eF x, ?_⟩
      exact congrArg i (eF.symm_apply_apply x)
  have hAB : A = B :=
    (AlgHom.fieldRange_of_normal gA).symm.trans hgA_range
  let eAB : A ≃ₐ[K] B := IntermediateField.equivOfEq hAB
  let χ : L ≃ₐ[K] L := eI.trans (eAB.symm.trans eF.symm)
  have hfχ (x : L) : f (χ x) = i x := by
    change f (eF.symm (eAB.symm (eI x))) = i x
    have h := congrArg Subtype.val
      (eF.apply_symm_apply (eAB.symm (eI x)))
    exact h
  let A₀ : IntermediateField K M := i₀.fieldRange
  let e₀ : L ≃ₐ[K] A₀ := AlgEquiv.ofInjectiveField i₀
  let : FiniteDimensional K A₀ := e₀.toLinearEquiv.finiteDimensional
  let : IsGalois K A₀ := IsGalois.of_algEquiv e₀
  let hA₀M : Algebra A₀ M := A₀.val.toRingHom.toAlgebra
  let : SMul A₀ M := hA₀M.toSMul
  let : Module A₀ M := hA₀M.toModule
  let : IsScalarTower K A₀ M :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change (((algebraMap K M x : M) : SeparableClosure K) :
          AlgebraicClosure K) =
        (((A₀.val (algebraMap K A₀ x) : M) : SeparableClosure K) :
          AlgebraicClosure K)
      exact congrArg (fun y : M ↦
        (((y : SeparableClosure K)) : AlgebraicClosure K))
          (A₀.val.commutes x).symm)
  let χA : A₀ ≃ₐ[K] A₀ := e₀.symm.trans (χ.trans e₀)
  let σ : M ≃ₐ[K] M := χA.liftNormal M
  have hσ (x : L) : σ (i₀ x) = i₀ (χ x) := by
    change σ (algebraMap A₀ M (e₀ x)) =
      algebraMap A₀ M (e₀ (χ x))
    rw [AlgEquiv.liftNormal_commutes]
    congr 1
    simp [χA]
  refine ⟨g₀.comp σ.toAlgHom, ?_⟩
  intro x
  change g₀ (σ (i₀ x)) = i x
  rw [hσ]
  exact hfχ x

end AlgebraicNumberTheory

end
