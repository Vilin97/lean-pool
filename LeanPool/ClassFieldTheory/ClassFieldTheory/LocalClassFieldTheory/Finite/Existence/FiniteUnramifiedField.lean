/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormContainment
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedComparison
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
/-!
# The standard finite unramified local extension

The abstract local class formation already constructs, for every positive
`d`, a canonical finite unramified abelian subextension of the local absolute
Galois group.  This file takes its actual fixed field in the chosen separable
closure and equips that field with the existing spectral local-field
structure.

No second Frobenius is introduced.  The canonical lift on this field is the
existing `arithmeticFrobeniusOfUnramifiedValuation`.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory

open scoped ValuativeRel
open ClassFormation LocalFieldTheory

/-- The actual fixed field of the canonical degree-`d` unramified factor. -/
abbrev localFiniteUnramifiedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    IntermediateField K (SeparableClosure K) :=
  abstractFixedField K (SeparableClosure K)
    (localFiniteUnramifiedAbelianSubextension K d hd).field

/-- The standard unramified fixed field is finite over its base. -/
noncomputable instance localFiniteUnramifiedField_finiteDimensional
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    FiniteDimensional K (localFiniteUnramifiedField K d hd) :=
  abstractFixedField_finiteDimensional K (SeparableClosure K)
    (localFiniteUnramifiedAbelianSubextension K d hd).field
    (finiteAbelianSubextension_finite_over_absoluteBase K
      (localFiniteUnramifiedAbelianSubextension K d hd))

/-- The standard unramified fixed field is abelian Galois over its base. -/
noncomputable instance localFiniteUnramifiedField_isAbelianGalois
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    IsAbelianGalois K (localFiniteUnramifiedField K d hd) :=
  finiteAbelianSubextension_fixedField_isAbelianGalois K
    (localFiniteUnramifiedAbelianSubextension K d hd)

/-- The canonical spectral norm on the standard unramified fixed field. -/
noncomputable instance localFiniteUnramifiedFieldNontriviallyNormedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    NontriviallyNormedField (localFiniteUnramifiedField K d hd) :=
  finiteExtensionSpectralNormedField K
    (localFiniteUnramifiedField K d hd)

/-- The valuation relation induced by the canonical spectral norm. -/
noncomputable instance localFiniteUnramifiedFieldValuativeRel
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    ValuativeRel (localFiniteUnramifiedField K d hd) :=
  finiteExtensionSpectralValuativeRel K
    (localFiniteUnramifiedField K d hd)

/-- A standard finite unramified fixed field is again a local field. -/
noncomputable instance localFiniteUnramifiedField_isNonarchimedeanLocalField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    IsNonarchimedeanLocalField (localFiniteUnramifiedField K d hd) :=
  finiteExtensionSpectralIsNonarchimedeanLocalField K
    (localFiniteUnramifiedField K d hd)

/-- The spectral valuation is the extension of the valuation on `K`. -/
noncomputable instance localFiniteUnramifiedField_valuationHasExtension
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation (localFiniteUnramifiedField K d hd)) :=
  finiteExtensionSpectralValuation_hasExtension K
    (localFiniteUnramifiedField K d hd)

/-- The fixed field has the degree prescribed by the abstract unramified
factor. -/
theorem localFiniteUnramifiedField_finrank
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    Module.finrank K (localFiniteUnramifiedField K d hd) = d := by
  let G := intrinsicAbsoluteGalois K
  let D := localResidueDatum K
  let B : FiniteAbstractField G :=
    intrinsicFiniteAbstractBase K
  let Bresidue := B.toFiniteResidueAbstractField D
  let U := localFiniteUnramifiedAbelianSubextension K d hd
  have hdegree :
      (U.toFiniteGaloisExtension.toFiniteAbstractExtension.degree : ℕ) = d := by
    have h := D.finiteUnramifiedExtension_degree Bresidue d hd
    change
      (U.toFiniteGaloisExtension.toFiniteAbstractExtension.degree : ℕ) = d at h
    exact h
  calc
    Module.finrank K (localFiniteUnramifiedField K d hd) =
        (abstractFixedField K (SeparableClosure K)
          U.field).fixingSubgroup.index :=
      IntermediateField.finrank_eq_fixingSubgroup_index
        (F := K) (SeparableClosure K)
        (abstractFixedField K (SeparableClosure K) U.field)
    _ = U.field.toSubgroup.index := by
      rw [InfiniteGalois.fixingSubgroup_fixedField U.field]
    _ = (CyclicCohomology.extensionSubgroup
          (intrinsicAbstractBase K) U.field U.below).index := by
      change U.field.toSubgroup.index =
        (U.field.toSubgroup.subgroupOf
          (intrinsicAbstractBase K).toSubgroup).index
      rw [show (intrinsicAbstractBase K).toSubgroup = ⊤ by
        simpa [G] using congrArg ClosedSubgroup.toSubgroup
          (closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K))]
      rw [← Subgroup.relIndex_top_right]
      rfl
    _ = (U.toFiniteGaloisExtension.toFiniteAbstractExtension.degree : ℕ) :=
      U.toFiniteGaloisExtension.toFiniteAbstractExtension.extensionSubgroup_index_eq_degree
    _ = d := hdegree

/-- The literal residue extension of the standard fixed field also has
degree `d`. -/
theorem localFiniteUnramifiedField_residue_finrank
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    @Module.finrank 𝓀[K]
      𝓀[localFiniteUnramifiedField K d hd] _ _
        (IsLocalRing.ResidueField.instModule
          (R := 𝒪[K])
          (S := 𝒪[localFiniteUnramifiedField K d hd])) = d := by
  let G := intrinsicAbsoluteGalois K
  let D := localResidueDatum K
  let B : FiniteAbstractField G :=
    intrinsicFiniteAbstractBase K
  let Bresidue := B.toFiniteResidueAbstractField D
  let U := localFiniteUnramifiedAbelianSubextension K d hd
  let H : FiniteAbstractField G :=
    ⟨U.field, finiteAbelianSubextension_finite_over_absoluteBase K U⟩
  let EU : FiniteAbstractFieldExtension G :=
    { field := H
      base := B
      below := U.below
      finiteQuotient := U.finite }
  have hrelative : (EU.residueDegree D : ℕ) = d := by
    have h := D.finiteUnramifiedExtension_residueDegree Bresidue d hd
    change (EU.residueDegree D : ℕ) = d at h
    exact h
  have hbase : (B.residueDegree D : ℕ) = 1 := by
    exact intrinsicFiniteAbstractBase_residueDegree_eq_one K
  have habsolute : (H.residueDegree D : ℕ) = d := by
    let ER := EU.toFiniteResidueAbstractExtension D
    have htower := ER.residueDegree_mul_absoluteResidueDegree D
    change
      (EU.residueDegree D : ℕ) * (B.residueDegree D : ℕ) =
        (H.residueDegree D : ℕ) at htower
    rw [hrelative, hbase, mul_one] at htower
    exact htower.symm
  have hcomparison :=
    localResidueDatum_residueDegree_eq_residueFinrank K H
  change
    (H.residueDegree D : ℕ) =
      @Module.finrank 𝓀[K]
        𝓀[localFiniteUnramifiedField K d hd] _ _
          (IsLocalRing.ResidueField.instModule
            (R := 𝒪[K])
            (S := 𝒪[localFiniteUnramifiedField K d hd])) at hcomparison
  exact hcomparison.symm.trans habsolute

/-- The standard fixed field is unramified for the actual local valuations. -/
noncomputable instance localFiniteUnramifiedField_isUnramifiedValuedExtension
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K
      (localFiniteUnramifiedField K d hd) where
  maximalIdeal_ramificationIdx_eq_one := by
    have hfund :=
      maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank K
        (localFiniteUnramifiedField K d hd)
    have hmax : (𝓂[K] : Ideal 𝒪[K]) ≠ ⊥ :=
      Ring.ne_bot_of_isMaximal_of_not_isField
        (IsLocalRing.maximalIdeal.isMaximal 𝒪[K])
        (IsDiscreteValuationRing.not_isField 𝒪[K])
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hmax,
      localFiniteUnramifiedField_residue_finrank K d hd,
      localFiniteUnramifiedField_finrank K d hd] at hfund
    apply Nat.eq_of_mul_eq_mul_right hd
    simpa only [one_mul] using hfund

/-- On the standard degree-`d` fixed field, the existing arithmetic
Frobenius has order exactly `d`. -/
theorem localFiniteUnramifiedField_arithmeticFrobenius_order
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    orderOf
        (arithmeticFrobeniusOfUnramifiedValuation K
          (localFiniteUnramifiedField K d hd)) =
      d := by
  rw [orderOf_arithmeticFrobeniusOfUnramifiedValuation,
    localFiniteUnramifiedField_finrank K d hd]

end LocalClassFieldTheory

end
