/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport
/-!
# Field-facing order reversal for finite abelian extensions

This module realizes a finite abelian extension inside a fixed separable
closure and packages it as an abstract finite abelian subextension. It then
transports the abstract order reversal for norm subgroups back to ordinary
field norms. The final lemmas record the standard open subgroups contained in
the norm subgroup of a finite abelian extension.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation

/-- A finite abelian extension, realized by an explicit embedding in the
fixed separable closure, as an abstract finite abelian subextension. -/
def finiteAbelianAbstractExtensionOfEmbedding
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (i : L →ₐ[K] SeparableClosure K) :
    FiniteAbelianSubextension (intrinsicAbstractBase K) where
  toFiniteGaloisExtension :=
    finiteGaloisAbstractExtensionOfEmbedding K L i
  commutative := by
    change IsMulCommutative
      ((closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
        extensionSubgroup
          (closedFixingSubgroup K (SeparableClosure K)
            (⊥ : IntermediateField K (SeparableClosure K)))
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
          (fixingSubgroupLeBase K (SeparableClosure K)
            (finiteGaloisFieldRangeOfEmbedding K L i)))
    let e := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
    exact
      { is_comm.comm := fun x y => by
          apply e.injective
          simp only [map_mul]
          exact
            (inferInstance :
              IsMulCommutative (Gal(L/K))).is_comm.comm (e x) (e y) }

/-- Under the canonical identification of the abstract base fixed units with
`Kˣ`, the abstract norm subgroup of an embedded finite abelian extension is
its ordinary field-norm subgroup. -/
theorem map_finiteAbelianAbstractExtension_normSubgroup_eq
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (i : L →ₐ[K] SeparableClosure K) :
    ((finiteAbelianAbstractExtensionOfEmbedding K L i).normSubgroup
        (intrinsicAbsoluteUnits K)).map
      (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
      additiveNormSubgroup K L := by
  let : FiniteDimensional K (AlgHom.fieldRange i) :=
    (AlgEquiv.ofInjectiveField i).toLinearEquiv.finiteDimensional
  let : IsGalois K (AlgHom.fieldRange i) :=
    IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField i)
  rw [show additiveNormSubgroup K L =
      additiveNormSubgroup K (AlgHom.fieldRange i) by
    exact congrArg Subgroup.toAddSubgroup
      (localNormSubgroup_fieldRange_eq K (SeparableClosure K) L i).symm]
  exact map_finiteNormSubgroup_eq_additiveNormSubgroup K
    (SeparableClosure K) (AlgHom.fieldRange i)

/-- Reverse inclusion of ordinary norm subgroups produces an embedding of
finite abelian extensions over the common local base field. -/
theorem nonempty_algHom_of_normSubgroup_le
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsAbelianGalois K L] [IsAbelianGalois K M]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (h : localNormSubgroup K M ≤ localNormSubgroup K L) :
    Nonempty (L →ₐ[K] M) := by
  let iL := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L
  let iM := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K M
  let AL := finiteAbelianAbstractExtensionOfEmbedding K L iL
  let AM := finiteAbelianAbstractExtensionOfEmbedding K M iM
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  have hAbs : AM.normSubgroup (intrinsicAbsoluteUnits K) ≤
      AL.normSubgroup (intrinsicAbsoluteUnits K) := by
    intro x hx
    have hxM : e.symm x ∈ additiveNormSubgroup K M := by
      rw [← map_finiteAbelianAbstractExtension_normSubgroup_eq K M iM]
      exact ⟨x, hx, rfl⟩
    have hxL : e.symm x ∈ additiveNormSubgroup K L := by
      change Additive.toMul (e.symm x) ∈ localNormSubgroup K L
      apply h
      exact hxM
    rw [← map_finiteAbelianAbstractExtension_normSubgroup_eq K L iL] at hxL
    rcases hxL with ⟨y, hy, hyx⟩
    have hyEq : y = x := by
      apply e.symm.injective
      exact hyx
    simpa [hyEq] using hy
  have hALAM : AL ≤ AM :=
    (FiniteAbelianSubextension.le_iff_normSubgroup_le
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)
      (intrinsicFiniteAbstractBase K) AL AM).2 hAbs
  have hRange : AlgHom.fieldRange iL ≤ AlgHom.fieldRange iM := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (AlgHom.fieldRange iM)]
    apply (IntermediateField.le_iff_le
      (AlgHom.fieldRange iM).fixingSubgroup (AlgHom.fieldRange iL)).2
    exact hALAM
  exact ⟨(finiteGaloisFieldRangeEquivOfEmbedding K M iM).symm.toAlgHom.comp
    ((IntermediateField.inclusion hRange).comp
      (finiteGaloisFieldRangeEquivOfEmbedding K L iL).toAlgHom)⟩

/-- For a prescribed prime element, the norm subgroup of a finite abelian
extension contains a standard subgroup `⟨ϖᵈ⟩ Uⁿ` for some positive
integers `d` and `n`. -/
theorem exists_uniformizerPrincipalSubgroup_le_normSubgroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) :
    ∃ d n : ℕ, 0 < d ∧ 1 ≤ n ∧
      LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤
        localNormSubgroup K L := by
  let : Finite (Gal(L/K)) := by
    apply Nat.finite_of_card_ne_zero
    rw [IsGalois.card_aut_eq_finrank K L]
    exact Nat.ne_of_gt Module.finrank_pos
  let : Finite (Abelianization (Gal(L/K))) :=
    Finite.of_surjective Abelianization.of QuotientGroup.mk_surjective
  let : Finite (NormQuotient K L) :=
    Finite.of_equiv
      (Abelianization (Gal(L/K)))
      (abelianizationEquivNormQuotient K L).toEquiv
  let : Finite (Kˣ ⧸ localNormSubgroup K L) := by
    change Finite (NormQuotient K L)
    infer_instance
  let : (localNormSubgroup K L).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨n, hn, hUn⟩ :=
    LocalFieldTheory.exists_fieldPrincipalUnits_le_of_isOpen K (localNormSubgroup K L)
      (localNormSubgroup_isOpen K L)
  refine ⟨(localNormSubgroup K L).index, n,
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, hn, ?_⟩
  apply sup_le
  · exact (Subgroup.zpowers_le).2
      ((localNormSubgroup K L).pow_index_mem ϖ)
  · exact hUn

/-- If the prescribed prime element is itself a norm, the norm subgroup
contains a standard subgroup with uniformizer exponent one. -/
theorem exists_uniformizerPrincipalSubgroup_one_le_normSubgroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : ϖ ∈ localNormSubgroup K L) :
    ∃ n : ℕ, 1 ≤ n ∧
      LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n ≤
        localNormSubgroup K L := by
  obtain ⟨n, hn, hUn⟩ :=
    LocalFieldTheory.exists_fieldPrincipalUnits_le_of_isOpen K (localNormSubgroup K L)
      (localNormSubgroup_isOpen K L)
  refine ⟨n, hn, sup_le ?_ hUn⟩
  simpa using (Subgroup.zpowers_le).2 hϖ

end LocalClassFieldTheory

end
