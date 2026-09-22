/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.FiniteUnramifiedField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelAbelian
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationInvariants
import Mathlib.FieldTheory.LinearDisjoint
/-!
# The unramified--Lubin--Tate diagonal field for an explicit uniformizer

This module constructs the diagonal descent field attached to an arbitrary
explicit uniformizer.  The unramified factor has the exact order of the inverse
finite Lubin--Tate unit action.  Arithmetic Frobenius on that factor and the
inverse unit action on the Lubin--Tate level therefore glue to one automorphism
of their compositum.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.IsNonarchimedeanLocalField
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open LubinTate

private theorem explicitLocalCompleteDVFValuation_hasExtension
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)] :
    (LocalFieldTheory.localCompleteDVF K).valuation.HasExtension
      (LocalFieldTheory.localCompleteDVF L).valuation := by
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change
    ValuativeRel.valuation L (algebraMap K L x) ≤ 1 ↔
      ValuativeRel.valuation K x ≤ 1
  exact Valuation.HasExtension.val_map_le_one_iff
    (ValuativeRel.valuation K) (ValuativeRel.valuation L) x

/-- With its spectral valuation, the finite Lubin--Tate level attached to an
explicit uniformizer has residue degree one over the local base field. -/
theorem lubinTateLevel_spectral_inertiaDeg_eq_one
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {π : (standardLocalField K).valuationSubring}
    (hπ : (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
      (π : K))
    (n : ℕ) :
    let T := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K T :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : NontriviallyNormedField T :=
      finiteExtensionSpectralNormedField K T
    letI : ValuativeRel T :=
      finiteExtensionSpectralValuativeRel K T
    letI : IsNonarchimedeanLocalField T :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K T
    letI : Valuation.HasExtension (ValuativeRel.valuation K)
        (ValuativeRel.valuation T) :=
      finiteExtensionSpectralValuation_hasExtension K T
    letI :
        (LocalFieldTheory.localCompleteDVF K).valuation.HasExtension
          (LocalFieldTheory.localCompleteDVF T).valuation :=
      explicitLocalCompleteDVFValuation_hasExtension K T
    (LocalFieldTheory.localCompleteDVF T).maximalIdeal.inertiaDeg
      (LocalFieldTheory.localCompleteDVF K).valuationSubring = 1 := by
  let T := standardLubinTateLevelField hπ n
  let : FiniteDimensional K T :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : NontriviallyNormedField T :=
    finiteExtensionSpectralNormedField K T
  let : ValuativeRel T :=
    finiteExtensionSpectralValuativeRel K T
  let : IsNonarchimedeanLocalField T :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K T
  let : Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation T) :=
    finiteExtensionSpectralValuation_hasExtension K T
  let base := (standardLocalField K).toCompleteDVF
  let chosen := standardLubinTateLevelCompleteDVF hπ n
  let spectral := LocalFieldTheory.localCompleteDVF T
  let : base.valuation.HasExtension spectral.valuation :=
    explicitLocalCompleteDVFValuation_hasExtension K T
  have hValuationRing :
      chosen.valuation.valuationSubring =
        spectral.valuation.valuationSubring :=
    valuationSubring_eq_of_finite_separable base chosen spectral.valuation
  have hdegree :
      degree base.toDVF chosen.toDVF =
        ramificationIndex base.toDVF chosen.toDVF *
          residueDegree base.toDVF chosen.toDVF :=
    standardLubinTateLevelCompleteDVF_fundamentalIdentity hπ n
  have hramification :
      ramificationIndex base.toDVF chosen.toDVF =
        degree base.toDVF chosen.toDVF :=
    standardLubinTateLevel_ramificationIndex_eq_degree hπ n
  have hdegreePos : 0 < degree base.toDVF chosen.toDVF := by
    change 0 < Module.finrank K T
    exact Module.finrank_pos
  have hresidue :
      residueDegree base.toDVF chosen.toDVF = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hdegreePos
    simpa [hramification] using hdegree.symm
  change chosen.maximalIdeal.inertiaDeg base.valuationSubring = 1 at hresidue
  let e : chosen.valuationSubring ≃ₐ[base.valuationSubring]
      spectral.valuationSubring :=
    { toFun := fun x => ⟨x, by
        rw [← hValuationRing]
        exact x.property⟩
      invFun := fun x => ⟨x, by
        rw [hValuationRing]
        exact x.property⟩
      left_inv := fun x => by
        apply Subtype.ext
        rfl
      right_inv := fun x => by
        apply Subtype.ext
        rfl
      map_mul' := fun x y => by
        apply Subtype.ext
        rfl
      map_add' := fun x y => by
        apply Subtype.ext
        rfl
      commutes' := fun x => by
        apply Subtype.ext
        rfl }
  have hmap :
      chosen.maximalIdeal.map e = spectral.maximalIdeal :=
    IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv
  have hinertia :
      spectral.maximalIdeal.inertiaDeg base.valuationSubring =
        chosen.maximalIdeal.inertiaDeg base.valuationSubring := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal base.maximalIdeal spectral.maximalIdeal,
      Ideal.inertiaDeg_eq_of_isMaximal base.maximalIdeal chosen.maximalIdeal]
    exact
      (Ideal.Quotient.algEquivOfEqMap base.maximalIdeal e
        hmap.symm).toLinearEquiv.finrank_eq.symm
  change spectral.maximalIdeal.inertiaDeg base.valuationSubring = 1
  exact hinertia.trans hresidue

private theorem explicitLocalCompleteDVF_ramificationIdx_eq_one_of_top
    (K M U : Type) [Field K] [Field M] [Field U]
    [Algebra K M] [Algebra K U] [Algebra M U] [IsScalarTower K M U]
    (base : CompleteDVF K) (middle : CompleteDVF M)
    (total : CompleteDVF U)
    [base.valuation.HasExtension middle.valuation]
    [base.valuation.HasExtension total.valuation]
    [middle.valuation.HasExtension total.valuation]
    [FiniteDimensional M U] [Algebra.IsSeparable M U]
    (htop :
      total.maximalIdeal.ramificationIdx base.valuationSubring = 1) :
    middle.maximalIdeal.ramificationIdx base.valuationSubring = 1 := by
  let : IsScalarTower base.valuationSubring middle.valuationSubring
      total.valuationSubring :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change
        algebraMap K U (x : K) =
          algebraMap M U (algebraMap K M (x : K))
      exact IsScalarTower.algebraMap_apply K M U (x : K))
  let : Algebra middle.valuationSubring U :=
    ((algebraMap total.valuationSubring U).comp
      (algebraMap middle.valuationSubring total.valuationSubring)).toAlgebra
  let : IsScalarTower middle.valuationSubring
      total.valuationSubring U :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite middle.valuationSubring
      total.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable middle total
  let : Module.IsTorsionFree middle.valuationSubring
      total.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      middle total
  let : Module.Free middle.valuationSubring
      total.valuationSubring :=
    Module.free_of_finite_type_torsion_free'
  have hdiv :
      middle.maximalIdeal.ramificationIdx base.valuationSubring ∣
        total.maximalIdeal.ramificationIdx base.valuationSubring :=
    middle.maximalIdeal.ramificationIdx_below_dvd total.maximalIdeal
  rw [htop] at hdiv
  exact Nat.eq_one_of_dvd_one hdiv

private theorem
    localFiniteUnramifiedField_inf_lubinTateLevelField_ramificationIdx
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {π : (standardLocalField K).valuationSubring}
    (hπ : (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
      (π : K))
    (d : ℕ) (hd : 0 < d) (n : ℕ) :
    let U := localFiniteUnramifiedField K d hd
    let T := standardLubinTateLevelField hπ n
    let M := U ⊓ T
    letI : FiniteDimensional K T :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : FiniteDimensional K M :=
      FiniteDimensional.of_injective
        (M.inclusion (show M ≤ U from inf_le_left)).toLinearMap
        (M.inclusion (show M ≤ U from inf_le_left)).injective
    letI : NontriviallyNormedField M :=
      finiteExtensionSpectralNormedField K M
    letI : ValuativeRel M :=
      finiteExtensionSpectralValuativeRel K M
    letI : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K M
    letI : Valuation.HasExtension (ValuativeRel.valuation K)
        (ValuativeRel.valuation M) :=
      finiteExtensionSpectralValuation_hasExtension K M
    let base := LocalFieldTheory.localCompleteDVF K
    let middle := LocalFieldTheory.localCompleteDVF M
    letI : base.valuation.HasExtension middle.valuation :=
      explicitLocalCompleteDVFValuation_hasExtension K M
    middle.maximalIdeal.ramificationIdx base.valuationSubring = 1 := by
  let U := localFiniteUnramifiedField K d hd
  let T := standardLubinTateLevelField hπ n
  let M := U ⊓ T
  let : FiniteDimensional K T :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : FiniteDimensional K M :=
    FiniteDimensional.of_injective
      (M.inclusion (show M ≤ U from inf_le_left)).toLinearMap
      (M.inclusion (show M ≤ U from inf_le_left)).injective
  let : NontriviallyNormedField M :=
    finiteExtensionSpectralNormedField K M
  let : ValuativeRel M :=
    finiteExtensionSpectralValuativeRel K M
  let : IsNonarchimedeanLocalField M :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K M
  let : Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension K M
  let : Algebra M U :=
    (M.inclusion (show M ≤ U from inf_le_left)).toRingHom.toAlgebra
  let : IsScalarTower K M U :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Valuation.HasExtension (ValuativeRel.valuation M)
      (ValuativeRel.valuation U) :=
    finiteExtensionSpectralValuation_hasExtension_of_tower K M U
  let : FiniteDimensional M U :=
    FiniteDimensional.right K M U
  let : Algebra.IsSeparable M U :=
    Algebra.isSeparable_tower_top_of_isSeparable
      (F := K) (L := M) (E := U)
  let base := LocalFieldTheory.localCompleteDVF K
  let middle := LocalFieldTheory.localCompleteDVF M
  let unramified := LocalFieldTheory.localCompleteDVF U
  let : base.valuation.HasExtension middle.valuation :=
    explicitLocalCompleteDVFValuation_hasExtension K M
  let : base.valuation.HasExtension unramified.valuation :=
    explicitLocalCompleteDVFValuation_hasExtension K U
  let : middle.valuation.HasExtension unramified.valuation :=
    explicitLocalCompleteDVFValuation_hasExtension M U
  have hramificationUnramified :
      unramified.maximalIdeal.ramificationIdx base.valuationSubring = 1 := by
    change
      (IsLocalRing.maximalIdeal
          (ValuativeRel.valuation U).integer).ramificationIdx
        (ValuativeRel.valuation K).integer = 1
    exact unramifiedValuation_ramificationIdx_eq_one K U
  exact explicitLocalCompleteDVF_ramificationIdx_eq_one_of_top
    K M U base middle unramified hramificationUnramified

private theorem
    localFiniteUnramifiedField_inf_lubinTateLevelField_inertiaDeg
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {π : (standardLocalField K).valuationSubring}
    (hπ : (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
      (π : K))
    (d : ℕ) (hd : 0 < d) (n : ℕ) :
    let U := localFiniteUnramifiedField K d hd
    let T := standardLubinTateLevelField hπ n
    let M := U ⊓ T
    letI : FiniteDimensional K T :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : FiniteDimensional K M :=
      FiniteDimensional.of_injective
        (M.inclusion (show M ≤ U from inf_le_left)).toLinearMap
        (M.inclusion (show M ≤ U from inf_le_left)).injective
    letI : NontriviallyNormedField M :=
      finiteExtensionSpectralNormedField K M
    letI : ValuativeRel M :=
      finiteExtensionSpectralValuativeRel K M
    letI : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K M
    letI : Valuation.HasExtension (ValuativeRel.valuation K)
        (ValuativeRel.valuation M) :=
      finiteExtensionSpectralValuation_hasExtension K M
    let base := LocalFieldTheory.localCompleteDVF K
    let middle := LocalFieldTheory.localCompleteDVF M
    letI : base.valuation.HasExtension middle.valuation :=
      explicitLocalCompleteDVFValuation_hasExtension K M
    middle.maximalIdeal.inertiaDeg base.valuationSubring = 1 := by
  let U := localFiniteUnramifiedField K d hd
  let T := standardLubinTateLevelField hπ n
  let M := U ⊓ T
  let : FiniteDimensional K T :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : FiniteDimensional K M :=
    FiniteDimensional.of_injective
      (M.inclusion (show M ≤ U from inf_le_left)).toLinearMap
      (M.inclusion (show M ≤ U from inf_le_left)).injective
  let : NontriviallyNormedField T :=
    finiteExtensionSpectralNormedField K T
  let : ValuativeRel T :=
    finiteExtensionSpectralValuativeRel K T
  let : IsNonarchimedeanLocalField T :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K T
  let : Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation T) :=
    finiteExtensionSpectralValuation_hasExtension K T
  let : NontriviallyNormedField M :=
    finiteExtensionSpectralNormedField K M
  let : ValuativeRel M :=
    finiteExtensionSpectralValuativeRel K M
  let : IsNonarchimedeanLocalField M :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K M
  let : Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension K M
  let : Algebra M T :=
    (M.inclusion (show M ≤ T from inf_le_right)).toRingHom.toAlgebra
  let : IsScalarTower K M T :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Valuation.HasExtension (ValuativeRel.valuation M)
      (ValuativeRel.valuation T) :=
    finiteExtensionSpectralValuation_hasExtension_of_tower K M T
  let base := LocalFieldTheory.localCompleteDVF K
  let middle := LocalFieldTheory.localCompleteDVF M
  let total := LocalFieldTheory.localCompleteDVF T
  let : base.valuation.HasExtension middle.valuation :=
    explicitLocalCompleteDVFValuation_hasExtension K M
  let : base.valuation.HasExtension total.valuation :=
    explicitLocalCompleteDVFValuation_hasExtension K T
  let : middle.valuation.HasExtension total.valuation :=
    explicitLocalCompleteDVFValuation_hasExtension M T
  let : IsScalarTower base.valuationSubring middle.valuationSubring
      total.valuationSubring :=
    IsScalarTower.of_algebraMap_eq' rfl
  have htotal :
      total.maximalIdeal.inertiaDeg base.valuationSubring = 1 := by
    exact lubinTateLevel_spectral_inertiaDeg_eq_one K hπ n
  have hinertiaDvd :
      middle.maximalIdeal.inertiaDeg base.valuationSubring ∣
        total.maximalIdeal.inertiaDeg base.valuationSubring :=
    middle.maximalIdeal.inertiaDeg_below_dvd total.maximalIdeal
  rw [htotal] at hinertiaDvd
  exact Nat.eq_one_of_dvd_one hinertiaDvd

/-- A canonical finite unramified field and the Lubin--Tate level attached to
an explicit uniformizer have trivial intersection in the chosen separable
closure. -/
theorem localFiniteUnramifiedField_inf_lubinTateLevelField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {π : (standardLocalField K).valuationSubring}
    (hπ : (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
      (π : K))
    (d : ℕ) (hd : 0 < d) (n : ℕ) :
    localFiniteUnramifiedField K d hd ⊓
        standardLubinTateLevelField hπ n =
      ⊥ := by
  let U := localFiniteUnramifiedField K d hd
  let T := standardLubinTateLevelField hπ n
  let M := U ⊓ T
  let : FiniteDimensional K T :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : FiniteDimensional K M :=
    FiniteDimensional.of_injective
      (M.inclusion (show M ≤ U from inf_le_left)).toLinearMap
      (M.inclusion (show M ≤ U from inf_le_left)).injective
  let : NontriviallyNormedField M :=
    finiteExtensionSpectralNormedField K M
  let : ValuativeRel M :=
    finiteExtensionSpectralValuativeRel K M
  let : IsNonarchimedeanLocalField M :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K M
  let : Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension K M
  let base := LocalFieldTheory.localCompleteDVF K
  let middle := LocalFieldTheory.localCompleteDVF M
  let : base.valuation.HasExtension middle.valuation :=
    explicitLocalCompleteDVFValuation_hasExtension K M
  have hramificationMiddle :
      middle.maximalIdeal.ramificationIdx base.valuationSubring = 1 := by
    exact
      localFiniteUnramifiedField_inf_lubinTateLevelField_ramificationIdx
        K hπ d hd n
  have hinertiaMiddle :
      middle.maximalIdeal.inertiaDeg base.valuationSubring = 1 := by
    exact
      localFiniteUnramifiedField_inf_lubinTateLevelField_inertiaDeg
        K hπ d hd n
  let : Module.Finite base.valuationSubring middle.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable base middle
  let : Module.IsTorsionFree base.valuationSubring
      middle.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      base middle
  let : Module.Free base.valuationSubring middle.valuationSubring :=
    Module.free_of_finite_type_torsion_free'
  have hbaseMaximalIdeal_ne :
      (base.maximalIdeal : Ideal base.valuationSubring) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal base.valuationSubring)
      (IsDiscreteValuationRing.not_isField base.valuationSubring)
  have hdegree :=
    maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrank K M
  change
    base.maximalIdeal.ramificationIdx' middle.maximalIdeal *
        middle.maximalIdeal.inertiaDeg base.valuationSubring =
      Module.finrank K M at hdegree
  rw [Ideal.ramificationIdx'_eq_ramificationIdx
      base.maximalIdeal middle.maximalIdeal hbaseMaximalIdeal_ne,
    hramificationMiddle, hinertiaMiddle, one_mul] at hdegree
  change M = ⊥
  exact IntermediateField.finrank_eq_one_iff.mp hdegree.symm

/-- A canonical finite unramified field is linearly disjoint from the finite
Lubin--Tate level attached to an explicit uniformizer. -/
theorem localFiniteUnramifiedField_linearDisjoint_lubinTateLevelField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {π : (standardLocalField K).valuationSubring}
    (hπ : (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
      (π : K))
    (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (localFiniteUnramifiedField K d hd).LinearDisjoint
      (standardLubinTateLevelField hπ n) := by
  let : FiniteDimensional K (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelField_finiteDimensional hπ n
  apply IntermediateField.LinearDisjoint.of_inf_eq_bot
  exact localFiniteUnramifiedField_inf_lubinTateLevelField
    K hπ d hd n

/-- The compositum on which arithmetic Frobenius and the inverse unit action
for an explicit uniformizer are combined.  The unramified degree is exactly
the order of the unit action. -/
abbrev lubinTateUniformizerDiagonalCompositumField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {π : (standardLocalField K).valuationSubring}
    (hπ : (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
      (π : K))
    (n : ℕ) (u : (standardLocalField K).valuationSubringˣ) :
    IntermediateField K (SeparableClosure K) :=
  let T := standardLubinTateLevelField hπ n
  letI : FiniteDimensional K T :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let σ : Gal(T/K) :=
    (standardLubinTateUnitParameterEquivGal
      (standardLocalField K) hπ n
      (standardLubinTateUnitParameterClass
        (standardLocalField K) n u))⁻¹
  let d := orderOf σ
  localFiniteUnramifiedField K d (orderOf_pos σ) ⊔ T

/-- The explicit-uniformizer diagonal compositum is finite over the base
field. -/
theorem lubinTateUniformizerDiagonalCompositumField_finiteDimensional
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {π : (standardLocalField K).valuationSubring}
    (hπ : (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
      (π : K))
    (n : ℕ) (u : (standardLocalField K).valuationSubringˣ) :
    FiniteDimensional K
      (lubinTateUniformizerDiagonalCompositumField K hπ n u) := by
  let T := standardLubinTateLevelField hπ n
  let : FiniteDimensional K T :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let σ : Gal(T/K) :=
    (standardLubinTateUnitParameterEquivGal
      (standardLocalField K) hπ n
      (standardLubinTateUnitParameterClass
        (standardLocalField K) n u))⁻¹
  let d := orderOf σ
  let hd : 0 < d := orderOf_pos σ
  let U := localFiniteUnramifiedField K d hd
  let C := U ⊔ T
  change FiniteDimensional K C
  exact U.finiteDimensional_sup T

/-- The explicit-uniformizer diagonal compositum is Galois over the base
field. -/
theorem lubinTateUniformizerDiagonalCompositumField_isGalois
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {π : (standardLocalField K).valuationSubring}
    (hπ : (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
      (π : K))
    (n : ℕ) (u : (standardLocalField K).valuationSubringˣ) :
    IsGalois K
      (lubinTateUniformizerDiagonalCompositumField K hπ n u) := by
  let T := standardLubinTateLevelField hπ n
  let : FiniteDimensional K T :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let σ : Gal(T/K) :=
    (standardLubinTateUnitParameterEquivGal
      (standardLocalField K) hπ n
      (standardLubinTateUnitParameterClass
        (standardLocalField K) n u))⁻¹
  let d := orderOf σ
  let hd : 0 < d := orderOf_pos σ
  let U := localFiniteUnramifiedField K d hd
  let C := U ⊔ T
  let : IsGalois K U := inferInstance
  let : IsGalois K T :=
    standardLubinTateLevelField_isGalois
      (F := standardLocalField K) hπ n
  let : Algebra.IsSeparable K C := inferInstance
  change IsGalois K C
  exact
    { to_isSeparable := inferInstance
      to_normal := inferInstance }

private theorem explicitRestrictNormalHom_toAlgAut_eq_one
    (K C : Type) [Field K] [Field C] [Algebra K C]
    (B : IntermediateField K C) [Normal K B]
    (δ : Gal(C/B)) :
    AlgEquiv.restrictNormalHom B
        (MulSemiringAction.toAlgAut Gal(C/B) K C δ) =
      1 := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  rw [AlgEquiv.restrictNormalHom_apply]
  exact δ.commutes x

private theorem explicitRestrictNormalHom_mul_inv_eq_one
    (K C : Type) [Field K] [Field C] [Algebra K C]
    (A : IntermediateField K C) [Normal K A]
    (σ τ : Gal(C/K)) (ρ : Gal(A/K))
    (hσ : AlgEquiv.restrictNormalHom A σ = ρ)
    (hτ : AlgEquiv.restrictNormalHom A τ = ρ) :
    AlgEquiv.restrictNormalHom A (σ * τ⁻¹) = 1 := by
  rw [map_mul_inv, hσ, hτ, mul_inv_cancel]

private theorem explicit_mem_fixingSubgroup_of_restrictNormalHom_eq_one
    (K C : Type) [Field K] [Field C] [Algebra K C]
    (A : IntermediateField K C) [Normal K A]
    (σ : Gal(C/K))
    (hσ : AlgEquiv.restrictNormalHom A σ = 1) :
    σ ∈ A.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let y : A := ⟨x, hx⟩
  have hy := congrArg (fun τ : Gal(A/K) => τ y) hσ
  have hyval := congrArg Subtype.val hy
  rw [AlgEquiv.restrictNormalHom_apply] at hyval
  simpa [y] using hyval

private theorem explicit_eq_one_of_mem_fixingSubgroup_of_sup_eq_top
    (K C : Type) [Field K] [Field C] [Algebra K C]
    (A B : IntermediateField K C) (σ : Gal(C/K))
    (hA : σ ∈ A.fixingSubgroup) (hB : σ ∈ B.fixingSubgroup)
    (hSup : A ⊔ B = ⊤) :
    σ = 1 := by
  have hFixSup : σ ∈ (A ⊔ B).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hA, hB⟩
  rw [hSup, IntermediateField.fixingSubgroup_top] at hFixSup
  exact Subgroup.mem_bot.mp hFixSup

private theorem explicitAlgEquiv_eq_of_restrict_eq_of_sup_eq_top
    (K C : Type) [Field K] [Field C] [Algebra K C]
    (A B : IntermediateField K C) [Normal K A] [Normal K B]
    (σ τ : Gal(C/K))
    (hA : AlgEquiv.restrictNormalHom A σ =
      AlgEquiv.restrictNormalHom A τ)
    (hB : AlgEquiv.restrictNormalHom B σ =
      AlgEquiv.restrictNormalHom B τ)
    (hSup : A ⊔ B = ⊤) :
    σ = τ := by
  let δ := σ * τ⁻¹
  have hδA : AlgEquiv.restrictNormalHom A δ = 1 := by
    exact explicitRestrictNormalHom_mul_inv_eq_one
      K C A σ τ (AlgEquiv.restrictNormalHom A σ) rfl hA.symm
  have hδB : AlgEquiv.restrictNormalHom B δ = 1 := by
    exact explicitRestrictNormalHom_mul_inv_eq_one
      K C B σ τ (AlgEquiv.restrictNormalHom B σ) rfl hB.symm
  have hFixA : δ ∈ A.fixingSubgroup :=
    explicit_mem_fixingSubgroup_of_restrictNormalHom_eq_one
      K C A δ hδA
  have hFixB : δ ∈ B.fixingSubgroup :=
    explicit_mem_fixingSubgroup_of_restrictNormalHom_eq_one
      K C B δ hδB
  have hδ : δ = 1 :=
    explicit_eq_one_of_mem_fixingSubgroup_of_sup_eq_top
      K C A B δ hFixA hFixB hSup
  exact mul_inv_eq_one.mp hδ

private theorem explicit_orderOf_eq_of_restrict_orders_of_sup_eq_top
    (K C : Type) [Field K] [Field C] [Algebra K C]
    (A B : IntermediateField K C) [Normal K A] [Normal K B]
    [Finite (Gal(A/K))] [Finite (Gal(B/K))]
    (σ : Gal(C/K)) (σA : Gal(A/K)) (σB : Gal(B/K)) (d : ℕ)
    (hA : AlgEquiv.restrictNormalHom A σ = σA)
    (hB : AlgEquiv.restrictNormalHom B σ = σB)
    (hAOrder : orderOf σA = d) (hBOrder : orderOf σB = d)
    (hSup : A ⊔ B = ⊤) :
    orderOf σ = d := by
  have hLower : d ∣ orderOf σ := by
    rw [← hAOrder, ← hA]
    exact orderOf_map_dvd (AlgEquiv.restrictNormalHom A) σ
  have hPowA :
      AlgEquiv.restrictNormalHom A (σ ^ d) = 1 := by
    rw [map_pow, hA, ← hAOrder, pow_orderOf_eq_one]
  have hPowB :
      AlgEquiv.restrictNormalHom B (σ ^ d) = 1 := by
    rw [map_pow, hB, ← hBOrder, pow_orderOf_eq_one]
  have hFixA : σ ^ d ∈ A.fixingSubgroup :=
    explicit_mem_fixingSubgroup_of_restrictNormalHom_eq_one
      K C A (σ ^ d) hPowA
  have hFixB : σ ^ d ∈ B.fixingSubgroup :=
    explicit_mem_fixingSubgroup_of_restrictNormalHom_eq_one
      K C B (σ ^ d) hPowB
  have hPow : σ ^ d = 1 :=
    explicit_eq_one_of_mem_fixingSubgroup_of_sup_eq_top
      K C A B (σ ^ d) hFixA hFixB hSup
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hPow) hLower

private theorem exists_explicitAlgEquiv_with_disjoint_restrictions
    (K C : Type) [Field K] [Field C] [Algebra K C]
    (A B : IntermediateField K C)
    [Normal K A] [Normal K B] [Normal K C]
    [FiniteDimensional K A] [FiniteDimensional B C] [IsGalois B C]
    (hInf : A ⊓ B = ⊥) (σA : Gal(A/K)) (σB : Gal(B/K)) :
    ∃ σ : Gal(C/K),
      AlgEquiv.restrictNormalHom A σ = σA ∧
        AlgEquiv.restrictNormalHom B σ = σB := by
  obtain ⟨σ₀, hσ₀⟩ :=
    (AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := B) (E := C)) σB
  let error : Gal(A/K) :=
    σA * (AlgEquiv.restrictNormalHom A σ₀)⁻¹
  obtain ⟨δ, hδ⟩ :=
    (IntermediateField.restrictRestrictAlgEquivMapHom_surjective
      (F := K) (E := C) A B hInf) error
  let δK : Gal(C/K) :=
    MulSemiringAction.toAlgAut Gal(C/B) K C δ
  have hδA : AlgEquiv.restrictNormalHom A δK = error := by
    change AlgEquiv.restrictNormalHom A δK = error at hδ
    exact hδ
  have hδB : AlgEquiv.restrictNormalHom B δK = 1 :=
    explicitRestrictNormalHom_toAlgAut_eq_one K C B δ
  refine ⟨δK * σ₀, ?_, ?_⟩
  · rw [map_mul, hδA]
    simp [error]
  · rw [map_mul, hδB, hσ₀, one_mul]

private theorem exists_lubinTateUniformizerDiagonalAutomorphism
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {π : (standardLocalField K).valuationSubring}
    (hπ : (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
      (π : K))
    (n : ℕ) (u : (standardLocalField K).valuationSubringˣ) :
    let T := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K T :=
      standardLubinTateLevelField_finiteDimensional hπ n
    let σT : Gal(T/K) :=
      (standardLubinTateUnitParameterEquivGal
        (standardLocalField K) hπ n
        (standardLubinTateUnitParameterClass
          (standardLocalField K) n u))⁻¹
    let d := orderOf σT
    let hd : 0 < d := orderOf_pos σT
    let U := localFiniteUnramifiedField K d hd
    let C := U ⊔ T
    let hUC : U ≤ C := le_sup_left
    let hTC : T ≤ C := le_sup_right
    let A := U.restrict hUC
    let B := T.restrict hTC
    let eU : U ≃ₐ[K] A := IntermediateField.restrictAlgEquiv hUC
    let eT : T ≃ₐ[K] B := IntermediateField.restrictAlgEquiv hTC
    letI : IsGalois K A := IsGalois.of_algEquiv eU
    letI : IsGalois K B := IsGalois.of_algEquiv eT
    let φ :=
      arithmeticFrobeniusOfUnramifiedValuation K U
    let σA : Gal(A/K) := (eU.symm.trans φ).trans eU
    let σB : Gal(B/K) := (eT.symm.trans σT).trans eT
    ∃ σ : Gal(C/K),
      AlgEquiv.restrictNormalHom A σ = σA ∧
        AlgEquiv.restrictNormalHom B σ = σB := by
  let T := standardLubinTateLevelField hπ n
  let : FiniteDimensional K T :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let σT : Gal(T/K) :=
    (standardLubinTateUnitParameterEquivGal
      (standardLocalField K) hπ n
      (standardLubinTateUnitParameterClass
        (standardLocalField K) n u))⁻¹
  let d := orderOf σT
  let hd : 0 < d := orderOf_pos σT
  let U := localFiniteUnramifiedField K d hd
  let C := U ⊔ T
  let hUC : U ≤ C := le_sup_left
  let hTC : T ≤ C := le_sup_right
  let A := U.restrict hUC
  let B := T.restrict hTC
  let eU : U ≃ₐ[K] A := IntermediateField.restrictAlgEquiv hUC
  let eT : T ≃ₐ[K] B := IntermediateField.restrictAlgEquiv hTC
  let : IsGalois K U := inferInstance
  let : IsGalois K T :=
    standardLubinTateLevelField_isGalois
      (F := standardLocalField K) hπ n
  let : IsGalois K A := IsGalois.of_algEquiv eU
  let : IsGalois K B := IsGalois.of_algEquiv eT
  let : FiniteDimensional K C :=
    lubinTateUniformizerDiagonalCompositumField_finiteDimensional
      K hπ n u
  let : IsGalois K C :=
    lubinTateUniformizerDiagonalCompositumField_isGalois
      K hπ n u
  let : FiniteDimensional B C :=
    FiniteDimensional.right K B C
  let : IsGalois B C :=
    IsGalois.tower_top_of_isGalois K B C
  let φ :=
    arithmeticFrobeniusOfUnramifiedValuation K U
  let σA : Gal(A/K) := (eU.symm.trans φ).trans eU
  let σB : Gal(B/K) := (eT.symm.trans σT).trans eT
  have hInf : U ⊓ T = ⊥ :=
    localFiniteUnramifiedField_inf_lubinTateLevelField
      K hπ d hd n
  have hInf' : A ⊓ B = ⊥ := by
    rw [← IntermediateField.lift_inj,
      IntermediateField.lift_bot,
      IntermediateField.lift_inf,
      IntermediateField.lift_restrict hUC,
      IntermediateField.lift_restrict hTC,
      hInf]
  exact exists_explicitAlgEquiv_with_disjoint_restrictions
    K C A B hInf' σA σB

/-- The diagonal automorphism whose restriction to the unramified factor is
arithmetic Frobenius and whose restriction to the explicit-uniformizer
Lubin--Tate level is the inverse unit action. -/
noncomputable def lubinTateUniformizerDiagonalAutomorphism
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {π : (standardLocalField K).valuationSubring}
    (hπ : (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
      (π : K))
    (n : ℕ) (u : (standardLocalField K).valuationSubringˣ) :
    Gal((lubinTateUniformizerDiagonalCompositumField K hπ n u)/K) :=
  Classical.choose
    (exists_lubinTateUniformizerDiagonalAutomorphism K hπ n u)

/-- The explicit-uniformizer diagonal automorphism restricts to arithmetic
Frobenius on its unramified factor. -/
theorem lubinTateUniformizerDiagonalAutomorphism_restrict_unramified
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {π : (standardLocalField K).valuationSubring}
    (hπ : (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
      (π : K))
    (n : ℕ) (u : (standardLocalField K).valuationSubringˣ) :
    let T := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K T :=
      standardLubinTateLevelField_finiteDimensional hπ n
    let σT : Gal(T/K) :=
      (standardLubinTateUnitParameterEquivGal
        (standardLocalField K) hπ n
        (standardLubinTateUnitParameterClass
          (standardLocalField K) n u))⁻¹
    let d := orderOf σT
    let hd : 0 < d := orderOf_pos σT
    let U := localFiniteUnramifiedField K d hd
    let C := U ⊔ T
    let hUC : U ≤ C := le_sup_left
    let A := U.restrict hUC
    let eU : U ≃ₐ[K] A := IntermediateField.restrictAlgEquiv hUC
    letI : IsGalois K A := IsGalois.of_algEquiv eU
    let φA : Gal(A/K) :=
      (eU.symm.trans
        (arithmeticFrobeniusOfUnramifiedValuation K U)).trans eU
    AlgEquiv.restrictNormalHom A
        (lubinTateUniformizerDiagonalAutomorphism K hπ n u) =
      φA :=
  (Classical.choose_spec
    (exists_lubinTateUniformizerDiagonalAutomorphism K hπ n u)).1

/-- The explicit-uniformizer diagonal automorphism restricts to the inverse
finite Lubin--Tate unit action on its ramified level. -/
theorem lubinTateUniformizerDiagonalAutomorphism_restrict_level
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {π : (standardLocalField K).valuationSubring}
    (hπ : (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
      (π : K))
    (n : ℕ) (u : (standardLocalField K).valuationSubringˣ) :
    let T := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K T :=
      standardLubinTateLevelField_finiteDimensional hπ n
    let σT : Gal(T/K) :=
      (standardLubinTateUnitParameterEquivGal
        (standardLocalField K) hπ n
        (standardLubinTateUnitParameterClass
          (standardLocalField K) n u))⁻¹
    let d := orderOf σT
    let hd : 0 < d := orderOf_pos σT
    let U := localFiniteUnramifiedField K d hd
    let C := U ⊔ T
    let hTC : T ≤ C := le_sup_right
    let B := T.restrict hTC
    let eT : T ≃ₐ[K] B := IntermediateField.restrictAlgEquiv hTC
    letI : IsGalois K B := IsGalois.of_algEquiv eT
    let σB : Gal(B/K) := (eT.symm.trans σT).trans eT
    AlgEquiv.restrictNormalHom B
        (lubinTateUniformizerDiagonalAutomorphism K hπ n u) =
      σB :=
  (Classical.choose_spec
    (exists_lubinTateUniformizerDiagonalAutomorphism K hπ n u)).2

/-- The two factor restrictions uniquely determine the diagonal automorphism. -/
theorem lubinTateUniformizerDiagonalAutomorphism_unique
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {π : (standardLocalField K).valuationSubring}
    (hπ : (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
      (π : K))
    (n : ℕ) (u : (standardLocalField K).valuationSubringˣ)
    (σ : Gal((lubinTateUniformizerDiagonalCompositumField K hπ n u)/K))
    (hσUnramified :
      let T := standardLubinTateLevelField hπ n
      letI : FiniteDimensional K T :=
        standardLubinTateLevelField_finiteDimensional hπ n
      let σT : Gal(T/K) :=
        (standardLubinTateUnitParameterEquivGal
          (standardLocalField K) hπ n
          (standardLubinTateUnitParameterClass
            (standardLocalField K) n u))⁻¹
      let d := orderOf σT
      let hd : 0 < d := orderOf_pos σT
      let U := localFiniteUnramifiedField K d hd
      let C := U ⊔ T
      let hUC : U ≤ C := le_sup_left
      let A := U.restrict hUC
      let eU : U ≃ₐ[K] A := IntermediateField.restrictAlgEquiv hUC
      letI : IsGalois K A := IsGalois.of_algEquiv eU
      let φA : Gal(A/K) :=
        (eU.symm.trans
          (arithmeticFrobeniusOfUnramifiedValuation K U)).trans eU
      AlgEquiv.restrictNormalHom A σ = φA)
    (hσLevel :
      let T := standardLubinTateLevelField hπ n
      letI : FiniteDimensional K T :=
        standardLubinTateLevelField_finiteDimensional hπ n
      let σT : Gal(T/K) :=
        (standardLubinTateUnitParameterEquivGal
          (standardLocalField K) hπ n
          (standardLubinTateUnitParameterClass
            (standardLocalField K) n u))⁻¹
      let d := orderOf σT
      let hd : 0 < d := orderOf_pos σT
      let U := localFiniteUnramifiedField K d hd
      let C := U ⊔ T
      let hTC : T ≤ C := le_sup_right
      let B := T.restrict hTC
      let eT : T ≃ₐ[K] B := IntermediateField.restrictAlgEquiv hTC
      letI : IsGalois K B := IsGalois.of_algEquiv eT
      let σB : Gal(B/K) := (eT.symm.trans σT).trans eT
      AlgEquiv.restrictNormalHom B σ = σB) :
    σ = lubinTateUniformizerDiagonalAutomorphism K hπ n u := by
  let T := standardLubinTateLevelField hπ n
  let : FiniteDimensional K T :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let σT : Gal(T/K) :=
    (standardLubinTateUnitParameterEquivGal
      (standardLocalField K) hπ n
      (standardLubinTateUnitParameterClass
        (standardLocalField K) n u))⁻¹
  let d := orderOf σT
  let hd : 0 < d := orderOf_pos σT
  let U := localFiniteUnramifiedField K d hd
  let C := U ⊔ T
  let hUC : U ≤ C := le_sup_left
  let hTC : T ≤ C := le_sup_right
  let A := U.restrict hUC
  let B := T.restrict hTC
  let eU : U ≃ₐ[K] A := IntermediateField.restrictAlgEquiv hUC
  let eT : T ≃ₐ[K] B := IntermediateField.restrictAlgEquiv hTC
  let : IsGalois K A := IsGalois.of_algEquiv eU
  let : IsGalois K B := IsGalois.of_algEquiv eT
  let φA : Gal(A/K) :=
    (eU.symm.trans
      (arithmeticFrobeniusOfUnramifiedValuation K U)).trans eU
  let σB : Gal(B/K) := (eT.symm.trans σT).trans eT
  let chosen := lubinTateUniformizerDiagonalAutomorphism K hπ n u
  have hσA : AlgEquiv.restrictNormalHom A σ = φA := by
    change AlgEquiv.restrictNormalHom A σ = φA at hσUnramified
    exact hσUnramified
  have hσB : AlgEquiv.restrictNormalHom B σ = σB := by
    change AlgEquiv.restrictNormalHom B σ = σB at hσLevel
    exact hσLevel
  have hchosenA : AlgEquiv.restrictNormalHom A chosen = φA := by
    have h :=
      lubinTateUniformizerDiagonalAutomorphism_restrict_unramified K hπ n u
    change AlgEquiv.restrictNormalHom A chosen = φA at h
    exact h
  have hchosenB : AlgEquiv.restrictNormalHom B chosen = σB := by
    have h := lubinTateUniformizerDiagonalAutomorphism_restrict_level K hπ n u
    change AlgEquiv.restrictNormalHom B chosen = σB at h
    exact h
  have hSup : A ⊔ B = ⊤ := by
    rw [← IntermediateField.lift_inj,
      IntermediateField.lift_top,
      IntermediateField.lift_sup,
      IntermediateField.lift_restrict hUC,
      IntermediateField.lift_restrict hTC]
  exact explicitAlgEquiv_eq_of_restrict_eq_of_sup_eq_top
    K C A B σ chosen (hσA.trans hchosenA.symm)
      (hσB.trans hchosenB.symm) hSup

private theorem lubinTateUniformizerDiagonalAutomorphism_order
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {π : (standardLocalField K).valuationSubring}
    (hπ : (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
      (π : K))
    (n : ℕ) (u : (standardLocalField K).valuationSubringˣ) :
    let T := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K T :=
      standardLubinTateLevelField_finiteDimensional hπ n
    let σT : Gal(T/K) :=
      (standardLubinTateUnitParameterEquivGal
        (standardLocalField K) hπ n
        (standardLubinTateUnitParameterClass
          (standardLocalField K) n u))⁻¹
    orderOf (lubinTateUniformizerDiagonalAutomorphism K hπ n u) =
      orderOf σT := by
  let T := standardLubinTateLevelField hπ n
  let : FiniteDimensional K T :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let σT : Gal(T/K) :=
    (standardLubinTateUnitParameterEquivGal
      (standardLocalField K) hπ n
      (standardLubinTateUnitParameterClass
        (standardLocalField K) n u))⁻¹
  let d := orderOf σT
  let hd : 0 < d := orderOf_pos σT
  let U := localFiniteUnramifiedField K d hd
  let C := U ⊔ T
  let hUC : U ≤ C := le_sup_left
  let hTC : T ≤ C := le_sup_right
  let A := U.restrict hUC
  let B := T.restrict hTC
  let eU : U ≃ₐ[K] A := IntermediateField.restrictAlgEquiv hUC
  let eT : T ≃ₐ[K] B := IntermediateField.restrictAlgEquiv hTC
  let : IsGalois K U := inferInstance
  let : IsGalois K T :=
    standardLubinTateLevelField_isGalois
      (F := standardLocalField K) hπ n
  let : IsGalois K A := IsGalois.of_algEquiv eU
  let : IsGalois K B := IsGalois.of_algEquiv eT
  let φ :=
    arithmeticFrobeniusOfUnramifiedValuation K U
  let σA : Gal(A/K) := (eU.symm.trans φ).trans eU
  let σB : Gal(B/K) := (eT.symm.trans σT).trans eT
  let σ := lubinTateUniformizerDiagonalAutomorphism K hπ n u
  let transportU : Gal(U/K) ≃* Gal(A/K) :=
    { AlgEquiv.equivCongr eU eU with
      map_mul' := by
        intro g h
        ext x
        simp }
  let transportT : Gal(T/K) ≃* Gal(B/K) :=
    { AlgEquiv.equivCongr eT eT with
      map_mul' := by
        intro g h
        ext x
        simp }
  have hσAOrder : orderOf σA = d := by
    rw [show σA = transportU φ by rfl, transportU.orderOf_eq,
      localFiniteUnramifiedField_arithmeticFrobenius_order K d hd]
  have hσBOrder : orderOf σB = d := by
    rw [show σB = transportT σT by rfl, transportT.orderOf_eq]
  have hrestrictA :
      AlgEquiv.restrictNormalHom A σ = σA := by
    have h :=
      lubinTateUniformizerDiagonalAutomorphism_restrict_unramified K hπ n u
    change AlgEquiv.restrictNormalHom A σ = σA at h
    exact h
  have hrestrictB :
      AlgEquiv.restrictNormalHom B σ = σB := by
    have h := lubinTateUniformizerDiagonalAutomorphism_restrict_level K hπ n u
    change AlgEquiv.restrictNormalHom B σ = σB at h
    exact h
  have hSup : A ⊔ B = ⊤ := by
    rw [← IntermediateField.lift_inj,
      IntermediateField.lift_top,
      IntermediateField.lift_sup,
      IntermediateField.lift_restrict hUC,
      IntermediateField.lift_restrict hTC]
  exact explicit_orderOf_eq_of_restrict_orders_of_sup_eq_top
    K C A B σ σA σB d hrestrictA hrestrictB hσAOrder hσBOrder hSup

/-- The field fixed by the explicit-uniformizer diagonal automorphism. -/
def lubinTateUniformizerDiagonalFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {π : (standardLocalField K).valuationSubring}
    (hπ : (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
      (π : K))
    (n : ℕ) (u : (standardLocalField K).valuationSubringˣ) :
    IntermediateField K
      (lubinTateUniformizerDiagonalCompositumField K hπ n u) :=
  IntermediateField.fixedField
    (Subgroup.zpowers
      (lubinTateUniformizerDiagonalAutomorphism K hπ n u))

/-- Diagonal fixed points remove the auxiliary unramified factor: the
fixed field has exactly the degree of the explicit-uniformizer Lubin--Tate
level. -/
theorem lubinTateUniformizerDiagonalFixedField_finrank
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {π : (standardLocalField K).valuationSubring}
    (hπ : (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
      (π : K))
    (n : ℕ) (u : (standardLocalField K).valuationSubringˣ) :
    Module.finrank K
        (lubinTateUniformizerDiagonalFixedField K hπ n u) =
      Module.finrank K (standardLubinTateLevelField hπ n) := by
  let T := standardLubinTateLevelField hπ n
  let : FiniteDimensional K T :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let σT : Gal(T/K) :=
    (standardLubinTateUnitParameterEquivGal
      (standardLocalField K) hπ n
      (standardLubinTateUnitParameterClass
        (standardLocalField K) n u))⁻¹
  let d := orderOf σT
  let hd : 0 < d := orderOf_pos σT
  let U := localFiniteUnramifiedField K d hd
  let C := U ⊔ T
  let σ := lubinTateUniformizerDiagonalAutomorphism K hπ n u
  let E := lubinTateUniformizerDiagonalFixedField K hπ n u
  let : FiniteDimensional K C :=
    lubinTateUniformizerDiagonalCompositumField_finiteDimensional
      K hπ n u
  let : FiniteDimensional E C :=
    FiniteDimensional.right K E C
  let : Module.Free E C := Module.Free.of_divisionRing E C
  have hEC : Module.finrank E C = d := by
    change Module.finrank
      (IntermediateField.fixedField (Subgroup.zpowers σ)) C = d
    rw [IntermediateField.finrank_fixedField_eq_card,
      Nat.card_zpowers]
    simpa [T, σT, d, C, σ] using
      lubinTateUniformizerDiagonalAutomorphism_order K hπ n u
  have hKC :
      Module.finrank K C = d * Module.finrank K T := by
    rw [show C = U ⊔ T by rfl,
      (localFiniteUnramifiedField_linearDisjoint_lubinTateLevelField
        K hπ d hd n).finrank_sup,
      localFiniteUnramifiedField_finrank K d hd]
  have hTower := Module.finrank_mul_finrank K E C
  rw [hEC, hKC] at hTower
  apply Nat.eq_of_mul_eq_mul_right hd
  exact hTower.trans (Nat.mul_comm d (Module.finrank K T))

end LocalClassFieldTheory

end
