/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.GroupTheory.Abelianization.Defs
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Conductor
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison
/-!
# Conductors and unramified extensions

For an unramified finite abelian extension, normalized valuation identifies
the norm subgroup and shows that all base-field units are norms. Hence its
conductor ideal is `1`.

Conversely, conductor one identifies the norm quotient order with the residue
degree. Finite local reciprocity and the degree formula then force the
ramification index to be one.
-/

@[expose] public section

noncomputable
section

namespace LocalClassFieldTheory

open scoped ValuativeRel IsMulCommutative
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

private theorem normQuotientFiniteOfIsAbelianGalois
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] :
    Finite (NormQuotient K L) := by
  exact Finite.of_equiv Gal(L/K)
    ((Abelianization.equivOfComm (H := Gal(L/K))).trans
      (abelianizationEquivNormQuotient K L)).toEquiv

/-- If every base integer unit is a norm, the actual norm quotient is the
cyclic quotient of the normalized value group by the residue degree.

This value-group comparison uses the separable norm-valuation formula for its
residue degree; no unramifiedness assumption is made here. -/
noncomputable def
    chosenNormQuotientEquivZModResidueFinrankOfFieldPrincipalUnitsZeroLe
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (hU : LocalFieldTheory.fieldPrincipalUnits K 0 ≤ localNormSubgroup K L) :
    NormQuotient K L ≃*
      Multiplicative
        (ZMod
          (@Module.finrank 𝓀[K] 𝓀[L] _ _
            (IsLocalRing.ResidueField.instModule
              (R := 𝒪[K])
              (S := 𝒪[L])))) := by
  let vK := multiplicativeIntegerValuation K
  let vL := multiplicativeIntegerValuation L
  let ϖK := Classical.choose (multiplicativeIntegerValuation_exists_uniformizer K)
  have hϖK := Classical.choose_spec (multiplicativeIntegerValuation_exists_uniformizer K)
  let ϖL := Classical.choose (multiplicativeIntegerValuation_exists_uniformizer L)
  have hϖL := Classical.choose_spec (multiplicativeIntegerValuation_exists_uniformizer L)
  have hformula :
      ∀ x : Lˣ,
        vK.val (LocalFieldTheory.normUnits K L x) =
          (@Module.finrank 𝓀[K] 𝓀[L] _ _
            (IsLocalRing.ResidueField.instModule
              (R := 𝒪[K])
              (S := 𝒪[L])) : ℤ) * vL.val x := by
    intro x
    simpa [vK, vL, multiplicativeIntegerValuation] using
      (v_normUnits_eq_residue_finrank_mul_of_isGalois K L x)
  have hzero :
      vK.zeroSubgroup ≤ LocalFieldTheory.DiscreteValuationField.fieldNormSubgroup K L := by
    intro x hx
    have hxval : valuationMap K (Additive.ofMul x) = 0 := by
      change vK.val x = 0 at hx
      simpa [vK, multiplicativeIntegerValuation,
        valuationMap_apply] using hx
    obtain ⟨u, hu⟩ :=
      (integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero K x).2 hxval
    have hxU : x ∈ LocalFieldTheory.fieldPrincipalUnits K 0 := by
      rw [← hu]
      exact ⟨u, by simp, rfl⟩
    have hxnorm := hU hxU
    simpa [LocalFieldTheory.DiscreteValuationField.fieldNormSubgroup,
      localNormSubgroup] using hxnorm
  have hsub : localNormSubgroup K L =
      LocalFieldTheory.DiscreteValuationField.fieldNormSubgroup K L := by
    rfl
  exact (normQuotientEquivOfSubgroupEq K L
      (LocalFieldTheory.DiscreteValuationField.fieldNormSubgroup K L) hsub).trans
    (LocalFieldTheory.DiscreteValuationField.fieldNormQuotientEquivZMod
      K L vK vL
        (@Module.finrank 𝓀[K] 𝓀[L] _ _
          (IsLocalRing.ResidueField.instModule
            (R := 𝒪[K])
            (S := 𝒪[L])))
        hformula hϖK hϖL hzero)

/-- Finite local reciprocity gives the order of the norm quotient in a finite
abelian extension: it is the field degree. -/
theorem card_normQuotient_eq_finrank_of_isAbelianGalois
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] :
    letI : Finite (NormQuotient K L) :=
      by exact normQuotientFiniteOfIsAbelianGalois K L
    Nat.card (NormQuotient K L) = Module.finrank K L := by
  let : Finite (NormQuotient K L) :=
    normQuotientFiniteOfIsAbelianGalois K L
  let : Finite (Abelianization Gal(L/K)) :=
    Finite.of_equiv Gal(L/K)
      (Abelianization.equivOfComm (H := Gal(L/K))).toEquiv
  calc
    Nat.card (NormQuotient K L) =
        Nat.card (Abelianization Gal(L/K)) :=
      Nat.card_congr (abelianizationEquivNormQuotient K L).toEquiv.symm
    _ = Nat.card Gal(L/K) :=
      Nat.card_congr (Abelianization.equivOfComm
        (H := Gal(L/K))).toEquiv.symm
    _ = Module.finrank K L := galoisGroup_card_eq_finrank K L

/-- In an actual finite unramified abelian extension, every base-field
integer unit lies in the field-norm subgroup. -/
theorem fieldPrincipalUnits_zero_le_normSubgroup_of_unramifiedValuation
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    LocalFieldTheory.fieldPrincipalUnits K 0 ≤ localNormSubgroup K L := by
  rw [normSubgroup_eq_unramifiedNormSubgroup_of_isIntegralClosure K L]
  rintro x ⟨u, _hu, rfl⟩
  apply (mem_unramifiedNormSubgroup_iff K (Module.finrank K L) _).2
  rw [valuationMap_apply, v_integerUnitsToFieldUnits]
  exact dvd_zero _

/-- An unramified finite abelian extension has conductor exponent zero. -/
theorem localConductorExponent_eq_zero_of_unramifiedValuation
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    localConductorExponent K L = 0 := by
  exact (localConductorExponent_eq_zero_iff K L).2
    (fieldPrincipalUnits_zero_le_normSubgroup_of_unramifiedValuation K L)

/-- An unramified finite abelian extension has conductor ideal `1`. -/
theorem localConductorIdeal_eq_one_of_unramifiedValuation
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    localConductorIdeal K L = 1 := by
  exact (localConductorIdeal_eq_one_iff_exponent_eq_zero K L).2
    (localConductorExponent_eq_zero_of_unramifiedValuation K L)

/-- A finite abelian extension whose conductor ideal is `1` is unramified.

The proof compares two computations of the actual norm quotient.  Its order
is the residue degree by the norm-valuation formula and the conductor-one
unit inclusion, while finite local reciprocity gives the field degree.
Cancelling the positive residue degree gives ramification index one. -/
theorem isFiniteUnramifiedValuationExtension_of_localConductorIdeal_eq_one
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    (hcond : localConductorIdeal K L = 1) :
    LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L := by
  have hU : LocalFieldTheory.fieldPrincipalUnits K 0 ≤ localNormSubgroup K L :=
    (localConductorIdeal_eq_one_iff K L).1 hcond
  let hequiv :=
    chosenNormQuotientEquivZModResidueFinrankOfFieldPrincipalUnitsZeroLe
      K L hU
  let : Finite (NormQuotient K L) :=
    normQuotientFiniteOfIsAbelianGalois K L
  have hcardResidue :
      Nat.card (NormQuotient K L) =
        @Module.finrank 𝓀[K] 𝓀[L] _ _
          (IsLocalRing.ResidueField.instModule
            (R := 𝒪[K])
            (S := 𝒪[L])) := by
    rw [Nat.card_congr hequiv.toEquiv]
    exact Nat.card_zmod
      (@Module.finrank 𝓀[K] 𝓀[L] _ _
        (IsLocalRing.ResidueField.instModule
          (R := 𝒪[K])
          (S := 𝒪[L])))
  have hcardDegree :
      Nat.card (NormQuotient K L) = Module.finrank K L :=
    card_normQuotient_eq_finrank_of_isAbelianGalois K L
  have hDegreeEqResidue :
      Module.finrank K L =
        @Module.finrank 𝓀[K] 𝓀[L] _ _
          (IsLocalRing.ResidueField.instModule
            (R := 𝒪[K])
            (S := 𝒪[L])) :=
    hcardDegree.symm.trans hcardResidue
  have hdegree :=
    maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank_of_isIntegralClosure
      K L
  have hp : (𝓂[K] : Ideal 𝒪[K]) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal 𝒪[K])
      (IsDiscreteValuationRing.not_isField 𝒪[K])
  have hdegreeNew :
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] *
          @Module.finrank 𝓀[K] 𝓀[L] _ _
            (IsLocalRing.ResidueField.instModule
              (R := 𝒪[K])
              (S := 𝒪[L])) =
        Module.finrank K L := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp]
    exact hdegree
  have hfpos :
      0 < @Module.finrank 𝓀[K] 𝓀[L] _ _
        (IsLocalRing.ResidueField.instModule
          (R := 𝒪[K])
          (S := 𝒪[L])) :=
    Module.finrank_pos
  have hcancel :
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] *
        @Module.finrank 𝓀[K] 𝓀[L] _ _
          (IsLocalRing.ResidueField.instModule
            (R := 𝒪[K])
            (S := 𝒪[L])) =
          1 * @Module.finrank 𝓀[K] 𝓀[L] _ _
            (IsLocalRing.ResidueField.instModule
              (R := 𝒪[K])
              (S := 𝒪[L])) := by
    calc
      _ = Module.finrank K L := hdegreeNew
      _ = @Module.finrank 𝓀[K] 𝓀[L] _ _
          (IsLocalRing.ResidueField.instModule
            (R := 𝒪[K])
            (S := 𝒪[L])) := hDegreeEqResidue
      _ = 1 * @Module.finrank 𝓀[K] 𝓀[L] _ _
          (IsLocalRing.ResidueField.instModule
            (R := 𝒪[K])
            (S := 𝒪[L])) := (one_mul _).symm
  exact ⟨Nat.eq_of_mul_eq_mul_right hfpos hcancel⟩

/-- A finite abelian extension is unramified if and only if its conductor
ideal is `1`. -/
theorem isFiniteUnramifiedValuationExtension_iff_localConductorIdeal_eq_one
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L ↔
      localConductorIdeal K L = 1 := by
  constructor
  · intro hunramified
    let : LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L :=
      hunramified
    exact localConductorIdeal_eq_one_of_unramifiedValuation K L
  · exact isFiniteUnramifiedValuationExtension_of_localConductorIdeal_eq_one K L

/-- A concrete finite abelian local extension is unramified exactly when
its local conductor exponent is zero. -/
theorem isUnramifiedValuedExtension_iff_localConductorExponent_eq_zero
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L ↔
      localConductorExponent K L = 0 :=
  (isFiniteUnramifiedValuationExtension_iff_localConductorIdeal_eq_one
      K L).trans
    (localConductorIdeal_eq_one_iff_exponent_eq_zero K L)

/-- Equivalently, a concrete finite abelian local extension is ramified
exactly when its local conductor exponent is nonzero. -/
theorem
    not_isUnramifiedValuedExtension_iff_localConductorExponent_ne_zero
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    ¬ IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L ↔
      localConductorExponent K L ≠ 0 :=
  not_congr
    (isUnramifiedValuedExtension_iff_localConductorExponent_eq_zero
      K L)

end LocalClassFieldTheory
