/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlaceCompletionInstances
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitPowerIndexFormulas
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Padic.PrincipalUnits
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.ValuedAdicComplete
public import Mathlib.NumberTheory.NumberField.ProductFormula
/-!
# Residue arithmetic for finite-place power indices

This file relates global ideal norms to the residue fields and ramification
invariants of the corresponding finite completions.
-/

@[expose] public section

open _root_.LocalFieldTheory.DiscreteValuationField.LocalField renaming
  valuation_residueCharacteristic_eq_exp_neg_ramificationIndex →
    valuation_residueCharacteristic_eq_exp_neg_ramificationIndex

open _root_.LocalFieldTheory.DiscreteValuationField.ValuedExtension renaming
  degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable →
    degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable

open _root_.LocalFieldTheory.DiscreteValuationField.ValuedExtension renaming
  exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image →
    exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image

open _root_.LocalFieldTheory.DiscreteValuationField.WithZeroValuation renaming
  exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective →
    exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective

open _root_.LocalFieldTheory.DiscreteValuationField.WithZeroValuation renaming
  isUniformizer_of_valuation_eq_exp_neg_one →
    isUniformizer_of_valuation_eq_exp_neg_one


open scoped NumberField NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]


open scoped Classical in
/-- The ideal norm is the cardinality of the residue field of the
corresponding adic completion. -/
theorem absNorm_eq_card_adicResidueField
    (v : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm v.asIdeal =
      Nat.card
        (Valued.ResidueField (v.adicCompletion K)) := by
  rw [Ideal.absNorm_apply]
  exact
    Nat.card_congr
      (ringOfIntegersQuotientEquivAdicResidueField
        v).toEquiv

open scoped Classical in
/-- The valuation-theoretic ramification index used by the local field
formula agrees with the extension ramification index. -/
theorem ramificationIndexOfWithZeroValuation_eq_extensionRamificationIndex
    {E : Type*} [Field E]
    (ν : Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete ν]
    [Finite
      (IsLocalRing.ResidueField ν.valuationSubring)]
    [CharZero E]
    (hν : Function.Surjective ν) :
    let F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
        ν
    letI :
        LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
          F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
        F
    LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation
        ν =
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
          F.residueCharacteristic).toDVF
        F.toCompleteDVF.toDVF := by
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
      ν
  let p := F.residueCharacteristic
  let :
      LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
        F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
      F
  let : Fact p.Prime :=
    ⟨F.residueCharacteristic_prime⟩
  let base :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p
  let target := F.toCompleteDVF
  let :
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p).IsRankOneDiscrete :=
    (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
      p).instCompleteDiscrete.isRankOneDiscrete
  let ϖ : base.valuationSubring :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring
      p (p : ℤ_[p])
  have hϖval :
      base.valuation (ϖ : ℚ_[p]) =
        WithZero.exp (-1 : ℤ) := by
    dsimp [base, ϖ]
    exact LocalFieldTheory.Padic.padicDVR_valuation_p p
  have hϖ :
      base.valuation.IsUniformizer
        (ϖ : ℚ_[p]) := by
    dsimp [base, ϖ] at hϖval ⊢
    exact
      isUniformizer_of_valuation_eq_exp_neg_one
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p)
        ((LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring
          p (p : ℤ_[p]) :
            (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
              p).valuationSubring) : ℚ_[p])
        hϖval
  obtain ⟨π, hπval⟩ :=
    exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
      ν hν
  have hπ :
      target.valuation.IsUniformizer (π : E) :=
    isUniformizer_of_valuation_eq_exp_neg_one
      ν (π : E) hπval
  obtain ⟨u, hu⟩ :=
    exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image
      base target hϖ hπ
  have huval :
      ν ((u : target.valuationSubring) : E) = 1 := by
    change
      ν (algebraMap target.valuationSubring E
        (u : target.valuationSubring)) = 1
    exact
      (Valuation.Integers.isUnit_iff_valuation_eq_one
        (Valuation.integer.integers ν)
        (x := (u : target.valuationSubring))).mp
        u.isUnit
  have hfield :
      ((ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap
          base.toDVF target.toDVF ϖ :
            target.valuationSubring) : E) =
        ((u : target.valuationSubring) : E) *
          (π : E) ^
            ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
              base.toDVF target.toDVF :=
    congrArg Subtype.val hu
  have hval := congrArg ν hfield
  have hpval :
      ν (p : E) =
        WithZero.exp
          (-(ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
            base.toDVF target.toDVF : ℤ)) := by
    rw [ν.map_mul, ν.map_pow, huval, hπval,
      one_mul] at hval
    calc
      ν (p : E) =
          WithZero.exp (-1 : ℤ) ^
            ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
              base.toDVF target.toDVF := by
        have himage :
            ((ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap
                base.toDVF target.toDVF ϖ : target.valuationSubring) : E) =
              (p : E) := by
          change algebraMap ℚ_[p] E (p : ℚ_[p]) = (p : E)
          exact map_natCast _ _
        exact (congrArg ν himage).symm.trans hval
      _ =
          WithZero.exp
            (ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
              base.toDVF target.toDVF •
                (-1 : ℤ)) :=
        (WithZero.exp_nsmul _ _).symm
      _ =
          WithZero.exp
            (-(ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
              base.toDVF target.toDVF : ℤ)) := by
        congr 1
        simp
  have hcustom :=
    valuation_residueCharacteristic_eq_exp_neg_ramificationIndex
      ν
  have hexp :
      WithZero.exp
          (-(LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation
            ν : ℤ)) =
        WithZero.exp
          (-(ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
            base.toDVF target.toDVF : ℤ)) :=
    hcustom.symm.trans
      (by
        simpa [F, p] using hpval)
  have hint :
      -(LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation
          ν : ℤ) =
        -(ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
          base.toDVF target.toDVF : ℤ) :=
    WithZero.exp_injective hexp
  exact_mod_cast neg_injective hint

open scoped Classical in
/-- The cardinality of a mixed-characteristic local residue field is
`p` to the residue degree. -/
theorem card_localField_residueField_eq_pow_residueDegree
    {E : Type*} [Field E]
    (ν : Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete ν]
    [Finite
      (IsLocalRing.ResidueField ν.valuationSubring)]
    [CharZero E] :
    let F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
        ν
    letI :
        LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
          F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
        F
    Nat.card F.residueField =
      F.residueCharacteristic ^
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
            F.residueCharacteristic).toDVF
          F.toCompleteDVF.toDVF := by
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
      ν
  let p := F.residueCharacteristic
  let :
      LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
        F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
      F
  let base :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p
  let target := F.toCompleteDVF
  let : Finite base.residueField :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF_residueField_finite p
  change
    Nat.card target.residueField =
      p ^
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF
  have hfinrank :
      Module.finrank base.residueField target.residueField =
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF := by
    rw [
      ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree_eq_finrank_quotient
        base target]
    rfl
  calc
    Nat.card target.residueField =
        Nat.card base.residueField ^
          Module.finrank base.residueField target.residueField :=
      Module.natCard_eq_pow_finrank
    _ = p ^
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF := by
      rw [hfinrank,
        LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF_residueField_card]

open scoped Classical in
/-- Degree over `ℚ_p` is ramification index times residue degree. -/
theorem finrank_qp_eq_ramificationIndex_mul_residueDegree
    {E : Type*} [Field E]
    (ν : Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete ν]
    [Finite
      (IsLocalRing.ResidueField ν.valuationSubring)]
    [CharZero E]
    (hν : Function.Surjective ν) :
    let F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
        ν
    letI :
        LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
          F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
        F
    Module.finrank ℚ_[F.residueCharacteristic] E =
      LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation
          ν *
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
            F.residueCharacteristic).toDVF
          F.toCompleteDVF.toDVF := by
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
      ν
  let :
      LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
        F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
      F
  let base :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
      F.residueCharacteristic
  let target := F.toCompleteDVF
  rw [
    ramificationIndexOfWithZeroValuation_eq_extensionRamificationIndex
      ν hν]
  exact
    degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable
      base target

open scoped Classical in
/-- The absolute norm of `v` is `p^f`, with `p` the residue
characteristic and `f` the local residue degree. -/
theorem absNorm_eq_residueCharacteristic_pow_residueDegree
    (v : HeightOneSpectrum (𝓞 K)) :
    let ν :
        Valuation
          (v.adicCompletion K)
          (WithZero (Multiplicative ℤ)) :=
      Valued.v
    let F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
        ν
    letI :
        LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
          F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
        F
    Ideal.absNorm v.asIdeal =
      F.residueCharacteristic ^
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
            F.residueCharacteristic).toDVF
          F.toCompleteDVF.toDVF := by
  let ν :
      Valuation
        (v.adicCompletion K)
        (WithZero (Multiplicative ℤ)) :=
    Valued.v
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
      ν
  let :
      LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
        F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
      F
  rw [absNorm_eq_card_adicResidueField]
  change
    Nat.card F.residueField =
      F.residueCharacteristic ^
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
            F.residueCharacteristic).toDVF
          F.toCompleteDVF.toDVF
  exact card_localField_residueField_eq_pow_residueDegree ν


end GlobalClassFieldTheory.ClassFieldAxiom
