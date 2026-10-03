/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicStructure.IntegralLattice
/-!
# Deep principal units in mixed characteristic

This module equips the canonical `Z_p` lattice with the normalized valuation
topology and transports integral-basis coordinates through the deep
exponential--logarithm equivalence.
-/

@[expose] public section

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF renaming
  mrangeRestrictNontriviallyNormedField →
    mrangeRestrictNontriviallyNormedField


noncomputable
section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

open scoped WithZero nonZeroDivisors
open Module

variable {K : Type u} [Field K]

/-! ### The canonical normalized-valuation model -/

/-- The canonical mixed-characteristic algebra and topology attached to a
normalized `ℤᵐ⁰`-valued local field.  The bundle retains both the integral
algebra context and the direct valued-field structure; installing it exposes
the coherent `Q_p`/`Z_p` scalar towers and valuation topology. -/
class MixedWithZeroValuationContext
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] where
  /-- The integral-algebra context for the local-field model obtained by
  restricting the normalized valuation to its nonzero value group. -/
  integralAlgebra :
    MixedIntegralAlgebraContext (ofWithZeroValuation v)
  /-- The valued-field structure on `K` whose valuation is the original
  normalized `WithZero (Multiplicative ℤ)`-valued valuation. -/
  valued : Valued K (WithZero (Multiplicative ℤ))

/-- The canonical normalized-valuation context. -/
@[implicit_reducible]
def mixedWithZeroValuationContext
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] :
    MixedWithZeroValuationContext v :=
  { integralAlgebra :=
      mixedIntegralAlgebraContext (ofWithZeroValuation v)
    valued := Valued.mk' v }

/--
The valued field carries the integral algebra context `MixedIntegralAlgebraContext
(ofWithZeroValuation v)`.
-/
instance mixedWithZeroValuationContextIntegralAlgebra
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]
    [ctx : MixedWithZeroValuationContext v] :
    MixedIntegralAlgebraContext (ofWithZeroValuation v) :=
  ctx.integralAlgebra

/-! ### Continuity for the normalized valuation used by
  the deep exponential–logarithm equivalence -/

/-- For a normalized `ℤᵐ⁰`-valued local field, the canonical embedding
`Q_p → K` is continuous for the direct topology induced by `v`. -/
theorem continuous_qpadicNumbersAlgebra_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Continuous (algebraMap ℚ_[F.residueCharacteristic] K) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let p : ℕ := F.residueCharacteristic
  let direct : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let restricted : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  have hrestricted :
      @Continuous ℚ_[p] K inferInstance restricted.toTopologicalSpace
        (algebraMap ℚ_[p] K) := by
    let : Valued K F.mrangeValueGroup := restricted
    let : NontriviallyNormedField K :=
      mrangeRestrictNontriviallyNormedField F.toCompleteDVF
    change Continuous
      (fun x : ℚ_[p] =>
        ((F.qpadicNumbersEquivQpadicClosureSubfield x :
          F.qpadicClosureSubfield) : K))
    exact continuous_subtype_val.comp
      F.qpadicNumbersToQpadicClosureSubfield_isUniformInducing.uniformContinuous.continuous
  have huniform :
      (Valued.mk' v).toUniformSpace =
        (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued
          F.toCompleteDVF).toUniformSpace := by
    change (Valued.mk' v).toUniformSpace =
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued
        (WithZeroValuationTopology.completeDVF v)).toUniformSpace
    exact WithZeroValuationTopology.valuedMk_uniformSpace_eq_mrangeRestrict v
  let : Valued K (WithZero (Multiplicative ℤ)) := direct
  rw [show direct.toTopologicalSpace = restricted.toTopologicalSpace by
    exact congrArg (fun U : UniformSpace K => U.toTopologicalSpace) huniform]
  exact hrestricted

/-- The restricted map `Z_p → O_K` is continuous in the direct valuation
topology. -/
theorem continuous_padicIntToValuationSubring_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Continuous F.padicIntToValuationSubring := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  apply Continuous.subtype_mk
  exact (continuous_qpadicNumbersAlgebra_ofWithZeroValuation v).comp
    continuous_subtype_val

/-- The natural scalar multiplication of `Z_p` on `O_K` is continuous. -/
theorem continuousSMul_padicInt_valuationSubring_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ContinuousSMul ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  refine ⟨?_⟩
  apply Continuous.subtype_mk
  change Continuous
    (fun z : ℤ_[F.residueCharacteristic] ×
        F.toCompleteDVF.valuationSubring =>
      ((F.padicIntToValuationSubring z.1 :
        F.toCompleteDVF.valuationSubring) : K) * (z.2 : K))
  exact
    (continuous_subtype_val.comp
      ((continuous_padicIntToValuationSubring_ofWithZeroValuation v).comp
        continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)

/-- The induced action on every maximal-ideal power is continuous. -/
theorem continuousSMul_padicInt_maximalIdealPow_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (n : ℕ) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ContinuousSMul ℤ_[F.residueCharacteristic]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : ContinuousSMul ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring :=
    continuousSMul_padicInt_valuationSubring_ofWithZeroValuation v
  refine ⟨?_⟩
  apply Continuous.subtype_mk
  change Continuous
    (fun z : ℤ_[F.residueCharacteristic] ×
        ((F.toCompleteDVF.maximalIdeal ^ n :
          Ideal F.toCompleteDVF.valuationSubring)) =>
      z.1 • (z.2 : F.toCompleteDVF.valuationSubring))
  exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)

/-- The canonical p-adic action on `U^1` is jointly continuous for the
direct normalized valuation topology. -/
theorem continuousSMul_padicInt_firstPrincipalUnit_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ContinuousSMul ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (F.toCompleteDVF) 1)) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact
    CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicContinuousSMulOfWithZeroValuation
      v

/-- Every stable higher principal-unit subgroup inherits the joint
continuous p-adic action from `U^1`. -/
theorem continuousSMul_padicInt_higherPrincipalUnit_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    {r : ℕ} (hr : 1 ≤ r) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    letI : Module ℤ_[F.residueCharacteristic]
        (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          (F.toCompleteDVF) r)) :=
      F.higherPrincipalUnitPadicModule hr
    ContinuousSMul ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (F.toCompleteDVF) r)) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : Module ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (F.toCompleteDVF) r)) :=
    F.higherPrincipalUnitPadicModule hr
  let : ContinuousSMul ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (F.toCompleteDVF) 1)) :=
    continuousSMul_padicInt_firstPrincipalUnit_ofWithZeroValuation v
  have hinc : Continuous (F.higherPrincipalUnitAddToFirst hr) := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hsmulFirst : Continuous
      (fun z : ℤ_[F.residueCharacteristic] ×
          Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            F.toCompleteDVF r) =>
        z.1 • F.higherPrincipalUnitAddToFirst hr z.2) :=
    continuous_fst.smul (hinc.comp continuous_snd)
  refine ⟨?_⟩
  apply Continuous.subtype_mk
  apply (continuous_subtype_val.comp hsmulFirst).congr
  intro z
  exact congrArg
    (fun y :
        Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          F.toCompleteDVF 1) =>
      ((Additive.toMul y :
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          F.toCompleteDVF 1) : F.toCompleteDVF.valuationSubringˣ))
    (F.higherPrincipalUnitAddToFirst_smul hr z.1 z.2).symm

/-- The integral-basis coordinates on a maximal-ideal power are a
homeomorphism for the direct normalized valuation topology. -/
noncomputable def mixedMaximalIdealPowHomeomorphPiOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (n : ℕ) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) ≃ₜ
      (Fin (Module.finrank ℚ_[F.residueCharacteristic] K) →
        ℤ_[F.residueCharacteristic]) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  letI : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let p : ℕ := F.residueCharacteristic
  let d : ℕ := Module.finrank ℚ_[p] K
  letI : Module.Finite ℤ_[p]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) :=
    F.mixed_maximalIdealPow_moduleFinite n
  letI : Module.Free ℤ_[p]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) :=
    F.mixed_maximalIdealPow_moduleFree n
  letI : ContinuousSMul ℤ_[p]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) :=
    continuousSMul_padicInt_maximalIdealPow_ofWithZeroValuation v n
  letI : ContinuousAdd
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) := by
    refine ⟨?_⟩
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact
      (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_fst)).add
      (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd))
  let b : Basis (Fin d) ℤ_[p]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) :=
    Module.finBasisOfFinrankEq ℤ_[p]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring))
      (by simpa [d] using
        F.mixed_maximalIdealPow_finrank n)
  let e := b.equivFun
  have heinv : Continuous e.symm := by
    have hsum : Continuous (fun x : Fin d → ℤ_[p] => ∑ i, x i • b i) := by
      fun_prop
    convert hsum using 1
    funext x
    exact b.equivFun_symm_apply x
  exact
    (e.symm.toEquiv.toHomeomorphOfContinuousClosed
      heinv heinv.isClosedMap).symm

/-! ### the deep exponential–logarithm equivalence connected to the integral basis -/

/-- The logarithmic depth inequality forces a positive filtration level. -/
theorem mixed_one_le_of_log_level
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    1 ≤ n := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  have hpden : (0 : ℚ) < (F.residueCharacteristic : ℚ) - 1 := by
    have hpq : (1 : ℚ) < F.residueCharacteristic := by
      exact_mod_cast F.residueCharacteristic_prime.one_lt
    linarith
  have hepos : (0 : ℚ) <
      (ramificationIndexOfWithZeroValuation v : ℚ) := by
    exact_mod_cast ramificationIndexOfWithZeroValuation_pos v
  have hnq : (0 : ℚ) < (n : ℚ) :=
    lt_trans (div_pos hepos hpden) hlevel
  exact_mod_cast hnq

/-- The logarithm direction of the deep exponential–logarithm equivalence, written as a topological
additive equivalence `U^n ≃ₜ+ m^n`. -/
noncomputable def mixedDeepLogContinuousAddEquiv
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (F.toCompleteDVF) n) ≃ₜ+
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  letI : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact continuousAddEquivOfMultiplicativeSource
    (MultiplicativeIntegerValuation.chosenExpLogContinuousMulEquiv
      v hv n hlevel)

/-- The deep logarithm is compatible with natural scalars (ordinary powers)
before the density argument upgrades it to all of `Z_p`. -/
theorem mixed_deepLog_map_natCast_smul
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ))
    (m : ℕ)
    (x : Additive
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        ((ofWithZeroValuation v).toCompleteDVF) n)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    let hn : 1 ≤ n := mixed_one_le_of_log_level v n hlevel
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    letI : Module ℤ_[F.residueCharacteristic]
        (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          (F.toCompleteDVF) n)) :=
      F.higherPrincipalUnitPadicModule hn
    mixedDeepLogContinuousAddEquiv
        v hv n hlevel
        ((m : ℤ_[F.residueCharacteristic]) • x) =
      (m : ℤ_[F.residueCharacteristic]) •
        mixedDeepLogContinuousAddEquiv
          v hv n hlevel x := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let hn : 1 ≤ n := mixed_one_le_of_log_level v n hlevel
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : Module ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (F.toCompleteDVF) n)) :=
    F.higherPrincipalUnitPadicModule hn
  dsimp only
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  change
    (mixedDeepLogContinuousAddEquiv v hv n hlevel).toAddEquiv.toAddMonoidHom
        (m • x) =
      m •
        (mixedDeepLogContinuousAddEquiv v hv n hlevel).toAddEquiv.toAddMonoidHom x
  exact
    (mixedDeepLogContinuousAddEquiv v hv n hlevel).toAddEquiv.toAddMonoidHom.map_nsmul
      m x

/-- At a depth allowed by the deep exponential–logarithm equivalence, logarithm is a `Z_p`-linear
equivalence from `U^n` to the additive ideal `m^n`. -/
noncomputable def mixedDeepLogLinearEquiv
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    let hn : 1 ≤ n := mixed_one_le_of_log_level v n hlevel
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    letI : Module ℤ_[F.residueCharacteristic]
        (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          (F.toCompleteDVF) n)) :=
      F.higherPrincipalUnitPadicModule hn
    Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (F.toCompleteDVF) n) ≃ₗ[
        ℤ_[F.residueCharacteristic]]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let hn : 1 ≤ n := mixed_one_le_of_log_level v n hlevel
  letI : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  letI : Module ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (F.toCompleteDVF) n)) :=
    F.higherPrincipalUnitPadicModule hn
  letI : ContinuousSMul ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (F.toCompleteDVF) n)) :=
    continuousSMul_padicInt_higherPrincipalUnit_ofWithZeroValuation v hn
  letI : ContinuousSMul ℤ_[F.residueCharacteristic]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) :=
    continuousSMul_padicInt_maximalIdealPow_ofWithZeroValuation v n
  let e := mixedDeepLogContinuousAddEquiv
    v hv n hlevel
  exact padicLinearEquivOfContinuousAddEquiv e.toAddEquiv e.continuous

/-- The deep principal-unit group is finite over `Z_p`; via logarithm it is
finite free of the same rank as `O_K`. -/
theorem mixed_deepPrincipalUnit_moduleFinite
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    let hn : 1 ≤ n := mixed_one_le_of_log_level v n hlevel
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    letI : Module ℤ_[F.residueCharacteristic]
        (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          (F.toCompleteDVF) n)) :=
      F.higherPrincipalUnitPadicModule hn
    Module.Finite ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (F.toCompleteDVF) n)) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let hn : 1 ≤ n := mixed_one_le_of_log_level v n hlevel
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : Module ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (F.toCompleteDVF) n)) :=
    F.higherPrincipalUnitPadicModule hn
  let : Module.Finite ℤ_[F.residueCharacteristic]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) :=
    F.mixed_maximalIdealPow_moduleFinite n
  exact Module.Finite.equiv
    (mixedDeepLogLinearEquiv
      v hv n hlevel).symm

/-- Integral-basis coordinates after logarithm give the algebraic coordinate isomorphism `U^n ≃
Z_p^d`. -/
noncomputable def mixedDeepPrincipalUnitLinearEquivPi
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    let hn : 1 ≤ n := mixed_one_le_of_log_level v n hlevel
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    letI : Module ℤ_[F.residueCharacteristic]
        (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          (F.toCompleteDVF) n)) :=
      F.higherPrincipalUnitPadicModule hn
    Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (F.toCompleteDVF) n) ≃ₗ[
        ℤ_[F.residueCharacteristic]]
      (Fin (Module.finrank ℚ_[F.residueCharacteristic] K) →
        ℤ_[F.residueCharacteristic]) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let hn : 1 ≤ n := mixed_one_le_of_log_level v n hlevel
  letI : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  letI : Module ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (F.toCompleteDVF) n)) :=
    F.higherPrincipalUnitPadicModule hn
  exact
    (mixedDeepLogLinearEquiv
      v hv n hlevel).trans
        (F.mixedMaximalIdealPowLinearEquivPi n)

/-- The same coordinate identification is a homeomorphism, as asserted
explicitly in the mixed-characteristic field-unit structure theorem. -/
noncomputable def mixedDeepPrincipalUnitHomeomorphPi
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (F.toCompleteDVF) n) ≃ₜ
      (Fin (Module.finrank ℚ_[F.residueCharacteristic] K) →
        ℤ_[F.residueCharacteristic]) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  letI : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact
    (mixedDeepLogContinuousAddEquiv
      v hv n hlevel).toHomeomorph.trans
        (mixedMaximalIdealPowHomeomorphPiOfWithZeroValuation
          v n)

end LocalField
end LocalFieldTheory.DiscreteValuationField
