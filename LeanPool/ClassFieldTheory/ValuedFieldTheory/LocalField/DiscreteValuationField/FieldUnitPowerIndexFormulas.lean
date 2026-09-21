/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicPowerIndex
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitStructure
/-!
# Power indices in local-field unit groups

The index formulas below use the actual principal-unit structures from
the field-unit structure theorem.  Both the natural-cardinality form and the literal rational
form involving the normalized local absolute value are recorded.
-/

noncomputable section

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

variable {K : Type u} [Field K]

/-- Reindex the countable p-adic product into the universe of the ambient
field.  This is algebraically invisible, but lets the generic product-index
calculation be instantiated without restricting the universe of `K`. -/
private noncomputable def padicIntNatPiMulEquivULift
    (p : ℕ) [Fact p.Prime] :
    Multiplicative (ℕ → ℤ_[p]) ≃*
      Multiplicative (ULift.{u, 0} ℕ → ℤ_[p]) := by
  let r : (ULift.{u, 0} ℕ → ℤ_[p]) ≃+ (ℕ → ℤ_[p]) :=
    { Equiv.piCongrLeft (fun _ : ℕ => ℤ_[p])
        (Equiv.ulift : ULift.{u, 0} ℕ ≃ ℕ) with
      map_add' := by
        intro x y
        rfl }
  exact AddEquiv.toMultiplicative r.symm

/-- The local-field power-index formula, first equality.  The uniformizer factor contributes
exactly `n`, independently of the characteristic. -/
theorem fieldIndex_eq_mul_unitIndex
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]
    (n : ℕ) [NeZero n]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v).valuationSubringˣ ⧸
        (powMonoidHom n :
          (MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v).valuationSubringˣ →*
          (MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v).valuationSubringˣ).range)] :
    let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K :=
      MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) := by
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K :=
    MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v
  have : Finite F.residueField := by
    change Finite (IsLocalRing.ResidueField v.valuationSubring)
    infer_instance
  let hex := F.exists_uniformizer
  let π := Classical.choose hex
  have hπ : F.valuation.IsUniformizer (π : K) := Classical.choose_spec hex
  exact card_fieldUnits_nthPowerQuotient_eq_mul_unit_nthPowerQuotient
    F hπ n

/-- The local-field power-index formula in mixed characteristic, in natural-cardinality form for
the full field-unit group. -/
theorem mixed_fieldIndex
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    {n : ℕ} [NeZero n]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((CompleteDVF.higherPrincipalUnitGroup
        (ofWithZeroValuation v).toCompleteDVF) 1 ⧸
        (powMonoidHom n : ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1) →* ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1)).range)] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    let d := Module.finrank ℚ_[F.residueCharacteristic] K
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * (Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) *
        F.residueCharacteristic ^
          (d * padicValNat F.residueCharacteristic n)) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let d := Module.finrank ℚ_[F.residueCharacteristic] K
  let hex :=
    WithZeroValuation.exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
      v hv
  let π := Classical.choose hex
  have hπval : v (π : K) = WithZero.exp (-1 : ℤ) :=
    Classical.choose_spec hex
  have hπ : v.IsUniformizer (π : K) :=
    WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
      v (π : K) hπval
  obtain ⟨a, e⟩ :=
    chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation
      v hv
  exact
    card_fieldUnits_nthPowerQuotient_of_mixedPrincipalUnitStructure
      (p := F.residueCharacteristic) (F := F.toCompleteDVF) hπ
      (ZMod (F.residueCharacteristic ^ a)) d e.symm.toMulEquiv

/-- The local-field power-index formula in mixed characteristic, in natural-cardinality form for
the valuation-ring unit group.  Its finite kernel is written as the canonical
field root group `μ_n(K)`. -/
theorem mixed_unitIndex
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    {n : ℕ} [NeZero n]
    [Finite
      ((CompleteDVF.higherPrincipalUnitGroup
        (ofWithZeroValuation v).toCompleteDVF) 1 ⧸
        (powMonoidHom n : ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1) →* ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1)).range)] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    let d := Module.finrank ℚ_[F.residueCharacteristic] K
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) *
        F.residueCharacteristic ^
          (d * padicValNat F.residueCharacteristic n) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let d := Module.finrank ℚ_[F.residueCharacteristic] K
  let hex :=
    WithZeroValuation.exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
      v hv
  let π := Classical.choose hex
  have hπval : v (π : K) = WithZero.exp (-1 : ℤ) :=
    Classical.choose_spec hex
  have hπ : v.IsUniformizer (π : K) :=
    WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
      v (π : K) hπval
  obtain ⟨a, e⟩ :=
    chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation
      v hv
  exact
    card_units_nthPowerQuotient_of_mixedPrincipalUnitStructure_fieldKernel
      (p := F.residueCharacteristic) (F := F.toCompleteDVF) hπ
      (ZMod (F.residueCharacteristic ^ a)) d e.symm.toMulEquiv

/-- In mixed characteristic, an exponent prime to the residue characteristic
has no principal-unit defect.  Thus the valuation-ring unit power index is
the cardinality of the canonical field root group `μ_n(K)`.  Finiteness of
the principal-unit quotient is obtained internally from the mixed
principal-unit structure. -/
theorem mixed_unitIndex_of_coprime
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    {n : ℕ} [NeZero n]
    [Fact
      (Nat.Coprime n
        (ofWithZeroValuation v).residueCharacteristic)] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let d := Module.finrank ℚ_[F.residueCharacteristic] K
  obtain ⟨a, e⟩ :=
    chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation
      v hv
  let U :=
    CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1
  let A :=
    ZMod (F.residueCharacteristic ^ a) ×
      (Fin d → ℤ_[F.residueCharacteristic])
  let : NeZero (F.residueCharacteristic ^ a) :=
    ⟨pow_ne_zero _ F.residueCharacteristic_prime.ne_zero⟩
  let : Finite
      (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) := by
    infer_instance
  let : Finite
      (U ⧸ (powMonoidHom n : U →* U).range) :=
    LocalFieldTheory.finite_nthPowerQuotient_of_mulEquiv
      U (Multiplicative A) n e.symm.toMulEquiv
  have hpnd : ¬ F.residueCharacteristic ∣ n :=
    F.residueCharacteristic_prime.coprime_iff_not_dvd.mp
      (Fact.out : Nat.Coprime n F.residueCharacteristic).symm
  have hpadic :
      padicValNat F.residueCharacteristic n = 0 :=
    padicValNat.eq_zero_of_not_dvd hpnd
  simpa only [F, hpadic, Nat.mul_zero, pow_zero, Nat.mul_one] using
    (mixed_unitIndex v hv (n := n))

/-- Literal mixed-characteristic field formula from the local-field power-index formula:
`(Kˣ : Kˣⁿ) = n #μ_n(K) / |n|_p`. -/
theorem mixed_fieldIndex_rationalFormula
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    {n : ℕ} [NeZero n]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((CompleteDVF.higherPrincipalUnitGroup
        (ofWithZeroValuation v).toCompleteDVF) 1 ⧸
        (powMonoidHom n : ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1) →* ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1)).range)] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    let d := Module.finrank ℚ_[F.residueCharacteristic] K
    (Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) : ℚ) =
      (n * Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) : ℕ) /
        normalizedLocalNatAbs F.residueCharacteristic d n := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let d := Module.finrank ℚ_[F.residueCharacteristic] K
  let hex :=
    WithZeroValuation.exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
      v hv
  let π := Classical.choose hex
  have hπval : v (π : K) = WithZero.exp (-1 : ℤ) :=
    Classical.choose_spec hex
  have hπ : v.IsUniformizer (π : K) :=
    WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
      v (π : K) hπval
  obtain ⟨a, e⟩ :=
    chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation
      v hv
  exact
    card_fieldUnits_nthPowerQuotient_of_mixedPrincipalUnitStructure_rationalFormula
      (p := F.residueCharacteristic) (F := F.toCompleteDVF) hπ
      (ZMod (F.residueCharacteristic ^ a)) d e.symm.toMulEquiv

/-- Literal mixed-characteristic unit formula from the local-field power-index formula:
`(U : Uⁿ) = #μ_n(K) / |n|_p`. -/
theorem mixed_unitIndex_rationalFormula
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    {n : ℕ} [NeZero n]
    [Finite
      ((CompleteDVF.higherPrincipalUnitGroup
        (ofWithZeroValuation v).toCompleteDVF) 1 ⧸
        (powMonoidHom n : ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1) →* ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1)).range)] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    let d := Module.finrank ℚ_[F.residueCharacteristic] K
    (Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) : ℚ) =
      Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) /
        normalizedLocalNatAbs F.residueCharacteristic d n := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let d := Module.finrank ℚ_[F.residueCharacteristic] K
  let hex :=
    WithZeroValuation.exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
      v hv
  let π := Classical.choose hex
  have hπval : v (π : K) = WithZero.exp (-1 : ℤ) :=
    Classical.choose_spec hex
  have hπ : v.IsUniformizer (π : K) :=
    WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
      v (π : K) hπval
  obtain ⟨a, e⟩ :=
    chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation
      v hv
  exact
    card_units_nthPowerQuotient_of_mixedPrincipalUnitStructure_rationalFormula
      (p := F.residueCharacteristic) (F := F.toCompleteDVF) hπ
      (ZMod (F.residueCharacteristic ^ a)) d e.symm.toMulEquiv

/-- The local-field power-index formula in equal characteristic.  The canonical
`NeZero n` and `Fact (Nat.Coprime n p)` instances state exactly the
hypotheses needed for multiplication by `n` on `ℤ_p`. -/
theorem equal_fieldIndex
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]
    [CharP K (ofWithZeroValuation v).residueCharacteristic]
    {n : ℕ} [NeZero n]
    [Fact (Nat.Coprime n (ofWithZeroValuation v).residueCharacteristic)]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((CompleteDVF.higherPrincipalUnitGroup
        (ofWithZeroValuation v).toCompleteDVF) 1 ⧸
        (powMonoidHom n : ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1) →* ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1)).range)] :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let hex := F.toCompleteDVF.exists_uniformizer
  let π := Classical.choose hex
  have hπ : v.IsUniformizer (π : K) := Classical.choose_spec hex
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let e := chosenFirstPrincipalUnitStructure_equalCharacteristic v
  exact
    card_fieldUnits_nthPowerQuotient_of_equalPrincipalUnitProduct
      (p := F.residueCharacteristic) (F := F.toCompleteDVF)
      (ι := ULift.{u, 0} ℕ) hπ
      (e.symm.toMulEquiv.trans
        (padicIntNatPiMulEquivULift F.residueCharacteristic))

/-- Equal-characteristic unit-index formula, with the kernel written as the
full field root group `μ_n(K)`. -/
theorem equal_unitIndex
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]
    [CharP K (ofWithZeroValuation v).residueCharacteristic]
    {n : ℕ} [NeZero n]
    [Fact (Nat.Coprime n (ofWithZeroValuation v).residueCharacteristic)]
    [Finite
      ((CompleteDVF.higherPrincipalUnitGroup
        (ofWithZeroValuation v).toCompleteDVF) 1 ⧸
        (powMonoidHom n : ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1) →* ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1)).range)] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let hex := F.toCompleteDVF.exists_uniformizer
  let π := Classical.choose hex
  have hπ : v.IsUniformizer (π : K) := Classical.choose_spec hex
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let e := chosenFirstPrincipalUnitStructure_equalCharacteristic v
  exact
    card_units_nthPowerQuotient_of_equalPrincipalUnitProduct
      (p := F.residueCharacteristic) (F := F.toCompleteDVF)
      (ι := ULift.{u, 0} ℕ) hπ
      (e.symm.toMulEquiv.trans
        (padicIntNatPiMulEquivULift F.residueCharacteristic))

/-- Literal equal-characteristic field formula from the local-field power-index formula.  Under
`Nat.Coprime n p` the normalized local absolute value of `n` is one. -/
theorem equal_fieldIndex_rationalFormula
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]
    [CharP K (ofWithZeroValuation v).residueCharacteristic]
    {n : ℕ} [NeZero n]
    [Fact (Nat.Coprime n (ofWithZeroValuation v).residueCharacteristic)]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((CompleteDVF.higherPrincipalUnitGroup
        (ofWithZeroValuation v).toCompleteDVF) 1 ⧸
        (powMonoidHom n : ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1) →* ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1)).range)] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    (Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) : ℚ) =
      (n * Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) : ℕ) /
        normalizedLocalNatAbs F.residueCharacteristic 0 n := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let hex := F.toCompleteDVF.exists_uniformizer
  let π := Classical.choose hex
  have hπ : v.IsUniformizer (π : K) := Classical.choose_spec hex
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let e := chosenFirstPrincipalUnitStructure_equalCharacteristic v
  exact
    card_fieldUnits_nthPowerQuotient_of_equalPrincipalUnitProduct_rationalFormula
      (p := F.residueCharacteristic) (F := F.toCompleteDVF)
      (ι := ULift.{u, 0} ℕ) hπ
      (e.symm.toMulEquiv.trans
        (padicIntNatPiMulEquivULift F.residueCharacteristic))

/-- Literal equal-characteristic unit formula from the local-field power-index formula. -/
theorem equal_unitIndex_rationalFormula
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]
    [CharP K (ofWithZeroValuation v).residueCharacteristic]
    {n : ℕ} [NeZero n]
    [Fact (Nat.Coprime n (ofWithZeroValuation v).residueCharacteristic)]
    [Finite
      ((CompleteDVF.higherPrincipalUnitGroup
        (ofWithZeroValuation v).toCompleteDVF) 1 ⧸
        (powMonoidHom n : ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1) →* ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1)).range)] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    (Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) : ℚ) =
      Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) /
        normalizedLocalNatAbs F.residueCharacteristic 0 n := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let hex := F.toCompleteDVF.exists_uniformizer
  let π := Classical.choose hex
  have hπ : v.IsUniformizer (π : K) := Classical.choose_spec hex
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let e := chosenFirstPrincipalUnitStructure_equalCharacteristic v
  exact
    card_units_nthPowerQuotient_of_equalPrincipalUnitProduct_rationalFormula
      (p := F.residueCharacteristic) (F := F.toCompleteDVF)
      (ι := ULift.{u, 0} ℕ) hπ
      (e.symm.toMulEquiv.trans
        (padicIntNatPiMulEquivULift F.residueCharacteristic))

end LocalField
end LocalFieldTheory.DiscreteValuationField
