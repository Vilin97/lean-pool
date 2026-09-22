/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.LocalRingEquiv
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.PrincipalUnitExpLogEquiv
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicPowerIndex
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UniformizerPrincipalQuotient
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Padic.NonarchimedeanLocalField
import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.NumberTheory.Padics.ProperSpace
/-!
# Principal units of the p-adic field

This file identifies the standard p-adic integer and complete-DVF models,
computes their principal-unit quotients, and records the logarithm/exponential
power formulas used by local cyclotomic norm calculations.
-/

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  card_unitsModHigherPrincipalUnitGroup_eq_quotientUnits →
    card_unitsModHigherPrincipalUnitGroup_eq_quotientUnits

open _root_.LocalFieldTheory.DiscreteValuationField.LocalField renaming
  ramificationIndexOfWithZeroValuation_intCast →
    ramificationIndexOfWithZeroValuation_intCast

open _root_.LocalFieldTheory.DiscreteValuationField.LocalField renaming
  valuation_natCast_factorial_eq_exp_neg_ramificationIndex_mul_padicValNat →
    valuation_natCast_factorial_eq_exp_neg_ramificationIndex_mul_padicValNat

open _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation renaming
  chosenExpLogContinuousMulEquiv →
    chosenExpLogContinuousMulEquiv

open _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation renaming
  completeDVFOfWithZeroValuation →
    completeDVFOfWithZeroValuation

open _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation renaming
  expSeriesFieldOfWithZeroValuation →
    expSeriesFieldOfWithZeroValuation

open _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation renaming
  principalUnitExpLogContinuousMulEquivOfExactOfWithZeroValuationScaled →
    principalUnitExpLogContinuousMulEquivOfExactOfWithZeroValuationScaled

open _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation renaming
  principalUnitExpLogMulEquivOfExactOfWithZeroValuationScaled →
    principalUnitExpLogMulEquivOfExactOfWithZeroValuationScaled

open _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation renaming
  principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled →
    principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled

open _root_.LocalFieldTheory.DiscreteValuationField.WithZeroValuation renaming
  exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective →
    exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective

open _root_.LocalFieldTheory.DiscreteValuationField.WithZeroValuation renaming
  isUniformizer_of_valuation_eq_exp_neg_one →
    isUniformizer_of_valuation_eq_exp_neg_one

open _root_.LocalFieldTheory.DiscreteValuationField.WithZeroValuationTopology renaming
  completeSpace_ofWithZeroValuation →
    completeSpace_ofWithZeroValuation


noncomputable section

open scoped ValuativeRel WithZero

namespace LocalFieldTheory.Padic

open LocalFieldTheory
open ValuationTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (p : ℕ) [Fact p.Prime]

/-- The valuative integer ring of `ℚ_p` is canonically equivalent to
`ℤ_p`. -/
noncomputable def integerRingEquivPadicInt :
    𝒪[ℚ_[p]] ≃+* ℤ_[p] where
  toFun x := ⟨x, (integer_mem_iff_norm_le_one p x).1 x.property⟩
  invFun x := ⟨x, (integer_mem_iff_norm_le_one p x).2 x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- The equivalence with `ℤ_p` preserves the underlying element of `ℚ_p`. -/
@[simp] theorem integerRingEquivPadicInt_coe (x : 𝒪[ℚ_[p]]) :
    ((integerRingEquivPadicInt p x : ℤ_[p]) : ℚ_[p]) = (x : ℚ_[p]) := rfl

/-- The valuative integer ring of `ℚ_p` is canonically equivalent to the
valuation subring of the bundled p-adic complete discrete valuation field. -/
noncomputable def integerRingEquivPadicDVRValuationSubring :
    𝒪[ℚ_[p]] ≃+*
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring :=
  (integerRingEquivPadicInt p).trans
    (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring p)

/-- The equivalence with the bundled p-adic valuation subring preserves the
underlying field element. -/
@[simp] theorem integerRingEquivPadicDVRValuationSubring_coe
    (x : 𝒪[ℚ_[p]]) :
    ((integerRingEquivPadicDVRValuationSubring p x :
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring) :
      ℚ_[p]) = (x : ℚ_[p]) := by
  rfl

/-- Transport to the bundled p-adic valuation ring identifies the two
definitions of the `n`-th principal-unit group. -/
theorem unitsMapEquiv_mem_higherPrincipalUnitGroup_iff
    (n : ℕ) (u : 𝒪[ℚ_[p]]ˣ) :
    Units.mapEquiv (integerRingEquivPadicDVRValuationSubring p).toMulEquiv u ∈
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p) n ↔
      u ∈ principalUnits ℚ_[p] n := by
  rw [LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff,
    mem_principalUnits_iff]
  change integerRingEquivPadicDVRValuationSubring p
      ((u : 𝒪[ℚ_[p]]) - 1) ∈
        IsLocalRing.maximalIdeal
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
            p).valuationSubring ^ n ↔
    (u : 𝒪[ℚ_[p]]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[ℚ_[p]] ^ n
  exact ringEquiv_mem_maximalIdeal_pow_iff
    (integerRingEquivPadicDVRValuationSubring p) n ((u : 𝒪[ℚ_[p]]) - 1)

/-- The image of p-adic principal units is the bundled complete-DVF
higher-principal-unit group. -/
theorem principalUnits_map_eq_higherPrincipalUnitGroup (n : ℕ) :
    (principalUnits ℚ_[p] n).map
        (Units.mapEquiv
          (integerRingEquivPadicDVRValuationSubring p).toMulEquiv).toMonoidHom =
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p) n := by
  let E := Units.mapEquiv
    (integerRingEquivPadicDVRValuationSubring p).toMulEquiv
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (unitsMapEquiv_mem_higherPrincipalUnitGroup_iff p n v).2 hv
  · intro hu
    refine ⟨E.symm u, ?_, ?_⟩
    · exact (unitsMapEquiv_mem_higherPrincipalUnitGroup_iff p n (E.symm u)).1
        (by simpa [E] using hu)
    · change E (E.symm u) = u
      exact E.apply_symm_apply u

/-- The quotient of p-adic integer units by principal units is equivalent to
the corresponding quotient in the bundled complete-DVF model. -/
noncomputable def integerUnitsPrincipalQuotEquivPadicDVR (n : ℕ) :
    IntegerUnitsPrincipalQuot ℚ_[p] n ≃*
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubringˣ ⧸
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p) n :=
  QuotientGroup.congr _ _
    (Units.mapEquiv
      (integerRingEquivPadicDVRValuationSubring p).toMulEquiv)
    (principalUnits_map_eq_higherPrincipalUnitGroup p n)

/-- Reduction modulo the `n`-th maximal-ideal power in the bundled p-adic
valuation ring is canonically `ZMod (p ^ n)`. -/
noncomputable def padicDVRQuotientEquivZMod (n : ℕ) :
    (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring ⧸
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).maximalIdeal ^
          n ≃+*
      ZMod (p ^ n) := by
  let F := LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p
  let e : F.valuationSubring ≃+* ℤ_[p] :=
    (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring p).symm
  have hmap : Ideal.map e.toRingHom (F.maximalIdeal ^ n) =
      Ideal.span ({(p : ℤ_[p]) ^ n} : Set ℤ_[p]) := by
    rw [ringEquiv_map_maximalIdeal_pow, PadicInt.maximalIdeal_eq_span_p,
      Ideal.span_singleton_pow]
  exact (Ideal.quotientEquiv (F.maximalIdeal ^ n)
      (Ideal.span ({(p : ℤ_[p]) ^ n} : Set ℤ_[p])) e hmap.symm).trans
    ((Ideal.quotEquivOfEq (PadicInt.ker_toZModPow n).symm).trans
      (RingHom.quotientKerEquivOfSurjective
        (ZMod.ringHom_surjective (PadicInt.toZModPow n))))

/-- The quotient of p-adic integer units by `U^(k+1)` has cardinality
`(p - 1) * p ^ k`. -/
theorem nat_card_integerUnitsPrincipalQuot_padic_succ (k : ℕ) :
    Nat.card (IntegerUnitsPrincipalQuot ℚ_[p] (k + 1)) =
      (p - 1) * p ^ k := by
  let F := LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p
  let : Finite F.residueField :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF_residueField_finite p
  calc
    Nat.card (IntegerUnitsPrincipalQuot ℚ_[p] (k + 1)) =
        Nat.card (F.valuationSubringˣ ⧸
          LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F (k + 1)) :=
      Nat.card_congr (integerUnitsPrincipalQuotEquivPadicDVR p (k + 1)).toEquiv
    _ = Nat.card ((F.valuationSubring ⧸ F.maximalIdeal ^ (k + 1))ˣ) :=
      card_unitsModHigherPrincipalUnitGroup_eq_quotientUnits
        F (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
    _ = Nat.card (ZMod (p ^ (k + 1)))ˣ :=
      Nat.card_congr
        (Units.mapEquiv (padicDVRQuotientEquivZMod p (k + 1)).toMulEquiv).toEquiv
    _ = Nat.totient (p ^ (k + 1)) := by
      rw [← Fintype.card_eq_nat_card, ZMod.card_units_eq_totient]
    _ = (p - 1) * p ^ k := by
      rw [Nat.totient_prime_pow (Fact.out : Nat.Prime p) (Nat.succ_pos k)]
      simp [Nat.mul_comm]

/-- The rational prime `p`, regarded as a unit of the field `ℚ_p`. -/
noncomputable def padicPrimeUnit : ℚ_[p]ˣ :=
  Units.mk0 (p : ℚ_[p]) (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)

/-- The rational prime `p`, regarded as an element of the p-adic integer
ring. -/
noncomputable def padicPrimeInteger : 𝒪[ℚ_[p]] :=
  (integerRingEquivPadicInt p).symm (p : ℤ_[p])

/-- Coercing the p-adic prime integer back to `ℚ_p` gives `p`. -/
@[simp] theorem padicPrimeInteger_coe :
    ((padicPrimeInteger p : 𝒪[ℚ_[p]]) : ℚ_[p]) = (p : ℚ_[p]) := rfl

/-- The p-adic prime integer is irreducible. -/
theorem padicPrimeInteger_irreducible :
    Irreducible (padicPrimeInteger p) := by
  exact (MulEquiv.irreducible_iff
    (integerRingEquivPadicInt p).symm.toMulEquiv).2
      ((PadicInt.prime_p : Prime (p : ℤ_[p])).irreducible)

/-- The normalized additive valuation of the field unit `p` is `-1` in the
field-unit convention used by local class field theory. -/
theorem valuationMap_padicPrimeUnit :
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap ℚ_[p]
        (Additive.ofMul (padicPrimeUnit p)) = -1 := by
  simpa [LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply] using
    (v_integerRingIrreducibleFieldUnit ℚ_[p]
      (padicPrimeInteger p) (padicPrimeInteger_irreducible p)
      (padicPrimeUnit p) rfl)

/-- The inverse of the p-adic prime unit is a normalized uniformizer of
additive valuation one. -/
theorem valuationMap_padicPrimeUnit_inv :
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap ℚ_[p]
        (Additive.ofMul (padicPrimeUnit p)⁻¹) = 1 := by
  rw [LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_ofMul_inv,
    valuationMap_padicPrimeUnit]
  norm_num

/-- The standard field-unit quotient generated by `p⁻¹` and `U^(k+1)` has
cardinality `(p - 1) * p ^ k`. -/
theorem nat_card_fieldUnitsUniformizerPrincipalQuot_padic_succ
    (k : ℕ) :
    Nat.card (ℚ_[p]ˣ ⧸ LocalFieldTheory.uniformizerPrincipalSubgroup ℚ_[p]
      (padicPrimeUnit p)⁻¹ 1 (k + 1)) = (p - 1) * p ^ k := by
  let := padicIsNonarchimedeanLocalField p
  calc
    Nat.card (ℚ_[p]ˣ ⧸ LocalFieldTheory.uniformizerPrincipalSubgroup ℚ_[p]
        (padicPrimeUnit p)⁻¹ 1 (k + 1)) =
        Nat.card (IntegerUnitsPrincipalQuot ℚ_[p] (k + 1)) :=
      Nat.card_congr
        (LocalFieldTheory.uniformizerPrincipalQuotientEquivIntegerUnitsPrincipalQuotient ℚ_[p]
          (padicPrimeUnit p)⁻¹
          (valuationMap_padicPrimeUnit_inv p) (k + 1)).toEquiv
    _ = (p - 1) * p ^ k :=
      nat_card_integerUnitsPrincipalQuot_padic_succ p k

/-- Every element of the `(k+1)`-st p-adic maximal-ideal power is the
`((p-1) * p^k)`-fold additive multiple of an element of the maximal ideal. -/
theorem padicInt_exists_degree_root_of_mem_maximalIdeal_pow_succ
    (k : ℕ) (z : ℤ_[p])
    (hz : z ∈ IsLocalRing.maximalIdeal ℤ_[p] ^ (k + 1)) :
    ∃ b : ℤ_[p],
      b ∈ IsLocalRing.maximalIdeal ℤ_[p] ∧
      ((p - 1) * p ^ k) • b = z := by
  have hpone : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
  have hptwo : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hpred_ne : p - 1 ≠ 0 := by omega
  have hp_not_dvd_pred : ¬ p ∣ p - 1 := by
    intro h
    have hle : p ≤ p - 1 := Nat.le_of_dvd (by omega) h
    omega
  have hvalpred : (p - 1 : ℤ_[p]).valuation = 0 := by
    have hvalNat : (((p - 1 : ℕ) : ℤ_[p])).valuation = 0 := by
      rw [LocalFieldTheory.DiscreteValuationField.padicInt_valuation_natCast,
        padicValNat.eq_zero_of_not_dvd hp_not_dvd_pred]
    rw [Nat.cast_sub hpone, Nat.cast_one] at hvalNat
    exact hvalNat
  have hpred_qp_ne : (p - 1 : ℤ_[p]) ≠ 0 := by exact_mod_cast hpred_ne
  have hpred_unit : IsUnit (p - 1 : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_eq_zpow_neg_valuation hpred_qp_ne,
      hvalpred]
    simp
  let u : ℤ_[p]ˣ := hpred_unit.unit
  have hu : (u : ℤ_[p]) = (p - 1 : ℤ_[p]) := hpred_unit.unit_spec
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hz
  obtain ⟨c, rfl⟩ := hz
  let b : ℤ_[p] := c * p * ((↑(u⁻¹) : ℤ_[p]))
  refine ⟨b, ?_, ?_⟩
  · rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
    refine ⟨c * (↑(u⁻¹) : ℤ_[p]), ?_⟩
    simp [b, mul_left_comm, mul_assoc]
  · simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_sub hpone,
      Nat.cast_one, Nat.cast_pow]
    rw [← hu]
    simp [b, pow_succ, mul_comm, mul_left_comm, mul_assoc]

/-- The residue field of the canonical p-adic discrete valuation is finite. -/
noncomputable instance padicDVR_residueField_finite :
    Finite (IsLocalRing.ResidueField
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation
        p).valuationSubring) := by
  simpa [LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF,
    ValuationTheory.DiscreteValuationField.CompleteDVF.residueField,
    ValuationTheory.DiscreteValuationField.CompleteDVF.valuationSubring,
    ValuationTheory.DiscreteValuationField.CompleteDVF.toDVF] using
      LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF_residueField_finite p

/-- The residue characteristic of the canonical p-adic discrete valuation
is `p`. -/
theorem padicDVR_residueCharacteristic :
    (LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation
        p)).residueCharacteristic = p := by
  let v := LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p
  let eO : ℤ_[p] ≃+* v.valuationSubring :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring p
  let eRes : IsLocalRing.ResidueField v.valuationSubring ≃+* ZMod p :=
    (IsLocalRing.ResidueField.mapEquiv eO).symm.trans
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntResidueFieldEquivZMod p)
  let : CharP (IsLocalRing.ResidueField v.valuationSubring) p :=
    charP_of_injective_ringHom (f := eRes.symm.toRingHom) eRes.symm.injective p
  change ringChar (IsLocalRing.ResidueField v.valuationSubring) = p
  exact ringChar.eq (IsLocalRing.ResidueField v.valuationSubring) p

/-- The canonical multiplicative discrete valuation sends `p` to
`exp (-1)`. -/
theorem padicDVR_valuation_p :
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p (p : ℚ_[p]) =
      WithZero.exp (-1 : ℤ) := by
  change (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p]
      (((p : ℤ_[p]) : ℚ_[p])) = WithZero.exp (-1 : ℤ)
  calc
    (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p]
        (((p : ℤ_[p]) : ℚ_[p])) =
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).intValuation (p : ℤ_[p]) := by
      simpa using
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation_of_algebraMap
          (K := ℚ_[p]) (p : ℤ_[p])
    _ = WithZero.exp (-1 : ℤ) :=
      IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p])
        (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
        PadicInt.maximalIdeal_eq_span_p

/-- The absolute ramification index of the canonical valuation on `ℚ_p` is
one. -/
theorem padicDVR_ramificationIndex_eq_one :
    LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p) = 1 := by
  let v := LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p
  have h :=
    ramificationIndexOfWithZeroValuation_intCast v
  rw [padicDVR_residueCharacteristic p, padicDVR_valuation_p p] at h
  simp only [WithZero.log_exp, neg_neg] at h
  exact_mod_cast h

/-- For odd `p`, depth one lies in the convergence range of the p-adic
logarithm and exponential. -/
theorem padicDVR_logExp_level_one_of_odd (hp2 : p ≠ 2) :
    (LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p) : ℚ) /
        (((LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation
            p)).residueCharacteristic : ℚ) - 1) <
      (1 : ℚ) := by
  rw [padicDVR_ramificationIndex_eq_one p,
    padicDVR_residueCharacteristic p]
  have hp3 : 3 ≤ p := by
    have hp2le : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    omega
  have hden : (0 : ℚ) < (p : ℚ) - 1 := by
    have hp1 : (1 : ℚ) < (p : ℚ) := by
      exact_mod_cast (Fact.out : Nat.Prime p).one_lt
    linarith
  rw [div_lt_one hden]
  have hi : (1 : ℤ) < Int.subNatNat p 1 := by
    rw [Int.subNatNat_eq_coe]
    omega
  exact_mod_cast hi

/-- For odd `p`, every positive depth lies in the convergence range of the
p-adic logarithm and exponential. -/
theorem padicDVR_logExp_level_succ_of_odd
    (hp2 : p ≠ 2) (k : ℕ) :
    (LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p) : ℚ) /
        (((LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation
            p)).residueCharacteristic : ℚ) - 1) <
      (k + 1 : ℚ) := by
  apply lt_of_lt_of_le (padicDVR_logExp_level_one_of_odd p hp2)
  exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))

/-- At a depth in the convergence range, exponential and logarithm identify
the multiplicative maximal-ideal power with the higher principal units. -/
noncomputable def expLogMulEquivOfWithZeroValuation
    {K : Type*} [Field K]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v) (n : ℕ)
    (hlevel :
      (LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation v
        : ℚ) /
          (((LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
            v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    Multiplicative
        ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
          Ideal
            (completeDVFOfWithZeroValuation v).valuationSubring) ≃*
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v) n := by
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let P :=
    chosenExpLogContinuousMulEquiv
      v hv n hlevel
  refine
    { toFun := fun a => P a
      invFun := fun u => P.symm u
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · exact P.left_inv
  · exact P.right_inv
  · exact P.map_mul

/-- The underlying field value of the exponential/logarithm equivalence is
given by the evaluated exponential series. -/
theorem expLogMulEquivOfWithZeroValuation_fieldVal
    {K : Type*} [Field K]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v) (n : ℕ)
    (hlevel :
      (LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation v
        : ℚ) /
          (((LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
            v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ))
    (a : Multiplicative
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal
          (completeDVFOfWithZeroValuation v).valuationSubring)) :
    let F :=
      completeDVFOfWithZeroValuation v
    let E := expLogMulEquivOfWithZeroValuation v hv n hlevel
    ((((E a : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n)
      : F.valuationSubringˣ) :
        F.valuationSubring) : K) =
      expSeriesFieldOfWithZeroValuation
        v (((a.toAdd : F.valuationSubring) : K))
          (fun m =>
            Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let p : ℕ :=
    (LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation v).residueCharacteristic
  let _ : Fact p.Prime := by
    dsimp [p]
    infer_instance
  simp only [expLogMulEquivOfWithZeroValuation]
  simp only [
    chosenExpLogContinuousMulEquiv,
    principalUnitExpLogContinuousMulEquivOfExactOfWithZeroValuationScaled,
    principalUnitExpLogMulEquivOfExactOfWithZeroValuationScaled]
  apply
    principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled
      (v := v) (p := p)
      (LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation v)
      n
  case hπval =>
    exact Classical.choose_spec
      (exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
        v hv)
  case hπ =>
    exact
      isUniformizer_of_valuation_eq_exp_neg_one
        v _
        (Classical.choose_spec
          (exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
            v hv))
  case hlevel => exact hlevel
  case hnval =>
    intro m
    exact
      valuation_natCast_factorial_eq_exp_neg_ramificationIndex_mul_padicValNat
        v m
  case hcomplete =>
    exact
      completeSpace_ofWithZeroValuation
        v

/-- For odd `p`, every element of `U^(k+1)` is a
`((p-1) * p^k)`-th power of an element of `U¹`. -/
theorem padicDVR_higherPrincipalUnit_degree_is_power_odd
    (hp2 : p ≠ 2) (k : ℕ) :
    let v := LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p
    let F :=
      completeDVFOfWithZeroValuation v
    ∀ u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F (k + 1),
      ∃ r : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 1,
        (r : F.valuationSubringˣ) ^ ((p - 1) * p ^ k) =
          (u : F.valuationSubringˣ) := by
  let v := LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p
  let F :=
    completeDVFOfWithZeroValuation v
  change ∀ u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F (k
    + 1),
    ∃ r : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 1,
      (r : F.valuationSubringˣ) ^ ((p - 1) * p ^ k) =
        (u : F.valuationSubringˣ)
  have hv : Function.Surjective v :=
    (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation_surjective ℚ_[p]
  let E1 := expLogMulEquivOfWithZeroValuation v hv 1
    (padicDVR_logExp_level_one_of_odd p hp2)
  let En := expLogMulEquivOfWithZeroValuation v hv (k + 1) (by
        simpa [Nat.cast_add, Nat.cast_one] using
          padicDVR_logExp_level_succ_of_odd p hp2 k)
  let eO : ℤ_[p] ≃+* F.valuationSubring :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring p
  intro u
  let a : Multiplicative (F.maximalIdeal ^ (k + 1) : Ideal F.valuationSubring) :=
    En.symm u
  let z : ℤ_[p] := eO.symm (a.toAdd : F.valuationSubring)
  have hz : z ∈ IsLocalRing.maximalIdeal ℤ_[p] ^ (k + 1) := by
    apply (ringEquiv_mem_maximalIdeal_pow_iff eO (k + 1) z).1
    simp [z]
  obtain ⟨b, hb, hdb⟩ :=
    padicInt_exists_degree_root_of_mem_maximalIdeal_pow_succ p k z hz
  have hbO : eO b ∈ F.maximalIdeal := by
    rw [← pow_one F.maximalIdeal]
    exact (ringEquiv_mem_maximalIdeal_pow_iff eO 1 b).2 (by simpa using hb)
  let b1 : (F.maximalIdeal ^ 1 : Ideal F.valuationSubring) :=
    ⟨eO b, by simpa using hbO⟩
  have hdbO : ((p - 1) * p ^ k) • (eO b) = (a.toAdd : F.valuationSubring) := by
    rw [← map_nsmul eO ((p - 1) * p ^ k) b, hdb]
    simp [z]
  let r : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 1 := E1
    (Multiplicative.ofAdd b1)
  refine ⟨r, ?_⟩
  have hua : En a = u := En.apply_symm_apply u
  have hrpow :
      r ^ ((p - 1) * p ^ k) =
        E1 ((Multiplicative.ofAdd b1) ^ ((p - 1) * p ^ k)) := by
    change E1 (Multiplicative.ofAdd b1) ^ ((p - 1) * p ^ k) =
      E1 ((Multiplicative.ofAdd b1) ^ ((p - 1) * p ^ k))
    exact (map_pow E1 (Multiplicative.ofAdd b1) ((p - 1) * p ^ k)).symm
  change ((r ^ ((p - 1) * p ^ k) :
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 1) :
      F.valuationSubringˣ) = (u : F.valuationSubringˣ)
  rw [hrpow, ← hua]
  apply Units.ext
  apply Subtype.ext
  have hleft := expLogMulEquivOfWithZeroValuation_fieldVal v hv 1
    (padicDVR_logExp_level_one_of_odd p hp2)
    ((Multiplicative.ofAdd b1) ^ ((p - 1) * p ^ k))
  have hright := expLogMulEquivOfWithZeroValuation_fieldVal v hv (k + 1)
    (by
      simpa [Nat.cast_add, Nat.cast_one] using
        padicDVR_logExp_level_succ_of_odd p hp2 k) a
  have hleft' :
      ((((E1 ((Multiplicative.ofAdd b1) ^ ((p - 1) * p ^ k)) :
          LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 1) :
            F.valuationSubringˣ) :
          F.valuationSubring) : ℚ_[p]) =
        expSeriesFieldOfWithZeroValuation
          v ((((Multiplicative.ofAdd b1) ^ ((p - 1) * p ^ k)).toAdd :
            F.valuationSubring) : ℚ_[p])
            (fun m =>
              Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)) := by
    exact hleft
  have hright' :
      ((((En a : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F
        (k + 1)) : F.valuationSubringˣ) :
          F.valuationSubring) : ℚ_[p]) =
        expSeriesFieldOfWithZeroValuation
          v ((a.toAdd : F.valuationSubring) : ℚ_[p])
            (fun m =>
              Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)) := by
    exact hright
  rw [hleft', hright']
  congr 2

end LocalFieldTheory.Padic

end
