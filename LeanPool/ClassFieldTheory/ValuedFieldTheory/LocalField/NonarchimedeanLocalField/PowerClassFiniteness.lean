/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedIntegerValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitStructure
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicPowerIndex
/-!
# Finiteness of local power-class groups

The multiplicative power-class group `Kˣ / Kˣⁿ` of a nonarchimedean local
field is finite whenever `n` is nonzero in `K`.  This is the finiteness input
for maximal Kummer extensions and the characteristic-zero local existence
theorem.
-/

@[expose] public section

open _root_.LocalFieldTheory.DiscreteValuationField.LocalField renaming
  chosenFirstPrincipalUnitStructureEqualCharacteristic →
    chosenFirstPrincipalUnitStructureEqualCharacteristic

open _root_.LocalFieldTheory.DiscreteValuationField.LocalField renaming
  chosenMixedFirstPrincipalUnitStructureOfWithZeroValuation →
    chosenMixedFirstPrincipalUnitStructureOfWithZeroValuation

open _root_.LocalFieldTheory.DiscreteValuationField renaming
  finite_fieldUnits_nthPowerQuotient_of_finite_principalUnits →
    finite_fieldUnits_nthPowerQuotient_of_finite_principalUnits


noncomputable section

namespace LocalFieldTheory

open scoped ValuativeRel
open LocalFieldTheory.DiscreteValuationField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The local power-class group is finite whenever the exponent is nonzero
in the field. -/
theorem finite_nthPowerQuotient_of_natCast_ne_zero
    (n : ℕ) (hnK : (n : K) ≠ 0) :
    Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) := by
  have hn : n ≠ 0 := by
    intro hn
    apply hnK
    simp [hn]
  let : NeZero n := ⟨hn⟩
  let v := localIntegerValuation K
  let F : LocalFieldTheory.DiscreteValuationField.LocalField K :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation v
  rcases CharP.exists' K with hcharZero | ⟨p, hp, hcharP⟩
  · let : CharZero K := hcharZero
    let :
        LocalFieldTheory.DiscreteValuationField.LocalField.MixedWithZeroValuationContext v :=
      LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContext v
    let d := Module.finrank ℚ_[F.residueCharacteristic] K
    obtain ⟨a, e⟩ :=
      chosenMixedFirstPrincipalUnitStructureOfWithZeroValuation
        v (localIntegerValuation_surjective K)
    let U1 :=
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        F.toCompleteDVF 1
    let A :=
      ZMod (F.residueCharacteristic ^ a) ×
        (Fin d → ℤ_[F.residueCharacteristic])
    let : Finite (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) := by
      infer_instance
    let emul : U1 ≃* Multiplicative A := by
      letI valuedK : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      letI : TopologicalSpace K := valuedK.toTopologicalSpace
      exact e.symm.toMulEquiv
    let : Finite (U1 ⧸ (powMonoidHom n : U1 →* U1).range) :=
      LocalFieldTheory.finite_nthPowerQuotient_of_mulEquiv U1 (Multiplicative A) n
        emul
    let hex := F.toCompleteDVF.exists_uniformizer
    let π := Classical.choose hex
    have hπ :
        F.toCompleteDVF.valuation.IsUniformizer (π : K) :=
      Classical.choose_spec hex
    exact
      finite_fieldUnits_nthPowerQuotient_of_finite_principalUnits
        F.toCompleteDVF hπ n
  · let : CharP K p := hcharP
    have hpne : p ≠ 0 := hp.out.ne_zero
    have hres : F.residueCharacteristic = p :=
      F.residueCharacteristic_eq_of_charP p hpne
    let : CharP K F.residueCharacteristic := by
      rw [hres]
      infer_instance
    have hpn : ¬ F.residueCharacteristic ∣ n := by
      intro hdiv
      apply hnK
      exact (CharP.cast_eq_zero_iff K F.residueCharacteristic n).2 hdiv
    let : Fact (Nat.Coprime n F.residueCharacteristic) :=
      ⟨(F.residueCharacteristic_prime.coprime_iff_not_dvd.mpr hpn).symm⟩
    let valuedK : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    let e :=
      chosenFirstPrincipalUnitStructureEqualCharacteristic
        v
    let U1 :=
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        F.toCompleteDVF 1
    let A := ℕ → ℤ_[F.residueCharacteristic]
    let : Finite (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) := by
      infer_instance
    let emul : U1 ≃* Multiplicative A := by
      letI : TopologicalSpace K := valuedK.toTopologicalSpace
      exact e.symm.toMulEquiv
    let : Finite (U1 ⧸ (powMonoidHom n : U1 →* U1).range) :=
      LocalFieldTheory.finite_nthPowerQuotient_of_mulEquiv U1 (Multiplicative A) n
        emul
    let hex := F.toCompleteDVF.exists_uniformizer
    let π := Classical.choose hex
    have hπ :
        F.toCompleteDVF.valuation.IsUniformizer (π : K) :=
      Classical.choose_spec hex
    exact
      finite_fieldUnits_nthPowerQuotient_of_finite_principalUnits
        F.toCompleteDVF hπ n

end LocalFieldTheory

end
