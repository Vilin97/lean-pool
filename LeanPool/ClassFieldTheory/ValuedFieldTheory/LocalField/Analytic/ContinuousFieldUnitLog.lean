/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.DenominatorValuation
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.FieldUnitLogUniqueness
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpAdditivity
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.FieldUnitLogExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.WithZeroValuationTopology
/-!
# The local-field logarithm

This file packages the ramification-scaled principal-unit logarithm as a
continuous homomorphism and extends it to field units with the unique
uniformizer value forced by `log p = 0`.
-/

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  mem_zeroSubgroup_iff_exists_valuationSubringUnitFieldUnitHom_eq →
    mem_zeroSubgroup_iff_exists_valuationSubringUnitFieldUnitHom_eq

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  valuationSubringUnitFieldUnitHom →
    valuationSubringUnitFieldUnitHom

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF renaming
  multiplicativeIntegerValuationOfUniformizer →
    multiplicativeIntegerValuationOfUniformizer

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF renaming
  multiplicativeIntegerValuationOfUniformizer_isUniformizer →
    multiplicativeIntegerValuationOfUniformizer_isUniformizer

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF renaming
  multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup →
    multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF renaming
  uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit →
    uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit


noncomputable section

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

open Filter
open scoped Topology

variable {K : Type u} [Field K]

/-- The ramification-scaled logarithm homomorphism on first principal units is
continuous.  Near the identity its valuation agrees with that of `u - 1`,
because one may restrict to an arbitrarily deep ball above `e/(p-1)`. -/
theorem continuous_principalUnitLogSeriesHomOfWithZeroValuationScaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e : ℕ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Continuous
      (principalUnitLogSeriesHomOfWithZeroValuationScaled
        (v := v) (p := p) e hnK hnval hcomplete) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K :=
    completeDVFOfWithZeroValuation v
  have hMulSubring :
      Continuous (fun z : F.valuationSubring × F.valuationSubring =>
        z.1 * z.2) := by
    apply Continuous.subtype_mk
    exact
      (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)
  let : ContinuousMul F.valuationSubring := ⟨hMulSubring⟩
  have hInv :
      Continuous (fun u : F.valuationSubringˣ => u⁻¹) := by
    rw [Units.continuous_iff]
    constructor
    · change Continuous (fun u : F.valuationSubringˣ =>
        ((u⁻¹ : F.valuationSubringˣ) : F.valuationSubring))
      exact Units.continuous_coe_inv
    · simpa using (Units.continuous_val :
        Continuous (fun u : F.valuationSubringˣ =>
          (u : F.valuationSubring)))
  have hMul :
      Continuous (fun z : F.valuationSubringˣ × F.valuationSubringˣ =>
        z.1 * z.2) := by
    rw [Units.continuous_iff]
    constructor
    · exact
        (Units.continuous_val.comp continuous_fst).mul
          (Units.continuous_val.comp continuous_snd)
    · change Continuous (fun z : F.valuationSubringˣ × F.valuationSubringˣ =>
        (((z.1 * z.2)⁻¹ : F.valuationSubringˣ) : F.valuationSubring))
      have hc : Continuous
          (fun z : F.valuationSubringˣ × F.valuationSubringˣ =>
            ((z.1⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
              ((z.2⁻¹ : F.valuationSubringˣ) : F.valuationSubring)) :=
        (Units.continuous_coe_inv.comp continuous_fst).mul
          (Units.continuous_coe_inv.comp continuous_snd)
      simpa [Units.val_inv_eq_inv_val, mul_comm] using hc
  let : ContinuousMul F.valuationSubringˣ := ⟨hMul⟩
  let : ContinuousInv F.valuationSubringˣ := ⟨hInv⟩
  have : IsTopologicalGroup F.valuationSubringˣ := by infer_instance
  have : IsTopologicalGroup
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) := by
    infer_instance
  let φ :=
    principalUnitLogSeriesHomOfWithZeroValuationScaled
      (v := v) (p := p) e hnK hnval hcomplete
  apply continuous_of_continuousAt_one φ
  dsimp [φ, principalUnitLogSeriesHomOfWithZeroValuationScaled]
  rw [ContinuousAt]
  suffices hlog :
    Tendsto
      (fun u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) 1 =>
        principalUnitLogSeriesOfWithZeroValuation v u hnK)
      (𝓝 1) (𝓝 0) by
    rw [principalUnitLogSeries_one_ofWithZeroValuation v hnK]
    change Tendsto
      (fun u => Multiplicative.ofAdd
        (principalUnitLogSeriesOfWithZeroValuation v u hnK))
      (𝓝 1) (𝓝 (Multiplicative.ofAdd (0 : K)))
    exact (continuous_ofAdd.tendsto (0 : K)).comp hlog
  rw [(Valued.hasBasis_nhds_zero K
    (WithZero (Multiplicative ℤ))).tendsto_right_iff]
  intro γ _
  let γ' : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := (.ofClass v))) γ
  obtain ⟨N₀, hN₀γ⟩ :=
    WithZero.exists_exp_neg_natCast_lt γ'.ne_zero
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ,
      (e : ℚ) / ((p : ℚ) - 1) < (N₁ : ℚ) :=
    exists_nat_gt ((e : ℚ) / ((p : ℚ) - 1))
  let N := max N₀ N₁
  have hNγ : WithZero.exp (-(N : ℤ)) <
      (γ' : WithZero (Multiplicative ℤ)) := by
    exact lt_of_le_of_lt
      (by
        apply WithZero.exp_le_exp.mpr
        simp only [neg_le_neg_iff]
        exact_mod_cast Nat.le_max_left N₀ N₁)
      hN₀γ
  have hNth :
      (e : ℚ) / ((p : ℚ) - 1) < (N : ℚ) :=
    lt_of_lt_of_le hN₁ (by exact_mod_cast Nat.le_max_right N₀ N₁)
  have hsubContinuous :
      Continuous
        (fun u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          (completeDVFOfWithZeroValuation v)) 1 =>
          principalUnitSubOneOfWithZeroValuation v u) := by
    unfold principalUnitSubOneOfWithZeroValuation
    fun_prop
  have hball :
      {x : K | v x < WithZero.exp (-(N : ℤ))} ∈ 𝓝 (0 : K) := by
    let g : (WithZero (Multiplicative ℤ))ˣ :=
      Valuation.IsRankOneDiscrete.generator v
    have hg : (g : WithZero (Multiplicative ℤ)) < 1 := by
      exact Valuation.IsRankOneDiscrete.generator_lt_one v
    let a : ℤ := WithZero.log (g : WithZero (Multiplicative ℤ))
    have ha : a ≤ -1 := by
      have ha0 : a < 0 := by
        have hlog := (WithZero.log_lt_log (Units.ne_zero g)
          (one_ne_zero : (1 : WithZero (Multiplicative ℤ)) ≠ 0)).2 hg
        simpa [a] using hlog
      omega
    let m := N + 1
    have hm :
        (g : WithZero (Multiplicative ℤ)) ^ m <
          WithZero.exp (-(N : ℤ)) := by
      rw [show m = N + 1 by rfl, ← WithZero.exp_log (Units.ne_zero g),
        ← WithZero.exp_nsmul, WithZero.exp_lt_exp]
      change ((N + 1 : ℕ) : ℤ) * a < -(N : ℤ)
      calc
        ((N + 1 : ℕ) : ℤ) * a ≤ ((N + 1 : ℕ) : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left ha (by omega)
        _ < -(N : ℤ) := by omega
    rcases Valuation.IsRankOneDiscrete.generator_mem_range K v with ⟨z, hz⟩
    have hz0 : z ≠ 0 := (Valuation.ne_zero_iff v).mp (by
      rw [hz]
      exact Units.ne_zero g)
    have hzm0 : z ^ m ≠ 0 := pow_ne_zero m hz0
    rw [Valued.mem_nhds_zero]
    refine ⟨Units.mk0 (v.restrict (z ^ m))
      ((Valuation.ne_zero_iff v.restrict).2 hzm0), ?_⟩
    intro x hx
    change v.restrict x < v.restrict (z ^ m) at hx
    have hx' : v x < v (z ^ m) := v.restrict_lt_iff.mp hx
    exact hx'.trans (by simpa [v.map_pow, hz] using hm)
  have hpre :
      {u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) 1 |
        v (principalUnitSubOneOfWithZeroValuation v u) <
          WithZero.exp (-(N : ℤ))} ∈ 𝓝 1 := by
    have hballOne :
        {x : K | v x < WithZero.exp (-(N : ℤ))} ∈
          𝓝 (principalUnitSubOneOfWithZeroValuation v
            (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
              (completeDVFOfWithZeroValuation v)) 1)) := by
      simpa using hball
    have ht := (hsubContinuous.tendsto
      (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v)) 1)) hballOne
    exact ht
  refine Filter.mem_of_superset hpre ?_
  intro u hu
  change
    v.restrict (principalUnitLogSeriesOfWithZeroValuation v u hnK) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  let x := principalUnitSubOneOfWithZeroValuation v u
  by_cases hx : x = 0
  · have hlog : principalUnitLogSeriesOfWithZeroValuation v u hnK = 0 := by
      simp [principalUnitLogSeriesOfWithZeroValuation, x, hx]
    rw [hlog, v.map_zero]
    exact zero_lt_iff.mpr
      (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
  · have hxv_ne : v x ≠ 0 := (_root_.Valuation.ne_zero_iff v).2 hx
    have hloglt : WithZero.log (v x) < -(N : ℤ) := by
      exact
        (WithZero.log_lt_log hxv_ne
          (WithZero.exp_ne_zero (a := -(N : ℤ)))).2 (by simpa [x] using hu)
    have hvalN :
        (N : ℤ) < (ofWithZeroValuation v).val (Units.mk0 x hx) := by
      change (N : ℤ) < -WithZero.log (v x)
      linarith
    have hthreshold :
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) :=
      lt_of_lt_of_le hNth (by exact_mod_cast hvalN.le)
    have hvx : v x < (1 : WithZero (Multiplicative ℤ)) :=
      principalUnitSubOne_val_lt_one_ofWithZeroValuation v u
    have hval :=
      valuation_logOnePlusSeriesField_eq_self_of_scaled_inv_sub_one_lt
        (v := v) (p := p) e (x := x) hx hnK hnval hvx hthreshold hcomplete
    rw [principalUnitLogSeriesOfWithZeroValuation, hval]
    exact lt_trans (by simpa [x] using hu) (by simpa [γ'] using hNγ)

/-- The residue characteristic has a nonzero uniformizer exponent.  This is
the algebraic point that makes the normalization `log p = 0` determine the
uniformizer value in the field-unit logarithm theorem. -/
theorem uniformizerValueExponent_residueCharacteristic_ne_zero
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    {π : (LocalField.ofWithZeroValuation v).valuationSubring}
    (hπ : (LocalField.ofWithZeroValuation v).toCompleteDVF.valuation.IsUniformizer
      (π : K)) :
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent
      (LocalField.ofWithZeroValuation v).toCompleteDVF) hπ
        (Units.mk0
          ((LocalField.ofWithZeroValuation v).residueCharacteristic : K)
          (LocalField.ofWithZeroValuation v).natCast_residueCharacteristic_ne_zero_of_charZero)
            ≠ 0 := by
  let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
  let pUnit : Kˣ :=
    Units.mk0 (F.residueCharacteristic : K)
      F.natCast_residueCharacteristic_ne_zero_of_charZero
  intro hm
  have hvalue :=
    (uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F.toCompleteDVF)
      hπ pUnit
  rw [hm, zpow_zero] at hvalue
  have hvalue' :=
    congrArg (fun γ : F.toCompleteDVF.ValueGroupˣ =>
      (γ : F.toCompleteDVF.ValueGroup)) hvalue
  have hpone : F.toCompleteDVF.valuation (F.residueCharacteristic : K) = 1 := by
    simpa [CompleteDVF.fieldUnitValueUnit, pUnit] using hvalue'.symm
  exact (ne_of_lt F.valuation_natCast_residueCharacteristic_lt_one) hpone

open CompleteDVF.higherPrincipalUnitGroup renaming
  fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF →
    fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF in
open CompleteDVF.higherPrincipalUnitGroup renaming
  fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply →
    fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply in
/-- Uniqueness of the corrected extension: agreement on first principal
units together with vanishing on one field unit of nonzero uniformizer
exponent determines the logarithm on all field units. -/
theorem fieldUnitLogHomWithUniformizerValue_unique_of_killing
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF K) [Finite F.residueField] [CharZero K]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      Multiplicative K) (a : Kˣ)
    (ha : (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent
      F) hπ a ≠ 0)
    (ψ : Kˣ →* Multiplicative K)
    (hψprincipal : ∀ u :
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1,
      ψ (valuationSubringUnitFieldUnitHom F
          (u : F.valuationSubringˣ)) = φ u)
    (hψa : ψ a = 1) :
    ψ = fieldUnitLogHomWithUniformizerValue F
      (fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
        F hπ) φ
      (uniformizerLogValueKilling F
        (fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
          F hπ) φ a) := by
  let d :=
    fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
      F hπ
  let L := fieldUnitLogHomWithUniformizerValue F d φ
    (uniformizerLogValueKilling F d φ a)
  let ϖ : Kˣ := Units.mk0 (π : K) hπ.ne_zero
  let z := d.symm a
  let m : ℤ := Multiplicative.toAdd z.2
  have hm : m ≠ 0 := by
    simpa [m, z, d] using ha
  have hLa : L a = 1 := by
    exact fieldUnitLogHomWithUniformizerValue_uniformizerLogValueKilling
      F d φ a hm
  have hψformula :
      Multiplicative.toAdd (ψ a) =
        Multiplicative.toAdd (φ z.1.2) +
          m • Multiplicative.toAdd (ψ ϖ) := by
    have hdecomp : d z = a := d.apply_symm_apply a
    rw [← hdecomp]
    rw [fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply]
    rw [ψ.map_mul, ψ.map_mul, ψ.map_zpow]
    rw [toAdd_mul, toAdd_mul, toAdd_zpow]
    rw [monoidHom_toMultiplicative_residueRoot_eq_one (K := K) F ψ z.1.1]
    rw [hψprincipal z.1.2]
    simp [ϖ, m]
  have hLformula :
      Multiplicative.toAdd (L a) =
        Multiplicative.toAdd (φ z.1.2) +
          m • Multiplicative.toAdd (L ϖ) := by
    have hdecomp : d z = a := d.apply_symm_apply a
    rw [← hdecomp]
    rw [fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply]
    rw [L.map_mul, L.map_mul, L.map_zpow]
    rw [toAdd_mul, toAdd_mul, toAdd_zpow]
    have hLprincipal :
        L (valuationSubringUnitFieldUnitHom F
            (z.1.2 : F.valuationSubringˣ)) = φ z.1.2 := by
      simpa [L, d] using
        fieldUnitLogHomWithUniformizerValue_eq_of_completeDVF_principal
          F hπ φ (uniformizerLogValueKilling F d φ a) z.1.2
    rw [monoidHom_toMultiplicative_residueRoot_eq_one (K := K) F L z.1.1]
    rw [hLprincipal]
    simp [ϖ, m]
  have hpow :
      m • Multiplicative.toAdd (ψ ϖ) =
        m • Multiplicative.toAdd (L ϖ) := by
    rw [hψa] at hψformula
    rw [hLa] at hLformula
    simpa only [toAdd_one] using
      add_left_cancel (hψformula.symm.trans hLformula)
  have hϖ : ψ ϖ = L ϖ := by
    apply Multiplicative.toAdd.injective
    exact zsmul_right_injective hm hpow
  apply monoidHom_toMultiplicative_ext_of_agree_principalUnits_and_uniformizer
    F ((multiplicativeIntegerValuationOfUniformizer F) hπ)
  · intro y
    exact
      mem_zeroSubgroup_iff_exists_valuationSubringUnitFieldUnitHom_eq
        (F := F)
          ((multiplicativeIntegerValuationOfUniformizer F) hπ)
        ((multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup F) hπ)
        y
  · exact
      (multiplicativeIntegerValuationOfUniformizer_isUniformizer F) hπ
  · intro u
    rw [hψprincipal u]
    simpa [L, d] using
      (fieldUnitLogHomWithUniformizerValue_eq_of_completeDVF_principal
        F hπ φ (uniformizerLogValueKilling F d φ a) u).symm
  · exact hϖ

open CompleteDVF.higherPrincipalUnitGroup renaming
  fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF →
    fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF in
open CompleteDVF.higherPrincipalUnitGroup renaming
  continuous_fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_mrangeRestrict →
    continuous_rootsPrincipalUnitsUniformizer_symm in
/-- The inverse of the uniformizer–residue–principal-unit decomposition field-unit decomposition
is continuous
also for the topology defined directly by a standard `ℤᵐ⁰`-valued valuation.
The proof transports the already established range-restricted result across
the equality of uniform structures. -/
theorem continuous_fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K)) :
    let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K :=
      completeDVFOfWithZeroValuation v
    letI : Finite F.residueField := by
      change Finite (IsLocalRing.ResidueField v.valuationSubring)
      infer_instance
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Continuous
      (fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
        F hπ).symm := by
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K :=
    completeDVFOfWithZeroValuation v
  let direct : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let restricted : Valued K
      (MonoidHom.mrange v.toMonoidWithZeroHom) :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have huniform :
      (Valued.mk' v).toUniformSpace =
        (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued
          F).toUniformSpace := by
    change (Valued.mk' v).toUniformSpace =
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued
        (WithZeroValuationTopology.completeDVF v)).toUniformSpace
    exact WithZeroValuationTopology.valuedMk_uniformSpace_eq_mrangeRestrict v
  have : Finite F.residueField := by
    change Finite (IsLocalRing.ResidueField v.valuationSubring)
    infer_instance
  let hcontinuousRestricted :=
    letI : Valued K
        (MonoidHom.mrange v.toMonoidWithZeroHom) := restricted
    continuous_rootsPrincipalUnitsUniformizer_symm
      F hπ
  have htop : direct.toTopologicalSpace = restricted.toTopologicalSpace := by
    exact congrArg (fun U : UniformSpace K => U.toTopologicalSpace) huniform
  let unitsTopology (t : TopologicalSpace K) : TopologicalSpace Kˣ :=
    letI : TopologicalSpace K := t
    inferInstance
  let factorsTopology (t : TopologicalSpace K) :
      TopologicalSpace
        (CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F) :=
    letI : TopologicalSpace K := t
    inferInstance
  have hdom :
      unitsTopology direct.toTopologicalSpace =
        unitsTopology restricted.toTopologicalSpace :=
    congrArg unitsTopology htop
  have hcod :
      factorsTopology direct.toTopologicalSpace =
        factorsTopology restricted.toTopologicalSpace :=
    congrArg factorsTopology htop
  let : Valued K (WithZero (Multiplicative ℤ)) := direct
  change @Continuous Kˣ
    (CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F)
    (unitsTopology direct.toTopologicalSpace)
    (factorsTopology direct.toTopologicalSpace)
    (fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
      F hπ).symm
  rw [hdom, hcod]
  exact hcontinuousRestricted

open CompleteDVF.higherPrincipalUnitGroup renaming
  fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF →
    fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF in
/-- The local-field structure theory, the field-unit logarithm theorem.  For a
mixed-characteristic local
field presented by a complete discrete `ℤᵐ⁰`-valued valuation, there is a
unique continuous additive logarithm on `Kˣ` which kills the residue
characteristic and restricts on `U¹` to the convergent logarithm series. -/
theorem existsUnique_continuous_log
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K] :
    let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
    let pUnit : Kˣ :=
      Units.mk0 (F.residueCharacteristic : K)
        F.natCast_residueCharacteristic_ne_zero_of_charZero
    let hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0) :=
      fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ∃! L : Kˣ →* Multiplicative K,
      Continuous L ∧
      L pUnit = 1 ∧
      ∀ u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        F.toCompleteDVF) 1,
        Multiplicative.toAdd
            (L (valuationSubringUnitFieldUnitHom
              F.toCompleteDVF (u : F.toCompleteDVF.valuationSubringˣ))) =
          principalUnitLogSeriesOfWithZeroValuation v u hnK := by
  let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
  let p : ℕ := F.residueCharacteristic
  let e : ℕ := LocalField.ramificationIndexOfWithZeroValuation v
  let pUnit : Kˣ :=
    Units.mk0 (F.residueCharacteristic : K)
      F.natCast_residueCharacteristic_ne_zero_of_charZero
  let hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0) :=
    fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  let hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))) := by
    intro n
    simpa [F, p, e] using
      LocalField.valuation_natCast_succ_eq_exp_neg_ramificationIndex_mul_padicValNat
        v n
  have hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K :=
    WithZeroValuationTopology.completeSpace_ofWithZeroValuation v
  let : Fact p.Prime := by
    dsimp [p, F]
    infer_instance
  let φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
    F.toCompleteDVF) 1 →* Multiplicative K :=
    principalUnitLogSeriesHomOfWithZeroValuationScaled
      (v := v) (p := p) e hnK hnval hcomplete
  have hφ :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      Continuous φ := by
    convert
      continuous_principalUnitLogSeriesHomOfWithZeroValuationScaled
        (v := v) (p := p) e hnK hnval hcomplete using 1
    all_goals rfl
  rcases F.exists_uniformizer with ⟨π, hπ⟩
  let d :=
    fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
      F.toCompleteDVF hπ
  let c : K := uniformizerLogValueKilling F.toCompleteDVF d φ pUnit
  let L : Kˣ →* Multiplicative K :=
    fieldUnitLogHomWithUniformizerValue F.toCompleteDVF d φ c
  have hpExponent :
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent
        F.toCompleteDVF) hπ pUnit ≠ 0 := by
    simpa [F, pUnit] using
      uniformizerValueExponent_residueCharacteristic_ne_zero v hπ
  have hLp : L pUnit = 1 := by
    simpa [L, c] using
      fieldUnitLogHomWithUniformizerValue_uniformizerLogValueKilling
        F.toCompleteDVF d φ pUnit (by simpa [d] using hpExponent)
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hd : Continuous d.symm := by
    convert
      continuous_fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_ofWithZeroValuation
        v hπ using 1
    all_goals rfl
  have hL : Continuous L := by
    exact
      (continuous_fieldUnitDecompositionLogHomWithUniformizerValue
        F.toCompleteDVF φ c hφ).comp hd
  have hLprincipal : ∀ u :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
    F.toCompleteDVF) 1,
      Multiplicative.toAdd
          (L (valuationSubringUnitFieldUnitHom
            F.toCompleteDVF (u : F.toCompleteDVF.valuationSubringˣ))) =
        principalUnitLogSeriesOfWithZeroValuation v u hnK := by
    intro u
    have hu :=
      fieldUnitLogHomWithUniformizerValue_eq_of_completeDVF_principal
        F.toCompleteDVF hπ φ c u
    rw [show L = fieldUnitLogHomWithUniformizerValue F.toCompleteDVF d φ c from rfl]
    rw [show d =
      fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
        F.toCompleteDVF hπ from rfl]
    rw [hu]
    exact
      principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd
        (v := v) (p := p) e hnK hnval hcomplete u
  refine ⟨L, ⟨hL, hLp, hLprincipal⟩, ?_⟩
  intro ψ hψ
  apply fieldUnitLogHomWithUniformizerValue_unique_of_killing
    F.toCompleteDVF hπ φ pUnit hpExponent ψ
  · intro u
    apply Multiplicative.toAdd.injective
    calc
      Multiplicative.toAdd
          (ψ (valuationSubringUnitFieldUnitHom
            F.toCompleteDVF (u : F.toCompleteDVF.valuationSubringˣ))) =
          principalUnitLogSeriesOfWithZeroValuation v u hnK := hψ.2.2 u
      _ = Multiplicative.toAdd (φ u) := by
        symm
        exact
          principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd
            (v := v) (p := p) e hnK hnval hcomplete u
  · exact hψ.2.1

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField
