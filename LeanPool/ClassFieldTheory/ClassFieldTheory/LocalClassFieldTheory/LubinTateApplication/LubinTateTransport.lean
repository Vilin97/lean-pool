/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Algebra.CharP.Subring
public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentUniformizerNormalization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.NormSubgroup
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.LocalRingEquiv
/-!
# Lubin--Tate application: transport to an equal-characteristic local field

The reusable Lubin--Tate calculation is carried out over the standard
Laurent-series model.  This application-layer file transports its exact
norm-subgroup result to an arbitrary equal-characteristic local field.  The
chosen field equivalence sends the inverse Laurent parameter to the prescribed
positive uniformizer, controls the required principal-unit filtration, and
transports both the finite Galois structure and the actual field-norm subgroup.
-/

@[expose] public section

noncomputable
section

open scoped LaurentSeries PowerSeries ValuativeRel

namespace LubinTate
namespace EqualCharacteristic

open LocalClassFieldTheory

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

open CompleteDVF.higherPrincipalUnitGroup renaming
  residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank →
    residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank in
/-- The positive residue-field degree used by the equal-characteristic
Laurent-series model. -/
noncomputable def equalCharacteristicResidueRank
    {L : Type} [Field L] (F : LocalField L) : ℕ+ :=
  ⟨CompleteDVF.higherPrincipalUnitGroup.iwasawaResidueRank F,
    Nat.pos_of_ne_zero fun hrank => by
      have hcard :=
        residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank
          F
      rw [hrank, pow_zero] at hcard
      exact
        (Finite.one_lt_card : 1 < Nat.card F.residueField).ne' hcard⟩

open CompleteDVF.higherPrincipalUnitGroup renaming
  residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank →
    residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank in
theorem equalCharacteristicResidueCard
    {L : Type} [Field L] (F : LocalField L) :
    Nat.card F.residueField =
      F.residueCharacteristic ^
        (equalCharacteristicResidueRank F : ℕ) := by
  simpa [equalCharacteristicResidueRank] using
    residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank F

/-! ## The prescribed prime element in the target local field -/

/-- The canonical complete-DVF package attached to the target local field. -/
noncomputable def equalCharacteristicTargetLocalField :
    LocalField K := by
  exact
    { toCompleteDVF := LocalFieldTheory.localCompleteDVF K
      residueFinite := by
        change Finite 𝓀[K]
        infer_instance }

/-- The target local-field package uses the canonical valuative relation on
the underlying field. -/
theorem equalCharacteristicTargetLocalField_valuation_eq :
    (equalCharacteristicTargetLocalField K).valuation =
      ValuativeRel.valuation K := by
  unfold equalCharacteristicTargetLocalField
  unfold LocalFieldTheory.localCompleteDVF
  unfold ValuationTheory.Valuations.completeDVFOfCompleteValuedField
  rfl

/-- The target valuation ring and the valuation ring in the chosen
complete-DVF package are the same subring of the field. -/
noncomputable def equalCharacteristicTargetIntegerEquiv :
    𝒪[K] ≃+* (equalCharacteristicTargetLocalField K).valuationSubring where
  toFun x := ⟨x, by
    have hx := x.property
    change ValuativeRel.valuation K (x : K) ≤ 1 at hx
    change (equalCharacteristicTargetLocalField K).valuation (x : K) ≤ 1
    rw [equalCharacteristicTargetLocalField_valuation_eq]
    exact hx⟩
  invFun x := ⟨x, by
    have hx := x.property
    change (equalCharacteristicTargetLocalField K).valuation (x : K) ≤ 1 at hx
    rw [equalCharacteristicTargetLocalField_valuation_eq] at hx
    change ValuativeRel.valuation K (x : K) ≤ 1
    exact hx⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_mul' := fun _ _ => rfl

/-- The integer-ring equivalence preserves the underlying field element. -/
@[simp]
theorem equalCharacteristicTargetIntegerEquiv_apply_coe (x : 𝒪[K]) :
    (((equalCharacteristicTargetIntegerEquiv K x :
      (equalCharacteristicTargetLocalField K).valuationSubring)) : K) =
      (x : K) := by
  rfl

/-- The inverse integer-ring equivalence preserves the underlying field element. -/
@[simp]
theorem equalCharacteristicTargetIntegerEquiv_symm_apply_coe
    (x : (equalCharacteristicTargetLocalField K).valuationSubring) :
    ((((equalCharacteristicTargetIntegerEquiv K).symm x : 𝒪[K])) : K) =
      (x : K) := by
  rfl

/-- The residue characteristic in the canonical local-field package is the
given positive characteristic. -/
theorem equalCharacteristicTargetResidueCharacteristicCharP
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    CharP K (equalCharacteristicTargetLocalField K).residueCharacteristic := by
  let F := equalCharacteristicTargetLocalField K
  have hres : F.residueCharacteristic = p :=
    F.residueCharacteristic_eq_of_charP p
      ((Fact.out : Nat.Prime p).ne_zero)
  rw [hres]
  infer_instance

private theorem equalCharacteristicUniformizerRatio_valuationMap
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    valuationMap K
        (Additive.ofMul
          (ϖ / inverseIntegerRingUniformizerFieldUnit K)) = 0 := by
  have hcanonical :
      valuationMap K
        (Additive.ofMul (inverseIntegerRingUniformizerFieldUnit K)) = 1 := by
    rw [valuationMap_apply]
    exact v_inverseIntegerRingUniformizerFieldUnit K
  rw [valuationMap_ofMul_div, hϖ, hcanonical, sub_self]

/-- The unit by which the canonical prime element must be changed in order
to obtain the inverse of the prescribed positive uniformizer. -/
noncomputable def equalCharacteristicUniformizerRatioIntegerUnit
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    𝒪[K]ˣ :=
  integerUnitOfValuationMapZero K
    (ϖ / inverseIntegerRingUniformizerFieldUnit K)
    (equalCharacteristicUniformizerRatio_valuationMap K ϖ hϖ)

/-- The uniformizer-ratio integer unit maps to the prescribed ratio of field units. -/
@[simp]
theorem integerUnitsToFieldUnits_equalCharacteristicUniformizerRatioIntegerUnit
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    integerUnitsToFieldUnits K
        (equalCharacteristicUniformizerRatioIntegerUnit K ϖ hϖ) =
      ϖ / inverseIntegerRingUniformizerFieldUnit K :=
  integerUnitOfValuationMapZero_spec K
    (ϖ / inverseIntegerRingUniformizerFieldUnit K)
    (equalCharacteristicUniformizerRatio_valuationMap K ϖ hϖ)

/-- A prime element of the target integer ring whose inverse in the field is
the prescribed positive uniformizer. -/
noncomputable def equalCharacteristicTargetUniformizerInteger
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) : 𝒪[K] :=
  chosenIntegerRingUniformizer K *
    ((equalCharacteristicUniformizerRatioIntegerUnit K ϖ hϖ)⁻¹ : 𝒪[K]ˣ)

/-- The adjusted prime element in the target integer ring is irreducible. -/
theorem equalCharacteristicTargetUniformizerInteger_irreducible
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    Irreducible
      (equalCharacteristicTargetUniformizerInteger K ϖ hϖ) := by
  unfold equalCharacteristicTargetUniformizerInteger
  exact
    (irreducible_mul_units
      (equalCharacteristicUniformizerRatioIntegerUnit K ϖ hϖ)⁻¹).2
      (chosenIntegerRingUniformizer_irreducible K)

/-- The adjusted target prime element coerces to the inverse prescribed uniformizer. -/
@[simp]
theorem equalCharacteristicTargetUniformizerInteger_coe
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    ((equalCharacteristicTargetUniformizerInteger K ϖ hϖ : 𝒪[K]) : K) =
      ((ϖ⁻¹ : Kˣ) : K) := by
  let η := inverseIntegerRingUniformizerFieldUnit K
  let u := equalCharacteristicUniformizerRatioIntegerUnit K ϖ hϖ
  have hu : integerUnitsToFieldUnits K u = ϖ / η := by
    exact
      integerUnitsToFieldUnits_equalCharacteristicUniformizerRatioIntegerUnit
        K ϖ hϖ
  change
    ((integerRingUniformizerFieldUnit K *
        integerUnitsToFieldUnits K u⁻¹ : Kˣ) : K) =
      ((ϖ⁻¹ : Kˣ) : K)
  have hunit :
      integerRingUniformizerFieldUnit K *
          integerUnitsToFieldUnits K u⁻¹ =
        ϖ⁻¹ := by
    rw [map_inv, hu]
    dsimp [η, inverseIntegerRingUniformizerFieldUnit]
    rw [div_eq_mul_inv, inv_inv, mul_inv_rev]
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  exact congrArg Units.val hunit

/-- The preceding prime element, in the valuation ring of the canonical
complete-DVF package. -/
noncomputable def equalCharacteristicTargetUniformizer
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    (equalCharacteristicTargetLocalField K).valuationSubring :=
  equalCharacteristicTargetIntegerEquiv K
    (equalCharacteristicTargetUniformizerInteger K ϖ hϖ)

/-- The target valuation-ring uniformizer coerces to the inverse prescribed field unit. -/
@[simp]
theorem equalCharacteristicTargetUniformizer_coe
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    ((equalCharacteristicTargetUniformizer K ϖ hϖ :
      (equalCharacteristicTargetLocalField K).valuationSubring) : K) =
      ((ϖ⁻¹ : Kˣ) : K) := by
  rw [equalCharacteristicTargetUniformizer,
    equalCharacteristicTargetIntegerEquiv_apply_coe,
    equalCharacteristicTargetUniformizerInteger_coe]

/-- The adjusted target prime element is a uniformizer for the canonical valuation. -/
theorem equalCharacteristicTargetUniformizer_isUniformizer
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    (equalCharacteristicTargetLocalField K).valuation.IsUniformizer
      (equalCharacteristicTargetUniformizer K ϖ hϖ : K) := by
  have hirr :
      Irreducible (equalCharacteristicTargetUniformizer K ϖ hϖ) :=
    (equalCharacteristicTargetUniformizerInteger_irreducible K ϖ hϖ).map
      (equalCharacteristicTargetIntegerEquiv K)
  exact Valuation.isUniformizer_of_maximalIdeal_eq_span
    (v := (equalCharacteristicTargetLocalField K).valuation)
    hirr.maximalIdeal_eq

/-! ## The Laurent equivalence -/

/-- The Laurent-series model of the target equal-characteristic local field,
normalized by the prescribed positive uniformizer. -/
noncomputable def equalCharacteristicTargetLaurentRingEquiv
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    (equalCharacteristicTargetLocalField K).residueField⸨X⸩ ≃+* K := by
  let F := equalCharacteristicTargetLocalField K
  letI : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  exact equalCharacteristicLaurentRingEquiv F
    (equalCharacteristicTargetUniformizer_isUniformizer K ϖ hϖ)

/-- The Laurent-series equivalence sends its formal uniformizer to the inverse prescribed unit. -/
@[simp]
theorem equalCharacteristicTargetLaurentRingEquiv_uniformizer
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ
        (equalCharacteristicLaurentUniformizer
          (equalCharacteristicTargetLocalField K)) =
      ((ϖ⁻¹ : Kˣ) : K) := by
  let F := equalCharacteristicTargetLocalField K
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  change
    equalCharacteristicLaurentRingEquiv F
        (equalCharacteristicTargetUniformizer_isUniformizer K ϖ hϖ)
        (equalCharacteristicLaurentUniformizer F) =
      ((ϖ⁻¹ : Kˣ) : K)
  unfold equalCharacteristicLaurentUniformizer
  rw [equalCharacteristicLaurentRingEquiv_algebraMap_X,
    equalCharacteristicTargetUniformizer_coe]

/-- The induced equivalence of field-unit groups. -/
noncomputable def equalCharacteristicTargetLaurentUnitsEquiv
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    (equalCharacteristicTargetLocalField K).residueField⸨X⸩ˣ ≃* Kˣ :=
  Units.mapEquiv
    (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ).toMulEquiv

/-- The Laurent parameter itself maps to the inverse prescribed
uniformizer, at the level of field units. -/
@[simp]
theorem equalCharacteristicTargetLaurentUnitsEquiv_uniformizer
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    equalCharacteristicTargetLaurentUnitsEquiv K p ϖ hϖ
        (equalCharacteristicLaurentUniformizerUnit
          (equalCharacteristicTargetLocalField K)) =
      ϖ⁻¹ := by
  apply Units.ext
  exact equalCharacteristicTargetLaurentRingEquiv_uniformizer K p ϖ hϖ

/-- The inverse Laurent parameter is sent exactly to the prescribed positive
uniformizer. -/
@[simp]
theorem equalCharacteristicTargetLaurentUnitsEquiv_uniformizer_inv
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    equalCharacteristicTargetLaurentUnitsEquiv K p ϖ hϖ
        (equalCharacteristicLaurentUniformizerUnit
          (equalCharacteristicTargetLocalField K))⁻¹ =
      ϖ := by
  rw [map_inv,
    equalCharacteristicTargetLaurentUnitsEquiv_uniformizer]
  simp

/-! ## Principal-unit containment under the Laurent equivalence -/

/-- A power-series higher unit remains a principal unit after evaluating the
Laurent parameter at the prescribed target prime element.  This pointwise
form is all that the equal-characteristic Laurent-series classification needs and avoids
  constructing a second, expensive
integer-ring equivalence. -/
theorem equalCharacteristicTargetLaurentUnitsEquiv_mem_fieldPrincipalUnits_of_mem_higherUnit
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (m : ℕ)
    (a :
      (equalCharacteristicTargetLocalField K).residueField⟦X⟧ˣ)
    (ha :
      a ∈ equalCharacteristicLubinTateHigherUnitSubgroup
        (equalCharacteristicTargetLocalField K) m) :
    equalCharacteristicTargetLaurentUnitsEquiv K p ϖ hϖ
        (equalCharacteristicPowerSeriesUnitToLaurentFieldUnit
          (equalCharacteristicTargetLocalField K) a) ∈
      LocalFieldTheory.fieldPrincipalUnits K (m + 1) := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let π := equalCharacteristicTargetUniformizer K ϖ hϖ
  let hπ := equalCharacteristicTargetUniformizer_isUniformizer K ϖ hϖ
  let eval :=
    CompleteDVF.EqualCharacteristicLaurent.adicPowerSeriesEvalSubringHom
      (F := F.toCompleteDVF) F.residueCharacteristic
      (n := equalCharacteristicResidueRank F)
      (equalCharacteristicResidueCard F) π hπ
  let uF : F.valuationSubringˣ := Units.map eval.toMonoidHom a
  let uK : 𝒪[K]ˣ :=
    Units.map (equalCharacteristicTargetIntegerEquiv K).symm.toMonoidHom uF
  have hcomp :=
    congrArg DFunLike.coe
      (CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom_comp_powerSeries
        (F := F.toCompleteDVF) F.residueCharacteristic
        (n := equalCharacteristicResidueRank F)
        (equalCharacteristicResidueCard F) π hπ)
  have heval (f : F.residueField⟦X⟧) :
      equalCharacteristicLaurentRingEquiv F hπ
          (algebraMap F.residueField⟦X⟧ B f) =
        ((eval f : F.valuationSubring) : K) := by
    rw [equalCharacteristicLaurentRingEquiv_apply]
    exact congrFun hcomp f
  have hX :
      eval (PowerSeries.X : F.residueField⟦X⟧) = π := by
    apply Subtype.ext
    change
      ((eval (PowerSeries.X : F.residueField⟦X⟧) :
        F.valuationSubring) : K) = (π : K)
    exact
      (heval (PowerSeries.X : F.residueField⟦X⟧)).symm.trans
        (equalCharacteristicLaurentRingEquiv_algebraMap_X F hπ)
  have hev :
      eval ((a : F.residueField⟦X⟧) - 1) ∈
        F.maximalIdeal ^ (m + 1) := by
    have ha' :=
      (mem_equalCharacteristicLubinTateHigherUnitSubgroup F m a).1 ha
    rw [F.maximalIdeal_pow_eq_span_uniformizer_pow hπ (m + 1),
      Ideal.mem_span_singleton]
    rw [Ideal.mem_span_singleton] at ha'
    obtain ⟨c, hc⟩ := ha'
    refine ⟨eval c, ?_⟩
    calc
      eval ((a : F.residueField⟦X⟧) - 1) =
          eval ((PowerSeries.X : F.residueField⟦X⟧) ^ (m + 1) * c) :=
        congrArg eval hc
      _ = π ^ (m + 1) * eval c := by
        rw [map_mul, map_pow, hX]
  have huF :
      (uF : F.valuationSubring) - 1 ∈
        F.maximalIdeal ^ (m + 1) := by
    change
      eval (a : F.residueField⟦X⟧) - 1 ∈
        F.maximalIdeal ^ (m + 1)
    simpa only [map_sub, map_one] using hev
  have huK : uK ∈ principalUnits K (m + 1) := by
    rw [mem_principalUnits_iff]
    have htransport :
        (equalCharacteristicTargetIntegerEquiv K).symm
            ((uF : F.valuationSubring) - 1) ∈
          IsLocalRing.maximalIdeal 𝒪[K] ^ (m + 1) :=
      (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
        (equalCharacteristicTargetIntegerEquiv K).symm (m + 1)
        ((uF : F.valuationSubring) - 1)).2 huF
    change
      (equalCharacteristicTargetIntegerEquiv K).symm
          (uF : F.valuationSubring) - 1 ∈
        IsLocalRing.maximalIdeal 𝒪[K] ^ (m + 1)
    simpa only [map_sub, map_one] using htransport
  refine ⟨uK, huK, ?_⟩
  rw [equalCharacteristicPowerSeriesUnitToLaurentFieldUnit_apply]
  apply Units.ext
  change
    (((equalCharacteristicTargetIntegerEquiv K).symm
        (eval (a : F.residueField⟦X⟧)) : 𝒪[K]) : K) =
      equalCharacteristicLaurentRingEquiv F hπ
        (algebraMap F.residueField⟦X⟧ B
          (a : F.residueField⟦X⟧))
  rw [equalCharacteristicTargetIntegerEquiv_symm_apply_coe]
  exact (heval (a : F.residueField⟦X⟧)).symm

/-- The normalized Laurent equivalence carries every level-m+1 principal
unit into the corresponding target principal-unit group. -/
theorem equalCharacteristicTargetLaurent_fieldPrincipalUnits_map_le
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    (LocalFieldTheory.fieldPrincipalUnits B (m + 1)).map
        (equalCharacteristicTargetLaurentUnitsEquiv
          K p ϖ hϖ).toMonoidHom ≤
      LocalFieldTheory.fieldPrincipalUnits K (m + 1) := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  change
    (LocalFieldTheory.fieldPrincipalUnits B (m + 1)).map
        (equalCharacteristicTargetLaurentUnitsEquiv
          K p ϖ hϖ).toMonoidHom ≤
      LocalFieldTheory.fieldPrincipalUnits K (m + 1)
  rw [←
    equalCharacteristicLubinTateHigherUnitSubgroup_map_toLaurentField_eq
      F m]
  rintro x ⟨y, ⟨a, ha, rfl⟩, rfl⟩
  exact
    equalCharacteristicTargetLaurentUnitsEquiv_mem_fieldPrincipalUnits_of_mem_higherUnit
      K p ϖ hϖ m a ha

/-- Consequently the explicit norm-subgroup computation maps the standard subgroup into the target
standard subgroup with the prescribed positive uniformizer. -/
theorem equalCharacteristicTargetLaurent_uniformizerPrincipalSubgroup_map_le
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    (LocalFieldTheory.uniformizerPrincipalSubgroup B
        (equalCharacteristicLaurentUniformizerUnit F)⁻¹
        1 (m + 1)).map
        (equalCharacteristicTargetLaurentUnitsEquiv
          K p ϖ hϖ).toMonoidHom ≤
      LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 (m + 1) := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  change
    (LocalFieldTheory.uniformizerPrincipalSubgroup B
        (equalCharacteristicLaurentUniformizerUnit F)⁻¹
        1 (m + 1)).map
        (equalCharacteristicTargetLaurentUnitsEquiv
          K p ϖ hϖ).toMonoidHom ≤
      LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 (m + 1)
  unfold LocalFieldTheory.uniformizerPrincipalSubgroup
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  apply sup_le_sup
  · apply (Subgroup.zpowers_le).2
    rw [map_pow]
    change
      (equalCharacteristicTargetLaurentUnitsEquiv K p ϖ hϖ
        ((equalCharacteristicLaurentUniformizerUnit F)⁻¹)) ^ 1 ∈
        Subgroup.zpowers (ϖ ^ 1)
    rw [equalCharacteristicTargetLaurentUnitsEquiv_uniformizer_inv]
    exact Subgroup.mem_zpowers (ϖ ^ 1)
  · exact
      equalCharacteristicTargetLaurent_fieldPrincipalUnits_map_le
        K p ϖ hϖ m

/-! ## Transport of the finite Lubin--Tate extension and its norm subgroup -/

/-- The level field with its base algebra transported from the Laurent model
to the target field. -/
@[reducible]
noncomputable def equalCharacteristicTransportedLubinTateLevelAlgebra
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    Algebra K (equalCharacteristicLubinTateLevelField F m) := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  letI : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  letI : Algebra B E := equalCharacteristicLubinTateLevelAlgebra F m
  letI : CharP K p := hKp
  exact RingHom.toAlgebra
    ((algebraMap B E).comp
      (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ).symm.toRingHom)

/-- The transported `K`-algebra map agrees with the original Laurent-series base map. -/
theorem equalCharacteristicTransportedLubinTateLevelAlgebra_comp
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F m
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F m
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
    (algebraMap K E).comp
        (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ).toRingHom =
      (RingEquiv.refl E).toRingHom.comp (algebraMap B E) := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  let : Algebra B E := equalCharacteristicLubinTateLevelAlgebra F m
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
  apply RingHom.ext
  intro x
  change
    (algebraMap B E)
        ((equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ).symm
          (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ x)) =
      (algebraMap B E) x
  rw [RingEquiv.symm_apply_apply]

/-- Finite-dimensionality of the uniformizer norm identity survives the change of base field. -/
theorem equalCharacteristicTransportedLubinTateLevel_finiteDimensional
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F m
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
    letI : Module K E := Algebra.toModule
    Module.Finite K E := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  let algBE : Algebra B E := equalCharacteristicLubinTateLevelAlgebra F m
  let : Algebra B E := algBE
  let : Module B E := algBE.toModule
  let : Module.Finite B E :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F m
  let : CharP K p := hKp
  let algKE : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
  let : Algebra K E := algKE
  let : Module K E := algKE.toModule
  exact Module.Finite.of_equiv_equiv
    (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ)
    (RingEquiv.refl E)
    (equalCharacteristicTransportedLubinTateLevelAlgebra_comp
      K p ϖ hϖ m)

/-- Galoisness of the uniformizer norm identity survives the same change of base field. -/
theorem equalCharacteristicTransportedLubinTateLevel_isGalois
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F m
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
    IsGalois K E := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  let : Algebra B E := equalCharacteristicLubinTateLevelAlgebra F m
  let : IsGalois B E :=
    equalCharacteristicLubinTateLevelField_isGalois F m
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
  exact IsGalois.of_equiv_equiv
    (F := B) («E» := E)
    (f := equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ)
    (g := RingEquiv.refl E)
    (equalCharacteristicTransportedLubinTateLevelAlgebra_comp
      K p ϖ hϖ m)

/-- Abelian Galoisness of the Lubin--Tate level field is preserved when its
base algebra is transported from the Laurent model to the target field. -/
theorem equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F m
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
    IsAbelianGalois K E := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  let : Algebra B E := equalCharacteristicLubinTateLevelAlgebra F m
  let : IsAbelianGalois B E :=
    equalCharacteristicLubinTateLevelField_isAbelianGalois F m
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
  let e := equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ
  have he (x : B) :
      algebraMap K E (e x) = algebraMap B E x := by
    have hcomp :=
      DFunLike.congr_fun
        (equalCharacteristicTransportedLubinTateLevelAlgebra_comp
          K p ϖ hϖ m) x
    simpa [e] using hcomp
  let : IsGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isGalois
      K p ϖ hϖ m
  let restrictToLaurent :
      Gal(E/K) →* Gal(E/B) :=
    { toFun := fun (σ : Gal(E/K)) =>
        show Gal(E/B) from
          { σ.toRingEquiv with
            commutes' := fun x => by
              rw [← he x]
              exact σ.commutes (e x) }
      map_one' := by
        ext x
        rfl
      map_mul' σ τ := by
        ext x
        rfl }
  have hrestrict :
      Function.Injective restrictToLaurent := by
    intro σ τ hστ
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun hστ x
  refine { is_comm.comm := fun σ τ => hrestrict ?_ }
  exact
    (inferInstance : IsMulCommutative (Gal(E/B))).is_comm.comm
      (restrictToLaurent σ) (restrictToLaurent τ)

/-- The actual norm subgroup of the transported level field. -/
noncomputable def equalCharacteristicTransportedLubinTateNormSubgroup
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (m : ℕ) : Subgroup Kˣ := by
  let F := equalCharacteristicTargetLocalField K
  letI : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  letI : CharP K p := hKp
  letI : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
  exact _root_.LocalFieldTheory.localNormSubgroup K E

private theorem equalCharacteristicTransported_normUnits
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (m : ℕ)
    (x :
      let F := equalCharacteristicTargetLocalField K
      letI : CharP K F.residueCharacteristic :=
        equalCharacteristicTargetResidueCharacteristicCharP K p
      (equalCharacteristicLubinTateLevelField F m)ˣ) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F m
    letI : Algebra B E := equalCharacteristicLubinTateLevelAlgebra F m
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
    equalCharacteristicTargetLaurentUnitsEquiv K p ϖ hϖ
        (LocalFieldTheory.normUnits B E x) =
      LocalFieldTheory.normUnits K E x := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  let : Algebra B E := equalCharacteristicLubinTateLevelAlgebra F m
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
  have hnorm :=
    Algebra.norm_eq_of_equiv_equiv
      (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ)
      (RingEquiv.refl E)
      (equalCharacteristicTransportedLubinTateLevelAlgebra_comp
        K p ϖ hϖ m)
      (x : E)
  apply Units.ext
  change
    equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ
        (Algebra.norm B (x : E)) =
      Algebra.norm K (x : E)
  rw [hnorm,
    (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ).apply_symm_apply]
  rfl

/-- Mapping the explicit norm-subgroup computation norm subgroup along the base-field
equivalence gives
the actual norm subgroup for the transported algebra. -/
theorem equalCharacteristicLubinTateNormSubgroup_map_eq_transported
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let N := equalCharacteristicLubinTateNormSubgroup F m
    letI : CharP K p := hKp
    N.map
        (equalCharacteristicTargetLaurentUnitsEquiv K p ϖ hϖ).toMonoidHom =
      equalCharacteristicTransportedLubinTateNormSubgroup K p ϖ hϖ m := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  let : Algebra B E := equalCharacteristicLubinTateLevelAlgebra F m
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
  change
    (_root_.LocalFieldTheory.localNormSubgroup B E).map
        (equalCharacteristicTargetLaurentUnitsEquiv K p ϖ hϖ).toMonoidHom =
      _root_.LocalFieldTheory.localNormSubgroup K E
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact
      ⟨z,
        (equalCharacteristicTransported_normUnits K p ϖ hϖ m z).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨LocalFieldTheory.normUnits B E z, ⟨z, rfl⟩, ?_⟩
    exact equalCharacteristicTransported_normUnits K p ϖ hϖ m z

/-- The explicit norm-subgroup computation over an arbitrary equal-characteristic local field: the
transported actual norm subgroup is contained in the prescribed standard
subgroup at division level m+1. -/
theorem equalCharacteristicTransportedLubinTateNormSubgroup_le_uniformizerPrincipalSubgroup
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    equalCharacteristicTransportedLubinTateNormSubgroup K p ϖ hϖ m ≤
      LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 (m + 1) := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  have hLubinTateNormSubgroup :
      equalCharacteristicLubinTateNormSubgroup F m =
        LocalFieldTheory.uniformizerPrincipalSubgroup B
          (equalCharacteristicLaurentUniformizerUnit F)⁻¹
          1 (m + 1) :=
    equalCharacteristicLubinTateNormSubgroup_eq_uniformizerPrincipalSubgroup
      F m
  let : CharP K p := hKp
  rw [← equalCharacteristicLubinTateNormSubgroup_map_eq_transported
      K p ϖ hϖ m,
    hLubinTateNormSubgroup]
  exact
    equalCharacteristicTargetLaurent_uniformizerPrincipalSubgroup_map_le
      K p ϖ hϖ m

/-- The same containment indexed directly by a positive division level. -/
theorem equalCharacteristicTransportedLubinTateNormSubgroup_le_of_pos
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) (hn : 1 ≤ n) :
    equalCharacteristicTransportedLubinTateNormSubgroup
        K p ϖ hϖ (n - 1) ≤
      LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n := by
  simpa [Nat.sub_add_cancel hn] using
    (equalCharacteristicTransportedLubinTateNormSubgroup_le_uniformizerPrincipalSubgroup
      K p ϖ hϖ (n - 1))

end EqualCharacteristic
end LubinTate
