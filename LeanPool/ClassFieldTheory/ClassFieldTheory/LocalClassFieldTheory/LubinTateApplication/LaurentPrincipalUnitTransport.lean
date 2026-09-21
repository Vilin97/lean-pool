/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.LubinTateTransport
/-!
# Exact principal-unit transport from the Laurent model

The normalized Laurent-series equivalence used in the equal-characteristic
Lubin--Tate construction restricts to an equivalence between the
power-series coefficient ring and the target integer ring.  Consequently it
carries every principal-unit level onto, rather than merely into, the
corresponding target principal-unit level.
-/

noncomputable section

open scoped LaurentSeries PowerSeries ValuativeRel

namespace LubinTate
namespace EqualCharacteristic

open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Power-series evaluation at the chosen target uniformizer, with codomain
the canonical target valuation ring. -/
noncomputable def equalCharacteristicTargetPowerSeriesEvalSubringHom
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    let F := equalCharacteristicTargetLocalField K
    F.residueField⟦X⟧ →+* F.valuationSubring := by
  let F := equalCharacteristicTargetLocalField K
  letI : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  exact
    CompleteDVF.EqualCharacteristicLaurent.adicPowerSeriesEvalSubringHom
      (F := F.toCompleteDVF) F.residueCharacteristic
      (n := equalCharacteristicResidueRank F)
      (equalCharacteristicResidueCard F)
      (equalCharacteristicTargetUniformizer K ϖ hϖ)
      (equalCharacteristicTargetUniformizer_isUniformizer K ϖ hϖ)

/-- Power-series evaluation agrees with the normalized Laurent equivalence
after both values are included in the target field. -/
theorem equalCharacteristicTargetPowerSeriesEvalSubringHom_coe
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (f :
      (equalCharacteristicTargetLocalField K).residueField⟦X⟧) :
    (((equalCharacteristicTargetPowerSeriesEvalSubringHom
        K p ϖ hϖ f :
          (equalCharacteristicTargetLocalField K).valuationSubring)) : K) =
      equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ
        (algebraMap
          (equalCharacteristicTargetLocalField K).residueField⟦X⟧
          (equalCharacteristicTargetLocalField K).residueField⸨X⸩ f) := by
  let F := equalCharacteristicTargetLocalField K
  let e := equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ
  let eval := equalCharacteristicTargetPowerSeriesEvalSubringHom K p ϖ hϖ
  let π := equalCharacteristicTargetUniformizer K ϖ hϖ
  let hπ := equalCharacteristicTargetUniformizer_isUniformizer K ϖ hϖ
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  have hcomp :=
    congrArg DFunLike.coe
      (CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom_comp_powerSeries
        (F := F.toCompleteDVF) F.residueCharacteristic
        (n := equalCharacteristicResidueRank F)
        (equalCharacteristicResidueCard F) π hπ)
  symm
  change
    equalCharacteristicLaurentRingEquiv F hπ
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩ f) =
      (((eval f : F.valuationSubring)) : K)
  rw [equalCharacteristicLaurentRingEquiv_apply]
  exact congrFun hcomp f

/-- The target power-series evaluation is bijective onto the target
valuation ring. -/
theorem equalCharacteristicTargetPowerSeriesEvalSubringHom_bijective
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    Function.Bijective
      (equalCharacteristicTargetPowerSeriesEvalSubringHom K p ϖ hϖ) := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let e := equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ
  let eval := equalCharacteristicTargetPowerSeriesEvalSubringHom K p ϖ hϖ
  have heval (f : F.residueField⟦X⟧) :
      (((eval f : F.valuationSubring)) : K) =
        e (algebraMap F.residueField⟦X⟧ B f) := by
    exact
      equalCharacteristicTargetPowerSeriesEvalSubringHom_coe
        K p ϖ hϖ f
  let π := equalCharacteristicTargetUniformizer K ϖ hϖ
  let hπ := equalCharacteristicTargetUniformizer_isUniformizer K ϖ hϖ
  change Function.Bijective eval
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  constructor
  · intro f g hfg
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := F.residueField)
    apply e.injective
    rw [← LaurentSeries.coe_algebraMap]
    rw [← heval f, ← heval g]
    exact congrArg F.valuation.valuationSubring.subtype hfg
  · exact
      CompleteDVF.EqualCharacteristicLaurent.adicPowerSeriesEvalSubringHom_surjective
        (F := F.toCompleteDVF) F.residueCharacteristic
        (n := equalCharacteristicResidueRank F)
        (equalCharacteristicResidueCard F)
        π hπ

/-- The normalized Laurent-series equivalence identifies the source and
target valuation rings.  This is the valuation-theoretic compatibility
needed to transport ramification groups across the change of base field. -/
theorem equalCharacteristicTargetLaurentRingEquiv_val_le_one_iff
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (x :
      let F := equalCharacteristicTargetLocalField K
      F.residueField⸨X⸩) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    ValuativeRel.valuation B x ≤ 1 ↔
      ValuativeRel.valuation K
        (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ x) ≤ 1 := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let e := equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ
  let eval := equalCharacteristicTargetPowerSeriesEvalSubringHom K p ϖ hϖ
  have heval (f : F.residueField⟦X⟧) :
      (((eval f : F.valuationSubring)) : K) =
        e (algebraMap F.residueField⟦X⟧ B f) := by
    exact
      equalCharacteristicTargetPowerSeriesEvalSubringHom_coe
        K p ϖ hϖ f
  have hbij : Function.Bijective eval :=
    equalCharacteristicTargetPowerSeriesEvalSubringHom_bijective
      K p ϖ hϖ
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let vB : Valuation B (WithZero (Multiplicative ℤ)) := Valued.v
  let : vB.Compatible := Valuation.Compatible.ofValuation vB
  change
    ValuativeRel.valuation B x ≤ 1 ↔
      ValuativeRel.valuation K (e x) ≤ 1
  rw [← map_one (ValuativeRel.valuation B),
    ← Valuation.Compatible.vle_iff_le
      (v := ValuativeRel.valuation B),
    Valuation.Compatible.vle_iff_le (v := vB)]
  simp only [map_one]
  constructor
  · intro hx
    obtain ⟨f, rfl⟩ :=
      (LaurentSeries.val_le_one_iff_eq_coe F.residueField x).1 hx
    rw [← LaurentSeries.coe_algebraMap]
    rw [← heval f]
    rw [← equalCharacteristicTargetLocalField_valuation_eq K]
    exact (eval f).property
  · intro hx
    let y : F.valuationSubring := ⟨e x, by
      change F.valuation (e x) ≤ 1
      rw [equalCharacteristicTargetLocalField_valuation_eq K]
      exact hx⟩
    obtain ⟨f, hf⟩ :=
      hbij.2 y
    have hfield :
        e (algebraMap F.residueField⟦X⟧ B f) = e x := by
      rw [← heval f]
      exact congrArg (fun z : F.valuationSubring => (z : K)) hf
    have hsource :
        algebraMap F.residueField⟦X⟧ B f = x :=
      e.injective hfield
    rw [← hsource]
    exact
      (LaurentSeries.val_le_one_iff_eq_coe
        F.residueField
        (algebraMap F.residueField⟦X⟧ B f)).2
        ⟨f, rfl⟩

/-- The normalized evaluation identifies the power-series coefficient ring
with the target field's canonical integer ring. -/
noncomputable def equalCharacteristicPowerSeriesEquivTargetInteger
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    let F := equalCharacteristicTargetLocalField K
    F.residueField⟦X⟧ ≃+* 𝒪[K] :=
  (RingEquiv.ofBijective
      (equalCharacteristicTargetPowerSeriesEvalSubringHom K p ϖ hϖ)
      (equalCharacteristicTargetPowerSeriesEvalSubringHom_bijective
        K p ϖ hϖ)).trans
    (equalCharacteristicTargetIntegerEquiv K).symm

/-- The induced equivalence from power-series units to target integer
units. -/
noncomputable def equalCharacteristicPowerSeriesUnitsEquivTargetInteger
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    let F := equalCharacteristicTargetLocalField K
    F.residueField⟦X⟧ˣ ≃* 𝒪[K]ˣ :=
  Units.mapEquiv
    (equalCharacteristicPowerSeriesEquivTargetInteger
      K p ϖ hϖ).toMulEquiv

/-- The target integer-unit equivalence preserves every explicit
Lubin--Tate higher-unit level. -/
theorem
    equalCharacteristicPowerSeriesUnitsEquivTargetInteger_mem_principalUnits_iff
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (m : ℕ)
    (a : (equalCharacteristicTargetLocalField K).residueField⟦X⟧ˣ) :
    equalCharacteristicPowerSeriesUnitsEquivTargetInteger
        K p ϖ hϖ a ∈ principalUnits K (m + 1) ↔
      a ∈ equalCharacteristicLubinTateHigherUnitSubgroup
        (equalCharacteristicTargetLocalField K) m := by
  let F := equalCharacteristicTargetLocalField K
  let r := equalCharacteristicPowerSeriesEquivTargetInteger K p ϖ hϖ
  rw [mem_principalUnits_iff,
    mem_equalCharacteristicLubinTateHigherUnitSubgroup]
  change
    r (a : F.residueField⟦X⟧) - 1 ∈
        IsLocalRing.maximalIdeal 𝒪[K] ^ (m + 1) ↔
      (a : F.residueField⟦X⟧) - 1 ∈
        Ideal.span ({PowerSeries.X ^ (m + 1)} :
          Set F.residueField⟦X⟧)
  have h :=
    ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
      r (m + 1) ((a : F.residueField⟦X⟧) - 1)
  simpa [map_sub, PowerSeries.maximalIdeal_eq_span_X,
    Ideal.span_singleton_pow] using h

/-- The explicit higher-unit subgroup maps exactly to the target principal
units. -/
theorem
    equalCharacteristicLubinTateHigherUnitSubgroup_map_eq_targetPrincipalUnits
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    (equalCharacteristicLubinTateHigherUnitSubgroup F m).map
        (equalCharacteristicPowerSeriesUnitsEquivTargetInteger
          K p ϖ hϖ).toMonoidHom =
      principalUnits K (m + 1) := by
  let F := equalCharacteristicTargetLocalField K
  let e :=
    equalCharacteristicPowerSeriesUnitsEquivTargetInteger K p ϖ hϖ
  ext u
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact
      (equalCharacteristicPowerSeriesUnitsEquivTargetInteger_mem_principalUnits_iff
        K p ϖ hϖ m a).2 ha
  · intro hu
    refine ⟨e.symm u, ?_, by simp [e]⟩
    exact
      (equalCharacteristicPowerSeriesUnitsEquivTargetInteger_mem_principalUnits_iff
        K p ϖ hϖ m (e.symm u)).1 (by simpa [e] using hu)

/-- Evaluation through the target integer ring agrees with applying the
Laurent field-unit equivalence to the canonical power-series unit. -/
theorem
    integerUnitsToFieldUnits_equalCharacteristicPowerSeriesUnitsEquivTargetInteger
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (a : (equalCharacteristicTargetLocalField K).residueField⟦X⟧ˣ) :
    integerUnitsToFieldUnits K
        (equalCharacteristicPowerSeriesUnitsEquivTargetInteger
          K p ϖ hϖ a) =
      equalCharacteristicTargetLaurentUnitsEquiv K p ϖ hϖ
        (equalCharacteristicPowerSeriesUnitToLaurentFieldUnit
          (equalCharacteristicTargetLocalField K) a) := by
  apply Units.ext
  change
    (((equalCharacteristicPowerSeriesEquivTargetInteger
        K p ϖ hϖ) (a :
          (equalCharacteristicTargetLocalField K).residueField⟦X⟧) :
        𝒪[K]) : K) =
      equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ
        (algebraMap
          (equalCharacteristicTargetLocalField K).residueField⟦X⟧
          (equalCharacteristicTargetLocalField K).residueField⸨X⸩
          (a :
            (equalCharacteristicTargetLocalField K).residueField⟦X⟧))
  exact
    equalCharacteristicTargetPowerSeriesEvalSubringHom_coe
      K p ϖ hϖ (a :
        (equalCharacteristicTargetLocalField K).residueField⟦X⟧)

/-- Exact subgroup form: the normalized Laurent equivalence carries
`U^(m+1)` onto the target group `U^(m+1)`. -/
theorem equalCharacteristicTargetLaurent_fieldPrincipalUnits_map_eq
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    (LocalFieldTheory.fieldPrincipalUnits B (m + 1)).map
        (equalCharacteristicTargetLaurentUnitsEquiv
          K p ϖ hϖ).toMonoidHom =
      LocalFieldTheory.fieldPrincipalUnits K (m + 1) := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let H := equalCharacteristicLubinTateHigherUnitSubgroup F m
  let source :=
    equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F
  let target :=
    equalCharacteristicPowerSeriesUnitsEquivTargetInteger K p ϖ hϖ
  let e := equalCharacteristicTargetLaurentUnitsEquiv K p ϖ hϖ
  have hsource : H.map source = LocalFieldTheory.fieldPrincipalUnits B (m + 1) := by
    simpa [H, source] using
      equalCharacteristicLubinTateHigherUnitSubgroup_map_toLaurentField_eq
        F m
  have htarget :
      H.map target.toMonoidHom = principalUnits K (m + 1) := by
    simpa [H, target] using
      equalCharacteristicLubinTateHigherUnitSubgroup_map_eq_targetPrincipalUnits
        K p ϖ hϖ m
  have hcomp :
      e.toMonoidHom.comp source =
        (integerUnitsToFieldUnits K).comp target.toMonoidHom := by
    apply DFunLike.ext _ _
    intro a
    exact
      (integerUnitsToFieldUnits_equalCharacteristicPowerSeriesUnitsEquivTargetInteger
        K p ϖ hϖ a).symm
  change
    (LocalFieldTheory.fieldPrincipalUnits B (m + 1)).map e.toMonoidHom =
      LocalFieldTheory.fieldPrincipalUnits K (m + 1)
  rw [← hsource, Subgroup.map_map, hcomp, ← Subgroup.map_map, htarget]
  rfl

end EqualCharacteristic
end LubinTate
