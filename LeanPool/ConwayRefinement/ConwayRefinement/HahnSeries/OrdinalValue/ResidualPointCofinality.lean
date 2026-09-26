/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPoint

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.StableInterval
import Mathlib.Order.Bounds.OrderIso
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Tactic.Linarith

/-!
# Cofinality of Berarducci residual points

This module proves the first conclusion of Berarducci, Lemma 6.8: for a nonpositive real Hahn
series `b` with `1 < v_J(b)`, the residual-point set `X(b)` has least upper bound zero.

Write `v_J(b) = ρ l`, where `ρ` is the residual value and `l` is the principal value. When
`1 < ρ`, the proof extracts, above any prescribed negative cutoff, a final support block of
ordinary order type `ρ`. Its real supremum is a residual point because translation makes that
block a stable interval of the germ.

The case `ρ = 1` requires a separate argument. Berarducci's proof takes the supremum of the
first `ρ(α + 1)` support elements and states that the resulting germ has value `ρ`. For
`ρ = 1` and limit `α`, that supremum can be an attained limit point, whose germ need not have
value one. The theorem is repaired without changing its statement: above any cutoff, take the
least later support exponent. It is isolated from below, so its germ lies in `(J + K) \ J` and
has value one.

-/

universe v

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace Berarducci

open HahnSeries

variable {K : Type v} [Field K]

private theorem ordinalValue_translatedTruncation_eq_one_of_isolatedBelow
    (b : Series K) {z y : ℝ}
    (hySupport : y ∈ (b : K⟦ℝ⟧).support) (hzy : z < y)
    (hgap : (b : K⟦ℝ⟧).support ∩ Set.Ioo z y = ∅) :
    ordinalValue (translatedTruncation (b : K⟦ℝ⟧) y) = 1 := by
  apply ordinalValue_eq_one_iff.mpr
  constructor
  · rw [mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem]
    rw [HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero]
    let q := translatedTruncation (b : K⟦ℝ⟧) y -
      HahnSeries.Nonpositive.C
        (HahnSeries.Nonpositive.constantCoeff (translatedTruncation (b : K⟦ℝ⟧) y))
    change HahnSeries.Nonpositive.supportSup q < 0
    by_cases hq : q = 0
    · simp [hq]
    · rw [HahnSeries.Nonpositive.supportSup_of_ne hq]
      apply WithBot.coe_lt_coe.mpr
      refine (csSup_le (HahnSeries.support_nonempty_iff.mpr ?_) ?_).trans_lt
        (sub_neg.mpr hzy)
      · simpa using hq
      · intro δ hδSupport
        apply le_of_not_gt
        intro hzyδ
        have hδ0 : δ ≤ 0 := HahnSeries.Nonpositive.support_subset q hδSupport
        rcases hδ0.eq_or_lt with rfl | hδ0
        · have hcoeff : (q : K⟦ℝ⟧).coeff 0 = 0 := by
            simp [q]
          exact (HahnSeries.mem_support _ _).mp hδSupport hcoeff
        · have hbySupport : y + δ ∈ (b : K⟦ℝ⟧).support := by
            rw [HahnSeries.mem_support]
            have hcoeff : (q : K⟦ℝ⟧).coeff δ =
                (b : K⟦ℝ⟧).coeff (y + δ) := by
              simp [q, hδ0.le, hδ0.ne]
            rw [← hcoeff]
            exact (HahnSeries.mem_support _ _).mp hδSupport
          have hby : y + δ < y := by linarith
          have hzby : z < y + δ := by linarith
          have : y + δ ∈ (b : K⟦ℝ⟧).support ∩ Set.Ioo z y :=
            ⟨hbySupport, hzby, hby⟩
          simp [hgap] at this
  · intro hmem
    have hconstant := constantCoeff_eq_zero_of_mem_negativeMonomialIdeal hmem
    have hyCoeff : (b : K⟦ℝ⟧).coeff y ≠ 0 :=
      (HahnSeries.mem_support _ _).mp hySupport
    apply hyCoeff
    simpa [HahnSeries.Nonpositive.constantCoeff_apply] using hconstant

private theorem isLUB_negativeSupport_translatedTruncation_of_cofinal_support
    (b : Series K) {gamma : ℝ} {B : Set ℝ}
    (hBSupport : B ⊆ (b : K⟦ℝ⟧).support)
    (hBlt : ∀ x ∈ B, x < gamma) (hBLUB : IsLUB B gamma) :
    IsLUB
      (((translatedTruncation (b : K⟦ℝ⟧) gamma : Series K) : K⟦ℝ⟧).support ∩
        Set.Iio 0) 0 := by
  have hshiftedLUB : IsLUB ((fun x ↦ -gamma + x) '' B) 0 := by
    simpa using (OrderIso.addLeft (-gamma)).isLUB_image'.mpr hBLUB
  have hshiftedSubset : (fun x ↦ -gamma + x) '' B ⊆
      ((translatedTruncation (b : K⟦ℝ⟧) gamma : Series K) : K⟦ℝ⟧).support ∩
        Set.Iio 0 := by
    rintro delta ⟨x, hxB, rfl⟩
    have hxCoeff : (b : K⟦ℝ⟧).coeff x ≠ 0 :=
      (HahnSeries.mem_support _ _).mp (hBSupport hxB)
    have hdelta0 : -gamma + x < 0 := by
      linarith [hBlt x hxB]
    constructor
    · rw [HahnSeries.mem_support, coeff_translatedTruncation, ite_eq_left hdelta0.le]
      simpa using hxCoeff
    · exact hdelta0
  constructor
  · intro delta hdelta
    exact hdelta.2.le
  · intro x hxUpper
    apply hshiftedLUB.2
    intro delta hdelta
    exact hxUpper (hshiftedSubset hdelta)

private theorem exists_cofinal_final_block_of_orderType_eq_mul
    {T : Set ℝ} (hT : T.IsPWO) (hT0 : T ⊆ Set.Iio 0)
    (hTLUB : IsLUB T 0) {rho l : Ordinal}
    (hrho : 0 < rho) (hl : Order.IsSuccLimit l)
    (hTType : hT.orderType = rho * l) {a : ℝ} (ha : a < 0) :
    ∃ (gamma : ℝ) (B : Set ℝ) (hB : B.IsPWO),
      a < gamma ∧ gamma < 0 ∧ B ⊆ T ∧ hB.orderType = rho ∧
        IsLUB B gamma ∧
          ∀ {x}, x ∈ B → ∀ {y}, y ∈ T → x < y → y < gamma → y ∈ B := by
  obtain ⟨z, hzT, haz, _⟩ := hTLUB.exists_between ha
  let hBelow : (T ∩ Set.Iio z).IsPWO := hT.mono Set.inter_subset_left
  have hBelowLt : hBelow.orderType < rho * l := by
    rw [← hTType]
    exact hT.orderType_inter_Iio_lt hzT
  obtain ⟨c, hc, hBelowMul⟩ :=
    (Ordinal.lt_mul_iff_of_isSuccLimit hl).mp hBelowLt
  let k := rho * Order.succ c
  have hck : rho * c ≤ k :=
    mul_le_mul_right (Order.le_succ c) rho
  have hBelowK : hBelow.orderType < k := hBelowMul.trans_le hck
  have hkType : k < hT.orderType := by
    rw [hTType]
    exact mul_lt_mul_of_pos_left (hl.succ_lt hc) hrho
  let d := hT.orderType - k
  have hkd : k + d = hT.orderType :=
    Ordinal.add_sub_cancel_of_le hkType.le
  obtain ⟨S, U, hS, hU, hST, hUT, hSU, hSType, hUType, hTUnion⟩ :=
    (hT.orderType_eq_add_iff k d).mp hkd.symm
  have hzS : z ∈ S := by
    have hzUnion : z ∈ S ∪ U := by
      rw [← hTUnion]
      exact hzT
    rcases hzUnion with hzS | hzU
    · exact hzS
    · exfalso
      have hSBelow : S ⊆ T ∩ Set.Iio z := by
        intro x hxS
        exact ⟨hST hxS, hSU x hxS z hzU⟩
      have hle := hS.orderType_mono hBelow hSBelow
      rw [hSType] at hle
      exact (not_lt_of_ge hle) hBelowK
  have hSne : S.Nonempty := ⟨z, hzS⟩
  have hdne : d ≠ 0 := Ordinal.sub_ne_zero_iff_lt.mpr hkType
  have hUne : U.Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro hUempty
    have hzero := hU.orderType_eq_zero.mpr hUempty
    rw [hUType] at hzero
    exact hdne hzero
  obtain ⟨u, huU⟩ := hUne
  have hSbdd : BddAbove S :=
    ⟨u, fun x hxS ↦ (hSU x hxS u huU).le⟩
  let gamma := sSup S
  have hSLUB : IsLUB S gamma := isLUB_csSup hSne hSbdd
  have hgamma0 : gamma < 0 :=
    (hSLUB.2 fun x hxS ↦ (hSU x hxS u huU).le).trans_lt (hT0 (hUT huU))
  have hagamma : a < gamma := haz.trans_le (hSLUB.1 hzS)
  have hSTypeSplit : hS.orderType = rho * c + rho := by
    rw [hSType]
    simp only [k, Ordinal.mul_succ]
  obtain ⟨A, B, hA, hB, hAS, hBS, hAB, hAType, hBType, hSUnion⟩ :=
    (hS.orderType_eq_add_iff (rho * c) rho).mp hSTypeSplit
  have hBne : B.Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro hBempty
    have hzero := hB.orderType_eq_zero.mpr hBempty
    rw [hBType] at hzero
    exact hrho.ne' hzero
  obtain ⟨b0, hb0B⟩ := hBne
  have hBLUB : IsLUB B gamma := by
    constructor
    · intro x hxB
      exact hSLUB.1 (hBS hxB)
    · intro x hxUpper
      apply hSLUB.2
      intro y hyS
      rw [hSUnion] at hyS
      rcases hyS with hyA | hyB
      · exact (hAB y hyA b0 hb0B).le.trans (hxUpper hb0B)
      · exact hxUpper hyB
  refine ⟨gamma, B, hB, hagamma, hgamma0, hBS.trans hST, hBType, hBLUB, ?_⟩
  intro x hxB y hyT hxy hygamma
  have hyUnion : y ∈ S ∪ U := by
    rw [← hTUnion]
    exact hyT
  rcases hyUnion with hyS | hyU
  · rw [hSUnion] at hyS
    rcases hyS with hyA | hyB
    · exfalso
      exact (not_lt_of_ge (hAB y hyA x hxB).le) hxy
    · exact hyB
  · exfalso
    have hgammaY : gamma ≤ y :=
      hSLUB.2 fun s hsS ↦ (hSU s hsS y hyU).le
    exact (not_lt_of_ge hgammaY) hygamma

private theorem ordinalValue_translatedTruncation_eq_of_cofinal_final_block
    (b : Series K) {eta gamma : ℝ} (rho : NatOrdinal)
    (hrhoPrincipal : Ordinal.IsAdditivelyPrincipal rho.val)
    (hrho : 1 < rho) {B : Set ℝ} (hB : B.IsPWO)
    (hBSub : B ⊆ negativeSupportTail b eta)
    (hBType : hB.orderType = rho.val) (hBLUB : IsLUB B gamma)
    (hgamma0 : gamma < 0)
    (hfinal : ∀ {x}, x ∈ B → ∀ {y}, y ∈ negativeSupportTail b eta →
      x < y → y < gamma → y ∈ B) :
    ordinalValue (translatedTruncation (b : K⟦ℝ⟧) gamma) = rho := by
  have hrhoVal : 1 < rho.val := NatOrdinal.one_lt_val.mpr hrho
  have hrhoLimit : Order.IsSuccLimit rho.val :=
    hrhoPrincipal.isSuccLimit_of_one_lt hrhoVal
  have hBOrderLimit : Order.IsSuccLimit hB.orderType := by
    rw [hBType]
    exact hrhoLimit
  have hBne : B.Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro hBempty
    have hzero := hB.orderType_eq_zero.mpr hBempty
    rw [hBType] at hzero
    exact (zero_lt_one.trans hrhoVal).ne' hzero
  have hBlt : ∀ x ∈ B, x < gamma := by
    intro x hxB
    obtain ⟨y, hyB, hxy⟩ :=
      hB.exists_gt_of_isSuccLimit_orderType hBOrderLimit hxB
    exact hxy.trans_le (hBLUB.1 hyB)
  let q : Series K := translatedTruncation (b : K⟦ℝ⟧) gamma
  have hqLUB : IsLUB ((q : K⟦ℝ⟧).support ∩ Set.Iio 0) 0 := by
    apply isLUB_negativeSupport_translatedTruncation_of_cofinal_support b
      (B := B) (gamma := gamma)
    · exact fun _ hxB ↦ negativeSupportTail_subset_support b eta (hBSub hxB)
    · exact hBlt
    · exact hBLUB
  have hqValue : 1 < ordinalValue q :=
    one_lt_ordinalValue_of_isLUB_negativeSupport hqLUB
  obtain ⟨theta, htheta, hstable⟩ :=
    exists_forall_later_negativeSupportTail_orderType_eq_ordinalValue q hqValue
  obtain ⟨b0, hb0B⟩ := hBne
  have hb0gamma : b0 < gamma := hBlt b0 hb0B
  have hthetaGamma : gamma + theta < gamma := by linarith
  have hmaxGamma : max (gamma + theta) b0 < gamma :=
    max_lt hthetaGamma hb0gamma
  obtain ⟨x, hxB, hmaxX, _⟩ := hBLUB.exists_between hmaxGamma
  have hxgamma : x < gamma := hBlt x hxB
  let xi := x - gamma
  have hthetaXi : theta < xi := by
    have hgammaThetaX : gamma + theta < x :=
      (le_max_left (gamma + theta) b0).trans_lt hmaxX
    dsimp only [xi]
    linarith
  have hxi0 : xi < 0 := by
    dsimp only [xi]
    linarith
  let BFinal := B ∩ Set.Ioi x
  let hBFinal : BFinal.IsPWO := hB.mono Set.inter_subset_left
  have hBUpper : ∃ y ∈ B, x < y :=
    hB.exists_gt_of_isSuccLimit_orderType hBOrderLimit hxB
  have hBPrincipal : Ordinal.IsPrincipal (fun a b ↦ a + b) hB.orderType := by
    rw [hBType]
    exact
      (Ordinal.isAdditivelyPrincipal_iff_ne_zero_and_isPrincipal_add.mp
        hrhoPrincipal).2
  have hBFinalType : hBFinal.orderType = hB.orderType :=
    hB.orderType_inter_Ioi_eq_of_isPrincipal hBPrincipal hBUpper
  have hsupport : negativeSupportTail q xi =
      (fun y ↦ -gamma + y) '' BFinal := by
    ext delta
    constructor
    · intro hdelta
      obtain ⟨hdeltaSupport, hxiDelta, hdelta0⟩ :=
        mem_negativeSupportTail_iff.mp hdelta
      rw [support_translatedTruncation] at hdeltaSupport
      obtain ⟨y, hySupport, hdelta⟩ := hdeltaSupport
      have hxy : x < y := by
        dsimp only [xi] at hxiDelta
        linarith
      have hygamma : y < gamma := by linarith
      have hyTail : y ∈ negativeSupportTail b eta := by
        apply mem_negativeSupportTail_iff.mpr
        exact ⟨hySupport.1,
          (mem_negativeSupportTail_iff.mp (hBSub hxB)).2.1.trans hxy,
          hygamma.trans hgamma0⟩
      have hyB : y ∈ B := hfinal hxB hyTail hxy hygamma
      exact ⟨y, ⟨hyB, hxy⟩, hdelta⟩
    · rintro ⟨y, ⟨hyB, hxy⟩, rfl⟩
      change x < y at hxy
      have hygamma : y < gamma := hBlt y hyB
      apply mem_negativeSupportTail_iff.mpr
      constructor
      · rw [support_translatedTruncation]
        exact ⟨y,
          ⟨negativeSupportTail_subset_support b eta (hBSub hyB), hygamma.le⟩, rfl⟩
      · constructor
        · dsimp only [xi]
          linarith
        · linarith
  let hShifted : ((fun y ↦ -gamma + y) '' BFinal).IsPWO :=
    hBFinal.image_of_monotone (OrderIso.addLeft (-gamma)).monotone
  let hQTail : (negativeSupportTail q xi).IsPWO :=
    (q : K⟦ℝ⟧).isPWO_support.mono (negativeSupportTail_subset_support q xi)
  apply NatOrdinal.val.injective
  calc
    (ordinalValue (translatedTruncation (b : K⟦ℝ⟧) gamma)).val =
        (ordinalValue q).val := rfl
    _ = hQTail.orderType := (hstable xi hthetaXi hxi0).symm
    _ = hShifted.orderType := hQTail.orderType_congr hShifted hsupport
    _ = hBFinal.orderType :=
      hBFinal.orderType_image_of_strictMonoOn
        ((OrderIso.addLeft (-gamma)).strictMono.strictMonoOn BFinal)
    _ = hB.orderType := hBFinalType
    _ = rho.val := hBType

private theorem residualPointSet_isLUB_zero_of_residualValue_eq_one
    (b : SeriesWithOrdinalValueAboveOne K) (hresidual : b.residualValue = 1) :
    IsLUB (residualPointSet b) 0 := by
  obtain ⟨eta, heta, _⟩ :=
    exists_negativeSupportTail_orderType_eq_ordinalValue b.1 b.2
  have htailLUB :=
    isLUB_negativeSupportTail_zero_of_one_lt_ordinalValue b.1 b.2 heta
  refine ⟨fun _ hx ↦ (residualPointSet_subset_Iio b hx).le, ?_⟩
  intro a ha
  apply le_of_not_gt
  intro ha0
  obtain ⟨z, hzTail, haz, _⟩ := htailLUB.exists_between ha0
  have hzTail' := mem_negativeSupportTail_iff.mp hzTail
  obtain ⟨w, hwTail, hzw, _⟩ := htailLUB.exists_between hzTail'.2.2
  let laterSupport := negativeSupportTail b.1 eta ∩ Set.Ioi z
  have hlaterPWO : laterSupport.IsPWO :=
    (b.1 : K⟦ℝ⟧).isPWO_support.mono fun _ hx ↦
      negativeSupportTail_subset_support b.1 eta hx.1
  have hwLater : w ∈ laterSupport := ⟨hwTail, hzw⟩
  obtain ⟨y, hyMinimal⟩ := hlaterPWO.exists_minimal ⟨w, hwLater⟩
  have hyTail : y ∈ negativeSupportTail b.1 eta := hyMinimal.1.1
  have hyTail' := mem_negativeSupportTail_iff.mp hyTail
  have hzy : z < y := hyMinimal.1.2
  have hgap : (b.1 : K⟦ℝ⟧).support ∩ Set.Ioo z y = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxLater : x ∈ laterSupport := by
      refine ⟨?_, hx.2.1⟩
      apply mem_negativeSupportTail_iff.mpr
      exact ⟨hx.1, hzTail'.2.1.trans hx.2.1, hx.2.2.trans hyTail'.2.2⟩
    exact (not_lt_of_ge (hyMinimal.le hxLater)) hx.2.2
  have hyValue : ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) y) = 1 :=
    ordinalValue_translatedTruncation_eq_one_of_isolatedBelow b.1 hyTail'.1 hzy hgap
  have hyResidual : y ∈ residualPointSet b := by
    apply mem_residualPointSet_iff.mpr
    exact ⟨hyTail'.2.2, hyValue.trans hresidual.symm⟩
  exact (not_lt_of_ge (ha hyResidual)) (haz.trans hzy)

private theorem residualPointSet_isLUB_zero_of_one_lt_residualValue
    (b : SeriesWithOrdinalValueAboveOne K) (hresidual : 1 < b.residualValue) :
    IsLUB (residualPointSet b) 0 := by
  obtain ⟨eta, heta, hstable⟩ :=
    exists_negativeSupportTail_orderType_eq_ordinalValue b.1 b.2
  let T := negativeSupportTail b.1 eta
  let hT : T.IsPWO :=
    (b.1 : K⟦ℝ⟧).isPWO_support.mono (negativeSupportTail_subset_support b.1 eta)
  have hT0 : T ⊆ Set.Iio 0 := fun _ hx ↦
    (mem_negativeSupportTail_iff.mp hx).2.2
  have hTLUB : IsLUB T 0 :=
    isLUB_negativeSupportTail_zero_of_one_lt_ordinalValue b.1 b.2 heta
  have hTType : hT.orderType =
      b.residualValue.val * b.principalValue.val :=
    hstable.trans b.residualValue_val_mul_principalValue_val.symm
  have hresidualVal : 1 < b.residualValue.val :=
    NatOrdinal.one_lt_val.mpr hresidual
  have hresidualPos : 0 < b.residualValue.val :=
    zero_lt_one.trans hresidualVal
  have hprincipalLimit : Order.IsSuccLimit b.principalValue.val :=
    b.principalValue_isInfiniteMultiplicativelyPrincipal.isSuccLimit
  refine ⟨fun _ hx ↦ (residualPointSet_subset_Iio b hx).le, ?_⟩
  intro a haUpper
  apply le_of_not_gt
  intro ha0
  have hmax0 : max a eta < 0 := max_lt ha0 heta
  obtain ⟨gamma, B, hB, hmaxGamma, hgamma0, hBSub, hBType, hBLUB, hfinal⟩ :=
    exists_cofinal_final_block_of_orderType_eq_mul hT hT0 hTLUB
      hresidualPos hprincipalLimit hTType hmax0
  have hgammaValue :
      ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) gamma) = b.residualValue :=
    ordinalValue_translatedTruncation_eq_of_cofinal_final_block b.1 b.residualValue
      b.residualValue_isAdditivelyPrincipal hresidual hB hBSub hBType hBLUB
        hgamma0 hfinal
  have hgammaResidual : gamma ∈ residualPointSet b :=
    mem_residualPointSet_iff.mpr ⟨hgamma0, hgammaValue⟩
  have hagamma : a < gamma :=
    (le_max_left a eta).trans_lt hmaxGamma
  exact (not_lt_of_ge (haUpper hgammaResidual)) hagamma

/-- The residual-point set has zero as its least upper bound. This is the cofinality conclusion in
the first part of Berarducci, Lemma 6.8. -/
theorem residualPointSet_isLUB_zero (b : SeriesWithOrdinalValueAboveOne K) :
    IsLUB (residualPointSet b) 0 := by
  have honeLe : 1 ≤ b.residualValue := by
    rw [Order.one_le_iff_pos]
    exact pos_iff_ne_zero.mpr b.residualValue_ne_zero
  rcases honeLe.eq_or_lt with hone | hone
  · exact residualPointSet_isLUB_zero_of_residualValue_eq_one b hone.symm
  · exact residualPointSet_isLUB_zero_of_one_lt_residualValue b hone

end Berarducci
