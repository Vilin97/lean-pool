/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalComponent
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.Statements.DegreeValuation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.OrdinalValueDegree
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeAssociatedGradedMap

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.Residue
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.StableInterval
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PrincipalAddition

/-!
# Principal series in the two degree filtrations

This module relates a principal Hahn series to Berarducci's ordinal value and then compares the
fixed homogeneous components for Hahn-series degree and ordinal-value degree. Both are components
of associated graded rings of `K((ℝ^{≤0}))`, and since `ordinalValueDegree b ≤ degree b`, the
identity of the ring induces the canonical component map `degreeLayerToPrincipalComponent` from the
degree-`α` component of `RV̂` to `P_α`: the generic map induced by a coarsening of filtrations.

For a principal series of Hahn-series degree `α`, its ordinal value is exactly `ω^α`. The proof
uses the stable negative support interval for positive degree and treats degree zero separately.
Consequently, two principal representatives of exact degree `α` determine the same class in the
degree-`α` component of `RV̂` precisely when their difference lies in `J_{ω^α}`. This is
the equal-degree case of LM24, Lemma 7.2.3, and is the case used to identify the source component
with
the intrinsic quotient `J_{ω^(α+1)} / J_{ω^α}`.

The proof uses the repaired equal-degree form of LM24, Proposition 3.6.2. The weaker printed
formulation is not assumed.

The comparison of the two filtrations, the principal classes of a fixed degree, and their
identification with `P_α` hold over every coefficient field. Characteristic zero
enters only for the multiplication of principal classes: the product of two principal series is
principal by LM24, Proposition 3.6.1, which rests on Berarducci, Theorem 9.7, and its degree is
the Hessenberg sum of the degrees by LM24, Theorem D.
-/

universe v

open scoped DirectSum HahnSeries NatOrdinal

public noncomputable section

namespace Berarducci

open HahnSeries

variable {K : Type v} [Field K]

/-- A principal series of Hahn-series degree `α` has ordinal value `ω^α`. -/
theorem ordinalValue_eq_wpow_of_isPrincipal {p : Series K} (hp : HahnSeries.Nonpositive.IsPrincipal
    p)
    {α : NatOrdinal}
    (hpDegree : (p : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal)) :
    ordinalValue p = ω^ α := by
  have hpType := hp.supportOrderType_eq_wpow_of_degree_eq hpDegree
  rcases eq_or_ne α 0 with rfl | hα
  · apply le_antisymm
    · simpa [hpType] using ordinalValue_le_supportOrderType p
    · rw [show (ω^ (0 : NatOrdinal)) = 1 by simp]
      rw [Order.one_le_iff_pos, pos_iff_ne_zero]
      intro hzero
      have hpJ := ordinalValue_eq_zero_iff.mp hzero
      have hpSupLt :=
        HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero.mp hpJ
      rw [hp.supportSup_eq_zero] at hpSupLt
      exact lt_irrefl 0 hpSupLt
  · have hαpos : 0 < α := bot_lt_iff_ne_bot.mpr hα
    have hpZeroCoeff := hp.constantCoeff_eq_zero_of_degree_pos hpDegree hαpos
    have hpOne : 1 < ordinalValue p :=
      one_lt_ordinalValue_of_constantCoeff_eq_zero_of_supportSup_eq_zero
        hpZeroCoeff hp.supportSup_eq_zero
    obtain ⟨η, hη, htail⟩ :=
      exists_negativeSupportTail_orderType_eq_ordinalValue p hpOne
    let hpSupport : (p : K⟦ℝ⟧).support.IsPWO := (p : K⟦ℝ⟧).isPWO_support
    let hpUpper : ((p : K⟦ℝ⟧).support ∩ Set.Ioi η).IsPWO :=
      hpSupport.mono Set.inter_subset_left
    let hpTail : (negativeSupportTail p η).IsPWO :=
      hpSupport.mono (negativeSupportTail_subset_support p η)
    have htailSet : negativeSupportTail p η =
        (p : K⟦ℝ⟧).support ∩ Set.Ioi η := by
      ext x
      simp only [mem_negativeSupportTail_iff, Set.mem_inter_iff, Set.mem_Ioi]
      constructor
      · rintro ⟨hxp, hηx, -⟩
        exact ⟨hxp, hηx⟩
      · rintro ⟨hxp, hηx⟩
        refine ⟨hxp, hηx, lt_of_le_of_ne
          (HahnSeries.Nonpositive.support_subset p hxp) ?_⟩
        intro hx
        subst x
        apply (HahnSeries.mem_support _ _).mp hxp
        simpa [HahnSeries.Nonpositive.constantCoeff_apply] using hpZeroCoeff
    have hpLUB : IsLUB (p : K⟦ℝ⟧).support 0 :=
      (HahnSeries.Nonpositive.supportSup_eq_coe_iff.mp hp.supportSup_eq_zero).2
    obtain ⟨y, hy, hηy, -⟩ := hpLUB.exists_between hη
    have hpPrincipal : Ordinal.IsPrincipal (fun a b ↦ a + b) hpSupport.orderType :=
      by
        simpa only [hpSupport, ← HahnSeries.supportOrderType_eq_setOrderType] using
          (Ordinal.isAdditivelyPrincipal_iff_ne_zero_and_isPrincipal_add.mp
            (HahnSeries.isWeaklyPrincipal_iff.mp hp.isWeaklyPrincipal)).2
    have hupperType : hpUpper.orderType = hpSupport.orderType :=
      hpSupport.orderType_inter_Ioi_eq_of_isPrincipal hpPrincipal ⟨y, hy, hηy⟩
    apply NatOrdinal.val.injective
    calc
      (ordinalValue p).val = hpTail.orderType := htail.symm
      _ = hpUpper.orderType := hpTail.orderType_congr hpUpper htailSet
      _ = hpSupport.orderType := hupperType
      _ = (p : K⟦ℝ⟧).supportOrderType :=
        (HahnSeries.supportOrderType_eq_setOrderType _).symm
      _ = (ω^ α).val := hpType

/-- On a principal series, Berarducci's exponent-valued ordinal value equals Hahn-series degree. -/
theorem ordinalValueDegree_eq_degree_of_isPrincipal
    {p : Series K} (hp : HahnSeries.Nonpositive.IsPrincipal p) :
    ordinalValueDegree p = (p : K⟦ℝ⟧).degree := by
  have hpDegreeNe : (p : K⟦ℝ⟧).degree ≠ ⊥ := by
    intro hbot
    exact hp.ne_zero (Subtype.ext (HahnSeries.degree_eq_bot.mp hbot))
  let α := (p : K⟦ℝ⟧).degree.unbot hpDegreeNe
  have hpDegree : (p : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal) :=
    (WithBot.coe_unbot _ hpDegreeNe).symm
  rw [hpDegree]
  exact (ordinalValueDegree_eq_coe_iff p α).mpr
    (ordinalValue_eq_wpow_of_isPrincipal hp hpDegree)

/-- Berarducci multiplicativity implies that the product of two principal series is principal.
This recovers LM24, Proposition 3.6.1 directly from the single ordinal-value prerequisite. -/
theorem OrdinalValueMultiplicative.isPrincipal_mul
    (hmul : OrdinalValueMultiplicative K) {b c : Series K}
    (hb : HahnSeries.Nonpositive.IsPrincipal b)
    (hc : HahnSeries.Nonpositive.IsPrincipal c) :
    HahnSeries.Nonpositive.IsPrincipal (b * c) := by
  have hbDegreeNe : (b : K⟦ℝ⟧).degree ≠ ⊥ := by
    intro hbot
    exact hb.ne_zero (Subtype.ext (HahnSeries.degree_eq_bot.mp hbot))
  have hcDegreeNe : (c : K⟦ℝ⟧).degree ≠ ⊥ := by
    intro hbot
    exact hc.ne_zero (Subtype.ext (HahnSeries.degree_eq_bot.mp hbot))
  let α := (b : K⟦ℝ⟧).degree.unbot hbDegreeNe
  let β := (c : K⟦ℝ⟧).degree.unbot hcDegreeNe
  have hbDegree : (b : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal) :=
    (WithBot.coe_unbot _ hbDegreeNe).symm
  have hcDegree : (c : K⟦ℝ⟧).degree = (β : WithBot NatOrdinal) :=
    (WithBot.coe_unbot _ hcDegreeNe).symm
  have hbValue := ordinalValue_eq_wpow_of_isPrincipal hb hbDegree
  have hcValue := ordinalValue_eq_wpow_of_isPrincipal hc hcDegree
  have hproductValue : ordinalValue (b * c) = ω^ (α + β) := by
    rw [hmul.ordinalValue_mul, hbValue, hcValue, ← NatOrdinal.wpow_add]
  have htypeLE : ((b * c : Series K) : K⟦ℝ⟧).supportOrderType ≤
      (ω^ (α + β)).val := by
    calc
      ((b * c : Series K) : K⟦ℝ⟧).supportOrderType ≤
          (NatOrdinal.of (b : K⟦ℝ⟧).supportOrderType *
            NatOrdinal.of (c : K⟦ℝ⟧).supportOrderType).val :=
        HahnSeries.supportOrderType_mul_le_naturalMul _ _
      _ = (ω^ (α + β)).val := by
        rw [hb.supportOrderType_eq_wpow_of_degree_eq hbDegree,
          hc.supportOrderType_eq_wpow_of_degree_eq hcDegree,
          NatOrdinal.of_val, NatOrdinal.of_val, NatOrdinal.wpow_add]
  have htypeGE : (ω^ (α + β)).val ≤
      ((b * c : Series K) : K⟦ℝ⟧).supportOrderType := by
    have h := NatOrdinal.val.monotone (ordinalValue_le_supportOrderType (b * c))
    rw [hproductValue, NatOrdinal.val_wpow, NatOrdinal.val_of] at h
    simpa only [NatOrdinal.val_wpow] using h
  have htype : ((b * c : Series K) : K⟦ℝ⟧).supportOrderType =
      (ω^ (α + β)).val := le_antisymm htypeLE htypeGE
  have hnotJ : b * c ∉ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
    rw [← ordinalValue_eq_zero_iff, hproductValue]
    exact NatOrdinal.wpow_ne_zero (α + β)
  rw [HahnSeries.Nonpositive.isPrincipal_iff]
  constructor
  · rw [HahnSeries.isWeaklyPrincipal_iff, htype, NatOrdinal.val_wpow]
    exact Ordinal.isAdditivelyPrincipal_omega0_opow (α + β).val
  · apply le_antisymm (HahnSeries.Nonpositive.supportSup_le_zero (b * c))
    apply le_of_not_gt
    intro hlt
    exact hnotJ
      (HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero.mpr hlt)

/-- Projection of a Hahn series in the weak degree cut to the degree-`α` component. -/
def degreeLayerMk (α : NatOrdinal) (b : Series K)
    (hb : (b : K⟦ℝ⟧).degree ≤ (α : WithBot NatOrdinal)) :
    (HahnSeries.Nonpositive.degreeValuation K).Component α := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  have hbValue : w b ≤ (α : WithBot NatOrdinal) := by
    change (HahnSeries.Nonpositive.degreeValuation K) b ≤
      (α : WithBot NatOrdinal)
    rw [HahnSeries.Nonpositive.degreeValuation_apply]
    exact hb
  exact w.componentMk α ⟨b, (w.mem_filtrationLE_iff α b).mpr hbValue⟩

/-- `degreeLayerMk` is the quotient map to a component of the degree-graded ring. -/
theorem degreeLayerMk_eq_componentMk (α : NatOrdinal) (b : Series K)
    (hb : (b : K⟦ℝ⟧).degree ≤ (α : WithBot NatOrdinal)) :
    degreeLayerMk α b hb =
      (HahnSeries.Nonpositive.degreeValuation K).componentMk α
        ⟨b, by
          rw [MaxAddDegree.mem_filtrationLE_iff,
            HahnSeries.Nonpositive.degreeValuation_apply]
          exact hb⟩ :=
  (rfl)

/-- A representative vanishes in the fixed component of `RV̂` exactly when its degree is
strictly below the component grade. -/
@[simp]
theorem degreeLayerMk_eq_zero_iff (α : NatOrdinal) (b : Series K)
    (hb : (b : K⟦ℝ⟧).degree ≤ (α : WithBot NatOrdinal)) :
    degreeLayerMk α b hb = 0 ↔
      (b : K⟦ℝ⟧).degree < (α : WithBot NatOrdinal) := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  change w.componentMk α ⟨b, _⟩ = 0 ↔ _
  rw [w.componentMk_eq_zero_iff,
    HahnSeries.Nonpositive.degreeValuation_apply]

variable (K) in
/-- The ordinal-value degree is bounded by Hahn-series degree: the degree filtration refines the
ordinal-value filtration. -/
theorem ordinalValueDegreeValuation_le_degreeValuation (b : Series K) :
    ordinalValueDegreeValuation K b ≤ HahnSeries.Nonpositive.degreeValuation K b := by
  rw [ordinalValueDegreeValuation_apply, HahnSeries.Nonpositive.degreeValuation_apply]
  exact ordinalValueDegree_le_degree b

variable (K) in
/-- The canonical additive map from the degree-`α` component of `RV̂` to `P_α`:
the component map of the associated graded rings induced by the identity of `K((ℝ^{≤0}))`, which
does not increase the degree because `ordinalValueDegree b ≤ degree b`. -/
def degreeLayerToPrincipalComponent (α : NatOrdinal) :
    (HahnSeries.Nonpositive.degreeValuation K).Component α →+
      PrincipalComponent K α :=
  (HahnSeries.Nonpositive.degreeValuation K).componentMap (ordinalValueDegreeValuation K)
    (RingHom.id (Series K)) (ordinalValueDegreeValuation_le_degreeValuation K) α

/-- The canonical component map is the generic component map of the two filtrations. -/
theorem degreeLayerToPrincipalComponent_eq_componentMap (α : NatOrdinal) :
    degreeLayerToPrincipalComponent K α =
      (HahnSeries.Nonpositive.degreeValuation K).componentMap (ordinalValueDegreeValuation K)
        (RingHom.id (Series K)) (ordinalValueDegreeValuation_le_degreeValuation K) α :=
  (rfl)

/-- On an arbitrary weak-filtration representative, the canonical component map keeps the
underlying Hahn series and changes only the quotient filtration. -/
theorem degreeLayerToPrincipalComponent_componentMk (α : NatOrdinal)
    (b : MaxAddDegree.filtrationLE
      (HahnSeries.Nonpositive.degreeValuation K) α) :
    degreeLayerToPrincipalComponent K α
        (MaxAddDegree.componentMk
          (HahnSeries.Nonpositive.degreeValuation K) α b) =
      (ordinalValueDegreeValuation K).componentMk α
        ⟨b, by
          rw [MaxAddDegree.mem_filtrationLE_iff,
            ordinalValueDegreeValuation_apply]
          have hbDegree :=
            (MaxAddDegree.mem_filtrationLE_iff
              (HahnSeries.Nonpositive.degreeValuation K) α b).mp b.2
          rw [HahnSeries.Nonpositive.degreeValuation_apply] at hbDegree
          exact (ordinalValueDegree_le_degree (b : Series K)).trans hbDegree⟩ := by
  rw [degreeLayerToPrincipalComponent, MaxAddDegree.componentMap_componentMk]
  apply congrArg ((ordinalValueDegreeValuation K).componentMk α)
  apply Subtype.ext
  rw [MaxAddDegree.coe_mapFiltrationLE, RingHom.id_apply]

/-- The canonical component map sends a degree-`α` representative to the same series modulo
the ordinal-value cut. -/
@[simp]
theorem degreeLayerToPrincipalComponent_mk (α : NatOrdinal) (b : Series K)
    (hbDegree : (b : K⟦ℝ⟧).degree ≤ (α : WithBot NatOrdinal)) :
    degreeLayerToPrincipalComponent K α
        (degreeLayerMk α b hbDegree) =
      principalComponentMk α b
        ((ordinalValueDegree_le_coe_iff b α).mp
          ((ordinalValueDegree_le_degree b).trans hbDegree)) := by
  let wDegree := HahnSeries.Nonpositive.degreeValuation K
  change degreeLayerToPrincipalComponent K α
      (wDegree.componentMk α ⟨b, _⟩) = _
  rw [degreeLayerToPrincipalComponent_componentMk, principalComponentMk_eq_componentMk]

/-- Projection to a fixed component of `RV̂` preserves addition of representatives. -/
theorem degreeLayerMk_add (α : NatOrdinal) (b c : Series K)
    (hb : (b : K⟦ℝ⟧).degree ≤ (α : WithBot NatOrdinal))
    (hc : (c : K⟦ℝ⟧).degree ≤ (α : WithBot NatOrdinal)) :
    degreeLayerMk α (b + c)
        ((HahnSeries.degree_add_le (b : K⟦ℝ⟧) (c : K⟦ℝ⟧)).trans
          (max_le hb hc)) =
      degreeLayerMk α b hb + degreeLayerMk α c hc := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  change w.componentMk α ⟨b + c, _⟩ =
    w.componentMk α ⟨b, _⟩ + w.componentMk α ⟨c, _⟩
  rw [← map_add]
  apply congrArg (w.componentMk α)
  rfl

/-- Projection to a fixed component of `RV̂` preserves negation of representatives. -/
theorem degreeLayerMk_neg (α : NatOrdinal) (b : Series K)
    (hb : (b : K⟦ℝ⟧).degree ≤ (α : WithBot NatOrdinal)) :
    degreeLayerMk α (-b) (by simpa using hb) =
      -degreeLayerMk α b hb := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  change w.componentMk α ⟨-b, _⟩ = -w.componentMk α ⟨b, _⟩
  rw [← map_neg]
  apply congrArg (w.componentMk α)
  rfl

/-- Multiplication in the degree-graded ring `RV̂` is induced by multiplication of
representatives. -/
theorem degreeLayerMk_mul {α β : NatOrdinal} (b c : Series K)
    (hb : (b : K⟦ℝ⟧).degree ≤ (α : WithBot NatOrdinal))
    (hc : (c : K⟦ℝ⟧).degree ≤ (β : WithBot NatOrdinal)) :
    (HahnSeries.Nonpositive.degreeValuation K).componentMul
        (degreeLayerMk α b hb)
        (degreeLayerMk β c hc) =
      degreeLayerMk (α + β) (b * c) (by
        rw [Subring.coe_mul]
        exact (HahnSeries.degree_mul_le _ _).trans (add_le_add hb hc)) := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  change w.componentMul (w.componentMk α ⟨b, _⟩) (w.componentMk β ⟨c, _⟩) =
    w.componentMk (α + β) ⟨b * c, _⟩
  rw [w.componentMul_componentMk]
  apply congrArg (w.componentMk (α + β))
  apply Subtype.ext
  exact w.coe_mulFiltrationLE _ _

/-- A constant Hahn series lies in the degree-zero weak filtration. -/
theorem degree_C_le_zero (k : K) :
    (((HahnSeries.Nonpositive.C : K →+* Series K) k : Series K) :
        K⟦ℝ⟧).degree ≤ (0 : WithBot NatOrdinal) := by
  rw [HahnSeries.degree_le_zero_iff]
  rw [HahnSeries.Nonpositive.coe_C, HahnSeries.C_apply]
  exact Set.Finite.subset (Set.finite_singleton 0)
    (HahnSeries.support_single_subset (a := 0) (r := k))

/-- A nonzero constant Hahn series has degree zero. -/
theorem degree_C_eq_zero_of_ne {k : K} (hk : k ≠ 0) :
    (((HahnSeries.Nonpositive.C : K →+* Series K) k : Series K) :
        K⟦ℝ⟧).degree = (0 : WithBot NatOrdinal) := by
  apply HahnSeries.degree_eq_zero.mpr
  constructor
  · simpa only [HahnSeries.Nonpositive.coe_C] using HahnSeries.C_ne_zero hk
  · rw [HahnSeries.Nonpositive.coe_C, HahnSeries.C_apply]
    exact Set.Finite.subset (Set.finite_singleton 0)
      (HahnSeries.support_single_subset (a := 0) (r := k))

variable (K) in
private def constantToDegreeNonpositiveSubring :
    K →+* (HahnSeries.Nonpositive.degreeValuation K).nonpositiveSubring :=
  let w := HahnSeries.Nonpositive.degreeValuation K
  (HahnSeries.Nonpositive.C : K →+* Series K).codRestrict w.nonpositiveSubring fun k ↦ by
    rw [w.mem_nonpositiveSubring_iff,
      HahnSeries.Nonpositive.degreeValuation_apply]
    exact degree_C_le_zero k

variable (K) in
/-- The scalar map from coefficients to the grade-zero residue ring of Hahn-series degree. -/
def degreeLayerScalarHom :
    K →+* (HahnSeries.Nonpositive.degreeValuation K).ResidueRing :=
  let w := HahnSeries.Nonpositive.degreeValuation K
  w.residueMap.comp (constantToDegreeNonpositiveSubring K)

/-- The scalar map into the degree-zero component sends a coefficient to the class of the
corresponding
constant Hahn series. -/
theorem degreeLayerScalarHom_apply (k : K) :
    degreeLayerScalarHom K k =
      degreeLayerMk 0
        ((HahnSeries.Nonpositive.C : K →+* Series K) k)
        (degree_C_le_zero k) := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  change w.residueMap _ = w.componentMk 0 _
  rw [w.residueMap_apply]
  apply congrArg (w.componentMk 0)
  apply Subtype.ext
  rw [w.coe_nonpositiveEquivFiltrationLEZero]
  rfl

/-- Each component of `RV̂` is canonically a vector space over the coefficient field. -/
noncomputable instance degreeLayerModule (α : NatOrdinal) :
    Module K
      ((HahnSeries.Nonpositive.degreeValuation K).Component α) :=
  Module.compHom _ (degreeLayerScalarHom K)

/-- Coefficient scalar multiplication on a component of `RV̂` is the action of the
corresponding grade-zero residue class. -/
theorem degreeLayer_smul_eq_residue_smul (alpha : NatOrdinal) (k : K)
    (x : (HahnSeries.Nonpositive.degreeValuation K).Component alpha) :
    k • x = degreeLayerScalarHom K k • x :=
  (rfl)

/-- Scalar multiplication in a component of `RV̂` is multiplication of a representative by
the corresponding constant Hahn series. -/
theorem smul_degreeLayerMk (α : NatOrdinal) (k : K) (b : Series K)
    (hb : (b : K⟦ℝ⟧).degree ≤ (α : WithBot NatOrdinal)) :
    k • degreeLayerMk α b hb =
      degreeLayerMk α
        ((HahnSeries.Nonpositive.C : K →+* Series K) k * b)
        (by
          rw [Subring.coe_mul]
          exact (HahnSeries.degree_mul_le _ _).trans
            ((add_le_add (degree_C_le_zero k) hb).trans_eq (zero_add _))) := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  rw [show k • degreeLayerMk α b hb =
      (degreeLayerScalarHom K k) • degreeLayerMk α b hb from rfl]
  rw [degreeLayerScalarHom_apply]
  apply DirectSum.of_injective (β := w.Component) α
  rw [DirectSum.of_zero_smul, DirectSum.of_mul_of]
  change DirectSum.of w.Component (0 + α)
      (w.componentMul
        (degreeLayerMk 0
          ((HahnSeries.Nonpositive.C : K →+* Series K) k)
          (degree_C_le_zero k))
        (degreeLayerMk α b hb)) = _
  rw [degreeLayerMk_mul]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply Sigma.ext (zero_add α)
  exact w.componentMk_heq_of_grade_eq_of_coe_eq (zero_add α) _ _ rfl

/-- The canonical map from the components of `RV̂` to the spaces `P_α` commutes with
homogeneous multiplication. -/
theorem degreeLayerToPrincipalComponent_componentMul {α β : NatOrdinal}
    (x : (HahnSeries.Nonpositive.degreeValuation K).Component α)
    (y : (HahnSeries.Nonpositive.degreeValuation K).Component β) :
    degreeLayerToPrincipalComponent K (α + β)
        (MaxAddDegree.componentMul
          (HahnSeries.Nonpositive.degreeValuation K) x y) =
      principalComponentMul
        (degreeLayerToPrincipalComponent K α x)
        (degreeLayerToPrincipalComponent K β y) := by
  rw [principalComponentMul_eq_componentMul]
  exact MaxAddDegree.componentMap_componentMul _ _ _ _ x y

/-- The canonical component map is compatible with the coefficient-field actions on the two
degree filtrations. -/
theorem degreeLayerToPrincipalComponent_map_smul (α : NatOrdinal) (k : K)
    (x : (HahnSeries.Nonpositive.degreeValuation K).Component α) :
    degreeLayerToPrincipalComponent K α (k • x) =
      k • degreeLayerToPrincipalComponent K α x := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  induction x using QuotientAddGroup.induction_on with
  | H x =>
      rw [w.coe_component_eq_componentMk]
      let b : Series K := x
      have hb : (b : K⟦ℝ⟧).degree ≤ (α : WithBot NatOrdinal) := by
        have hbValue := (w.mem_filtrationLE_iff α b).mp x.2
        rw [HahnSeries.Nonpositive.degreeValuation_apply] at hbValue
        exact hbValue
      change degreeLayerToPrincipalComponent K α
          (k • degreeLayerMk α b hb) =
        k • degreeLayerToPrincipalComponent K α
          (degreeLayerMk α b hb)
      rw [smul_degreeLayerMk, degreeLayerToPrincipalComponent_mk,
        degreeLayerToPrincipalComponent_mk, smul_principalComponentMk]

variable (K) in
/-- The canonical component map, bundled as a `K`-linear map. -/
def degreeLayerToPrincipalComponentLinear (α : NatOrdinal) :
    (HahnSeries.Nonpositive.degreeValuation K).Component α →ₗ[K]
      PrincipalComponent K α :=
  { degreeLayerToPrincipalComponent K α with
    map_smul' := degreeLayerToPrincipalComponent_map_smul α }

@[simp]
theorem degreeLayerToPrincipalComponentLinear_apply (α : NatOrdinal)
    (x : (HahnSeries.Nonpositive.degreeValuation K).Component α) :
    degreeLayerToPrincipalComponentLinear K α x =
      degreeLayerToPrincipalComponent K α x :=
  (rfl)

/-- For exact-degree principal representatives, equality in the degree component is exactly
congruence modulo `J_{ω^α}`. This is the equal-degree case of LM24, Lemma 7.2.3. -/
theorem degreeLayerMk_eq_iff_ordinalValue_sub_lt (α : NatOrdinal) {b c : Series K}
    (hb : HahnSeries.Nonpositive.IsPrincipal b)
    (hc : HahnSeries.Nonpositive.IsPrincipal c)
    (hbDegree : (b : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal))
    (hcDegree : (c : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal)) :
    degreeLayerMk α b hbDegree.le =
        degreeLayerMk α c hcDegree.le ↔
      ordinalValue (b - c) < ω^ α := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  change w.componentMk α ⟨b, _⟩ = w.componentMk α ⟨c, _⟩ ↔ _
  rw [w.componentMk_eq_componentMk_iff,
    HahnSeries.Nonpositive.degreeValuation_apply]
  constructor
  · intro hdegree
    apply (ordinalValueDegree_lt_coe_iff (b - c) α).mp
    exact (ordinalValueDegree_le_degree (b - c)).trans_lt hdegree
  · intro hvalue
    have hdegreeLE : ((b - c : Series K) : K⟦ℝ⟧).degree ≤
        (α : WithBot NatOrdinal) := by
      change ((b : K⟦ℝ⟧) - (c : K⟦ℝ⟧)).degree ≤
        (α : WithBot NatOrdinal)
      calc
        ((b : K⟦ℝ⟧) - (c : K⟦ℝ⟧)).degree =
            ((b : K⟦ℝ⟧) + -(c : K⟦ℝ⟧)).degree := by
          rw [sub_eq_add_neg]
        _ ≤ max (b : K⟦ℝ⟧).degree (-(c : K⟦ℝ⟧)).degree :=
          HahnSeries.degree_add_le _ _
        _ = (α : WithBot NatOrdinal) := by
          rw [HahnSeries.degree_neg, hbDegree, hcDegree, max_self]
    apply lt_of_le_of_ne hdegreeLE
    intro hdegreeEq
    have hdiffDegree : ((b - c : Series K) : K⟦ℝ⟧).degree =
        (α : WithBot NatOrdinal) := hdegreeEq
    have hnegDegree : ((-c : Series K) : K⟦ℝ⟧).degree =
        (b : K⟦ℝ⟧).degree := by
      simp only [Subring.coe_neg, HahnSeries.degree_neg, hbDegree, hcDegree]
    have hsumDegree :
        (((b + (-c) : Series K) : K⟦ℝ⟧)).degree =
          (b : K⟦ℝ⟧).degree := by
      simpa only [sub_eq_add_neg, hbDegree] using hdiffDegree
    have hdiffPrincipal : HahnSeries.Nonpositive.IsPrincipal (b - c) := by
      have hprincipal := hb.add_of_degree_eq hc.neg hnegDegree hsumDegree
      simpa only [sub_eq_add_neg] using hprincipal
    have hordinalValue := ordinalValue_eq_wpow_of_isPrincipal hdiffPrincipal hdiffDegree
    rw [hordinalValue] at hvalue
    exact lt_irrefl _ hvalue

/-- A homogeneous class of `RV̂` is principal when it is zero or has a principal
representative of exactly that degree. This is the source predicate from LM24, Definition 5.2.1. -/
def IsPrincipalDegreeClass (α : NatOrdinal)
    (x : (HahnSeries.Nonpositive.degreeValuation K).Component α) :
    Prop :=
  x = 0 ∨
    ∃ (p : Series K) (_hp : HahnSeries.Nonpositive.IsPrincipal p)
      (hpDegree : (p : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal)),
      x = degreeLayerMk α p hpDegree.le

/-- Characterization of a principal homogeneous class of `RV̂` by a representative. -/
theorem isPrincipalDegreeClass_iff (α : NatOrdinal)
    (x : (HahnSeries.Nonpositive.degreeValuation K).Component α) :
    IsPrincipalDegreeClass α x ↔
      x = 0 ∨
        ∃ (p : Series K) (_hp : HahnSeries.Nonpositive.IsPrincipal p)
          (hpDegree : (p : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal)),
          x = degreeLayerMk α p hpDegree.le :=
  (Iff.rfl)

variable (K) in
/-- The principal classes of a fixed Hahn degree form the `K`-subspace `P_α` from LM24,
Proposition 5.2.4 and Corollary 5.2.5. -/
def principalDegreeClasses (α : NatOrdinal) :
    Submodule K
      ((HahnSeries.Nonpositive.degreeValuation K).Component α) where
  carrier := {x | IsPrincipalDegreeClass α x}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro x y hx hy
    change IsPrincipalDegreeClass α x at hx
    change IsPrincipalDegreeClass α y at hy
    change IsPrincipalDegreeClass α (x + y)
    rw [isPrincipalDegreeClass_iff] at hx hy ⊢
    rcases hx with rfl | ⟨p, hp, hpDegree, rfl⟩
    · simpa using hy
    rcases hy with rfl | ⟨q, hq, hqDegree, rfl⟩
    · exact Or.inr ⟨p, hp, hpDegree, by simp⟩
    have hsumLE : (((p + q : Series K) : K⟦ℝ⟧)).degree ≤
        (α : WithBot NatOrdinal) :=
      (HahnSeries.degree_add_le (p : K⟦ℝ⟧) (q : K⟦ℝ⟧)).trans
        (max_le hpDegree.le hqDegree.le)
    have hprojection :
        degreeLayerMk α p hpDegree.le +
            degreeLayerMk α q hqDegree.le =
          degreeLayerMk α (p + q) hsumLE :=
      (degreeLayerMk_add α p q hpDegree.le hqDegree.le).symm
    by_cases hzero : degreeLayerMk α (p + q) hsumLE = 0
    · exact Or.inl (hprojection.trans hzero)
    · have hsumNotLt : ¬(((p + q : Series K) : K⟦ℝ⟧).degree <
          (α : WithBot NatOrdinal)) := by
        intro hlt
        apply hzero
        let w := HahnSeries.Nonpositive.degreeValuation K
        change w.componentMk α ⟨p + q, _⟩ = 0
        rw [w.componentMk_eq_zero_iff,
          HahnSeries.Nonpositive.degreeValuation_apply]
        exact hlt
      have hsumDegree : (((p + q : Series K) : K⟦ℝ⟧)).degree =
          (α : WithBot NatOrdinal) :=
        le_antisymm hsumLE (le_of_not_gt hsumNotLt)
      have hsumPrincipal : HahnSeries.Nonpositive.IsPrincipal (p + q) :=
        hp.add_of_degree_eq hq
          (hqDegree.trans hpDegree.symm)
          (hsumDegree.trans hpDegree.symm)
      exact Or.inr ⟨p + q, hsumPrincipal, hsumDegree, hprojection⟩
  smul_mem' := by
    intro k x hx
    change IsPrincipalDegreeClass α x at hx
    change IsPrincipalDegreeClass α (k • x)
    rw [isPrincipalDegreeClass_iff] at hx ⊢
    rcases hx with rfl | ⟨p, hp, hpDegree, rfl⟩
    · exact Or.inl (smul_zero k)
    · by_cases hk : k = 0
      · subst k
        exact Or.inl
          (zero_smul K (degreeLayerMk α p hpDegree.le))
      · have hkpDegree :
            ((((HahnSeries.Nonpositive.C : K →+* Series K) k) * p : Series K) :
                K⟦ℝ⟧).degree = (α : WithBot NatOrdinal) := by
          rw [← ordinalValueDegree_eq_degree_of_isPrincipal (hp.const_mul hk),
            ordinalValueDegree_C_mul hk, ordinalValueDegree_eq_degree_of_isPrincipal hp, hpDegree]
        exact Or.inr
          ⟨(HahnSeries.Nonpositive.C : K →+* Series K) k * p,
            hp.const_mul hk, hkpDegree,
            smul_degreeLayerMk α k p hpDegree.le⟩

/-- Membership in the source presentation `P_α` is exactly the principal-class predicate. -/
theorem mem_principalDegreeClasses_iff (α : NatOrdinal)
    (x : (HahnSeries.Nonpositive.degreeValuation K).Component α) :
    x ∈ principalDegreeClasses K α ↔
      IsPrincipalDegreeClass α x :=
  (Iff.rfl)

variable (K) in
/-- Restriction of the canonical component map to the source principal subspace. -/
def principalDegreeClassesToPrincipalComponent (α : NatOrdinal) :
    principalDegreeClasses K α →ₗ[K] PrincipalComponent K α :=
  (degreeLayerToPrincipalComponentLinear K α).comp
    (principalDegreeClasses K α).subtype

/-- The restricted map is the canonical map on the underlying homogeneous class. -/
@[simp]
theorem principalDegreeClassesToPrincipalComponent_apply
    (α : NatOrdinal) (x : principalDegreeClasses K α) :
    principalDegreeClassesToPrincipalComponent K α x =
      degreeLayerToPrincipalComponent K α x :=
  (rfl)

/-- The restricted canonical map commutes with coefficient scalar multiplication. -/
theorem principalDegreeClassesToPrincipalComponent_smul
    (α : NatOrdinal) (k : K) (x : principalDegreeClasses K α) :
    principalDegreeClassesToPrincipalComponent K α (k • x) =
      k • principalDegreeClassesToPrincipalComponent K α x :=
  map_smul (principalDegreeClassesToPrincipalComponent K α) k x

private theorem principalComponentMk_ne_zero_of_isPrincipal (α : NatOrdinal)
    {p : Series K} (hp : HahnSeries.Nonpositive.IsPrincipal p)
    (hpDegree : (p : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal))
    (hpBound : ordinalValue p < ω^ (α + 1)) :
    principalComponentMk α p hpBound ≠ 0 := by
  intro hzero
  have hlt := (principalComponentMk_eq_zero_iff α p hpBound).mp hzero
  rw [ordinalValue_eq_wpow_of_isPrincipal hp hpDegree] at hlt
  exact lt_irrefl (ω^ α) hlt

variable (K) in
private theorem principalDegreeClassesToPrincipalComponent_injective (α : NatOrdinal) :
    Function.Injective (principalDegreeClassesToPrincipalComponent K α) := by
  intro x y hxy
  apply Subtype.ext
  change degreeLayerToPrincipalComponent K α x =
    degreeLayerToPrincipalComponent K α y at hxy
  have hx := (mem_principalDegreeClasses_iff α _).mp x.2
  have hy := (mem_principalDegreeClasses_iff α _).mp y.2
  rw [isPrincipalDegreeClass_iff] at hx hy
  rcases hx with hx0 | ⟨p, hp, hpDegree, hxp⟩
  · rcases hy with hy0 | ⟨q, hq, hqDegree, hyq⟩
    · exact hx0.trans hy0.symm
    · rw [hx0, hyq, map_zero, degreeLayerToPrincipalComponent_mk] at hxy
      exact (principalComponentMk_ne_zero_of_isPrincipal α hq hqDegree _
        hxy.symm).elim
  · rcases hy with hy0 | ⟨q, hq, hqDegree, hyq⟩
    · rw [hxp, hy0, degreeLayerToPrincipalComponent_mk, map_zero] at hxy
      exact (principalComponentMk_ne_zero_of_isPrincipal α hp hpDegree _ hxy).elim
    · rw [hxp, hyq, degreeLayerToPrincipalComponent_mk,
        degreeLayerToPrincipalComponent_mk] at hxy
      have hpBound : ordinalValue p < ω^ (α + 1) :=
        (ordinalValueDegree_le_coe_iff p α).mp
          ((ordinalValueDegree_le_degree p).trans hpDegree.le)
      have hqBound : ordinalValue q < ω^ (α + 1) :=
        (ordinalValueDegree_le_coe_iff q α).mp
          ((ordinalValueDegree_le_degree q).trans hqDegree.le)
      have hcongr : ordinalValue (p - q) < ω^ α :=
        (principalComponentMk_eq_iff α p q hpBound hqBound).mp hxy
      exact hxp.trans
        (((degreeLayerMk_eq_iff_ordinalValue_sub_lt α hp hq
          hpDegree hqDegree).mpr hcongr).trans hyq.symm)

variable (K) in
private theorem principalDegreeClassesToPrincipalComponent_surjective (α : NatOrdinal) :
    Function.Surjective (principalDegreeClassesToPrincipalComponent K α) := by
  intro x
  by_cases hx : x = 0
  · refine ⟨0, ?_⟩
    subst x
    exact map_zero _
  · obtain ⟨p, hpBound, hp, hpDegree, hpx⟩ :=
      exists_principal_representative_of_ne_zero α x hx
    let pClass := degreeLayerMk α p hpDegree.le
    have hpClass : pClass ∈ principalDegreeClasses K α := by
      rw [mem_principalDegreeClasses_iff, isPrincipalDegreeClass_iff]
      exact Or.inr ⟨p, hp, hpDegree, rfl⟩
    refine ⟨⟨pClass, hpClass⟩, ?_⟩
    change degreeLayerToPrincipalComponent K α pClass = x
    rw [show pClass = degreeLayerMk α p hpDegree.le from rfl,
      degreeLayerToPrincipalComponent_mk]
    exact hpx

variable (K) in
/-- The source homogeneous principal classes are canonically linearly equivalent to the intrinsic
quotient `J_{ω^(α+1)} / J_{ω^α}`. This formalizes LM24, Remark 7.2.4. -/
def principalDegreeClassesEquivPrincipalComponent (α : NatOrdinal) :
    principalDegreeClasses K α ≃ₗ[K] PrincipalComponent K α :=
  LinearEquiv.ofBijective
    (principalDegreeClassesToPrincipalComponent K α)
    ⟨principalDegreeClassesToPrincipalComponent_injective K α,
      principalDegreeClassesToPrincipalComponent_surjective K α⟩

/-- The canonical equivalence is the canonical component map on underlying classes. -/
@[simp]
theorem principalDegreeClassesEquivPrincipalComponent_apply
    (α : NatOrdinal) (x : principalDegreeClasses K α) :
    principalDegreeClassesEquivPrincipalComponent K α x =
      degreeLayerToPrincipalComponent K α x :=
  (rfl)

section Multiplication

variable [CharZero K]

/-- Multiplication of principal classes, inherited from the degree-graded ring
ring: the product of two principal series of degrees `α` and `β` is principal of degree `α + β`
(LM24, Proposition 3.6.1 and Theorem D). -/
def principalDegreeClassesMul {α β : NatOrdinal}
    (x : principalDegreeClasses K α)
    (y : principalDegreeClasses K β) :
    principalDegreeClasses K (α + β) := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  refine ⟨w.componentMul x y, ?_⟩
  rw [mem_principalDegreeClasses_iff, isPrincipalDegreeClass_iff]
  have hx := (mem_principalDegreeClasses_iff α _).mp x.2
  have hy := (mem_principalDegreeClasses_iff β _).mp y.2
  rw [isPrincipalDegreeClass_iff] at hx hy
  rcases hx with hx0 | ⟨p, hp, hpDegree, hxp⟩
  · exact Or.inl (by rw [hx0]; simp)
  rcases hy with hy0 | ⟨q, hq, hqDegree, hyq⟩
  · exact Or.inl (by rw [hy0]; simp)
  have hpqDegree : ((p * q : Series K) : K⟦ℝ⟧).degree =
      ((α + β : NatOrdinal) : WithBot NatOrdinal) := by
    rw [HahnSeries.Nonpositive.degree_mul, hpDegree, hqDegree, WithBot.coe_add]
  apply Or.inr
  refine ⟨p * q, OrdinalValueMultiplicative.isPrincipal_mul ordinalValueMultiplicative hp hq,
    hpqDegree, ?_⟩
  calc
    w.componentMul x y = w.componentMul
        (degreeLayerMk α p hpDegree.le)
        (degreeLayerMk β q hqDegree.le) := by rw [hxp, hyq]
    _ = degreeLayerMk (α + β) (p * q) hpqDegree.le :=
      degreeLayerMk_mul p q hpDegree.le hqDegree.le

/-- Multiplication of the source classes is multiplication in the degree-graded ring
ring on underlying classes. -/
theorem coe_principalDegreeClassesMul {α β : NatOrdinal}
    (x : principalDegreeClasses K α)
    (y : principalDegreeClasses K β) :
    (principalDegreeClassesMul x y :
        (HahnSeries.Nonpositive.degreeValuation K).Component
          (α + β)) =
      (HahnSeries.Nonpositive.degreeValuation K).componentMul x y :=
  (rfl)

/-- The canonical equivalence from source principal classes to the spaces `P_α` commutes with
homogeneous multiplication. -/
theorem principalDegreeClassesEquivPrincipalComponent_mul {α β : NatOrdinal}
    (x : principalDegreeClasses K α)
    (y : principalDegreeClasses K β) :
    principalDegreeClassesEquivPrincipalComponent K (α + β)
        (principalDegreeClassesMul x y) =
      principalComponentMul
        (principalDegreeClassesEquivPrincipalComponent K α x)
        (principalDegreeClassesEquivPrincipalComponent K β y) := by
  rw [principalDegreeClassesEquivPrincipalComponent_apply,
    principalDegreeClassesEquivPrincipalComponent_apply,
    principalDegreeClassesEquivPrincipalComponent_apply,
    coe_principalDegreeClassesMul]
  exact degreeLayerToPrincipalComponent_componentMul
    (x : (HahnSeries.Nonpositive.degreeValuation K).Component α)
    (y : (HahnSeries.Nonpositive.degreeValuation K).Component β)

end Multiplication

end Berarducci
