/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.RV
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueValuation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NormalForm

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.Residue
import Mathlib.Tactic.Abel

/-!
# The spaces `P_α`

For an exponent `α`, this module defines the space `P_α` intrinsically as

`J_{ω^(α+1)} / J_{ω^α}`.

Here `J_{ω^α}` is the additive subgroup of series whose ordinal value is strictly below `ω^α`.
In Lean, the quotient is the grade-`α` component of the multiplicative degree
`ordinalValueDegreeValuation K`, the leading Cantor exponent of `v_J`. Thus the quotient structure
and representative independence are inherited from the generic associated-graded construction;
no basis, complement, or chosen family of representatives occurs in the definition.

The representative API proves that equality is congruence modulo `J_{ω^α}`. It also proves the
characterization from LM24, Remark 7.2.4: every nonzero class has a principal Hahn series
representative of exact degree `α`. This characterization is a theorem about the intrinsic
quotient, not its primitive definition.

Constants act through the degree-zero residue ring, giving every homogeneous component its canonical
`K`-module structure. Everything here holds over an arbitrary coefficient field: the components and
their multiplication use only the max-additive degree structure of `ordinalValueDegreeValuation`,
that is, Berarducci, Lemma 5.5, and never the multiplicativity of the ordinal value.
-/

universe v

public noncomputable section

namespace Berarducci

open HahnSeries
open scoped DirectSum

variable {K : Type v} [Field K]

variable (K) in
/-- The source space `J_{ω^α}` of series whose ordinal value is below `ω^α`. -/
abbrev ordinalValueCut (α : NatOrdinal) :=
  (ordinalValueDegreeValuation K).filtrationLT α

theorem mem_ordinalValueCut_iff (α : NatOrdinal) (b : Series K) :
    b ∈ ordinalValueCut K α ↔ ordinalValue b < ω^ α :=
  mem_ordinalValueDegreeValuation_filtrationLT_iff b α

variable (K) in
/-- The source space `J_{ω^(α+1)}` is the weak degree filtration at `α`. -/
theorem ordinalValueCut_add_one_eq_filtrationLE (α : NatOrdinal) :
    ordinalValueCut K (α + 1) =
      (ordinalValueDegreeValuation K).filtrationLE α := by
  ext b
  rw [mem_ordinalValueCut_iff,
    mem_ordinalValueDegreeValuation_filtrationLE_iff]

variable (K) in
/-- The space `P_α = J_{ω^(α+1)} / J_{ω^α}`. -/
abbrev PrincipalComponent (α : NatOrdinal) :=
  (ordinalValueDegreeValuation K).Component α

/-- The class in `P_α` of a series in `J_{ω^(α+1)}`. -/
def principalComponentMk (α : NatOrdinal)
    (b : Series K) (hb : ordinalValue b < ω^ (α + 1)) : PrincipalComponent K α :=
  let w := ordinalValueDegreeValuation K
  w.componentMk α ⟨b, (mem_ordinalValueDegreeValuation_filtrationLE_iff b α).mpr hb⟩

/-- `principalComponentMk` is the associated-graded quotient map on the ordinal-value filtration. -/
theorem principalComponentMk_eq_componentMk (α : NatOrdinal)
    (b : Series K) (hb : ordinalValue b < ω^ (α + 1)) :
    principalComponentMk α b hb =
      (ordinalValueDegreeValuation K).componentMk α
        ⟨b, (mem_ordinalValueDegreeValuation_filtrationLE_iff b α).mpr hb⟩ :=
  (rfl)

@[simp]
theorem principalComponentMk_eq_zero_iff
    (α : NatOrdinal) (b : Series K) (hb : ordinalValue b < ω^ (α + 1)) :
    principalComponentMk α b hb = 0 ↔ ordinalValue b < ω^ α := by
  let w := ordinalValueDegreeValuation K
  change w.componentMk α ⟨b, _⟩ = 0 ↔ _
  rw [w.componentMk_eq_zero_iff]
  rw [show w b = ordinalValueDegree b from
    ordinalValueDegreeValuation_apply b]
  exact ordinalValueDegree_lt_coe_iff b α

/-- Equality in `P_α` is congruence modulo the strict cut `J_{ω^α}`. -/
theorem principalComponentMk_eq_iff (α : NatOrdinal) (b c : Series K)
    (hb : ordinalValue b < ω^ (α + 1))
    (hc : ordinalValue c < ω^ (α + 1)) :
    principalComponentMk α b hb = principalComponentMk α c hc ↔
      ordinalValue (b - c) < ω^ α := by
  let w := ordinalValueDegreeValuation K
  change w.componentMk α ⟨b, _⟩ = w.componentMk α ⟨c, _⟩ ↔ _
  rw [← sub_eq_zero, ← map_sub, w.componentMk_eq_zero_iff]
  change w (b - c) < (α : WithBot NatOrdinal) ↔ _
  rw [ordinalValueDegreeValuation_apply]
  exact ordinalValueDegree_lt_coe_iff (b - c) α

/-- Every class in `P_α` has a representative in its weak ordinal-value cut. -/
theorem exists_principalComponentMk (α : NatOrdinal) (x : PrincipalComponent K α) :
    ∃ (b : Series K) (hb : ordinalValue b < ω^ (α + 1)),
      principalComponentMk α b hb = x := by
  let w := ordinalValueDegreeValuation K
  induction x using QuotientAddGroup.induction_on with
  | H b =>
      have hb : ordinalValue (b : Series K) < ω^ (α + 1) :=
        (mem_ordinalValueDegreeValuation_filtrationLE_iff (b : Series K) α).mp b.2
      refine ⟨b, hb, ?_⟩
      rw [show principalComponentMk α b hb =
          w.componentMk α ⟨(b : Series K), _⟩ from rfl,
        w.coe_component_eq_componentMk]

private theorem supportSup_eq_zero_of_not_mem_nearConstantSubgroup
    {b : Series K} (hb : b ∉ nearConstantSubgroup K) :
    HahnSeries.Nonpositive.supportSup b = 0 := by
  apply le_antisymm (HahnSeries.Nonpositive.supportSup_le_zero b)
  apply le_of_not_gt
  intro hlt
  apply hb
  apply negativeMonomialIdeal_le_nearConstantSubgroup
  exact HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero.mpr hlt

private theorem principal_representative_of_ordinalValue_eq_wpow
    (α : NatOrdinal) (hα : 0 < α) (b : Series K)
    (hbValue : ordinalValue b = ω^ α) :
    ∃ (p : Series K),
      HahnSeries.Nonpositive.IsPrincipal p ∧
        (p : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal) ∧
        ordinalValue p < ω^ (α + 1) ∧
        ordinalValue (b - p) < ω^ α := by
  have hbOne : 1 < ordinalValue b := by
    rw [hbValue]
    simpa using NatOrdinal.wpow_lt_wpow.mpr hα
  have hbNear : b ∉ nearConstantSubgroup K := one_lt_ordinalValue_iff.mp hbOne
  obtain ⟨p, hbp, hpTypeNat⟩ :=
    mem_representativeOrderTypes_iff.mp
      (ordinalValue_mem_representativeOrderTypes b)
  have hpNear : p ∉ nearConstantSubgroup K := by
    intro hpNear
    apply hbNear
    have hsum := (nearConstantSubgroup K).add_mem hbp hpNear
    simpa only [sub_add_cancel] using hsum
  have hpType : (p : K⟦ℝ⟧).supportOrderType = (ω^ α).val := by
    have h := congrArg NatOrdinal.val hpTypeNat
    rw [hbValue] at h
    simpa using h
  have hpPrincipal : HahnSeries.Nonpositive.IsPrincipal p := by
    rw [HahnSeries.Nonpositive.isPrincipal_iff]
    constructor
    · rw [HahnSeries.isWeaklyPrincipal_iff, hpType, NatOrdinal.val_wpow]
      exact Ordinal.isAdditivelyPrincipal_omega0_opow α.val
    · exact supportSup_eq_zero_of_not_mem_nearConstantSubgroup hpNear
  have hpDegree : (p : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal) := by
    rw [HahnSeries.degree_eq_cantorDegree, hpType,
      ← NatOrdinal.cantorDegree_eq_ordinalCantorDegree,
      NatOrdinal.cantorDegree_wpow]
  have hpBound : ordinalValue p < ω^ (α + 1) := by
    apply (ordinalValue_le_supportOrderType p).trans_lt
    rw [hpType]
    exact NatOrdinal.val.strictMono (NatOrdinal.wpow_lt_wpow.mpr (lt_add_one α))
  have hdiffBound : ordinalValue (b - p) < ω^ α := by
    by_cases hdiffJ : b - p ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K
    · rw [ordinalValue_of_mem_negativeMonomialIdeal hdiffJ]
      exact NatOrdinal.wpow_pos α
    · rw [ordinalValue_of_mem_nearConstantSubgroup_of_not_mem_negativeMonomialIdeal
        hbp hdiffJ]
      simpa using NatOrdinal.wpow_lt_wpow.mpr hα
  exact ⟨p, hpPrincipal, hpDegree, hpBound, hdiffBound⟩

private theorem principal_representative_of_ordinalValue_eq_one (b : Series K)
    (hbValue : ordinalValue b = 1) :
    ∃ (p : Series K),
      HahnSeries.Nonpositive.IsPrincipal p ∧
        (p : K⟦ℝ⟧).degree = (0 : WithBot NatOrdinal) ∧
        ordinalValue p < ω^ (0 + 1 : NatOrdinal) ∧
        ordinalValue (b - p) < ω^ (0 : NatOrdinal) := by
  have hb := ordinalValue_eq_one_iff.mp hbValue
  let k := HahnSeries.Nonpositive.constantCoeff b
  have hk : k ≠ 0 := by
    intro hk
    apply hb.2
    have hmem := mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem.mp hb.1
    simpa [k, hk] using hmem
  let p : Series K := HahnSeries.Nonpositive.C k
  have hpPrincipal : HahnSeries.Nonpositive.IsPrincipal p :=
    HahnSeries.Nonpositive.isPrincipal_C hk
  have hpDegree : (p : K⟦ℝ⟧).degree = (0 : WithBot NatOrdinal) := by
    change ((HahnSeries.Nonpositive.C k : Series K) : K⟦ℝ⟧).degree =
      (0 : WithBot NatOrdinal)
    rw [HahnSeries.Nonpositive.coe_C]
    change (HahnSeries.C (Γ := ℝ) k).degree = (0 : WithBot NatOrdinal)
    rw [HahnSeries.C_apply, HahnSeries.degree_eq_cantorDegree,
      HahnSeries.supportOrderType_single hk, Ordinal.cantorDegree_one]
  have hpBound : ordinalValue p < ω^ (0 + 1 : NatOrdinal) := by
    rw [show p = HahnSeries.Nonpositive.C k from rfl, ordinalValue_C_of_ne hk]
    simpa using NatOrdinal.wpow_lt_wpow.mpr (zero_lt_one : (0 : NatOrdinal) < 1)
  have hdiffJ : b - p ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K :=
    mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem.mp hb.1
  have hdiffBound : ordinalValue (b - p) < ω^ (0 : NatOrdinal) := by
    rw [ordinalValue_of_mem_negativeMonomialIdeal hdiffJ]
    exact NatOrdinal.wpow_pos 0
  exact ⟨p, hpPrincipal, hpDegree, hpBound, hdiffBound⟩

/-- Every nonzero class in `P_α` has a principal representative of exact series degree
`α`. This is the representative characterization in LM24, Remark 7.2.4. -/
@[blueprint "fact:principal-series-representatives"
  (phase := "Ordinal value and degree")
  (title := "Principal representatives of $\\mathrm P_\\alpha$ (LM24, Remark 7.2.4)")
  (statement := /--
    Every nonzero element of $\Prin_\alpha$ is represented by a principal
    series $p$ of exact degree $\alpha$.
  -/)
  (proof := /--
  A nonzero class in $P_\alpha$ has a representative $b$ with
  $v_J(b)=\omega^\alpha$.  The principal-part theorem replaces $b$ by a
  principal series $p$ of degree $\alpha$ with $v_J(b-p)<\omega^\alpha$;
  this is exactly equality in the quotient.
  -/)]
theorem exists_principal_representative_of_ne_zero (α : NatOrdinal)
    (x : PrincipalComponent K α) (hx : x ≠ 0) :
    ∃ (p : Series K) (hpBound : ordinalValue p < ω^ (α + 1)),
      HahnSeries.Nonpositive.IsPrincipal p ∧
        (p : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal) ∧
        principalComponentMk α p hpBound = x := by
  obtain ⟨b, hbBound, hbx⟩ := exists_principalComponentMk α x
  have hbNotLower : ¬ordinalValue b < ω^ α := by
    intro hbLower
    apply hx
    rw [← hbx]
    exact (principalComponentMk_eq_zero_iff α b hbBound).mpr hbLower
  have hbDegreeLE : ordinalValueDegree b ≤ (α : WithBot NatOrdinal) :=
    (ordinalValueDegree_le_coe_iff b α).mpr hbBound
  have hbDegreeGE : (α : WithBot NatOrdinal) ≤ ordinalValueDegree b := by
    apply le_of_not_gt
    intro hbDegreeLT
    exact hbNotLower ((ordinalValueDegree_lt_coe_iff b α).mp hbDegreeLT)
  have hbDegree : ordinalValueDegree b = (α : WithBot NatOrdinal) :=
    le_antisymm hbDegreeLE hbDegreeGE
  have hbValue : ordinalValue b = ω^ α :=
    (ordinalValueDegree_eq_coe_iff b α).mp hbDegree
  rcases eq_or_ne α 0 with rfl | hα
  · obtain ⟨p, hp, hpDegree, hpBound, hdiff⟩ :=
      principal_representative_of_ordinalValue_eq_one b (by simpa using hbValue)
    refine ⟨p, hpBound, hp, hpDegree, ?_⟩
    calc
      principalComponentMk 0 p hpBound =
          principalComponentMk 0 b hbBound :=
        (principalComponentMk_eq_iff 0 p b hpBound hbBound).mpr (by
          have hdiffEq : p - b = -(b - p) := by abel
          rw [hdiffEq, ordinalValue_neg]
          exact hdiff)
      _ = x := hbx
  · obtain ⟨p, hp, hpDegree, hpBound, hdiff⟩ :=
      principal_representative_of_ordinalValue_eq_wpow α
        (bot_lt_iff_ne_bot.mpr hα) b hbValue
    refine ⟨p, hpBound, hp, hpDegree, ?_⟩
    calc
      principalComponentMk α p hpBound =
          principalComponentMk α b hbBound :=
        (principalComponentMk_eq_iff α p b hpBound hbBound).mpr (by
          have hdiffEq : p - b = -(b - p) := by abel
          rw [hdiffEq, ordinalValue_neg]
          exact hdiff)
      _ = x := hbx

/-- Multiplication `P_α × P_β → P_{α + β}`, where addition is the Hessenberg sum. -/
def principalComponentMul {α β : NatOrdinal} :
    PrincipalComponent K α → PrincipalComponent K β → PrincipalComponent K (α + β) :=
  (ordinalValueDegreeValuation K).componentMul

/-- Intrinsic homogeneous multiplication is the associated-graded component multiplication. -/
theorem principalComponentMul_eq_componentMul {α β : NatOrdinal}
    (x : PrincipalComponent K α) (y : PrincipalComponent K β) :
    principalComponentMul x y =
      (ordinalValueDegreeValuation K).componentMul x y :=
  (rfl)

/-- Products of representatives from the weak cuts at `α` and `β` lie in the weak cut at
`α + β`. -/
theorem ordinalValue_mul_lt_wpow_add_one {α β : NatOrdinal}
    {b c : Series K} (hb : ordinalValue b < ω^ (α + 1))
    (hc : ordinalValue c < ω^ (β + 1)) :
    ordinalValue (b * c) < ω^ (α + β + 1) := by
  apply (ordinalValueDegree_le_coe_iff (b * c) (α + β)).mp
  exact (ordinalValueDegree_mul_le_add b c).trans (add_le_add
    ((ordinalValueDegree_le_coe_iff b α).mpr hb)
    ((ordinalValueDegree_le_coe_iff c β).mpr hc))

/-- Homogeneous multiplication is induced by multiplication of representatives. -/
@[simp]
theorem principalComponentMul_mk {α β : NatOrdinal} (b c : Series K)
    (hb : ordinalValue b < ω^ (α + 1))
    (hc : ordinalValue c < ω^ (β + 1)) :
    principalComponentMul
        (principalComponentMk α b hb)
        (principalComponentMk β c hc) =
      principalComponentMk (α + β) (b * c)
        (ordinalValue_mul_lt_wpow_add_one hb hc) := by
  let w := ordinalValueDegreeValuation K
  change w.componentMul
      (w.componentMk α ⟨b, _⟩)
      (w.componentMk β ⟨c, _⟩) =
    w.componentMk (α + β) ⟨b * c, _⟩
  rw [w.componentMul_componentMk]
  apply congrArg (w.componentMk (α + β))
  apply Subtype.ext
  exact w.coe_mulFiltrationLE _ _

/-- A constant has ordinal value below the first positive principal cut. -/
theorem ordinalValue_C_lt_wpow_one (k : K) :
    ordinalValue ((HahnSeries.Nonpositive.C : K →+* Series K) k) <
      ω^ (0 + 1 : NatOrdinal) := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [ordinalValue_C_of_ne hk]
    simpa only [zero_add, NatOrdinal.wpow_zero] using
      NatOrdinal.wpow_lt_wpow.mpr (zero_lt_one : (0 : NatOrdinal) < 1)

variable (K) in
private def constantToOrdinalValueNonpositiveSubring :
    K →+* (ordinalValueDegreeValuation K).nonpositiveSubring :=
  let w := ordinalValueDegreeValuation K
  (HahnSeries.Nonpositive.C : K →+* Series K).codRestrict w.nonpositiveSubring fun k ↦ by
    rw [w.mem_nonpositiveSubring_iff,
      ordinalValueDegreeValuation_apply]
    by_cases hk : k = 0
    · subst k
      simp
    · rw [ordinalValueDegree_C_of_ne hk]

variable (K) in
/-- The scalar map from constants to the grade-zero residue ring of the exponent-valued order
value. -/
def principalComponentScalarHom :
    K →+* (ordinalValueDegreeValuation K).ResidueRing :=
  let w := ordinalValueDegreeValuation K
  w.residueMap.comp (constantToOrdinalValueNonpositiveSubring K)

/-- The scalar map `K → P_0` sends a coefficient to the class of the corresponding constant
series. -/
theorem principalComponentScalarHom_apply (k : K) :
    principalComponentScalarHom K k =
      principalComponentMk 0
        ((HahnSeries.Nonpositive.C : K →+* Series K) k)
        (ordinalValue_C_lt_wpow_one k) := by
  let w := ordinalValueDegreeValuation K
  change w.residueMap _ = w.componentMk 0 _
  rw [w.residueMap_apply]
  apply congrArg (w.componentMk 0)
  apply Subtype.ext
  rw [w.coe_nonpositiveEquivFiltrationLEZero]
  rfl

variable (K) in
/-- Distinct coefficients determine distinct classes in `P_0`. -/
theorem principalComponentScalarHom_injective :
    Function.Injective (principalComponentScalarHom K) := by
  intro k l hkl
  have hsub : principalComponentScalarHom K (k - l) = 0 := by
    rw [map_sub, hkl, sub_self]
  rw [principalComponentScalarHom_apply,
    principalComponentMk_eq_zero_iff] at hsub
  by_contra hne
  rw [ordinalValue_C_of_ne (sub_ne_zero.mpr hne)] at hsub
  exact (lt_irrefl (1 : NatOrdinal)) (by
    simpa only [NatOrdinal.wpow_zero] using hsub)

variable (K) in
/-- Every grade-zero principal class is represented by a unique coefficient. -/
theorem principalComponentScalarHom_surjective :
    Function.Surjective (principalComponentScalarHom K) := by
  intro x
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  obtain ⟨p, hpBound, _, _, hpx⟩ :=
    exists_principal_representative_of_ne_zero 0 x hx
  let k := HahnSeries.Nonpositive.constantCoeff p
  refine ⟨k, ?_⟩
  rw [principalComponentScalarHom_apply, ← hpx]
  apply (principalComponentMk_eq_iff 0
    (HahnSeries.Nonpositive.C k) p
    (ordinalValue_C_lt_wpow_one k) hpBound).mpr
  have hpNotLower : ¬ordinalValue p < ω^ (0 : NatOrdinal) := by
    intro hpLower
    apply hx
    rw [← hpx]
    exact (principalComponentMk_eq_zero_iff 0 p hpBound).mpr hpLower
  have hpDegreeLE : ordinalValueDegree p ≤ (0 : WithBot NatOrdinal) :=
    (ordinalValueDegree_le_coe_iff p 0).mpr hpBound
  have hpDegreeGE : (0 : WithBot NatOrdinal) ≤ ordinalValueDegree p := by
    apply le_of_not_gt
    intro hpDegreeLT
    exact hpNotLower ((ordinalValueDegree_lt_coe_iff p 0).mp hpDegreeLT)
  have hpValue : ordinalValue p = 1 := by
    simpa only [NatOrdinal.wpow_zero] using
      (ordinalValueDegree_eq_coe_iff p 0).mp
        (le_antisymm hpDegreeLE hpDegreeGE)
  have hpJ :
      p - HahnSeries.Nonpositive.C k ∈
        HahnSeries.Nonpositive.negativeMonomialIdeal K :=
    mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem.mp
      (ordinalValue_eq_one_iff.mp hpValue).1
  rw [show HahnSeries.Nonpositive.C k - p =
      -(p - HahnSeries.Nonpositive.C k) by abel]
  rw [ordinalValue_neg, ordinalValue_of_mem_negativeMonomialIdeal hpJ]
  exact NatOrdinal.wpow_pos 0

/-- The space `P_0` is nontrivial because it contains the coefficient field. -/
instance principalComponentZeroNontrivial :
    Nontrivial (PrincipalComponent K 0) :=
  (principalComponentScalarHom_injective K).nontrivial

/-- Every `P_α` is canonically a vector space over `K`. -/
noncomputable instance principalComponentModule (α : NatOrdinal) :
    Module K (PrincipalComponent K α) :=
  Module.compHom (PrincipalComponent K α) (principalComponentScalarHom K)

/-- Scalar multiplication on `P_α` is multiplication of a representative by the corresponding
constant series. -/
theorem smul_principalComponentMk (α : NatOrdinal)
    (k : K) (b : Series K) (hb : ordinalValue b < ω^ (α + 1)) :
    k • principalComponentMk α b hb =
      principalComponentMk α
        ((HahnSeries.Nonpositive.C : K →+* Series K) k * b)
        (by
          simpa only [zero_add] using
            ordinalValue_mul_lt_wpow_add_one
              (ordinalValue_C_lt_wpow_one k) hb) := by
  let w := ordinalValueDegreeValuation K
  rw [show k • principalComponentMk α b hb =
      (principalComponentScalarHom K k) • principalComponentMk α b hb from rfl]
  rw [principalComponentScalarHom_apply]
  apply DirectSum.of_injective (β := w.Component) α
  rw [DirectSum.of_zero_smul, DirectSum.of_mul_of]
  change DirectSum.of w.Component (0 + α)
      (principalComponentMul
        (principalComponentMk 0
          ((HahnSeries.Nonpositive.C : K →+* Series K) k)
          (ordinalValue_C_lt_wpow_one k))
        (principalComponentMk α b hb)) = _
  rw [principalComponentMul_mk]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply Sigma.ext (zero_add α)
  exact w.componentMk_heq_of_grade_eq_of_coe_eq (zero_add α) _ _ rfl

end Berarducci
