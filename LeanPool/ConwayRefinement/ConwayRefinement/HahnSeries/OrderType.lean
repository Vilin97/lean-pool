/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SeparatedSupport
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Truncation
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.Degree
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SetOrderType
public import LeanPool.ConwayRefinement.ConwayRefinement.Order.Archimedean
public import Mathlib.RingTheory.HahnSeries.Multiplication

import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.Sumset

/-!
# Support order type and degree of a Hahn series

LM24 orders the support of a generalized power series by increasing exponent. Accordingly,
`HahnSeries.supportOrderType` is the ordinal type of the strict order `<` on the support; no order
reversal occurs in this module. For a linearly ordered exponent type, Mathlib's `IsPWO` support
condition is equivalent to the well-foundedness needed for this ordinal type.

If the exponent type belongs to `Type u`, the order type and degree belong to `Ordinal.{u}` and
`WithBot NatOrdinal.{u}`, independently of the universe of the coefficients. The degree uses
LM24's convention: a nonzero series has the leading Cantor exponent of its support order type,
whereas the zero series has degree `⊥`.

These definitions formalize LM24, Sections 1.2, 1.5, 2.2, and 3.1. Multiplicativity is a later
theorem and is not built into the definitions.

The support-decomposition theorems use the strict lower-to-upper relation
`HahnSeries.SupportBelow` and the generic support lemmas in
`ConwayRefinement.HahnSeries.SeparatedSupport`.
-/

universe u v

public noncomputable section

namespace HahnSeries

open Ordinal

variable {R : Type v} {G : Type u} [LinearOrder G]

section ZeroCoefficients

variable [Zero R]

/-- The ordinary ordinal order type of a Hahn series support, ordered by increasing exponent. -/
def supportOrderType (x : R⟦G⟧) : Ordinal.{u} :=
  x.isPWO_support.orderType

/-- Support order type is the generic order type of the partially well-ordered support. -/
theorem supportOrderType_eq_setOrderType (x : R⟦G⟧) :
    supportOrderType x = x.isPWO_support.orderType :=
  (rfl)

/-- Compute `supportOrderType` from an order isomorphism out of the support. -/
theorem supportOrderType_eq_typeLT {x : R⟦G⟧} {A : Type u} [LinearOrder A]
    [WellFoundedLT A] (e : x.support ≃o A) :
    supportOrderType x = typeLT A :=
  x.isPWO_support.orderType_eq_typeLT_of_orderIso e

/-- Compute `supportOrderType` from a relation isomorphism to an arbitrary well-order. -/
theorem supportOrderType_eq_type_of_relIso {x : R⟦G⟧} {A : Type u}
    {r : A → A → Prop} [IsWellOrder A r]
    (e : Subrel (· < · : G → G → Prop) (· ∈ x.support) ≃r r) :
    supportOrderType x = Ordinal.type r :=
  x.isPWO_support.orderType_eq_type_of_relIso e

@[simp]
theorem supportOrderType_eq_zero {x : R⟦G⟧} : supportOrderType x = 0 ↔ x = 0 := by
  rw [supportOrderType, Set.IsPWO.orderType_eq_zero]
  exact support_eq_empty_iff

@[simp]
theorem supportOrderType_zero : supportOrderType (0 : R⟦G⟧) = 0 :=
  supportOrderType_eq_zero.mpr rfl

/-- A nonzero single-term Hahn series has ordinary support order type one. -/
theorem supportOrderType_single {a : G} {r : R} (hr : r ≠ 0) :
    (HahnSeries.single a r).supportOrderType = 1 := by
  have hsupport : (HahnSeries.single a r).support = {a} :=
    HahnSeries.support_single_of_ne hr
  let singletonOrderIso : ({a} : Set G) ≃o PUnit :=
    { toEquiv := Equiv.Set.singleton a
      map_rel_iff' := by simp }
  let e : (HahnSeries.single a r).support ≃o PUnit :=
    (Set.orderIsoOfEq _ {a} hsupport).trans singletonOrderIso
  rw [supportOrderType_eq_typeLT e]
  exact Ordinal.type_eq_one_of_unique _

/-- Inclusion of supports cannot decrease their ordinary ordinal order type. -/
theorem supportOrderType_mono {x y : R⟦G⟧} (h : x.support ⊆ y.support) :
    supportOrderType x ≤ supportOrderType y :=
  Set.IsPWO.orderType_mono x.isPWO_support y.isPWO_support h

/-- A Hahn series has finite support exactly when its support order type is below `ω`. -/
theorem support_finite_iff_supportOrderType_lt_omega {x : R⟦G⟧} :
    x.support.Finite ↔ supportOrderType x < Ordinal.omega0 :=
  x.isPWO_support.finite_iff_orderType_lt_omega

/-- The leading Cantor exponent of the support order type, with value `⊥` at zero. -/
def degree (x : R⟦G⟧) : WithBot NatOrdinal.{u} :=
  Ordinal.cantorDegree x.supportOrderType

/-- Degree is the leading Cantor exponent of the support order type. -/
theorem degree_eq_cantorDegree (x : R⟦G⟧) :
    degree x = Ordinal.cantorDegree x.supportOrderType :=
  (rfl)

@[simp]
theorem degree_eq_bot {x : R⟦G⟧} : degree x = ⊥ ↔ x = 0 := by
  rw [degree, Ordinal.cantorDegree_eq_bot, supportOrderType_eq_zero]

@[simp]
theorem degree_zero : degree (0 : R⟦G⟧) = ⊥ :=
  degree_eq_bot.mpr rfl

/-- Degree zero is equivalent to nonzero finite support. -/
@[simp]
theorem degree_eq_zero {x : R⟦G⟧} :
    degree x = (0 : WithBot NatOrdinal) ↔ x ≠ 0 ∧ x.support.Finite := by
  rw [degree, Ordinal.cantorDegree_eq_zero]
  constructor
  · rintro ⟨hot, hlt⟩
    exact ⟨supportOrderType_eq_zero.not.mp hot,
      support_finite_iff_supportOrderType_lt_omega.mpr hlt⟩
  · rintro ⟨hx, hfinite⟩
    exact ⟨supportOrderType_eq_zero.not.mpr hx,
      support_finite_iff_supportOrderType_lt_omega.mp hfinite⟩

/-- The degree of a nonzero Hahn series is nonnegative. -/
theorem zero_le_degree_of_ne_zero {x : R⟦G⟧} (hx : x ≠ 0) :
    0 ≤ x.degree := by
  rw [degree_eq_cantorDegree,
    Ordinal.cantorDegree_of_ne_zero (supportOrderType_eq_zero.not.mpr hx)]
  exact WithBot.coe_le_coe.mpr bot_le

/-- Degree is at most zero exactly for finite-support Hahn series, including the zero series. -/
@[simp]
theorem degree_le_zero_iff {x : R⟦G⟧} :
    degree x ≤ 0 ↔ x.support.Finite := by
  constructor
  · intro hdegree
    by_cases hx : x = 0
    · simp [hx]
    · have hzero : 0 ≤ degree x := zero_le_degree_of_ne_zero hx
      have hxDegree : degree x = 0 := le_antisymm hdegree hzero
      exact (degree_eq_zero.mp hxDegree).2
  · intro hfinite
    by_cases hx : x = 0
    · simp [hx]
    · rw [degree_eq_zero.mpr ⟨hx, hfinite⟩]

/-- A Hahn series has positive degree exactly when its support is infinite. -/
theorem degree_pos_iff_support_infinite {x : R⟦G⟧} :
    0 < degree x ↔ x.support.Infinite := by
  rw [← not_le, degree_le_zero_iff]
  exact Set.not_finite

/-- Degree is strictly below zero exactly at the zero Hahn series. -/
@[simp]
theorem degree_lt_zero_iff {x : R⟦G⟧} :
    degree x < 0 ↔ x = 0 := by
  constructor
  · intro hdegree
    by_contra hx
    exact (not_lt_of_ge (zero_le_degree_of_ne_zero hx)) hdegree
  · rintro rfl
    simp

/-- This is LM24's maximum characterization of the degree of a nonzero Hahn series. -/
theorem coe_le_degree_iff {x : R⟦G⟧} {a : Ordinal.{u}} (hx : x ≠ 0) :
    (NatOrdinal.of a : WithBot NatOrdinal) ≤ degree x ↔
      Ordinal.omega0 ^ a ≤ supportOrderType x := by
  exact Ordinal.coe_le_cantorDegree_iff (supportOrderType_eq_zero.not.mpr hx)

/-- A degree lies strictly below `α` exactly when the support order type lies strictly below
`ω^α`. -/
theorem degree_lt_coe_iff_supportOrderType_lt_wpow (x : R⟦G⟧)
    (α : NatOrdinal) :
    degree x < (α : WithBot NatOrdinal) ↔
      supportOrderType x < (ω^ α).val := by
  by_cases hx : x = 0
  · subst x
    rw [degree_zero, supportOrderType_zero]
    constructor
    · intro _
      exact NatOrdinal.val.strictMono (NatOrdinal.wpow_pos α)
    · intro _
      exact WithBot.bot_lt_coe α
  · rw [← not_le, ← not_le]
    apply not_congr
    simpa only [NatOrdinal.of_val, NatOrdinal.val_wpow] using
      coe_le_degree_iff (x := x) (a := α.val) hx

/-- Inclusion of supports cannot decrease degree. -/
theorem degree_mono_support {x y : R⟦G⟧} (h : x.support ⊆ y.support) :
    degree x ≤ degree y :=
  Ordinal.cantorDegree_mono (supportOrderType_mono h)

/-- Weak lower truncation cannot increase degree. This strengthens the final consequence following
LM24, Definition 3.2.2 by removing its unnecessary properness hypothesis. -/
theorem degree_truncLE_le (c : G) (x : R⟦G⟧) :
    (truncLE c x).degree ≤ x.degree :=
  degree_mono_support (support_truncLE_subset c x)

end ZeroCoefficients

section Addition

variable [AddMonoid R]

/-- A Hahn series has support order type `a + b` exactly when it is a sum whose first support lies
strictly below its second support and whose summands have support order types `a` and `b`. This is
LM24, Proposition 3.2.1, generalized from field coefficients and a fixed cardinal support bound to
additive-monoid coefficients and unrestricted Hahn series. The constructed summands have supports
contained in the original support, so the result restricts to the source's support regime. -/
theorem supportOrderType_eq_add_iff (x : R⟦G⟧) (a b : Ordinal.{u}) :
    x.supportOrderType = a + b ↔
      ∃ y z : R⟦G⟧,
        SupportBelow y z ∧
          y.supportOrderType = a ∧
          z.supportOrderType = b ∧
          x = y + z := by
  classical
  constructor
  · intro htype
    rw [supportOrderType_eq_setOrderType] at htype
    obtain ⟨s, t, hs, ht, hsx, htx, hst, hsa, htb, hunion⟩ :=
      (x.isPWO_support.orderType_eq_add_iff a b).mp htype
    let y : R⟦G⟧ := filter (· ∈ s) x
    let z : R⟦G⟧ := filter (· ∈ t) x
    have hsy : y.support = s := by
      change (filter (· ∈ s) x).support = s
      rw [support_filter]
      ext i
      constructor
      · exact fun hi ↦ hi.2
      · exact fun hi ↦ ⟨hsx hi, hi⟩
    have htz : z.support = t := by
      change (filter (· ∈ t) x).support = t
      rw [support_filter]
      ext i
      constructor
      · exact fun hi ↦ hi.2
      · exact fun hi ↦ ⟨htx hi, hi⟩
    have hsum : x = y + z := by
      ext i
      by_cases hi : i ∈ x.support
      · rw [hunion] at hi
        rcases hi with his | hit
        · have hit' : i ∉ t := by
            intro hit
            exact (hst i his i hit).false
          change x.coeff i =
            (filter (· ∈ s) x).coeff i + (filter (· ∈ t) x).coeff i
          simp [his, hit']
        · have his' : i ∉ s := by
            intro his
            exact (hst i his i hit).false
          change x.coeff i =
            (filter (· ∈ s) x).coeff i + (filter (· ∈ t) x).coeff i
          simp [his', hit]
      · have hcoeff : x.coeff i = 0 := not_ne_iff.mp hi
        have his : i ∉ s := fun his ↦ hi (hsx his)
        have hit : i ∉ t := fun hit ↦ hi (htx hit)
        change x.coeff i =
          (filter (· ∈ s) x).coeff i + (filter (· ∈ t) x).coeff i
        simp [his, hit, hcoeff]
    refine ⟨y, z, ?_, ?_, ?_, hsum⟩
    · rw [supportBelow_iff]
      simpa only [hsy, htz] using hst
    · calc
        y.supportOrderType = y.isPWO_support.orderType :=
          supportOrderType_eq_setOrderType y
        _ = hs.orderType := Set.IsPWO.orderType_congr _ _ hsy
        _ = a := hsa
    · calc
        z.supportOrderType = z.isPWO_support.orderType :=
          supportOrderType_eq_setOrderType z
        _ = ht.orderType := Set.IsPWO.orderType_congr _ _ htz
        _ = b := htb
  · rintro ⟨y, z, hyz, hya, hzb, rfl⟩
    have hsupport : (y + z).support = y.support ∪ z.support :=
      support_add_eq_union_of_supportBelow y z hyz
    rw [supportOrderType_eq_setOrderType]
    apply ((y + z).isPWO_support.orderType_eq_add_iff a b).mpr
    refine ⟨y.support, z.support, y.isPWO_support, z.isPWO_support, ?_, ?_, ?_,
      ?_, ?_, hsupport⟩
    · rw [hsupport]
      exact Set.subset_union_left
    · rw [hsupport]
      exact Set.subset_union_right
    · intro i hi j hj
      exact hyz.lt hi hj
    · exact (supportOrderType_eq_setOrderType y).symm.trans hya
    · exact (supportOrderType_eq_setOrderType z).symm.trans hzb

/-- A decomposition from `supportOrderType_eq_add_iff` is uniquely determined by the order type of
its lower summand. This is the uniqueness used when LM24 iterates Proposition 3.2.1. -/
theorem add_decomposition_unique {x₀ x₁ y₀ y₁ : R⟦G⟧}
    (hx : SupportBelow x₀ x₁)
    (hy : SupportBelow y₀ y₁)
    (htype : x₀.supportOrderType = y₀.supportOrderType)
    (hsum : x₀ + x₁ = y₀ + y₁) :
    x₀ = y₀ ∧ x₁ = y₁ := by
  have hxSupport : (x₀ + x₁).support = x₀.support ∪ x₁.support :=
    support_add_eq_union_of_supportBelow x₀ x₁ hx
  have hySupport : (x₀ + x₁).support = y₀.support ∪ y₁.support :=
    (congrArg support hsum).trans (support_add_eq_union_of_supportBelow y₀ y₁ hy)
  have htype' : x₀.isPWO_support.orderType = y₀.isPWO_support.orderType := by
    rw [← supportOrderType_eq_setOrderType, ← supportOrderType_eq_setOrderType]
    exact htype
  obtain ⟨hlower, hupper⟩ :=
    Set.IsPWO.orderType_split_unique x₀.isPWO_support y₀.isPWO_support
      (fun _ hi _ hj ↦ hx.lt hi hj) (fun _ hi _ hj ↦ hy.lt hi hj)
      hxSupport hySupport htype'
  constructor
  · ext i
    by_cases hi : i ∈ x₀.support
    · have hi' : i ∈ y₀.support := hlower ▸ hi
      have hx₁ : x₁.coeff i = 0 := by
        rw [← not_ne_iff, ← mem_support]
        intro hi₁
        exact (hx.lt hi hi₁).false
      have hy₁ : y₁.coeff i = 0 := by
        rw [← not_ne_iff, ← mem_support]
        intro hi₁
        exact (hy.lt hi' hi₁).false
      have hcoeff := congrArg (fun z : R⟦G⟧ => z.coeff i) hsum
      simpa [hx₁, hy₁] using hcoeff
    · have hi' : i ∉ y₀.support := by
        rw [← hlower]
        exact hi
      exact (not_ne_iff.mp hi).trans (not_ne_iff.mp hi').symm
  · ext i
    by_cases hi : i ∈ x₁.support
    · have hi' : i ∈ y₁.support := hupper ▸ hi
      have hx₀ : x₀.coeff i = 0 := by
        rw [← not_ne_iff, ← mem_support]
        intro hi₀
        exact (hx.lt hi₀ hi).false
      have hy₀ : y₀.coeff i = 0 := by
        rw [← not_ne_iff, ← mem_support]
        intro hi₀
        exact (hy.lt hi₀ hi').false
      have hcoeff := congrArg (fun z : R⟦G⟧ => z.coeff i) hsum
      simpa [hx₀, hy₀] using hcoeff
    · have hi' : i ∉ y₁.support := by
        rw [← hupper]
        exact hi
      exact (not_ne_iff.mp hi).trans (not_ne_iff.mp hi').symm

/-- The support order type of a pairwise support-separated finite sum is the ordinary ordinal sum
of the support order types, in list order. -/
theorem supportOrderType_list_sum {l : List R⟦G⟧} (hpair : l.Pairwise SupportBelow) :
    l.sum.supportOrderType = (l.map supportOrderType).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.pairwise_cons] at hpair
      have hbelow : SupportBelow x xs.sum := supportBelow_list_sum hpair.1
      have hadd := (supportOrderType_eq_add_iff (x + xs.sum)
        x.supportOrderType xs.sum.supportOrderType).mpr
          ⟨x, xs.sum, hbelow, rfl, rfl, rfl⟩
      simp only [List.sum_cons, List.map_cons, hadd, ih hpair.2]

/-- The support order type splits at a strict lower and weak upper truncation. This is the first
order-type equality following LM24, Definition 3.2.2. -/
theorem supportOrderType_eq_truncLT_add_truncGE (c : G) (x : R⟦G⟧) :
    x.supportOrderType =
      (truncLT c x).supportOrderType + (truncGE c x).supportOrderType := by
  apply (supportOrderType_eq_add_iff x _ _).mpr
  refine ⟨truncLT c x, truncGE c x, ?_, rfl, rfl, ?_⟩
  · rw [supportBelow_iff]
    intro i hi j hj
    rw [support_truncLT] at hi
    rw [support_truncGE] at hj
    exact hi.2.trans_le hj.2
  · exact (truncLT_add_truncGE c x).symm

/-- The support order type splits at a weak lower and strict upper truncation. This is the second
order-type equality following LM24, Definition 3.2.2. -/
theorem supportOrderType_eq_truncLE_add_truncGT (c : G) (x : R⟦G⟧) :
    x.supportOrderType =
      (truncLE c x).supportOrderType + (truncGT c x).supportOrderType := by
  apply (supportOrderType_eq_add_iff x _ _).mpr
  refine ⟨truncLE c x, truncGT c x, ?_, rfl, rfl, ?_⟩
  · rw [supportBelow_iff]
    intro i hi j hj
    rw [support_truncLE] at hi
    rw [support_truncGT] at hj
    exact hi.2.trans_lt hj.2
  · exact (truncLE_add_truncGT c x).symm

/-- A proper weak lower truncation has strictly smaller support order type. This is the strict
inequality following LM24, Definition 3.2.2. -/
theorem supportOrderType_truncLE_lt (c : G) {x : R⟦G⟧} (h : truncLE c x ≠ x) :
    (truncLE c x).supportOrderType < x.supportOrderType := by
  have hupper : truncGT c x ≠ 0 := by
    intro hzero
    apply h
    calc
      truncLE c x = truncLE c x + truncGT c x := by rw [hzero, add_zero]
      _ = x := truncLE_add_truncGT c x
  rw [supportOrderType_eq_truncLE_add_truncGT c x]
  exact lt_add_of_pos_right _
    (pos_iff_ne_zero.mpr (supportOrderType_eq_zero.not.mpr hupper))

/-- The order type of the support of a sum is at most the Hessenberg sum of the two support order
types. This is LM24, Proposition 3.1.1(1), generalized from a field of coefficients. -/
theorem supportOrderType_add_le_naturalAdd (x y : R⟦G⟧) :
    supportOrderType (x + y) ≤
      (NatOrdinal.of x.supportOrderType + NatOrdinal.of y.supportOrderType).val := by
  calc
    supportOrderType (x + y) = (x + y).isPWO_support.orderType :=
      supportOrderType_eq_setOrderType (x + y)
    _ ≤ (x.isPWO_support.union y.isPWO_support).orderType :=
      Set.IsPWO.orderType_mono (x + y).isPWO_support
        (x.isPWO_support.union y.isPWO_support) (support_add_subset x y)
    _ ≤ (NatOrdinal.of x.supportOrderType +
        NatOrdinal.of y.supportOrderType).val := by
      simpa only [← supportOrderType_eq_setOrderType] using
        Set.IsPWO.orderType_union_le_naturalAdd x.isPWO_support y.isPWO_support

/-- The degree of a sum is at most the maximum of the two degrees. This is LM24,
Corollary 3.1.2(1), generalized from a field of coefficients. -/
theorem degree_add_le (x y : R⟦G⟧) :
    degree (x + y) ≤ max (degree x) (degree y) := by
  calc
    degree (x + y) = Ordinal.cantorDegree (x + y).supportOrderType :=
      degree_eq_cantorDegree (x + y)
    _ ≤ Ordinal.cantorDegree
        (NatOrdinal.of x.supportOrderType + NatOrdinal.of y.supportOrderType).val :=
      Ordinal.cantorDegree_mono (supportOrderType_add_le_naturalAdd x y)
    _ = NatOrdinal.cantorDegree
        (NatOrdinal.of x.supportOrderType + NatOrdinal.of y.supportOrderType) :=
      (NatOrdinal.cantorDegree_eq_ordinalCantorDegree _).symm
    _ = max (degree x) (degree y) := by
      rw [NatOrdinal.cantorDegree_add, NatOrdinal.cantorDegree_of,
        NatOrdinal.cantorDegree_of, degree_eq_cantorDegree,
        degree_eq_cantorDegree]

end Addition

section AddGroup

variable [AddGroup R]

/-- Negation preserves ordinary support order type. -/
@[simp]
theorem supportOrderType_neg (x : R⟦G⟧) :
    (-x).supportOrderType = x.supportOrderType := by
  calc
    (-x).supportOrderType = (-x).isPWO_support.orderType :=
      supportOrderType_eq_setOrderType (-x)
    _ = x.isPWO_support.orderType :=
      Set.IsPWO.orderType_congr _ _ support_neg
    _ = x.supportOrderType := (supportOrderType_eq_setOrderType x).symm

/-- Negation preserves degree. -/
@[simp]
theorem degree_neg (x : R⟦G⟧) : (-x).degree = x.degree := by
  rw [degree_eq_cantorDegree, degree_eq_cantorDegree, supportOrderType_neg]

/-- Adding a series of strictly smaller degree does not change the larger degree. -/
theorem degree_add_eq_left_of_lt {x y : R⟦G⟧}
    (h : y.degree < x.degree) : (x + y).degree = x.degree := by
  apply le_antisymm
  · calc
      (x + y).degree ≤ max x.degree y.degree := degree_add_le x y
      _ = x.degree := max_eq_left h.le
  · apply le_of_not_gt
    intro hsum
    have hreverse := degree_add_le (x + y) (-y)
    rw [degree_neg, add_neg_cancel_right] at hreverse
    exact (not_lt_of_ge hreverse) (max_lt hsum h)

end AddGroup

section Multiplication

variable [AddCommMonoid G] [IsOrderedCancelAddMonoid G]
variable [NonUnitalNonAssocSemiring R]

/-- The order type of the support of a product is at most the Hessenberg product of the two support
order types. This is LM24, Proposition 3.1.1(2), generalized from an ordered abelian exponent group
and a field of coefficients. -/
theorem supportOrderType_mul_le_naturalMul (x y : R⟦G⟧) :
    supportOrderType (x * y) ≤
      (NatOrdinal.of x.supportOrderType * NatOrdinal.of y.supportOrderType).val := by
  calc
    supportOrderType (x * y) = (x * y).isPWO_support.orderType :=
      supportOrderType_eq_setOrderType (x * y)
    _ ≤ (x.isPWO_support.add y.isPWO_support).orderType :=
      Set.IsPWO.orderType_mono (x * y).isPWO_support
        (x.isPWO_support.add y.isPWO_support) support_mul_subset
    _ ≤ (NatOrdinal.of x.supportOrderType *
        NatOrdinal.of y.supportOrderType).val := by
      simpa only [← supportOrderType_eq_setOrderType] using
        Set.IsPWO.orderType_add_le_naturalMul x.isPWO_support y.isPWO_support

/-- The degree of a product is at most the Hessenberg sum of the two degrees. This is LM24,
Corollary 3.1.2(2), generalized from an ordered abelian exponent group and a field of
coefficients. -/
theorem degree_mul_le (x y : R⟦G⟧) :
    degree (x * y) ≤ degree x + degree y := by
  calc
    degree (x * y) = Ordinal.cantorDegree (x * y).supportOrderType :=
      degree_eq_cantorDegree (x * y)
    _ ≤ Ordinal.cantorDegree
        (NatOrdinal.of x.supportOrderType * NatOrdinal.of y.supportOrderType).val :=
      Ordinal.cantorDegree_mono (supportOrderType_mul_le_naturalMul x y)
    _ = NatOrdinal.cantorDegree
        (NatOrdinal.of x.supportOrderType * NatOrdinal.of y.supportOrderType) :=
      (NatOrdinal.cantorDegree_eq_ordinalCantorDegree _).symm
    _ = degree x + degree y := by
      rw [NatOrdinal.cantorDegree_mul, NatOrdinal.cantorDegree_of,
        NatOrdinal.cantorDegree_of, degree_eq_cantorDegree,
        degree_eq_cantorDegree]

end Multiplication


section Archimedean

variable [AddCommGroup G] [IsOrderedAddMonoid G] [Archimedean G] [Zero R]

/-- Over an Archimedean exponent group every support is countable, so every support order type
is below `ω₁`. -/
theorem supportOrderType_lt_omega_one (x : R⟦G⟧) : supportOrderType x < ω₁ :=
  x.isPWO_support.orderType_lt_omega_one_of_countable
    x.isPWO_support.countable_of_archimedean

/-- Over an Archimedean exponent group every degree is a countable ordinal. -/
theorem degree_lt_omega_one (x : R⟦G⟧) :
    degree x < (NatOrdinal.of ω₁ : WithBot NatOrdinal.{u}) := by
  rw [degree_eq_cantorDegree]
  by_cases h0 : supportOrderType x = 0
  · rw [h0, Ordinal.cantorDegree_zero]
    exact WithBot.bot_lt_coe _
  · rw [Ordinal.cantorDegree_of_ne_zero h0, WithBot.coe_lt_coe, NatOrdinal.of_lt_iff]
    exact (Ordinal.log_le_self _ _).trans_lt (supportOrderType_lt_omega_one x)

end Archimedean

end HahnSeries
