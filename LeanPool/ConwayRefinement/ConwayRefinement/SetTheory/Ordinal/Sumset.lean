/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SetOrderType
public import Mathlib.Data.Finset.MulAntidiagonal

import LeanPool.ConwayRefinement.CombinatorialGames.NatOrdinal.Pow
import Mathlib.Data.Sum.Order
import Mathlib.Order.Hom.Lex
import Mathlib.SetTheory.Ordinal.Principal

/-!
# Order type of a sumset

For partially well-ordered subsets of a linearly ordered cancellative commutative additive monoid,
this module bounds the ordinary order type of their pointwise sum by the Hessenberg product of
their order types. The result specializes to LM24, Fact 2.2.3(3), where the ambient type is an
ordered abelian group.

The proof follows the principal-block induction underlying the cited result. If both order types
are additive principal, every proper initial segment of the sumset is covered by two smaller
sumsets. Otherwise, a nonprincipal factor is split after its leading Cantor monomial, compatibly
with Hessenberg addition, and distributivity reduces the claim to strictly smaller products.
-/

universe u

public noncomputable section

open scoped Pointwise

namespace Set.IsPWO

open Ordinal

variable {α : Type u} [LinearOrder α] {s : Set α}

private theorem orderType_le_of_forall_inter_Iio_lt (hs : s.IsPWO) {o : Ordinal}
    (h : ∀ x ∈ s,
      (hs.mono (s := s ∩ Set.Iio x) Set.inter_subset_left).orderType < o) :
    hs.orderType ≤ o := by
  apply le_of_forall_lt
  intro c hc
  let : WellFoundedLT s := hs.isWF
  have hType : typeLT s = hs.orderType :=
    (orderType_eq_typeLT_of_orderIso hs (OrderIso.refl s)).symm
  have hc' : c < typeLT s := hc.trans_eq hType.symm
  let x : s := Ordinal.enum (· < ·) ⟨c, hc'⟩
  have hxRank : Ordinal.typein (· < · : s → s → Prop) x = c :=
    Ordinal.typein_enum _ hc'
  simpa only [orderType_inter_Iio_eq_typein hs x.2, hxRank] using h x.1 x.2

private theorem exists_naturalAdd_split (hs : s.IsPWO) (hzero : hs.orderType ≠ 0)
    (hnot : ¬Ordinal.IsPrincipal (· + ·) hs.orderType) :
    ∃ (s₀ s₁ : Set α) (hs₀ : s₀.IsPWO) (hs₁ : s₁.IsPWO),
      s₀ ∪ s₁ = s ∧
        NatOrdinal.of hs.orderType =
          NatOrdinal.of hs₀.orderType + NatOrdinal.of hs₁.orderType ∧
        hs₀.orderType < hs.orderType ∧ hs₁.orderType < hs.orderType := by
  let d : Ordinal := Ordinal.log Ordinal.omega0 hs.orderType
  let p : Ordinal := Ordinal.omega0 ^ d
  have hp_le : p ≤ hs.orderType := Ordinal.opow_log_le_self Ordinal.omega0 hzero
  have hp_ne : p ≠ hs.orderType := by
    intro hp
    apply hnot
    rw [hp.symm]
    exact Ordinal.isPrincipal_add_omega0_opow d
  have hp_lt : p < hs.orderType := hp_le.lt_of_ne hp_ne
  let : WellFoundedLT s := hs.isWF
  have hType : typeLT s = hs.orderType :=
    (orderType_eq_typeLT_of_orderIso hs (OrderIso.refl s)).symm
  have hp_type : p < typeLT s := hp_lt.trans_eq hType.symm
  let x : s := Ordinal.enum (· < ·) ⟨p, hp_type⟩
  let s₀ : Set α := s ∩ Set.Iio x.1
  let s₁ : Set α := s ∩ Set.Ici x.1
  let hs₀ : s₀.IsPWO := hs.mono Set.inter_subset_left
  let hs₁ : s₁.IsPWO := hs.mono Set.inter_subset_left
  have hs₀_orderType : hs₀.orderType = p := by
    rw [orderType_inter_Iio_eq_typein hs x.2]
    exact Ordinal.typein_enum _ hp_type
  have hsplit : hs₀.orderType + hs₁.orderType = hs.orderType :=
    orderType_inter_Iio_add_inter_Ici hs x.2
  have hs₁_orderType : hs₁.orderType = hs.orderType - p := by
    rw [hs₀_orderType] at hsplit
    exact (Ordinal.sub_eq_of_add_eq hsplit).symm
  have hs₁_lt : hs₁.orderType < hs.orderType := by
    rw [hs₁_orderType]
    exact (Ordinal.isLeast_sub_lt_omega0_opow_log hzero).1
  have htail_bound : hs.orderType - p < Ordinal.omega0 ^ (d + 1) := by
    apply (Ordinal.sub_le_self _ _).trans_lt
    exact Ordinal.lt_opow_succ_log_self Ordinal.one_lt_omega0 hs.orderType
  have hnatural : NatOrdinal.of hs.orderType =
      NatOrdinal.of hs₀.orderType + NatOrdinal.of hs₁.orderType := by
    have htail_bound' : NatOrdinal.of (hs.orderType - p) <
        ω^ (NatOrdinal.of d + 1) := by
      simpa only [NatOrdinal.of_omega0_opow, NatOrdinal.of_add_one] using
        NatOrdinal.of.strictMono htail_bound
    calc
      NatOrdinal.of hs.orderType = NatOrdinal.of (p + (hs.orderType - p)) := by
        rw [Ordinal.add_sub_cancel_of_le hp_le]
      _ = ω^ NatOrdinal.of d + NatOrdinal.of (hs.orderType - p) := by
        exact (NatOrdinal.wpow_add_of_lt htail_bound').symm
      _ = NatOrdinal.of hs₀.orderType + NatOrdinal.of hs₁.orderType := by
        rw [hs₀_orderType, hs₁_orderType, NatOrdinal.of_omega0_opow]
  refine ⟨s₀, s₁, hs₀, hs₁, ?_, hnatural, hs₀_orderType ▸ hp_lt, hs₁_lt⟩
  ext z
  simp only [s₀, s₁, Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici]
  constructor
  · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
  · intro hz
    exact (lt_or_ge z x.1).imp (And.intro hz) (And.intro hz)

/-- Covering a proper initial segment of a sumset: every element of `s + t` below `x + y` lies in
`(s ∩ Iio x) + t` or in `s + (t ∩ Iio y)`. -/
private theorem add_inter_Iio_subset_union [AddCommMonoid α] [IsOrderedCancelAddMonoid α]
    {s t : Set α} (x y : α) :
    (s + t) ∩ Set.Iio (x + y) ⊆ (s ∩ Set.Iio x + t) ∪ (s + t ∩ Set.Iio y) := by
  rintro z ⟨hz, hzlt⟩
  rcases Set.mem_add.mp hz with ⟨x', hx's, y', hy't, rfl⟩
  by_cases hx' : x' < x
  · left
    exact Set.mem_add.mpr ⟨x', ⟨hx's, hx'⟩, y', hy't, rfl⟩
  · right
    apply Set.mem_add.mpr
    refine ⟨x', hx's, y', ⟨hy't, ?_⟩, rfl⟩
    by_contra hy'
    exact (not_le_of_gt hzlt) (add_le_add (le_of_not_gt hx') (le_of_not_gt hy'))

/-- The principal case of the sumset bound. If both order types are additive principal, hence
powers `ω ^ d` and `ω ^ e`, every proper initial segment of `s + t` is covered by two sumsets
whose Hessenberg products are strictly below `ω ^ d ⊗ ω ^ e = ω ^ (d ⊕ e)`, and that power is
closed under Hessenberg addition. The bounds for the smaller products are the induction
hypothesis `ih`. -/
private theorem orderType_add_le_naturalMul_of_isPrincipal [AddCommMonoid α]
    [IsOrderedCancelAddMonoid α] {s t : Set α} (hs : s.IsPWO) (ht : t.IsPWO)
    (hsZero : hs.orderType ≠ 0) (htZero : ht.orderType ≠ 0)
    (hsPrincipal : Ordinal.IsPrincipal (· + ·) hs.orderType)
    (htPrincipal : Ordinal.IsPrincipal (· + ·) ht.orderType)
    (ih : ∀ {s' t' : Set α} (hs' : s'.IsPWO) (ht' : t'.IsPWO),
      NatOrdinal.of hs'.orderType * NatOrdinal.of ht'.orderType <
          NatOrdinal.of hs.orderType * NatOrdinal.of ht.orderType →
        (hs'.add ht').orderType ≤
          (NatOrdinal.of hs'.orderType * NatOrdinal.of ht'.orderType).val) :
    (hs.add ht).orderType ≤
      (NatOrdinal.of hs.orderType * NatOrdinal.of ht.orderType).val := by
  let a : NatOrdinal := NatOrdinal.of hs.orderType
  let b : NatOrdinal := NatOrdinal.of ht.orderType
  change (hs.add ht).orderType ≤ (a * b).val
  have ha : 0 < a := pos_iff_ne_zero.mpr (NatOrdinal.of_ne_zero.mpr hsZero)
  have hb : 0 < b := pos_iff_ne_zero.mpr (NatOrdinal.of_ne_zero.mpr htZero)
  rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp hsPrincipal with
    hsZero' | ⟨d, hd⟩
  · exact (hsZero hsZero').elim
  rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp htPrincipal with
    htZero' | ⟨e, he⟩
  · exact (htZero htZero').elim
  have hsPower : hs.orderType = Ordinal.omega0 ^ d := hd.symm
  have htPower : ht.orderType = Ordinal.omega0 ^ e := he.symm
  have hproduct : a * b = ω^ (NatOrdinal.of d + NatOrdinal.of e) := by
    simp only [a, b, hsPower, htPower, NatOrdinal.of_omega0_opow]
    exact (NatOrdinal.wpow_add _ _).symm
  apply orderType_le_of_forall_inter_Iio_lt (hs.add ht)
  intro z hz
  rcases Set.mem_add.mp hz with ⟨x, hxs, y, hyt, rfl⟩
  let sx : Set α := s ∩ Set.Iio x
  let ty : Set α := t ∩ Set.Iio y
  let hsx : sx.IsPWO := hs.mono Set.inter_subset_left
  let hty : ty.IsPWO := ht.mono Set.inter_subset_left
  let hInitial : ((s + t) ∩ Set.Iio (x + y)).IsPWO :=
    (hs.add ht).mono Set.inter_subset_left
  have hsx_lt : hsx.orderType < hs.orderType := orderType_inter_Iio_lt hs hxs
  have hty_lt : hty.orderType < ht.orderType := orderType_inter_Iio_lt ht hyt
  have hleftProduct : NatOrdinal.of hsx.orderType * b < a * b :=
    mul_lt_mul_of_pos_right (NatOrdinal.of.strictMono hsx_lt) hb
  have hrightProduct : a * NatOrdinal.of hty.orderType < a * b :=
    mul_lt_mul_of_pos_left (NatOrdinal.of.strictMono hty_lt) ha
  have hleft' : NatOrdinal.of (hsx.add ht).orderType ≤
      NatOrdinal.of hsx.orderType * b := by
    simpa only [b, NatOrdinal.of_val] using NatOrdinal.of.monotone (ih hsx ht hleftProduct)
  have hright' : NatOrdinal.of (hs.add hty).orderType ≤
      a * NatOrdinal.of hty.orderType := by
    simpa only [a, NatOrdinal.of_val] using NatOrdinal.of.monotone (ih hs hty hrightProduct)
  calc
    hInitial.orderType ≤ ((hsx.add ht).union (hs.add hty)).orderType :=
      orderType_mono hInitial ((hsx.add ht).union (hs.add hty))
        (add_inter_Iio_subset_union x y)
    _ ≤ (NatOrdinal.of (hsx.add ht).orderType +
        NatOrdinal.of (hs.add hty).orderType).val :=
      orderType_union_le_naturalAdd (hsx.add ht) (hs.add hty)
    _ ≤ (NatOrdinal.of hsx.orderType * b +
        a * NatOrdinal.of hty.orderType).val := by
      apply NatOrdinal.val.monotone
      exact add_le_add hleft' hright'
    _ < (a * b).val := by
      apply NatOrdinal.val.lt_iff_lt.mpr
      rw [hproduct]
      exact NatOrdinal.add_lt_wpow (hleftProduct.trans_eq hproduct)
        (hrightProduct.trans_eq hproduct)

/-- The distributivity step of the sumset bound, splitting the left factor. If `s = s₀ ∪ s₁`
with `ot(s) = ot(s₀) ⊕ ot(s₁)` and both pieces of strictly smaller order type, then
`s + t = (s₀ + t) ∪ (s₁ + t)`, and the union bound together with the induction hypothesis `ih`
for the two smaller products gives the bound for `s + t`. -/
private theorem orderType_add_le_naturalMul_of_union_left [AddCommMonoid α]
    [IsOrderedCancelAddMonoid α] {s t : Set α} (hs : s.IsPWO) (ht : t.IsPWO)
    {s₀ s₁ : Set α} (hs₀ : s₀.IsPWO) (hs₁ : s₁.IsPWO) (hsUnion : s₀ ∪ s₁ = s)
    (hsNatural : NatOrdinal.of hs.orderType =
      NatOrdinal.of hs₀.orderType + NatOrdinal.of hs₁.orderType)
    (hs₀_lt : hs₀.orderType < hs.orderType) (hs₁_lt : hs₁.orderType < hs.orderType)
    (htZero : ht.orderType ≠ 0)
    (ih : ∀ {s' t' : Set α} (hs' : s'.IsPWO) (ht' : t'.IsPWO),
      NatOrdinal.of hs'.orderType * NatOrdinal.of ht'.orderType <
          NatOrdinal.of hs.orderType * NatOrdinal.of ht.orderType →
        (hs'.add ht').orderType ≤
          (NatOrdinal.of hs'.orderType * NatOrdinal.of ht'.orderType).val) :
    (hs.add ht).orderType ≤
      (NatOrdinal.of hs.orderType * NatOrdinal.of ht.orderType).val := by
  let a : NatOrdinal := NatOrdinal.of hs.orderType
  let b : NatOrdinal := NatOrdinal.of ht.orderType
  change (hs.add ht).orderType ≤ (a * b).val
  have hb : 0 < b := pos_iff_ne_zero.mpr (NatOrdinal.of_ne_zero.mpr htZero)
  have h₀Measure : NatOrdinal.of hs₀.orderType * b < a * b :=
    mul_lt_mul_of_pos_right (NatOrdinal.of.strictMono hs₀_lt) hb
  have h₁Measure : NatOrdinal.of hs₁.orderType * b < a * b :=
    mul_lt_mul_of_pos_right (NatOrdinal.of.strictMono hs₁_lt) hb
  have h₀' : NatOrdinal.of (hs₀.add ht).orderType ≤
      NatOrdinal.of hs₀.orderType * b := by
    simpa only [b, NatOrdinal.of_val] using NatOrdinal.of.monotone (ih hs₀ ht h₀Measure)
  have h₁' : NatOrdinal.of (hs₁.add ht).orderType ≤
      NatOrdinal.of hs₁.orderType * b := by
    simpa only [b, NatOrdinal.of_val] using NatOrdinal.of.monotone (ih hs₁ ht h₁Measure)
  calc
    (hs.add ht).orderType = ((hs₀.add ht).union (hs₁.add ht)).orderType := by
      apply orderType_congr
      rw [← Set.union_add, hsUnion]
    _ ≤ (NatOrdinal.of (hs₀.add ht).orderType +
        NatOrdinal.of (hs₁.add ht).orderType).val :=
      orderType_union_le_naturalAdd (hs₀.add ht) (hs₁.add ht)
    _ ≤ (NatOrdinal.of hs₀.orderType * b +
        NatOrdinal.of hs₁.orderType * b).val := by
      apply NatOrdinal.val.monotone
      exact add_le_add h₀' h₁'
    _ = (a * b).val := by rw [← add_mul, ← hsNatural]

/-- The distributivity step of the sumset bound, splitting the right factor. If `t = t₀ ∪ t₁`
with `ot(t) = ot(t₀) ⊕ ot(t₁)` and both pieces of strictly smaller order type, then
`s + t = (s + t₀) ∪ (s + t₁)`, and the union bound together with the induction hypothesis `ih`
for the two smaller products gives the bound for `s + t`. -/
private theorem orderType_add_le_naturalMul_of_union_right [AddCommMonoid α]
    [IsOrderedCancelAddMonoid α] {s t : Set α} (hs : s.IsPWO) (ht : t.IsPWO)
    {t₀ t₁ : Set α} (ht₀ : t₀.IsPWO) (ht₁ : t₁.IsPWO) (htUnion : t₀ ∪ t₁ = t)
    (htNatural : NatOrdinal.of ht.orderType =
      NatOrdinal.of ht₀.orderType + NatOrdinal.of ht₁.orderType)
    (ht₀_lt : ht₀.orderType < ht.orderType) (ht₁_lt : ht₁.orderType < ht.orderType)
    (hsZero : hs.orderType ≠ 0)
    (ih : ∀ {s' t' : Set α} (hs' : s'.IsPWO) (ht' : t'.IsPWO),
      NatOrdinal.of hs'.orderType * NatOrdinal.of ht'.orderType <
          NatOrdinal.of hs.orderType * NatOrdinal.of ht.orderType →
        (hs'.add ht').orderType ≤
          (NatOrdinal.of hs'.orderType * NatOrdinal.of ht'.orderType).val) :
    (hs.add ht).orderType ≤
      (NatOrdinal.of hs.orderType * NatOrdinal.of ht.orderType).val := by
  let a : NatOrdinal := NatOrdinal.of hs.orderType
  let b : NatOrdinal := NatOrdinal.of ht.orderType
  change (hs.add ht).orderType ≤ (a * b).val
  have ha : 0 < a := pos_iff_ne_zero.mpr (NatOrdinal.of_ne_zero.mpr hsZero)
  have h₀Measure : a * NatOrdinal.of ht₀.orderType < a * b :=
    mul_lt_mul_of_pos_left (NatOrdinal.of.strictMono ht₀_lt) ha
  have h₁Measure : a * NatOrdinal.of ht₁.orderType < a * b :=
    mul_lt_mul_of_pos_left (NatOrdinal.of.strictMono ht₁_lt) ha
  have h₀' : NatOrdinal.of (hs.add ht₀).orderType ≤
      a * NatOrdinal.of ht₀.orderType := by
    simpa only [a, NatOrdinal.of_val] using NatOrdinal.of.monotone (ih hs ht₀ h₀Measure)
  have h₁' : NatOrdinal.of (hs.add ht₁).orderType ≤
      a * NatOrdinal.of ht₁.orderType := by
    simpa only [a, NatOrdinal.of_val] using NatOrdinal.of.monotone (ih hs ht₁ h₁Measure)
  calc
    (hs.add ht).orderType = ((hs.add ht₀).union (hs.add ht₁)).orderType := by
      apply orderType_congr
      rw [← Set.add_union, htUnion]
    _ ≤ (NatOrdinal.of (hs.add ht₀).orderType +
        NatOrdinal.of (hs.add ht₁).orderType).val :=
      orderType_union_le_naturalAdd (hs.add ht₀) (hs.add ht₁)
    _ ≤ (a * NatOrdinal.of ht₀.orderType +
        a * NatOrdinal.of ht₁.orderType).val := by
      apply NatOrdinal.val.monotone
      exact add_le_add h₀' h₁'
    _ = (a * b).val := by rw [← mul_add, ← htNatural]

/-- The order type of a pointwise sum is at most the Hessenberg product of the two order types.
This specializes to LM24, Fact 2.2.3(3). -/
theorem orderType_add_le_naturalMul [AddCommMonoid α] [IsOrderedCancelAddMonoid α]
    {s t : Set α} (hs : s.IsPWO) (ht : t.IsPWO) :
    (hs.add ht).orderType ≤
      (NatOrdinal.of hs.orderType * NatOrdinal.of ht.orderType).val := by
  by_cases hsZero : hs.orderType = 0
  · have hsEmpty : s = ∅ := hs.orderType_eq_zero.mp hsZero
    have hsumEmpty : s + t = ∅ := by rw [hsEmpty, Set.empty_add]
    rw [(hs.add ht).orderType_eq_zero.mpr hsumEmpty, hsZero]
    simp
  by_cases htZero : ht.orderType = 0
  · have htEmpty : t = ∅ := ht.orderType_eq_zero.mp htZero
    have hsumEmpty : s + t = ∅ := by rw [htEmpty, Set.add_empty]
    rw [(hs.add ht).orderType_eq_zero.mpr hsumEmpty, htZero]
    simp
  have ih : ∀ {s' t' : Set α} (hs' : s'.IsPWO) (ht' : t'.IsPWO),
      NatOrdinal.of hs'.orderType * NatOrdinal.of ht'.orderType <
          NatOrdinal.of hs.orderType * NatOrdinal.of ht.orderType →
        (hs'.add ht').orderType ≤
          (NatOrdinal.of hs'.orderType * NatOrdinal.of ht'.orderType).val :=
    fun hs' ht' _ ↦ orderType_add_le_naturalMul hs' ht'
  by_cases hsPrincipal : Ordinal.IsPrincipal (· + ·) hs.orderType
  · by_cases htPrincipal : Ordinal.IsPrincipal (· + ·) ht.orderType
    · exact orderType_add_le_naturalMul_of_isPrincipal hs ht hsZero htZero
        hsPrincipal htPrincipal ih
    · obtain ⟨t₀, t₁, ht₀, ht₁, htUnion, htNatural, ht₀_lt, ht₁_lt⟩ :=
        exists_naturalAdd_split ht htZero htPrincipal
      exact orderType_add_le_naturalMul_of_union_right hs ht ht₀ ht₁ htUnion htNatural
        ht₀_lt ht₁_lt hsZero ih
  · obtain ⟨s₀, s₁, hs₀, hs₁, hsUnion, hsNatural, hs₀_lt, hs₁_lt⟩ :=
      exists_naturalAdd_split hs hsZero hsPrincipal
    exact orderType_add_le_naturalMul_of_union_left hs ht hs₀ hs₁ hsUnion hsNatural
      hs₀_lt hs₁_lt htZero ih
termination_by NatOrdinal.of hs.orderType * NatOrdinal.of ht.orderType
decreasing_by
  all_goals
    change _ < _
    assumption

end Set.IsPWO
