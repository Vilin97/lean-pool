/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.NatOrdinal.Basic
public import Mathlib.Order.WellFoundedSet
public import Mathlib.SetTheory.Ordinal.Principal
public import Mathlib.SetTheory.Cardinal.Aleph

import Mathlib.Data.Sum.Order
import Mathlib.Order.Hom.Set

/-!
# Order type of a partially well-ordered set

A partially well-ordered subset of a linear order is well-ordered by the induced strict order.
This module assigns it that ordinary ordinal order type. The order is always the ambient order,
with no reversal.

The union theorem proves a slightly more general form of LM24, Fact 2.2.3(2): the two sets need not
first be exhibited as subsets of a common well-ordered set. Its right-hand side uses addition in
`NatOrdinal`, hence Hessenberg's natural sum rather than ordinary ordinal addition.

Mathlib supplies `Ordinal.type_sum_lex`, `Ordinal.type_eq`, `OrderIso.sumLexIioIci`, and ordinal
enumeration, but no theorem equivalent to LM24, Fact 2.2.3(1), nor its uniqueness consequence.
The proof reuses the lexicographic-sum and order-isomorphism infrastructure rather than defining
a new ordinal representation.
-/

universe u

public noncomputable section

namespace Set.IsPWO

open Ordinal

variable {α : Type u} [LinearOrder α] {s t : Set α}

@[reducible] private def isWellOrder (hs : s.IsPWO) :
    IsWellOrder s (Subrel (· < ·) (· ∈ s)) where
  wf := hs.isWF
  trichotomous := fun _ _ hab hba ↦
    Subtype.ext (le_antisymm (le_of_not_gt hba) (le_of_not_gt hab))

/-- The ordinary ordinal order type of a partially well-ordered subset of a linear order. -/
def orderType (hs : s.IsPWO) : Ordinal.{u} :=
  @Ordinal.type s (Subrel (· < ·) (· ∈ s)) (isWellOrder hs)

/-- A countable partially well-ordered set has order type below `ω₁`. -/
theorem orderType_lt_omega_one_of_countable (hs : s.IsPWO) (hc : s.Countable) :
    hs.orderType < ω₁ := by
  rw [orderType, Cardinal.lt_omega_iff_card_lt, card_type, Cardinal.lt_aleph_one_iff,
    Cardinal.le_aleph0_iff_set_countable]
  exact hc

/-- The order type does not depend on the proof that the set is partially well-ordered. -/
theorem orderType_proof_irrel (hs ht : s.IsPWO) : hs.orderType = ht.orderType := by
  rfl

/-- A partially well-ordered set has order type zero exactly when it is empty. -/
@[simp]
theorem orderType_eq_zero (hs : s.IsPWO) : hs.orderType = 0 ↔ s = ∅ := by
  letI := isWellOrder hs
  rw [orderType, Ordinal.type_eq_zero_iff_isEmpty, isEmpty_subtype]
  exact Set.eq_empty_iff_forall_notMem.symm

/-- For a globally well-ordered ambient type, `orderType` agrees with `typeLT` on the subtype. -/
theorem orderType_eq_typeLT [WellFoundedLT α] (hs : s.IsPWO) :
    hs.orderType = typeLT s := by
  rfl

/-- Compute the order type through an order isomorphism from the set to a well-ordered type. -/
theorem orderType_eq_typeLT_of_orderIso {A : Type u} [LinearOrder A] [WellFoundedLT A]
    (hs : s.IsPWO) (e : s ≃o A) : hs.orderType = typeLT A := by
  letI := isWellOrder hs
  let er : Subrel (· < ·) (· ∈ s) ≃r (· < · : A → A → Prop) :=
    e.toRelIsoLT
  exact er.ordinalType_congr

/-- A partially well-ordered set is order-isomorphic to the canonical well order of its ordinary
order type. -/
theorem nonempty_orderIso_toType (hs : s.IsPWO) : Nonempty (hs.orderType.ToType ≃o s) := by
  letI : WellFoundedLT s := hs.isWF
  have htypes : typeLT hs.orderType.ToType = typeLT s := by
    rw [type_toType]
    exact hs.orderType_eq_typeLT_of_orderIso (OrderIso.refl s)
  exact ⟨OrderIso.ofRelIsoLT (Classical.choice (Ordinal.type_eq.mp htypes))⟩

/-- Compute the order type through a relation isomorphism from the set to an arbitrary
well-order. -/
theorem orderType_eq_type_of_relIso {A : Type u} {r : A → A → Prop}
    [IsWellOrder A r] (hs : s.IsPWO)
    (e : Subrel (· < ·) (· ∈ s) ≃r r) :
    hs.orderType = Ordinal.type r := by
  letI := isWellOrder hs
  exact e.ordinalType_congr

/-- Equal subsets have equal order types. -/
theorem orderType_congr (hs : s.IsPWO) (ht : t.IsPWO) (h : s = t) :
    hs.orderType = ht.orderType := by
  subst t
  rfl

/-- Inclusion of partially well-ordered subsets cannot decrease their ordinary order type. -/
theorem orderType_mono (hs : s.IsPWO) (ht : t.IsPWO) (h : s ⊆ t) :
    hs.orderType ≤ ht.orderType := by
  letI := isWellOrder hs
  letI := isWellOrder ht
  exact (Subrel.inclusionEmbedding (· < ·) h).ordinal_type_le

/-- A strictly increasing image has the same ordinary order type as the original partially
well-ordered set. -/
theorem orderType_image_of_strictMonoOn {B : Type u} [LinearOrder B]
    (hs : s.IsPWO) {f : α → B} (hf : StrictMonoOn f s) :
    (hs.image_of_monotoneOn hf.monotoneOn).orderType = hs.orderType := by
  letI : WellFoundedLT s := hs.isWF
  let e : s ≃o f '' s :=
    StrictMonoOn.orderIso f s hf
  exact
    ((hs.image_of_monotoneOn hf.monotoneOn).orderType_eq_typeLT_of_orderIso e.symm).trans
      (hs.orderType_eq_typeLT_of_orderIso (OrderIso.refl s)).symm

/-- A well-ordered set has order type `a + b` exactly when it is the union of a set of order
type `a` followed strictly by a set of order type `b`. This is LM24, Fact 2.2.3(1). -/
theorem orderType_eq_add_iff (hs : s.IsPWO) (a b : Ordinal.{u}) :
    hs.orderType = a + b ↔
      ∃ (s₀ s₁ : Set α) (hs₀ : s₀.IsPWO) (hs₁ : s₁.IsPWO),
        s₀ ⊆ s ∧
          s₁ ⊆ s ∧
          (∀ x ∈ s₀, ∀ y ∈ s₁, x < y) ∧
          hs₀.orderType = a ∧
          hs₁.orderType = b ∧
          s = s₀ ∪ s₁ := by
  constructor
  · intro htype
    letI : WellFoundedLT s := hs.isWF
    letI : WellFoundedLT (a.ToType ⊕ₗ b.ToType) :=
      Sum.lex_wf wellFounded_lt wellFounded_lt
    have htypes : typeLT s = typeLT (a.ToType ⊕ₗ b.ToType) := by
      calc
        typeLT s = hs.orderType :=
          (hs.orderType_eq_typeLT_of_orderIso (OrderIso.refl s)).symm
        _ = a + b := htype
        _ = typeLT (a.ToType ⊕ₗ b.ToType) := by
          symm
          calc
            typeLT (a.ToType ⊕ₗ b.ToType) =
                Ordinal.type (Sum.Lex (· < · : a.ToType → a.ToType → Prop)
                  (· < · : b.ToType → b.ToType → Prop)) :=
              (Sum.Lex.toLexRelIsoLT (α := a.ToType)
                (β := b.ToType)).ordinalType_congr.symm
            _ = a + b := by
              rw [Ordinal.type_sum_lex, Ordinal.type_toType, Ordinal.type_toType]
    let e : s ≃o a.ToType ⊕ₗ b.ToType :=
      OrderIso.ofRelIsoLT (Classical.choice (Ordinal.type_eq.mp htypes))
    let left : a.ToType ↪o α :=
      OrderEmbedding.ofStrictMono
        (fun x ↦ (e.symm (Sum.inlₗ x)).1)
        (fun _ _ hxy ↦ e.symm.strictMono (Sum.Lex.inl_strictMono hxy))
    let right : b.ToType ↪o α :=
      OrderEmbedding.ofStrictMono
        (fun x ↦ (e.symm (Sum.inrₗ x)).1)
        (fun _ _ hxy ↦ e.symm.strictMono (Sum.Lex.inr_strictMono hxy))
    let s₀ : Set α := Set.range left
    let s₁ : Set α := Set.range right
    have hs₀s : s₀ ⊆ s := by
      rintro x ⟨y, rfl⟩
      exact (e.symm (Sum.inlₗ y)).2
    have hs₁s : s₁ ⊆ s := by
      rintro x ⟨y, rfl⟩
      exact (e.symm (Sum.inrₗ y)).2
    let hs₀ : s₀.IsPWO := hs.mono hs₀s
    let hs₁ : s₁.IsPWO := hs.mono hs₁s
    have hs₀type : hs₀.orderType = a := by
      rw [hs₀.orderType_eq_typeLT_of_orderIso left.orderIso.symm,
        Ordinal.type_toType]
    have hs₁type : hs₁.orderType = b := by
      rw [hs₁.orderType_eq_typeLT_of_orderIso right.orderIso.symm,
        Ordinal.type_toType]
    have hbefore : ∀ x ∈ s₀, ∀ y ∈ s₁, x < y := by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      exact e.symm.strictMono (Sum.Lex.inl_lt_inr x y)
    have hunion : s = s₀ ∪ s₁ := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases heq : e ⟨x, hx⟩ with y | y
        · left
          refine ⟨y, ?_⟩
          change (e.symm (Sum.inlₗ y)).1 = x
          have h := e.symm_apply_apply ⟨x, hx⟩
          rw [heq] at h
          exact congrArg Subtype.val h
        · right
          refine ⟨y, ?_⟩
          change (e.symm (Sum.inrₗ y)).1 = x
          have h := e.symm_apply_apply ⟨x, hx⟩
          rw [heq] at h
          exact congrArg Subtype.val h
      · exact Set.union_subset hs₀s hs₁s
    exact ⟨s₀, s₁, hs₀, hs₁, hs₀s, hs₁s, hbefore, hs₀type, hs₁type, hunion⟩
  · rintro ⟨s₀, s₁, hs₀, hs₁, hs₀s, hs₁s, hbefore, hs₀type, hs₁type, hunion⟩
    let f : s₀ ⊕ₗ s₁ → s
      | Sum.inlₗ x => ⟨x, hs₀s x.2⟩
      | Sum.inrₗ x => ⟨x, hs₁s x.2⟩
    have hf : StrictMono f := by
      intro x y hxy
      rcases x with x | x <;> rcases y with y | y
      · have hxy' : x < y :=
          (Sum.Lex.inl_lt_inl_iff (α := s₀) (β := s₁)).mp hxy
        exact hxy'
      · exact hbefore x x.2 y y.2
      · exact (Sum.Lex.not_inr_lt_inl hxy).elim
      · have hxy' : x < y :=
          (Sum.Lex.inr_lt_inr_iff (α := s₀) (β := s₁)).mp hxy
        exact hxy'
    have hsurj : Function.Surjective f := by
      rintro ⟨x, hx⟩
      rw [hunion] at hx
      rcases hx with hx | hx
      · exact ⟨Sum.inlₗ ⟨x, hx⟩, rfl⟩
      · exact ⟨Sum.inrₗ ⟨x, hx⟩, rfl⟩
    let e : s₀ ⊕ₗ s₁ ≃o s := hf.orderIsoOfSurjective f hsurj
    letI : WellFoundedLT s₀ := hs₀.isWF
    letI : WellFoundedLT s₁ := hs₁.isWF
    letI : WellFoundedLT (s₀ ⊕ₗ s₁) :=
      Sum.lex_wf wellFounded_lt wellFounded_lt
    calc
      hs.orderType = typeLT (s₀ ⊕ₗ s₁) :=
        hs.orderType_eq_typeLT_of_orderIso e.symm
      _ = typeLT s₀ + typeLT s₁ := Ordinal.type_sum_lex _ _
      _ = hs₀.orderType + hs₁.orderType := by
        rw [hs₀.orderType_eq_typeLT_of_orderIso (OrderIso.refl s₀),
          hs₁.orderType_eq_typeLT_of_orderIso (OrderIso.refl s₁)]
      _ = a + b := by rw [hs₀type, hs₁type]

/-- A partially well-ordered set is finite exactly when its order type is below `ω`. -/
theorem finite_iff_orderType_lt_omega (hs : s.IsPWO) :
    s.Finite ↔ hs.orderType < Ordinal.omega0 := by
  letI := isWellOrder hs
  rw [Set.Finite, ← Cardinal.mk_lt_aleph0_iff]
  rw [orderType, ← Ordinal.card_type (Subrel (· < ·) (· ∈ s)), Ordinal.card_lt_aleph0]

/-- Every infinite partially well-ordered set is an initial block of nonzero limit order type
followed by a finite final block. The split removes the finite remainder after ordinal division of
the order type by `ω`. -/
theorem finite_or_exists_limit_initial_finite_final (hs : s.IsPWO) :
    s.Finite ∨
      ∃ (s₀ s₁ : Set α) (hs₀ : s₀.IsPWO) (_ : s₁.IsPWO),
        s₀ ⊆ s ∧
          s₁ ⊆ s ∧
          (∀ x ∈ s₀, ∀ y ∈ s₁, x < y) ∧
          Order.IsSuccLimit hs₀.orderType ∧
          s₁.Finite ∧
          s = s₀ ∪ s₁ := by
  by_cases hfinite : s.Finite
  · exact Or.inl hfinite
  · right
    have homega : Ordinal.omega0 ≤ hs.orderType := by
      exact le_of_not_gt (hfinite ∘ hs.finite_iff_orderType_lt_omega.mpr)
    have hdivpos : 0 < hs.orderType / Ordinal.omega0 := by
      exact (Ordinal.div_pos Ordinal.omega0_ne_zero).mpr homega
    have hlimit : Order.IsSuccLimit
        (Ordinal.omega0 * (hs.orderType / Ordinal.omega0)) :=
      Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 hdivpos
    have hmodlt : hs.orderType % Ordinal.omega0 < Ordinal.omega0 :=
      Ordinal.mod_lt hs.orderType Ordinal.omega0_ne_zero
    have hdecomp :
        hs.orderType = Ordinal.omega0 * (hs.orderType / Ordinal.omega0) +
          hs.orderType % Ordinal.omega0 :=
      (Ordinal.div_add_mod hs.orderType Ordinal.omega0).symm
    obtain ⟨s₀, s₁, hs₀, hs₁, hs₀s, hs₁s, hbefore, hs₀type, hs₁type, hunion⟩ :=
      (hs.orderType_eq_add_iff
        (Ordinal.omega0 * (hs.orderType / Ordinal.omega0))
        (hs.orderType % Ordinal.omega0)).mp hdecomp
    refine ⟨s₀, s₁, hs₀, hs₁, hs₀s, hs₁s, hbefore, ?_, ?_, hunion⟩
    · rwa [hs₀type]
    · rw [hs₁.finite_iff_orderType_lt_omega, hs₁type]
      exact hmodlt

private def belowRelIso {x : α} (hx : x ∈ s) :
    Subrel (· < ·) (· ∈ s ∩ Set.Iio x) ≃r
      Subrel (Subrel (· < ·) (· ∈ s))
        (Subrel (· < ·) (· ∈ s) · ⟨x, hx⟩) where
  toFun a := ⟨⟨a.1, a.2.1⟩, a.2.2⟩
  invFun a := ⟨a.1.1, a.1.2, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private def interIioOrderIso {x : α} (hx : x ∈ s) :
    ↥(s ∩ Set.Iio x) ≃o Set.Iio (⟨x, hx⟩ : s) where
  toFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  invFun z := ⟨z.1.1, z.1.2, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private def interIciOrderIso {x : α} (hx : x ∈ s) :
    ↥(s ∩ Set.Ici x) ≃o Set.Ici (⟨x, hx⟩ : s) where
  toFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  invFun z := ⟨z.1.1, z.1.2, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The part of a partially well-ordered set strictly below one of its elements has order type
equal to the index of that element. -/
theorem orderType_inter_Iio_eq_typein [WellFoundedLT s]
    (hs : s.IsPWO) {x : α} (hx : x ∈ s) :
    (hs.mono (s := s ∩ Set.Iio x) Set.inter_subset_left).orderType =
      Ordinal.typein (· < · : s → s → Prop) ⟨x, hx⟩ := by
  letI : WellFoundedLT s := hs.isWF
  rw [orderType_eq_typeLT_of_orderIso _ (interIioOrderIso hx), ← Ordinal.type_Iio_lt]

/-- Splitting a partially well-ordered set at one of its elements splits its order type. -/
theorem orderType_inter_Iio_add_inter_Ici [WellFoundedLT s]
    (hs : s.IsPWO) {x : α} (hx : x ∈ s) :
    (hs.mono (s := s ∩ Set.Iio x) Set.inter_subset_left).orderType +
        (hs.mono (s := s ∩ Set.Ici x) Set.inter_subset_left).orderType =
      hs.orderType := by
  letI : WellFoundedLT (Set.Iio (⟨x, hx⟩ : s) ⊕ₗ Set.Ici (⟨x, hx⟩ : s)) :=
    Sum.lex_wf wellFounded_lt wellFounded_lt
  rw [orderType_eq_typeLT_of_orderIso _ (interIioOrderIso hx),
    orderType_eq_typeLT_of_orderIso _ (interIciOrderIso hx),
    ← Ordinal.type_sum_lex]
  calc
    _ = typeLT s :=
      (OrderIso.sumLexIioIci (⟨x, hx⟩ : s)).toRelIsoLT.ordinalType_congr
    _ = hs.orderType :=
      (orderType_eq_typeLT_of_orderIso hs (OrderIso.refl s)).symm

/-- Every ordinal below the order type is realized as the order type of the part strictly below
some element. -/
theorem exists_orderType_inter_Iio_eq (hs : s.IsPWO) {k : Ordinal.{u}}
    (hk : k < hs.orderType) :
    ∃ x, ∃ _ : x ∈ s,
      (hs.mono (s := s ∩ Set.Iio x) Set.inter_subset_left).orderType = k := by
  letI : WellFoundedLT s := hs.isWF
  have htype : k < Ordinal.type (· < · : s → s → Prop) := by
    rwa [← hs.orderType_eq_typeLT_of_orderIso (OrderIso.refl s)]
  obtain ⟨y, hy⟩ := Ordinal.typein_surj (· < · : s → s → Prop) htype
  exact ⟨y.1, y.2, (orderType_inter_Iio_eq_typein hs y.2).trans (by simpa using hy)⟩

/-- The part of a partially well-ordered set strictly below one of its elements has strictly smaller
order type. -/
theorem orderType_inter_Iio_lt (hs : s.IsPWO) {x : α} (hx : x ∈ s) :
    (hs.mono (s := s ∩ Set.Iio x) Set.inter_subset_left).orderType < hs.orderType := by
  letI := isWellOrder hs
  let hbelow := hs.mono (s := s ∩ Set.Iio x) Set.inter_subset_left
  letI := isWellOrder hbelow
  calc
    hbelow.orderType = Ordinal.type
        (Subrel (Subrel (· < ·) (· ∈ s))
          (Subrel (· < ·) (· ∈ s) · ⟨x, hx⟩)) :=
      (belowRelIso hx).ordinalType_congr
    _ = Ordinal.typein (Subrel (· < ·) (· ∈ s)) ⟨x, hx⟩ :=
      Ordinal.type_subrel _ _
    _ < hs.orderType := Ordinal.typein_lt_type _ _

/-- If every closed initial segment has order type below `o`, then the whole partially
well-ordered set has order type at most `o`. -/
theorem orderType_le_of_forall_inter_Iic_lt (hs : s.IsPWO) {o : Ordinal}
    (h : ∀ x ∈ s,
      (hs.mono (s := s ∩ Set.Iic x) Set.inter_subset_left).orderType < o) :
    hs.orderType ≤ o := by
  by_contra hle
  have ho : o < hs.orderType := lt_of_not_ge hle
  letI := isWellOrder hs
  obtain ⟨x, hx⟩ :=
    Ordinal.typein_surj (Subrel (· < ·) (· ∈ s)) ho
  let hbelow := hs.mono (s := s ∩ Set.Iio x.1) Set.inter_subset_left
  letI := isWellOrder hbelow
  have hiio :
      (hs.mono (s := s ∩ Set.Iio x.1) Set.inter_subset_left).orderType = o := by
    calc
      hbelow.orderType = Ordinal.type
          (Subrel (Subrel (· < ·) (· ∈ s))
            (Subrel (· < ·) (· ∈ s) · x)) :=
        (belowRelIso x.2).ordinalType_congr
      _ = Ordinal.typein (Subrel (· < ·) (· ∈ s)) x :=
        Ordinal.type_subrel _ _
      _ = o := hx
  have hsubset : s ∩ Set.Iio x.1 ⊆ s ∩ Set.Iic x.1 := by
    intro y hy
    exact ⟨hy.1, hy.2.le⟩
  have hmono :=
    (hs.mono (s := s ∩ Set.Iio x.1) Set.inter_subset_left).orderType_mono
      (hs.mono (s := s ∩ Set.Iic x.1) Set.inter_subset_left) hsubset
  exact (not_lt_of_ge (hiio ▸ hmono)) (h x.1 x.2)

/-- If the ordinary order type is a limit ordinal, every member has a strictly larger member. -/
theorem exists_gt_of_isSuccLimit_orderType
    (hs : s.IsPWO) (hlimit : Order.IsSuccLimit hs.orderType)
    {x : α} (hx : x ∈ s) :
    ∃ y ∈ s, x < y := by
  letI : WellFoundedLT s := hs.isWF
  have hprelimit : Order.IsSuccPrelimit
      (Ordinal.type (fun x y : s ↦ x < y)) := by
    rw [← hs.orderType_eq_typeLT_of_orderIso (OrderIso.refl s)]
    exact hlimit.isSuccPrelimit
  letI : NoMaxOrder s :=
    Ordinal.isSuccPrelimit_type_lt_iff.mp hprelimit
  obtain ⟨y, hxy⟩ : ∃ y : s, (⟨x, hx⟩ : s) < y :=
    exists_gt (⟨x, hx⟩ : s)
  exact ⟨y.1, y.2, hxy⟩

/-- A nonempty partially well-ordered set with no maximum has successor-limit order type. This is
the converse of `Set.IsPWO.exists_gt_of_isSuccLimit_orderType`. -/
theorem isSuccLimit_orderType_of_forall_exists_gt
    (hs : s.IsPWO) (hne : s.Nonempty) (hgt : ∀ x ∈ s, ∃ y ∈ s, x < y) :
    Order.IsSuccLimit hs.orderType := by
  letI : WellFoundedLT s := hs.isWF
  have hnomax : NoMaxOrder s := by
    constructor
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, hxy⟩ := hgt x hx
    exact ⟨⟨y, hy⟩, hxy⟩
  refine ⟨?_, ?_⟩
  · rw [isMin_iff_eq_bot, Ordinal.bot_eq_zero, hs.orderType_eq_zero]
    obtain ⟨x, hx⟩ := hne
    intro hempty
    rw [hempty] at hx
    exact hx
  · rw [hs.orderType_eq_typeLT_of_orderIso (OrderIso.refl s)]
    exact Ordinal.isSuccPrelimit_type_lt_iff.mpr hnomax

/-- A nonempty final segment of a partially well-ordered set of additively principal order type
has the same order type as the whole set. -/
theorem orderType_inter_Ioi_eq_of_isPrincipal
    (hs : s.IsPWO) (hprincipal : IsPrincipal (fun a b ↦ a + b) hs.orderType)
    {x : α} (hupper : ∃ y ∈ s, x < y) :
    (hs.mono (s := s ∩ Set.Ioi x) Set.inter_subset_left).orderType = hs.orderType := by
  let lower : Set α := s ∩ Set.Iic x
  let upper : Set α := s ∩ Set.Ioi x
  let hlower : lower.IsPWO := hs.mono Set.inter_subset_left
  let hupperPWO : upper.IsPWO := hs.mono Set.inter_subset_left
  change hupperPWO.orderType = hs.orderType
  have hlowerBeforeUpper : ∀ a ∈ lower, ∀ b ∈ upper, a < b := by
    intro a ha b hb
    exact ha.2.trans_lt hb.2
  have hsUnion : s = lower ∪ upper := by
    ext a
    simp only [lower, upper, Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi]
    constructor
    · intro ha
      rcases le_or_gt a x with hax | hxa
      · exact Or.inl ⟨ha, hax⟩
      · exact Or.inr ⟨ha, hxa⟩
    · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
  have hsplit : hs.orderType = hlower.orderType + hupperPWO.orderType := by
    apply (hs.orderType_eq_add_iff hlower.orderType hupperPWO.orderType).mpr
    exact ⟨lower, upper, hlower, hupperPWO, Set.inter_subset_left,
      Set.inter_subset_left, hlowerBeforeUpper, rfl, rfl, hsUnion⟩
  obtain ⟨y, hyS, hxy⟩ := hupper
  have hlowerSubset : lower ⊆ s ∩ Set.Iio y := by
    intro a ha
    exact ⟨ha.1, ha.2.trans_lt hxy⟩
  have hlowerLt : hlower.orderType < hs.orderType :=
    (hlower.orderType_mono
      (hs.mono (s := s ∩ Set.Iio y) Set.inter_subset_left) hlowerSubset).trans_lt
        (hs.orderType_inter_Iio_lt hyS)
  apply le_antisymm
  · exact hupperPWO.orderType_mono hs Set.inter_subset_left
  · apply le_of_not_gt
    intro hupperLt
    have hsumLt := hprincipal hlowerLt hupperLt
    change hlower.orderType + hupperPWO.orderType < hs.orderType at hsumLt
    rw [← hsplit] at hsumLt
    exact (lt_irrefl hs.orderType) hsumLt

/-- Two decompositions into a first part followed strictly by a second part are equal when their
first parts have the same order type. -/
theorem orderType_split_unique {s₀ s₁ t₀ t₁ : Set α}
    (hs₀ : s₀.IsPWO) (ht₀ : t₀.IsPWO)
    (hsBefore : ∀ x ∈ s₀, ∀ y ∈ s₁, x < y)
    (htBefore : ∀ x ∈ t₀, ∀ y ∈ t₁, x < y)
    (hsUnion : s = s₀ ∪ s₁) (htUnion : s = t₀ ∪ t₁)
    (htype : hs₀.orderType = ht₀.orderType) :
    s₀ = t₀ ∧ s₁ = t₁ := by
  have hs₀t₀ : s₀ ⊆ t₀ := by
    intro x hx
    by_contra hxt₀
    have hxs : x ∈ s := by
      rw [hsUnion]
      exact Set.mem_union_left s₁ hx
    rw [htUnion] at hxs
    have hxt₁ : x ∈ t₁ := hxs.resolve_left hxt₀
    have ht₀sub : t₀ ⊆ s₀ ∩ Set.Iio x := by
      intro y hyt₀
      have hyx : y < x := htBefore y hyt₀ x hxt₁
      have hys : y ∈ s := by
        rw [htUnion]
        exact Set.mem_union_left t₁ hyt₀
      rw [hsUnion] at hys
      refine ⟨?_, hyx⟩
      exact hys.resolve_right fun hys₁ ↦ (hsBefore x hx y hys₁).not_gt hyx
    have hlt : ht₀.orderType < hs₀.orderType :=
      (orderType_mono ht₀
        (hs₀.mono (s := s₀ ∩ Set.Iio x) Set.inter_subset_left) ht₀sub).trans_lt
          (orderType_inter_Iio_lt hs₀ hx)
    exact hlt.ne htype.symm
  have ht₀s₀ : t₀ ⊆ s₀ := by
    intro x hx
    by_contra hxs₀
    have hxs : x ∈ s := by
      rw [htUnion]
      exact Set.mem_union_left t₁ hx
    rw [hsUnion] at hxs
    have hxs₁ : x ∈ s₁ := hxs.resolve_left hxs₀
    have hs₀sub : s₀ ⊆ t₀ ∩ Set.Iio x := by
      intro y hys₀
      have hyx : y < x := hsBefore y hys₀ x hxs₁
      have hys : y ∈ s := by
        rw [hsUnion]
        exact Set.mem_union_left s₁ hys₀
      rw [htUnion] at hys
      refine ⟨?_, hyx⟩
      exact hys.resolve_right fun hyt₁ ↦ (htBefore x hx y hyt₁).not_gt hyx
    have hlt : hs₀.orderType < ht₀.orderType :=
      (orderType_mono hs₀
        (ht₀.mono (s := t₀ ∩ Set.Iio x) Set.inter_subset_left) hs₀sub).trans_lt
          (orderType_inter_Iio_lt ht₀ hx)
    exact hlt.ne htype
  have hs₀eq : s₀ = t₀ := Set.Subset.antisymm hs₀t₀ ht₀s₀
  refine ⟨hs₀eq, Set.Subset.antisymm ?_ ?_⟩
  · intro x hxs₁
    have hxs : x ∈ s := by
      rw [hsUnion]
      exact Set.mem_union_right s₀ hxs₁
    rw [htUnion] at hxs
    exact hxs.resolve_left fun hxt₀ ↦
      (hsBefore x (hs₀eq ▸ hxt₀) x hxs₁).false
  · intro x hxt₁
    have hxs : x ∈ s := by
      rw [htUnion]
      exact Set.mem_union_right t₀ hxt₁
    rw [hsUnion] at hxs
    exact hxs.resolve_left fun hxs₀ ↦
      (htBefore x (hs₀eq ▸ hxs₀) x hxt₁).false

private theorem orderType_inter_Iio_mono (hs : s.IsPWO) {x y : α} (hxy : x ≤ y) :
    (hs.mono Set.inter_subset_left (s := s ∩ Set.Iio x)).orderType ≤
      (hs.mono Set.inter_subset_left (s := s ∩ Set.Iio y)).orderType := by
  apply orderType_mono
  intro z hz
  exact ⟨hz.1, hz.2.trans_le hxy⟩

private theorem orderType_inter_Iio_lt_inter_Iio (hs : s.IsPWO) {x y : α}
    (hx : x ∈ s) (hxy : x < y) :
    (hs.mono Set.inter_subset_left (s := s ∩ Set.Iio x)).orderType <
      (hs.mono Set.inter_subset_left (s := s ∩ Set.Iio y)).orderType := by
  let hsy : (s ∩ Set.Iio y).IsPWO := hs.mono Set.inter_subset_left
  have hxsy : x ∈ s ∩ Set.Iio y := ⟨hx, hxy⟩
  have hlt := hsy.orderType_inter_Iio_lt hxsy
  have heq : (s ∩ Set.Iio y) ∩ Set.Iio x = s ∩ Set.Iio x := by
    ext z
    constructor
    · exact fun hz ↦ ⟨hz.1.1, hz.2⟩
    · exact fun hz ↦ ⟨⟨hz.1, hz.2.trans hxy⟩, hz.2⟩
  rw [orderType_congr _ _ heq] at hlt
  exact hlt

/-- The order type of a union is at most the Hessenberg sum of the two order types. This
specializes to LM24, Fact 2.2.3(2). -/
theorem orderType_union_le_naturalAdd (hs : s.IsPWO) (ht : t.IsPWO) :
    (hs.union ht).orderType ≤
      (NatOrdinal.of hs.orderType + NatOrdinal.of ht.orderType).val := by
  let hsBelow (x : α) : (s ∩ Set.Iio x).IsPWO :=
    hs.mono Set.inter_subset_left
  let htBelow (x : α) : (t ∩ Set.Iio x).IsPWO :=
    ht.mono Set.inter_subset_left
  let rankS (x : α) : NatOrdinal := NatOrdinal.of (hsBelow x).orderType
  let rankT (x : α) : NatOrdinal := NatOrdinal.of (htBelow x).orderType
  let total : NatOrdinal := NatOrdinal.of hs.orderType + NatOrdinal.of ht.orderType
  have rank_lt_total (x : α) (hx : x ∈ s ∪ t) : rankS x + rankT x < total := by
    have hsle : rankS x ≤ NatOrdinal.of hs.orderType :=
      NatOrdinal.of.monotone (orderType_mono (hsBelow x) hs Set.inter_subset_left)
    have htle : rankT x ≤ NatOrdinal.of ht.orderType :=
      NatOrdinal.of.monotone (orderType_mono (htBelow x) ht Set.inter_subset_left)
    rcases hx with hxs | hxt
    · exact add_lt_add_of_lt_of_le
        (NatOrdinal.of.strictMono (orderType_inter_Iio_lt hs hxs)) htle
    · exact add_lt_add_of_le_of_lt hsle
        (NatOrdinal.of.strictMono (orderType_inter_Iio_lt ht hxt))
  let rank (x : ↥(s ∪ t)) : total.val.ToType :=
    Ordinal.ToType.mk ⟨(rankS x.1 + rankT x.1).val,
      NatOrdinal.val.lt_iff_lt.mpr (rank_lt_total x.1 x.2)⟩
  have rank_strict {x y : ↥(s ∪ t)} (hxy : x < y) : rank x < rank y := by
    have hsle : rankS x.1 ≤ rankS y.1 :=
      NatOrdinal.of.monotone (orderType_inter_Iio_mono hs hxy.le)
    have htle : rankT x.1 ≤ rankT y.1 :=
      NatOrdinal.of.monotone (orderType_inter_Iio_mono ht hxy.le)
    have hsum : rankS x.1 + rankT x.1 < rankS y.1 + rankT y.1 := by
      rcases x.2 with hxs | hxt
      · exact add_lt_add_of_lt_of_le
          (NatOrdinal.of.strictMono
            (orderType_inter_Iio_lt_inter_Iio hs hxs hxy)) htle
      · exact add_lt_add_of_le_of_lt hsle
          (NatOrdinal.of.strictMono
            (orderType_inter_Iio_lt_inter_Iio ht hxt hxy))
    exact Ordinal.ToType.mk.lt_iff_lt.mpr (NatOrdinal.val.lt_iff_lt.mpr hsum)
  let e : Subrel (· < ·) (· ∈ s ∪ t) ↪r
      (· < · : total.val.ToType → total.val.ToType → Prop) :=
    RelEmbedding.ofMonotone rank fun _ _ hxy ↦ rank_strict hxy
  letI := isWellOrder (hs.union ht)
  change Ordinal.type (Subrel (· < ·) (· ∈ s ∪ t)) ≤ total.val
  simpa only [Ordinal.type_toType] using e.ordinal_type_le

end Set.IsPWO
