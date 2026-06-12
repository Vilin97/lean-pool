/-
Copyright (c) 2026 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import LeanPool.SetTheory.Basic
import LeanPool.SetTheory.OrderTheory
import Mathlib.Tactic.Cases

/-!
# Ordinals in models of ZF

This module develops the theory of ordinals inside a von Neumann model of ZF, including
their order structure and the correspondence with Mathlib's `Ordinal` type.
-/

noncomputable section

open Function Order Ordinal SetTheory ZFSet

variable {M} [ZFStructure M] [hM : IsVonNeumann M]

namespace SetTheory

/-- The `IsOrdinal` declaration. -/
@[realize] def IsOrdinal (x : M) := IsTransitive x ∧ ∀ y ∈ x, IsTransitive y
/-- The `IsStrongLimit` declaration. -/
@[realize] def IsStrongLimit (κ : M) := IsOrdinal κ ∧ ∀ α ∈ κ, cardLT (𝓟 α) κ
/-- The `IsOrdinalValuedFunc` declaration. -/
@[realize] def IsOrdinalValuedFunc (f : M) := IsFunc f ∧ ∀ x ∈ Ran f, IsOrdinal x

@[toV_simps] lemma IsOrdinal.toV (α : M) : IsOrdinal ↓α ↔ IsOrdinal α := by
  simp only [IsOrdinal, toV_simps]

@[toZFSet_simps] lemma IsOrdinal.toZFSet (α : M) : IsOrdinal α ↔ (⇓α).IsOrdinal := by
  convert (IsOrdinal.toV α).symm using 1
  simp only [IsOrdinal, isOrdinal_iff_forall_mem_isTransitive, toZFSet_simps]

@[simp] lemma isOrdinal_empty : IsOrdinal (∅ : M) := by
  simp [IsOrdinal, IsTransitive]

lemma _root_.ZFSet.IsOrdinal.mem_iff_lt
    {x y : ZFSet} (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x ∈ y ↔ x < y := by
  simp only [lt_iff_le_not_ge, ZFSet.le_def]
  rw [hy.not_subset_iff_mem hx, iff_and_self]
  exact hy.isTransitive _

lemma IsOrdinal.mem_iff_lt {x y : M} (hx : IsOrdinal x) (hy : IsOrdinal y) :
    x ∈ y ↔ x < y := by
  revert hx hy
  simpa only [toZFSet_simps] using fun hx hy => hx.mem_iff_lt hy

variable (M) in
/-- The `Ordinals` declaration. -/
abbrev Ordinals := {x : M // IsOrdinal x}

/-- The `rank` declaration. -/
def rank (x : M) : M := by
  split_vonNeumann hM
  · refine ⟨(⇓x).rank.toZFSet, ?_⟩
    simpa only [toZFSet_simps, mem_vonNeumann, rank_toZFSet] using x.2
  · exact ↓(⇓x).rank.toZFSet

@[toZFSet_simps] lemma toZFSet_rank {x : M} : ⇓(rank x) = (⇓x).rank.toZFSet := by
  split_vonNeumann hM <;> rfl

lemma rank_mem {x y : M} (mem : x ∈ y) : rank x < rank y := by
  simp only [toZFSet_simps, toZFSet_strictMono.lt_iff_lt] at mem ⊢
  exact ZFSet.rank_lt_of_mem mem

lemma rank_mono {x y : M} (sub : x ⊆ y) : rank x ≤ rank y := by
  simp only [toZFSet_simps, toZFSet_strictMono.le_iff_le] at sub ⊢
  exact ZFSet.rank_mono sub

lemma rank_ordinal {α : M} (hα : IsOrdinal α) : rank α = α := by
  simp only [toZFSet_simps] at hα ⊢
  exact hα.toZFSet_rank_eq

@[simp] lemma isOrdinal_rank {α : M} : IsOrdinal (rank α) := by
  rw [IsOrdinal.toZFSet, toZFSet_rank]
  exact isOrdinal_toZFSet _

lemma IsOrdinal.mem {α β : M} (hx : IsOrdinal α) (hy : β ∈ α) : IsOrdinal β := by
  simp only [toZFSet_simps] at *
  exact hx.mem hy

lemma IsOrdinal.lt_of_mem {α β : M} (hx : IsOrdinal α) (hy : β ∈ α) : β < α := by
  rwa [(hx.mem hy).mem_iff_lt hx] at hy

lemma IsOrdinal.not_le_iff {α β : M} (hα : IsOrdinal α) (hβ : IsOrdinal β) : ¬α ≤ β ↔ β < α := by
  revert α β
  simp (config := {contextual := true}) only [← IsOrdinal.mem_iff_lt, toZFSet_simps]
  exact fun hα hβ => hα.not_subset_iff_mem hβ

lemma rank_enoughTransitive {x : M} : rank (enoughTransitive x).1 = rank x := by
  rw [ToZFSet.eq, toZFSet_rank, toZFSet_rank, toZFSet_enoughTransitive, ZFSet.rank_vonNeumann]

lemma rank_trcl {x : M} : rank (trcl x) = rank x := by
  apply le_antisymm
  · transitivity rank (enoughTransitive x).1
    · exact rank_mono (trcl_sub (enoughTransitive x).2.1 (enoughTransitive x).2.2)
    · exact rank_enoughTransitive.le
  · exact rank_mono sub_trcl

lemma rank_singleton {x : M} : rank {x} = succ (rank x) := by
  simp [toZFSet_simps]

/-- The `rankFunc` declaration. -/
def rankFunc (x : M) : ((trcl {x}) : M) → (succ (rank x) : M) := by
  refine fun | ⟨y, hy⟩ => ⟨rank y, ?_⟩
  erw [IsOrdinal.mem_iff_lt (by simp)
    (by simpa [toZFSet_simps] using isOrdinal_succ (isOrdinal_toZFSet (⇓x).rank))]
  replace hy := rank_mem hy
  rwa [rank_trcl, rank_singleton] at hy

/-- The `IsRankFunction` declaration. -/
@[realize] def IsRankFunction (x : M) (f : M) :=
  IsOrdinalValuedFunc f ∧ IsTransitive (Dom f) ∧ x ∈ Dom f ∧ PreserveMem f

lemma isRankFunction_rankFunc {x : M} : IsRankFunction x (funcToSet (rankFunc x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [IsOrdinalValuedFunc, isFunc_funcToSet, mem_Ran_funcToSet_iff, true_and]
    rintro y ⟨z, hz, ⟨_⟩⟩
    simp [rankFunc]
  · simp [isTransitive_trcl]
  · simpa using sub_trcl (by simp)
  · simp only [PreserveMem]
    intro a ha b hb mem
    rw [dom_funcToSet] at ha hb
    simp only [apply_funcToSet, *]
    simp (disch := simp) only [rankFunc, IsOrdinal.mem_iff_lt]
    exact rank_mem mem

@[realize] lemma rankAux.eu (x : M) :
    ∃! α, IsGLB {α | ∃ f, IsRankFunction x f ∧ apply f x = α} α := by
  rw [exists_minimal]
  exact ⟨_, funcToSet (rankFunc x), isRankFunction_rankFunc, rfl⟩

theorem rank_induction {p : M → Prop}
    (x : M) (h : ∀ x, (∀ y, rank y < rank x → p y) → p x) : p x := by
  set α := (⇓x).rank with hx
  clear_value α
  revert x
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    refine fun x hx => h x (fun y hy => ih (⇓y).rank (hx ▸ ?_) _ rfl)
    simpa only [toZFSet_simps, toZFSet_rank, toZFSet_strictMono.lt_iff_lt] using hy

lemma rankAux_eq_rank {x : M} : rankAux x = rank x := by
  rw [rankAux.eq_iff]
  apply IsLeast.isGLB
  refine ⟨⟨funcToSet (rankFunc x), isRankFunction_rankFunc, ?_⟩, ?_⟩
  · have : x ∈ trcl ({x} : M) := sub_trcl (by simp)
    simp [this, apply_funcToSet, rankFunc]
  · simp only [lowerBounds, IsRankFunction, Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro x f ord_val dom_trans hx preserve_mem ⟨_⟩
    induction x using rank_induction with
    | _ x ind =>
      intro α hα
      have ord_α := isOrdinal_rank.mem hα
      have ord_f_x := ord_val.2 _ (apply_mem_Ran ord_val.1 hx)
      erw [ord_α.mem_iff_lt ord_f_x]
      have ord_α_ZFSet := ord_α
      erw [ord_α.mem_iff_lt isOrdinal_rank] at hα
      simp only [toZFSet_simps] at hα ord_α_ZFSet
      rw [← ord_α_ZFSet.toZFSet_rank_eq, toZFSet_strictMono.lt_iff_lt, lt_rank_iff] at hα
      clear ord_α_ZFSet
      rcases hα with ⟨y, hy, le₁⟩
      obtain ⟨y, ⟨_⟩⟩ := exists_toZFSet_of_mem hy
      rw [← ToZFSet.mem] at hy
      rw [← toZFSet_strictMono.le_iff_le, ← toZFSet_rank, ← toZFSet_rank, ← ToZFSet.le] at le₁
      have y_in_Dom := dom_trans hx hy
      have le₂ := ind _ (rank_mem hy) y_in_Dom
      have lt₃ := preserve_mem _ y_in_Dom _ hx hy
      have ord_f_y := ord_val.2 _ (apply_mem_Ran ord_val.1 y_in_Dom)
      rw [rank_ordinal ord_α] at le₁
      replace lt₃ := ord_f_x.lt_of_mem lt₃
      exact Trans.trans (Trans.trans le₁ le₂) lt₃

open Classical in
instance : LinearOrder (Ordinals M) where
  lt := (· < ·)
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := fun _ _ _ => le_trans
  le_antisymm := fun _ _ => le_antisymm
  toDecidableLE := by infer_instance
  le_total := by
    simp (config := {contextual := true}) only [
      Subtype.forall, Subtype.mk_le_mk, toZFSet_simps, ZFSet.le_def,
      IsOrdinal.subset_iff_eq_or_mem
    ]
    intro x hx y hy
    have := hx.mem_trichotomous hy
    tauto

instance : WellFoundedLT (Ordinals M) where
  wf := by
    have : (· < · : Ordinals M → _ → _) = ((· ∈ ·) on (⇓·.1)) := by
      ext x y
      rw [onFun, ← ToZFSet.mem, x.2.mem_iff_lt y.2, Subtype.coe_lt_coe]
    rw [this]
    refine RelEmbedding.wellFounded ⟨⟨(⇓·.1), ?_⟩, ?_⟩ ZFSet.mem_wf
    · simp [Injective, toZFSet_simps]
    · simp

instance : OrderBot (Ordinals M) where
  bot := ⟨∅, isOrdinal_empty⟩
  bot_le := by simp [toZFSet_simps]

instance : ConditionallyCompleteLinearOrderBot (Ordinals M) :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

lemma sSup_empty_ordinals : sSup (∅ : Set (Ordinals M)) = ⊥ := by
  simp

@[simp] lemma sInf_empty_ordinals : sInf (∅ : Set (Ordinals M)) = ⊥ := by
  simp [sInf]

/-- The `toOrdinal` declaration. -/
def toOrdinal : Ordinals M ↪o Ordinal.{0} where
  toFun α := (⇓α.1).rank
  map_rel_iff' := by
    simpa only [Subtype.forall, toZFSet_simps, Subtype.mk_le_mk]
      using fun α hα β hβ => hα.rank_le_iff_subset hβ
  inj' := by
    simpa only [Injective, Subtype.forall, IsOrdinal.toZFSet, Subtype.mk.injEq, ToZFSet.eq]
      using fun α hα β hβ => (hα.rank_inj hβ).mp

variable (M) in
/-- The `maxOrdinal` declaration. -/
def maxOrdinal : WithTop Ordinal.{0} := by
  split_vonNeumann hM
  · exact .some μ
  · exact ⊤

lemma maxOrdinal_vonNeumann {μ} [Fact (IsSuccLimit μ)] : maxOrdinal (V_ μ) = μ := rfl
lemma maxOrdinal_V : maxOrdinal V = ⊤ := rfl

@[toZFSet_simps] lemma toZFSet_toOrdinal {α : Ordinals M} : (toOrdinal α).toZFSet = ⇓α.1 := by
  simp only [toOrdinal, RelEmbedding.coe_mk, Embedding.coeFn_mk]
  rw [IsOrdinal.toZFSet_rank_eq]
  simpa only [toZFSet_simps] using α.2

lemma exists_toOrdinal_eq {α : Ordinal.{0}} (hα : α < maxOrdinal M) :
    ∃ β : Ordinals M, toOrdinal β = α := by
  split_vonNeumann hM
  · simp only [maxOrdinal_vonNeumann, WithTop.coe_lt_coe] at hα
    refine ⟨⟨⟨α.toZFSet, by simpa [mem_vonNeumann]⟩, ?_⟩, ?_⟩
    · simp [toZFSet_simps, isOrdinal_toZFSet]
    · apply toZFSet_injective
      simp [toZFSet_simps]
  · refine ⟨⟨↓α.toZFSet, by simp [toZFSet_simps, isOrdinal_toZFSet]⟩, ?_⟩
    apply toZFSet_injective
    rw [toZFSet_toOrdinal]
    exact ToZFSet.toZFSet_V

lemma toOrdinal_lt {α : Ordinals M} : toOrdinal α < maxOrdinal M := by
  split_vonNeumann hM
  · simpa [toOrdinal, maxOrdinal, toZFSet_simps] using mem_vonNeumann.mp α.1.2
  · simp [maxOrdinal]

instance comOrdinals : ContinuousOrderMapBounded (Subtype.val : Ordinals M → M) where
  monotone := by simp [Monotone]
  preimage_Ici_closed := fun x S hsub hne hbdd => hsub (csInf_mem hne)
  preimage_Iic_closed := by
    intro x S hsub hne hbdd α hα
    have ord_α := (sSup S).2.mem hα
    change α ∈ (sSup S).1 at hα
    rw [ord_α.mem_iff_lt (sSup S).2, show α = (⟨α, ord_α⟩ : Ordinals M).1 from rfl,
      Subtype.coe_lt_coe, lt_csSup_iff hbdd hne] at hα
    rcases hα with ⟨s, hs, lt⟩
    rw [← Subtype.coe_lt_coe, ← ord_α.mem_iff_lt s.2] at lt
    exact hsub hs lt
  bounded_preimage_Ici := fun x => by simp
  bounded_preimage_Iic := by
    refine fun x => ⟨⟨rank x, isOrdinal_rank⟩, ?_⟩
    simp only [upperBounds, Set.mem_preimage, Set.mem_Iic, Subtype.forall, Set.mem_setOf_eq,
      Subtype.mk_le_mk]
    intro y y_ord le
    rw [← rank_ordinal y_ord]
    exact rank_mono le

instance comToOrdinal : ContinuousOrderMap (toOrdinal (M := M)) where
  monotone := toOrdinal.monotone
  preimage_Ici_closed := by
    intro α
    by_cases! hα : α < maxOrdinal M
    · obtain ⟨β, ⟨_⟩⟩ := exists_toOrdinal_eq hα
      simpa using sInfClosed_Ici β
    · convert sInfClosed_bot
      ext x
      simpa using WithTop.coe_lt_coe.mp (lt_of_lt_of_le toOrdinal_lt hα)
  preimage_Iic_closed := by
    intro α
    by_cases! hα : α < maxOrdinal M
    · obtain ⟨β, ⟨_⟩⟩ := exists_toOrdinal_eq hα
      simpa using sSupClosed_Iic β
    · convert sSupClosed_top
      ext x
      simpa using WithTop.coe_le_coe.mp (le_of_lt (lt_of_lt_of_le toOrdinal_lt hα))

end SetTheory
