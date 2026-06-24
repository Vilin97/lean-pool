/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arithmetization.ISigmaOne.HFS.Basic

/-!

# Sequence

-/

noncomputable section «lp_nc_section_1»

namespace LO
namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

/-- Imported declaration from the Incompleteness formalization. -/
def Seq (s : V) : Prop := IsMapping s ∧ ∃ l, domain s = under l

/-- Imported declaration from the Incompleteness formalization. -/
lemma _root_.LO.Arith.Seq.isMapping {s : V} (h : Seq s) : IsMapping s := h.1

private lemma seq_iff (s : V) :
    Seq s ↔ IsMapping s ∧ ∃ l ≤ 2 * s, ∃ d ≤ 2 * s, d = domain s ∧ d = under l :=
  ⟨by rintro ⟨hs, l, h⟩
      exact ⟨hs, l, (by
      calc
        l ≤ domain s := by simp [h]
        _ ≤ 2 * s    := by simp), ⟨domain s , by simp,  rfl, h⟩⟩,
   by rintro ⟨hs, l, _, _, _, rfl, h⟩; exact ⟨hs, l, h⟩⟩

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.seqDef : Sg0.Semisentence 1 := .mkSigma
  “s. !isMappingDef s ∧ ∃ l <⁺ 2 * s, ∃ d <⁺ 2 * s, !domainDef d s ∧ !underDef d l” (by simp)

lemma seq_defined : Sg0-Predicate (Seq : V → Prop) via seqDef := by
  intro v
  simp only [Fin.isValue, seq_iff, ↓existsAndEq, domain_bound, true_and, seqDef,
    Nat.succ_eq_add_one, Nat.reduceAdd, HierarchySymbol.Semiformula.val_mkSigma,
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.cons_val_fin_one,
    Semiterm.val_bvar, Matrix.constant_eq_singleton, isMapping_defined_iff, Matrix.vecCons_zero,
    Semiformula.eval_bexLTSucc', Semiterm.val_operator₂, Semiterm.val_const,
    Structure.numeral_eq_numeral, numeral_two_eq_two, Structure.Mul.mul, Matrix.cons_val_one,
    Matrix.comp_vecCons', Matrix.cons_app_two, domain_defined_iff, under_defined_iff,
    LogicalConnective.Prop.and_eq, exists_eq_right_right, and_congr_right_iff]
  intro hs
  constructor
  · rintro ⟨l, hl, hdom⟩
    exact ⟨l, hl, by
      rw [←hdom]
      simp, hdom.symm⟩
  · rintro ⟨l, hl, _, hdom⟩
    exact ⟨l, hl, hdom.symm⟩

@[simp] lemma seq_defined_iff (v) :
    Semiformula.Evalbm V v seqDef.val ↔ Seq (v 0) := seq_defined.df.iff v

instance seq_definable : Sg0-Predicate (Seq : V → Prop) := seq_defined.to_definable

instance seq_definable' (ℌ) : ℌ-Predicate (Seq : V → Prop) := seq_definable.of_zero

section «lp_section_1»

open Lean PrettyPrinter Delaborator

/-- Imported declaration from the Incompleteness formalization. -/
syntax ":Seq " firstOrderTerm : firstOrderFormula

scoped macro_rules
  | `(foFormula[$binders* | $fbinders* | :Seq $t:firstOrderTerm]) =>
    `(foFormula[$binders* | $fbinders* | !seqDef.val $t])

end «lp_section_1»

lemma lh_exists_uniq (s : V) : ∃! l, (Seq s → domain s = under l) ∧ (¬Seq s → l = 0) := by
  by_cases h : Seq s
  · rcases h with ⟨h, l, hl⟩
    exact ExistsUnique.intro l
      (by simp [show Seq s from ⟨h, l, hl⟩, hl])
      (by simp [show Seq s from ⟨h, l, hl⟩, hl])
  · simp [h]

/-- Imported declaration from the Incompleteness formalization. -/
def lh (s : V) : V := Classical.choose! (lh_exists_uniq s)

lemma lh_prop (s : V) : (Seq s → domain s = under (lh s)) ∧ (¬Seq s → lh s = 0) :=
  Classical.choose!_spec (lh_exists_uniq s)

lemma lh_prop_of_not_seq {s : V} (h : ¬Seq s) : lh s = 0 := (lh_prop s).2 h

lemma _root_.LO.Arith.Seq.domain_eq {s : V} (h : Seq s) : domain s = under (lh s) := (lh_prop s).1 h

@[simp] lemma lh_bound (s : V) : lh s ≤ 2 * s := by
  by_cases hs : Seq s
  · calc
      lh s ≤ under (lh s) := le_under _
      _    ≤ 2 * s        := by simp [←hs.domain_eq]
  · simp [lh_prop_of_not_seq hs]

private lemma lh_graph (l s : V) :
    l = lh s ↔ (Seq s → ∃ d ≤ 2 * s, d = domain s ∧ d = under l) ∧ (¬Seq s → l = 0) :=
  ⟨by
    rintro rfl
    by_cases Hs : Seq s <;> simp [Hs, ←Seq.domain_eq, lh_prop_of_not_seq], by
    rintro ⟨h, hn⟩
    by_cases Hs : Seq s
    · rcases h Hs with ⟨_, _, rfl, h⟩; simpa [h] using Hs.domain_eq
    · simp [lh_prop_of_not_seq Hs, hn Hs]⟩

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.lhDef : Sg0.Semisentence 2 := .mkSigma
  “l s. (!seqDef s → ∃ d <⁺ 2 * s, !domainDef d s ∧ !underDef d l) ∧ (¬!seqDef s → l = 0)” (by simp)

lemma lh_defined : Sg0-Function₁ (lh : V → V) via lhDef := by
  intro v; simp [lhDef, -exists_eq_right_right, lh_graph]

@[simp] lemma lh_defined_iff (v) :
    Semiformula.Evalbm V v lhDef.val ↔ v 0 = lh (v 1) := lh_defined.df.iff v

instance lh_definable : Sg0-Function₁ (lh : V → V) := lh_defined.to_definable

instance lh_definable' (ℌ) : ℌ-Function₁ (lh : V → V) := lh_definable.of_zero

instance : Bounded₁ (lh : V → V) := ⟨‘x. 2 * x’, fun _ ↦ by simp⟩

lemma _root_.LO.Arith.Seq.exists {s : V} (h : Seq s) {x : V} (hx : x < lh s) : ∃ y, ⟪x, y⟫ ∈ s :=
  h.isMapping x (by simpa [h.domain_eq] using hx) |>.exists

lemma _root_.LO.Arith.Seq.nth_exists_uniq {s : V} (h : Seq s) {x : V} (hx : x < lh s) :
    ∃! y, ⟪x, y⟫ ∈ s := h.isMapping x (by simpa [h.domain_eq] using hx)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Seq.nth {s : V} (h : Seq s) {x : V} (hx : x < lh s) : V :=
  Classical.choose! (h.nth_exists_uniq hx)

@[simp] lemma _root_.LO.Arith.Seq.nth_mem {s : V} (h : Seq s) {x : V} (hx : x < lh s) :
    ⟪x, h.nth hx⟫ ∈ s := Classical.choose!_spec (h.nth_exists_uniq hx)

lemma _root_.LO.Arith.Seq.nth_uniq {s : V} (h : Seq s) {x y : V} (hx : x < lh s) (hy : ⟪x, y⟫ ∈ s) :
    y = h.nth hx :=
    (h.nth_exists_uniq hx).unique hy (by simp)

@[simp] lemma _root_.LO.Arith.Seq.nth_lt {s : V} (h : Seq s) {x} (hx : x < lh s) : h.nth hx < s :=
  lt_of_mem_rng (h.nth_mem hx)

lemma _root_.LO.Arith.Seq.lh_eq_of {s : V} (H : Seq s) {l} (h : domain s = under l) : lh s = l := by
  simpa [H.domain_eq] using h

lemma _root_.LO.Arith.Seq.lt_lh_iff {s : V} (h : Seq s) {i} : i < lh s ↔ i ∈ domain s :=
  by simp [h.domain_eq]

lemma _root_.LO.Arith.Seq.lt_lh_of_mem {s : V} (h : Seq s) {i x} (hix : ⟪i, x⟫ ∈ s) : i < lh s :=
  h.lt_lh_iff.mpr (mem_domain_iff.mpr ⟨x, hix⟩)

/-- Imported declaration from the Incompleteness formalization. -/
def seqCons (s x : V) : V := insert ⟪lh s, x⟫ s

section «lp_section_2»

/-- Imported declaration from the Incompleteness formalization. -/
lemma znth_existsUnique (s i : V) :
    ∃! x, (Seq s ∧ i < lh s → ⟪i, x⟫ ∈ s) ∧ (¬(Seq s ∧ i < lh s) → x = 0) := by
  by_cases h : Seq s ∧ i < lh s
  · simp only [h, and_self, forall_const, not_true_eq_false, IsEmpty.forall_iff, and_true]
    exact h.1.nth_exists_uniq h.2
  · simp only [h, IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and,
      existsUnique_eq]

/-- Imported declaration from the Incompleteness formalization. -/
def znth (s i : V) : V := Classical.choose! (znth_existsUnique s i)

protected lemma _root_.LO.Arith.Seq.znth
    {s i : V} (h : Seq s) (hi : i < lh s) : ⟪i, znth s i⟫ ∈ s :=
  Classical.choose!_spec (znth_existsUnique s i) |>.1 ⟨h, hi⟩

lemma _root_.LO.Arith.Seq.znth_eq_of_mem {s i : V} (h : Seq s) (hi : ⟪i, x⟫ ∈ s) : znth s i = x :=
  h.isMapping.uniq (h.znth (h.lt_lh_of_mem hi)) hi

lemma znth_prop_not {s i : V} (h : ¬Seq s ∨ lh s ≤ i) : znth s i = 0 :=
  Classical.choose!_spec (znth_existsUnique s i) |>.2 (by simpa [-not_and, not_and_or] using h)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.znthDef : Sg0.Semisentence 3 := .mkSigma
  “x s i. ∃ l <⁺ 2 * s, !lhDef l s ∧ (:Seq s ∧ i < l → i ∼[s] x) ∧ (¬(:Seq s ∧ i < l) → x = 0)” (by
    simp)

private lemma znth_graph {x s i : V} :
    x = znth s i ↔ ∃ l ≤ 2 * s, l = lh s ∧ (Seq s ∧ i < l → ⟪i, x⟫ ∈ s) ∧ (¬(Seq s ∧
        i < l) → x = 0) := by simp [znth, Classical.choose!_eq_iff]

lemma znth_defined : Sg0-Function₂ (znth : V → V → V) via znthDef := by
  intro v;
  simpa [znthDef, -not_and, not_and_or] using znth_graph (V := V)

@[simp] lemma eval_znthDef (v) :
    Semiformula.Evalbm V v znthDef.val ↔ v 0 = znth (v 1) (v 2) := znth_defined.df.iff v

instance znth_definable : Sg0-Function₂ (znth : V → V → V) := znth_defined.to_definable

instance znth_definable' (ℌ) : ℌ-Function₂ (znth : V → V → V) := znth_definable.of_zero

end «lp_section_2»

-- infixr:67 " ::ˢ " => seqCons

/-- Imported notation from the Incompleteness formalization. -/
infixr:67 " ⁀' " => seqCons

@[simp] lemma seq_empty : Seq (∅ : V) := ⟨by simp, 0, by simp⟩

@[simp] lemma lh_empty : lh (∅ : V) = 0 := by
  have :
      under (lh ∅ : V) = under 0 := by
    simpa using (Eq.symm (Seq.domain_eq (V := V) (s := ∅) (by simp)))
  exact under_inj.mp this

/-- Imported declaration from the Incompleteness formalization. -/
lemma _root_.LO.Arith.Seq.isempty_of_lh_eq_zero {s : V} (Hs : Seq s) (h : lh s = 0) : s = ∅ :=
  by simpa [h] using Hs.domain_eq

@[simp] lemma _root_.LO.Arith.Seq.subset_seqCons (s x : V) : s ⊆ s ⁀' x := by simp [seqCons]

lemma _root_.LO.Arith.Seq.lt_seqCons {s} (hs : Seq s) (x : V) : s < s ⁀' x :=
  lt_iff_le_and_ne.mpr <| ⟨le_of_subset <| by simp, by
    simp only [seqCons, ne_eq]; intro A
    have : ⟪lh s, x⟫ ∈ s := by simpa [←A] using mem_insert ⟪lh s, x⟫ s
    simpa using hs.lt_lh_of_mem this⟩

lemma _root_.LO.Arith.Seq.mem_seqCons (s x : V) : ⟪lh s, x⟫ ∈ s ⁀' x := by simp [seqCons]

protected lemma _root_.LO.Arith.Seq.seqCons {s : V} (h : Seq s) (x : V) : Seq (s ⁀' x) :=
  ⟨h.isMapping.insert (by simp [h.domain_eq]), lh s + 1, by simp [seqCons, h.domain_eq]⟩

@[simp] lemma _root_.LO.Arith.Seq.lh_seqCons (x : V) {s} (h : Seq s) : lh (s ⁀' x) = lh s + 1 := by
  have : under (lh s + 1) = under (lh (s ⁀' x)) := by
    simpa [seqCons, h.domain_eq] using (h.seqCons x).domain_eq
  exact Eq.symm <| under_inj.mp this

lemma mem_seqCons_iff {i x z s : V} : ⟪i, x⟫ ∈ s ⁀' z ↔ (i = lh s ∧ x = z) ∨ ⟪i, x⟫ ∈ s :=
  by simp [seqCons]

@[simp] lemma lh_mem_seqCons (s z : V) : ⟪lh s, z⟫ ∈ s ⁀' z := by simp [seqCons]

@[simp] lemma lh_mem_seqCons_iff {s x z : V} (H : Seq s) : ⟪lh s, x⟫ ∈ s ⁀' z ↔ x = z := by
  simp only [seqCons, mem_bitInsert_iff, pair_ext_iff, true_and, or_iff_left_iff_imp]
  intro h; have := H.lt_lh_of_mem h; simp at this

lemma _root_.LO.Arith.Seq.mem_seqCons_iff_of_lt {s x z : V} (hi : i < lh s) :
    ⟪i, x⟫ ∈ s ⁀' z ↔ ⟪i, x⟫ ∈ s := by
  simp only [seqCons, mem_bitInsert_iff, pair_ext_iff, or_iff_right_iff_imp, and_imp]
  rintro rfl; simp at hi

@[simp] lemma lh_not_mem {s} (Ss : Seq s) (x : V) : ⟪lh s, x⟫ ∉ s :=
  fun h ↦ by have := Ss.lt_lh_of_mem h; simp at this

section «lp_section_3»

lemma seqCons_graph (t x s : V) :
    t = s ⁀' x ↔ ∃ l ≤ 2 * s, l = lh s ∧ ∃ p ≤ (2 * s + x + 1) ^ 2, p = ⟪l, x⟫ ∧ t = insert p s :=
  ⟨by rintro rfl
      exact ⟨lh s, by simp[], rfl, ⟪lh s, x⟫,
        le_trans (pair_le_pair_left (by simp) x) (pair_polybound (2 * s) x), rfl, by rfl⟩,
   by rintro ⟨l, _, rfl, p, _, rfl, rfl⟩; rfl⟩

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.seqConsDef : Sg0.Semisentence 3 := .mkSigma
  “t s x. ∃ l <⁺ 2 * s, !lhDef l s ∧ ∃ p <⁺ (2 * s + x + 1)², !pairDef p l x ∧ !insertDef t p s”
    (by simp)

lemma seqCons_defined : Sg0-Function₂ (seqCons : V → V → V) via seqConsDef := by
  intro v; simp [seqConsDef, seqCons_graph]

@[simp] lemma seqCons_defined_iff (v) :
    Semiformula.Evalbm V v seqConsDef.val ↔ v 0 = v 1 ⁀' v 2 := seqCons_defined.df.iff v

instance seqCons_definable : Sg0-Function₂ (seqCons : V → V → V) := seqCons_defined.to_definable

instance seqCons_definable' (ℌ) : ℌ-Function₂ (seqCons : V → V → V) := seqCons_definable.of_zero

@[simp] lemma natCast_empty : ((∅ : ℕ) : V) = ∅ := by simp [emptyset_def]

lemma seqCons_absolute (s a : ℕ) : ((s ⁀' a : ℕ) : V) = (s : V) ⁀' (a : V) := by
  simpa using DefinedFunction.shigmaZero_absolute_func V seqCons_defined seqCons_defined ![s, a]

end «lp_section_3»

lemma _root_.LO.Arith.Seq.restr {s : V} (H : Seq s) {i : V} (hi : i ≤ lh s) : Seq (s ↾ under i) :=
  ⟨H.isMapping.restr (under i), i, domain_restr_of_subset_domain (by simp [H.domain_eq, hi])⟩

lemma _root_.LO.Arith.Seq.restr_lh {s : V} (H : Seq s) {i : V} (hi : i ≤ lh s) :
    lh (s ↾ under i) = i :=
  (H.restr hi).lh_eq_of (domain_restr_of_subset_domain <| by simp [H.domain_eq, hi])

lemma domain_bitRemove_of_isMapping_of_mem {x y s : V} (hs : IsMapping s) (hxy : ⟪x, y⟫ ∈ s) :
    domain (bitRemove ⟪x, y⟫ s) = bitRemove x (domain s) := by
  apply mem_ext
  simp only [mem_domain_iff, mem_bitRemove_iff, ne_eq, pair_ext_iff, not_and]
  intro x₁
  constructor
  · rintro ⟨y₁, hy₁, hx₁y₁⟩; exact ⟨by rintro rfl; exact hy₁ rfl (hs.uniq hx₁y₁ hxy), y₁, hx₁y₁⟩
  · intro ⟨hx, y₁, hx₁y₁⟩
    exact ⟨y₁, by intro _; contradiction, hx₁y₁⟩

lemma _root_.LO.Arith.Seq.eq_of_eq_of_subset {s₁ s₂ : V} (H₁ : Seq s₁) (H₂ : Seq s₂)
    (hl : lh s₁ = lh s₂) (h : s₁ ⊆ s₂) : s₁ = s₂ := by
  apply mem_ext; intro u
  constructor
  · intro hu; exact h hu
  · intro hu
    have :
        π₁ u < lh s₁ := by
      simpa [hl] using H₂.lt_lh_of_mem
        (show ⟪π₁ u, π₂ u⟫ ∈ s₂ from by simpa using hu)
    have : ∃ y, ⟪π₁ u, y⟫ ∈ s₁ := H₁.exists this
    rcases this with ⟨y, hy⟩
    have : y = π₂ u := H₂.isMapping.uniq (h hy) (show ⟪π₁ u, π₂ u⟫ ∈ s₂ from by simpa using hu)
    rcases this with rfl
    simpa using hy

lemma subset_pair {s t : V} (h : ∀ i x, ⟪i, x⟫ ∈ s → ⟪i, x⟫ ∈ t) : s ⊆ t := by
  intro u hu
  simpa using h (π₁ u) (π₂ u) (by simpa using hu)

lemma _root_.LO.Arith.Seq.lh_ext {s₁ s₂ : V} (H₁ : Seq s₁) (H₂ : Seq s₂) (h : lh s₁ = lh s₂)
    (H : ∀ i x₁ x₂, ⟪i, x₁⟫ ∈ s₁ → ⟪i, x₂⟫ ∈ s₂ →
        x₁ = x₂) : s₁ = s₂ := H₁.eq_of_eq_of_subset H₂ h <| subset_pair <| by
      intro i x hx
      have hi : i < lh s₂ := by simpa [← h] using H₁.lt_lh_of_mem hx
      rcases H i _ _ hx (H₂.nth_mem hi)
      simp

@[simp] lemma _root_.LO.Arith.Seq.seqCons_ext {a₁ a₂ s₁ s₂ : V} (H₁ : Seq s₁) (H₂ : Seq s₂) :
    s₁ ⁀' a₁ = s₂ ⁀' a₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  ⟨by intro h
      have hs₁s₂ : lh s₁ = lh s₂ := by simpa [H₁, H₂] using congr_arg lh h
      have hs₁ : ⟪lh s₁, a₁⟫ ∈ s₂ ⁀' a₂ := by simpa [h] using lh_mem_seqCons s₁ a₁
      have hs₂ : ⟪lh s₁, a₂⟫ ∈ s₂ ⁀' a₂ := by simp [hs₁s₂]
      have ha₁a₂ : a₁ = a₂ := (H₂.seqCons a₂).isMapping.uniq hs₁ hs₂
      have : s₁ ⊆ s₂ := subset_pair <| by
        intro i x hix
        have :
            i = lh s₂ ∧ x = a₂ ∨ ⟪i, x⟫ ∈ s₂ := by
          simpa [mem_seqCons_iff, h] using Seq.subset_seqCons s₁ a₁ hix
        rcases this with (⟨rfl, rfl⟩ | hix₂)
        · have := H₁.lt_lh_of_mem hix; simp [hs₁s₂] at this
        · assumption
      exact ⟨ha₁a₂, H₁.eq_of_eq_of_subset H₂ hs₁s₂ this⟩,
   by rintro ⟨rfl, rfl⟩; rfl⟩

/-- TODO: move to Lemmata.lean -/
lemma ne_zero_iff_one_le {a : V} : a ≠ 0 ↔ 1 ≤ a :=
  Iff.trans pos_iff_ne_zero.symm (pos_iff_one_le (a := a))

lemma _root_.LO.Arith.Seq.cases_iff {s : V} : Seq s ↔ s = ∅ ∨ ∃ x s', Seq s' ∧ s = s' ⁀' x :=
  ⟨fun h ↦ by
  by_cases hs : lh s = 0
  · left
    simpa [hs] using h.domain_eq
  · right
    let i := lh s - 1
    have hi : i < lh s := pred_lt_self_of_pos (pos_iff_ne_zero.mpr hs)
    have lhs_eq : lh s = i + 1 := Eq.symm <| tsub_add_cancel_of_le <| ne_zero_iff_one_le.mp hs
    let s' := bitRemove ⟪i, h.nth hi⟫ s
    have his : ⟪i, h.nth hi⟫ ∈ s := h.nth_mem hi
    have hdoms' : domain s' = under i := by
      simp only [domain_bitRemove_of_isMapping_of_mem h.isMapping his, h.domain_eq, s']
      apply mem_ext
      simp only [lhs_eq, under_succ, mem_bitRemove_iff, ne_eq, mem_bitInsert_iff,
        mem_under_iff, and_or_left, not_and_self, false_or, and_iff_right_iff_imp]
      intro j hj; exact ne_of_lt hj
    have hs' : Seq s' := ⟨ h.isMapping.of_subset (by simp [s']), i, hdoms' ⟩
    have hs'i : lh s' = i := by simpa [hs'.domain_eq] using hdoms'
    exact ⟨h.nth hi, s', hs', mem_ext <| fun v ↦ by
      simp only [seqCons, hs'i, mem_bitInsert_iff]
      simp [s']
      by_cases hv : v = ⟪i, h.nth hi⟫ <;> simp [hv]⟩,
  by  rintro (rfl | ⟨x, s', hs', rfl⟩)
      · simp
      · exact hs'.seqCons x⟩

alias ⟨Seq.cases, _⟩ := Seq.cases_iff

@[elab_as_elim]
theorem seq_induction (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
  (hnil : P ∅) (hcons : ∀ s x, Seq s → P s → P (s ⁀' x)) :
    ∀ {s : V}, Seq s → P s := by
  intro s sseq
  induction s using order_induction_h_sigma1
  · exact Γ
  · definability
  case ind s ih =>
    have : s = ∅ ∨ ∃ x s', Seq s' ∧ s = s' ⁀' x := sseq.cases
    rcases this with (rfl | ⟨x, s, hs, rfl⟩)
    · exact hnil
    · exact hcons s x hs (ih s (hs.lt_seqCons x) hs)

/-- `!⟦x, y, z, ...⟧` notation for `Seq` -/
syntax "!⟦" term,* "⟧" : term

macro_rules
  | `(!⟦$terms:term,*, $term:term⟧) => `(seqCons !⟦$terms,*⟧ $term)
  | `(!⟦$term:term⟧) => `(seqCons ∅ $term)
  | `(!⟦⟧) => `(∅)

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander seqCons]
def vecConsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ !⟦$term2, $terms,*⟧ $term) => `(!⟦$term2, $terms,*, $term⟧)
  | `($_ !⟦$term2⟧ $term) => `(!⟦$term2, $term⟧)
  | `($_ ∅ $term) => `(!⟦$term⟧)
  | _ => throw ()

@[simp] lemma singleton_seq (x : V) : Seq !⟦x⟧ := by apply Seq.seqCons; simp

@[simp] lemma doubleton_seq (x y : V) : Seq !⟦x, y⟧ := by apply Seq.seqCons; simp

@[simp] lemma mem_singleton_seq_iff (x y : V) : ⟪0, x⟫ ∈ !⟦y⟧ ↔ x = y := by simp [mem_seqCons_iff]

section «lp_section_4»

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.mkSeq₁Def : Sg0.Semisentence 2 := .mkSigma
  “s x. !seqConsDef s 0 x” (by simp)

lemma mkSeq₁_defined : Sg0-Function₁ (fun x : V ↦ !⟦x⟧) via mkSeq₁Def := by
  intro v; simp [mkSeq₁Def]; rfl

@[simp] lemma eval_mkSeq₁Def (v) :
    Semiformula.Evalbm V v mkSeq₁Def.val ↔ v 0 = !⟦v 1⟧ := mkSeq₁_defined.df.iff v

instance mkSeq₁_definable : Sg0-Function₁ (fun x : V ↦ !⟦x⟧) := mkSeq₁_defined.to_definable

instance mkSeq₁_definable' (Γ) : Γ-Function₁ (fun x : V ↦ !⟦x⟧) := mkSeq₁_definable.of_zero

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.mkSeq₂Def : Sg1.Semisentence 3 := .mkSigma
  “s x y. ∃ sx, !mkSeq₁Def sx x ∧ !seqConsDef s sx y” (by simp)

lemma mkSeq₂_defined : Sg1-Function₂ (fun x y : V ↦ !⟦x, y⟧) via mkSeq₂Def := by
  intro v; simp [mkSeq₂Def]

@[simp] lemma eval_mkSeq₂Def (v) :
    Semiformula.Evalbm V v mkSeq₂Def.val ↔ v 0 = !⟦v 1, v 2⟧ := mkSeq₂_defined.df.iff v

instance mkSeq₂_definable : Sg1-Function₂ (fun x y : V ↦ !⟦x, y⟧) := mkSeq₂_defined.to_definable

instance mkSeq₂_definable' (Γ m) : Γ-[m + 1]-Function₂ (fun x y : V ↦ !⟦x, y⟧) :=
  mkSeq₂_definable.of_sigmaOne

end «lp_section_4»

theorem sigmaOne_skolem_seq {R : V → V → Prop} (hP : Sg1-Relation R) {l}
    (H : ∀ x < l, ∃ y, R x y) : ∃ s, Seq s ∧ lh s = l ∧ ∀ i x, ⟪i, x⟫ ∈ s → R i x := by
  rcases sigmaOne_skolem hP (show ∀ x ∈ under l, ∃ y, R x y by simpa using H) with ⟨s, ms, sdom, h⟩
  have : Seq s := ⟨ms, l, sdom⟩
  exact ⟨s, this, by simpa [this.domain_eq] using sdom, h⟩

theorem «sigmaOne_skolem_seq!» {R : V → V → Prop} (hP : Sg1-Relation R) {l}
    (H : ∀ x < l, ∃! y, R x y) : ∃! s, Seq s ∧ lh s = l ∧ ∀ i x, ⟪i, x⟫ ∈ s → R i x := by
  have : ∀ x < l, ∃ y, R x y := fun x hx ↦ (H x hx).exists
  rcases sigmaOne_skolem_seq hP this with ⟨s, Ss, rfl, hs⟩
  exact ExistsUnique.intro s ⟨Ss, rfl, hs⟩ (by
    rintro s' ⟨Ss', hss', hs'⟩
    exact Seq.lh_ext Ss' Ss hss' (fun i x₁ x₂ h₁ h₂ ↦ H i (Ss.lt_lh_of_mem h₂) |>.unique (hs' i x₁
      h₁) (hs i x₂ h₂)))

section «lp_section_5»

/-- Imported declaration from the Incompleteness formalization. -/
def vecToSeq : {n : ℕ} → (Fin n → V) → V
  | 0,     _ => ∅
  | n + 1, v => vecToSeq (v ·.castSucc) ⁀' v (Fin.last n)

@[simp] lemma vecToSeq_nil : vecToSeq ![] = (∅ : V) := by simp [vecToSeq]

@[simp] lemma vecToSeq_vecCons {n} (v : Fin n → V) (a : V) :
    vecToSeq (v <: a) = vecToSeq v ⁀' a := by simp [vecToSeq]

@[simp] lemma vecToSeq_seq {n} (v : Fin n → V) : Seq (vecToSeq v) := by
  induction n with
  | zero => simp [vecToSeq]
  | succ n ih =>
    simpa only [vecToSeq] using (ih _).seqCons _

@[simp] lemma lh_vecToSeq {n} (v : Fin n → V) : lh (vecToSeq v) = n := by
  induction n with
  | zero => simp [vecToSeq]
  | succ n ih => simp [vecToSeq, *]

lemma mem_vectoSeq {n : ℕ} (v : Fin n → V) (i : Fin n) : ⟪(i : V), v i⟫ ∈ vecToSeq v := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    simp only [vecToSeq]
    cases i using Fin.lastCases with
    | last => simp [mem_seqCons_iff]
    | cast i =>
      simp only [Fin.val_castSucc, mem_seqCons_iff, lh_vecToSeq, Nat.cast_inj]
      right; exact ih (v ·.castSucc) i

end «lp_section_5»

open HierarchySymbol

lemma order_ball_induction_sigma1 {f : V → V → V} (hf : Sg1-Function₂ f) {P : V → V → Prop} (hP :
    Sg1-Relation P)
    (ind : ∀ x y, (∀ x' < x, ∀ y' ≤ f x y, P x' y') → P x y) : ∀ x y, P x y := by
  have maxf : ∀ x y, ∃ m, ∀ x' ≤ x, ∀ y' ≤ y, f x' y' ≤ m := by
    intro x y;
    rcases sigma₁_replacement₂ hf (under (x + 1)) (under (y + 1)) |>.exists with ⟨m, hm⟩
    exact ⟨m, fun x' hx' y' hy' ↦
      le_of_lt <| lt_of_mem <| hm (f x' y') |>.mpr
        ⟨x', by simpa [lt_succ_iff_le, le_def] using hx',
          y', by simpa [lt_succ_iff_le, le_def] using hy', rfl⟩⟩
  intro x y
  have : ∀ k ≤ x, ∃ W, Seq W ∧ k + 1 = lh W ∧
      ⟪0, y⟫ ∈ W ∧
      ∀ l < k, ∀ m < W, ∀ m' < W, ⟪l, m⟫ ∈ W → ⟪l + 1, m'⟫ ∈ W →
          ∀ x' ≤ x - l, ∀ y' ≤ m, f x' y' ≤ m' := by
    intro k hk
    induction k using induction_sigma1
    · apply Boldface.imp (Boldface.comp₂ (by definability) (by definability))
      apply Boldface.ex
      apply Boldface.and (Boldface.comp₁ (by definability))
      apply Boldface.and
        (Boldface.comp₂
          (BoldfaceFunction.comp₂ (.var _) (.const _))
          (BoldfaceFunction.comp₁ (.var _)))
      apply Boldface.and
        (Boldface.comp₂ (.var 0) (by definability))
      iterate 3 apply Boldface.ball_lt (.var _)
      apply Boldface.imp
        (Boldface.comp₂ (.var _) (BoldfaceFunction.comp₂ (.var _) (.var _)))
      apply Boldface.imp
        (Boldface.comp₂ (.var _) (BoldfaceFunction.comp₂ (BoldfaceFunction.comp₂ (.var _) (.const
          _)) (.var _)))
      apply Boldface.ball_le
        (Boldface.comp₂
          (.var _)
          (BoldfaceFunction.comp₂ (.const _) (.var _)))
      apply Boldface.ball_le (.var _)
      apply Boldface.comp₂
        (BoldfaceFunction.comp₂
          (.var _) (.var _)) (.var _)
    case zero => exact ⟨!⟦y⟧, by simp⟩
    case succ k ih =>
      rcases ih (le_trans le_self_add hk) with ⟨W, SW, hkW, hW₀, hWₛ⟩
      let m₀ := SW.nth (show k < lh W by simp [←hkW])
      have : ∃ m₁, ∀ x' ≤ x - k, ∀ y' ≤ m₀, f x' y' ≤ m₁ := maxf (x - k) m₀
      rcases this with ⟨m₁, hm₁⟩
      exact ⟨W ⁀' m₁, SW.seqCons m₁, by simp [SW, hkW], Seq.subset_seqCons _ _ hW₀, by
        intro l hl m _ m' _ hm hm' x' hx' y' hy'
        rcases show l ≤ k from lt_succ_iff_le.mp hl with (rfl | hl)
        · have hmm₀ : m = m₀ := by
            simp only [mem_seqCons_iff, ←hkW, left_eq_add, one_ne_zero, false_and,
              false_or] at hm
            exact SW.isMapping.uniq hm (by simp [m₀])
          have hm'm₁ : m' = m₁ := by simpa [SW, hkW, mem_seqCons_iff] using hm'
          simpa [hm'm₁] using hm₁ x' hx' y' (by simp [←hmm₀, hy'])
        · have Hm : ⟪l, m⟫ ∈ W := Seq.mem_seqCons_iff_of_lt (by simpa [←hkW]) |>.mp hm
          have Hm' : ⟪l + 1, m'⟫ ∈ W := Seq.mem_seqCons_iff_of_lt (by simpa [←hkW]) |>.mp hm'
          exact hWₛ l hl m (lt_of_mem_rng Hm) m' (lt_of_mem_rng Hm') Hm Hm' x' hx' y' hy'⟩
  rcases this x (by rfl) with ⟨W, SW, hxW, hW₀, hWₛ⟩
  have : ∀ i ≤ x, ∀ m < W, ⟪x - i, m⟫ ∈ W → ∀ x' ≤ i, ∀ y' ≤ m, P x' y' := by
    intro i
    induction i using induction_sigma1
    · apply Boldface.imp
        (Boldface.comp₂ (.var _) (.const _))
      apply Boldface.ball_lt (.const _)
      apply Boldface.imp
        (Boldface.comp₂
          (.const _)
          (BoldfaceFunction.comp₂
            (BoldfaceFunction.comp₂
              (.const _) (.var _)) (.var _)))
      apply Boldface.ball_le (.var _)
      apply Boldface.ball_le (.var _)
      apply Boldface.comp₂ (.var _) (.var _)
    case zero =>
      intro _ _ _ _ _ h y' _
      rcases nonpos_iff_eq_zero.mp h
      exact ind 0 y' (by simp)
    case succ i ih' =>
      intro hi m _ hm x' hx' y' hy'
      have ih :
          ∀ m < W, ⟪x - i, m⟫ ∈ W → ∀ x' ≤ i, ∀ y' ≤ m, P x' y' := ih' (le_trans le_self_add hi)
      refine ind x' y' ?_
      intro x'' hx'' y'' hy''
      let m₁ := SW.nth (show x - i < lh W by simp [←hxW, lt_succ_iff_le])
      have : f x' y' ≤ m₁ :=
        hWₛ (x - (i + 1)) (tsub_lt_iff_left hi |>.mpr (by simp)) m (lt_of_mem_rng hm) m₁ (by simp
          [m₁]) hm
          (by rw [←sub_sub,
            sub_add_self_of_le (show 1 ≤ x - i from le_tsub_of_add_le_left hi)]; simp [m₁])
          x' (by simp [tsub_tsub_cancel_of_le hi, hx']) y' hy'
      exact ih m₁ (by simp [m₁]) (by simp [m₁]) x'' (lt_succ_iff_le.mp (lt_of_lt_of_le hx'' hx'))
        y'' (le_trans hy'' this)
  exact this x (by rfl) y (lt_of_mem_rng hW₀) (by simpa using hW₀) x (by rfl) y (by rfl)

lemma order_ball_induction_sigma1' {f : V → V} (hf : Sg1-Function₁ f) {P : V → V → Prop} (hP :
    Sg1-Relation P)
    (ind : ∀ x y, (∀ x' < x, ∀ y' ≤ f y, P x' y') → P x y) : ∀ x y, P x y :=
  have : Sg1-Function₂ (fun _ ↦ f) := BoldfaceFunction.comp₁ (by simp)
  order_ball_induction_sigma1 this hP ind

lemma order_ball_induction₂_sigma1 {fy fz : V → V → V → V}
    (hfy : Sg1-Function₃ fy) (hfz : Sg1-Function₃ fz) {P : V → V → V → Prop} (hP : Sg1-Relation₃ P)
    (ind : ∀ x y z, (∀ x' < x, ∀ y' ≤ fy x y z, ∀ z' ≤ fz x y z, P x' y' z') → P x y z) :
    ∀ x y z, P x y z := by
  let Q : V → V → Prop := fun x w ↦ P x (π₁ w) (π₂ w)
  have hQ : Sg1-Relation Q := by
    simp only [Q]
    apply Boldface.comp₃ (.var _)
      (BoldfaceFunction.comp₁ (.var _))
      (BoldfaceFunction.comp₁ (.var _))
  let f : V → V → V := fun x w ↦ ⟪fy x (π₁ w) (π₂ w), fz x (π₁ w) (π₂ w)⟫
  have hf : Sg1-Function₂ f := by
    simp only [f]
    apply BoldfaceFunction.comp₂
    · apply BoldfaceFunction.comp₃ (.var _)
      · apply BoldfaceFunction.comp₁ (.var _)
      · apply BoldfaceFunction.comp₁ (.var _)
    · apply BoldfaceFunction.comp₃ (.var _)
      · apply BoldfaceFunction.comp₁ (.var _)
      · apply BoldfaceFunction.comp₁ (.var _)
  intro x y z
  simpa [Q] using order_ball_induction_sigma1 hf hQ (fun x w ih ↦
    ind x (π₁ w) (π₂ w) (fun x' hx' y' hy' z' hz' ↦ by
      simpa [Q] using ih x' hx' ⟪y', z'⟫ (pair_le_pair hy' hz')))
    x ⟪y, z⟫

lemma order_ball_induction₃_sigma1 {fy fz fw : V → V → V → V → V}
    (hfy : Sg1-Function₄ fy) (hfz : Sg1-Function₄ fz) (hfw : Sg1-Function₄ fw) {P : V → V → V →
        V → Prop} (hP : Sg1-Relation₄ P)
    (ind : ∀ x y z w, (∀ x' < x, ∀ y' ≤ fy x y z w, ∀ z' ≤ fz x y z w, ∀ w' ≤ fw x y z w, P x' y'
      z' w') → P x y z w) :
    ∀ x y z w, P x y z w := by
  let Q : V → V → Prop := fun x v ↦ P x (π₁ v) (π₁ (π₂ v)) (π₂ (π₂ v))
  have hQ : Sg1-Relation Q := by
    simp only [Q]
    apply Boldface.comp₄
      (.var _)
      (BoldfaceFunction.comp₁ <| .var _)
      (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
      (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
  let f : V → V → V := fun x v ↦
    ⟪fy x (π₁ v) (π₁ (π₂ v)) (π₂ (π₂ v)), fz x (π₁ v) (π₁ (π₂ v)) (π₂ (π₂ v)), fw x (π₁ v) (π₁ (π₂
      v)) (π₂ (π₂ v))⟫
  have hf : Sg1-Function₂ f := by
    simp only [f]
    apply BoldfaceFunction.comp₂
    · apply BoldfaceFunction.comp₄
        (.var _)
        (BoldfaceFunction.comp₁ <| .var _)
        (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
        (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
    · apply BoldfaceFunction.comp₂
      · apply BoldfaceFunction.comp₄
          (.var _)
          (BoldfaceFunction.comp₁ <| .var _)
          (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
          (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
      · apply BoldfaceFunction.comp₄
          (.var _)
          (BoldfaceFunction.comp₁ <| .var _)
          (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
          (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
  intro x y z w
  have := order_ball_induction_sigma1 hf hQ (fun x v ih ↦
    ind x (π₁ v) (π₁ (π₂ v)) (π₂ (π₂ v)) (fun x' hx' y' hy' z' hz' w' hw' ↦ by
      simpa [Q] using ih x' hx' ⟪y', z', w'⟫ (pair_le_pair hy' <| pair_le_pair hz' hw')))
    x ⟪y, z, w⟫
  simpa [Q] using this

end Arith
end LO

end «lp_nc_section_1»
