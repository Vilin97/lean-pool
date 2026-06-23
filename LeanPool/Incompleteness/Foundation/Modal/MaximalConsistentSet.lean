/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Formula
import LeanPool.Incompleteness.Foundation.Modal.Entailment.K

/-! # MaximalConsistentSet -/


namespace LO
namespace Modal

open Entailment

variable {α : Type*}
variable {S} [Entailment (Formula α) S]
variable {𝓢 : S}

namespace FormulaSet

variable {T : FormulaSet α}

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Consistent (𝓢 : S) (T : FormulaSet α) := T *⊬[𝓢] ⊥

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Inconsistent (𝓢 : S) (T : FormulaSet α) := ¬(Consistent 𝓢 T)

lemma def_consistent : Consistent 𝓢 T ↔ ∀ Γ, (∀ ψ ∈ Γ, ψ ∈ T) → Γ ⊬[𝓢] ⊥ := by
  constructor;
  · intro h;
    simpa using Context.provable_iff.not.mp h;
  · intro h;
    apply Context.provable_iff.not.mpr; push Not;
    assumption;

lemma def_inconsistent : Inconsistent 𝓢 T ↔ ∃ (Γ :
    List (Formula α)), (∀ ψ ∈ Γ, ψ ∈ T) ∧ Γ ⊢[𝓢]! ⊥ := by
  unfold Inconsistent;
  apply not_iff_not.mp;
  push Not;
  exact def_consistent;

lemma union_consistent : Consistent 𝓢 (T₁ ∪ T₂) → (Consistent 𝓢 T₁) ∧ (Consistent 𝓢 T₂) := by
  intro h;
  replace h := def_consistent.mp h;
  constructor <;> {
    apply def_consistent.mpr;
    intro Γ hΓ;
    exact h Γ <| by tauto_set;
  }

variable [Entailment.Classical 𝓢]

lemma emptyset_consistent [H_consis : Entailment.Consistent 𝓢] :
    Consistent 𝓢 ∅ := by classical
  obtain ⟨f, hf⟩ := H_consis.exists_unprovable;
  apply def_consistent.mpr;
  intro Γ hΓ; by_contra hC;
  replace hΓ := List.eq_nil_iff_forall_not_mem.mpr hΓ; subst hΓ;
  have : 𝓢 ⊢! f := efq'! <| hC ⨀ verum!;
  contradiction;

variable [DecidableEq α]

omit [DecidableEq α] in
lemma not_mem_of_mem_neg (T_consis : Consistent 𝓢 T) (h : ∼φ ∈ T) : φ ∉ T := by classical
  by_contra hC;
  have : [φ, ∼φ] ⊬[𝓢] ⊥ := (def_consistent.mp T_consis) [φ, ∼φ] (by simp_all);
  have : [φ, ∼φ] ⊢[𝓢]! ⊥ := Entailment.botOfMemEither! (φ := φ) (Γ := [φ, ∼φ]) (by simp) (by simp);
  contradiction;

omit [DecidableEq α] in
lemma not_mem_neg_of_mem (T_consis : Consistent 𝓢 T) (h : φ ∈ T) : ∼φ ∉ T := by classical
  by_contra hC;
  have : [φ, ∼φ] ⊬[𝓢] ⊥ := (def_consistent.mp T_consis) [φ, ∼φ] (by simp_all);
  have : [φ, ∼φ] ⊢[𝓢]! ⊥ := Entailment.botOfMemEither! (φ := φ) (Γ := [φ, ∼φ]) (by simp) (by simp);
  contradiction;

omit [DecidableEq α] in
lemma iff_insert_consistent : Consistent 𝓢 (insert φ T) ↔ ∀ {Γ :
    List (Formula α)}, (∀ ψ ∈ Γ, ψ ∈ T) → 𝓢 ⊬ φ ⋏ ⋀Γ ==> ⊥ := by classical
  constructor;
  · intro h Γ hΓ;
    by_contra hC;
    have : 𝓢 ⊬ φ ⋏ ⋀Γ ==> ⊥ :=
        iff_imply_left_cons_conj'!.not.mp <| (def_consistent.mp h) (φ :: Γ) (by
        rintro ψ hq;
        simp only [List.mem_cons] at hq;
        cases hq with
        | inl h => subst h; simp only [Set.mem_insert_iff, true_or];
        | inr h =>
          simp only [Set.mem_insert_iff];
          right; exact hΓ ψ h;
      );
    contradiction;
  · intro h;
    apply def_consistent.mpr;
    intro Γ hΓ;
    have  : 𝓢 ⊬ φ ⋏ ⋀List.remove φ Γ ==> ⊥ := @h (Γ.remove φ) (by
      intro ψ hq;
      have := by simpa using hΓ ψ <| List.mem_of_mem_remove hq;
      cases this with
      | inl h => simpa [h] using List.mem_remove_iff.mp hq;
      | inr h => assumption;
    );
    by_contra hC;
    have := FiniteContext.provable_iff.mp hC;
    have :=
      imp_trans''! and_comm! <| imply_left_remove_conj! (φ := φ) <|
          FiniteContext.provable_iff.mp hC;
    contradiction;

omit [DecidableEq α] in
lemma iff_insert_inconsistent :
    Inconsistent 𝓢 (insert φ T) ↔ ∃ Γ, (∀ φ ∈ Γ, φ ∈ T) ∧ 𝓢 ⊢! φ ⋏ ⋀Γ ==> ⊥ := by classical
  unfold Inconsistent;
  apply not_iff_not.mp;
  push Not;
  exact iff_insert_consistent;

omit [DecidableEq α] in
lemma provable_iff_insert_neg_not_consistent : Inconsistent 𝓢 (insert (∼φ) T) ↔ T *⊢[𝓢]! φ := by
  classical
  constructor;
  · intro h;
    apply Context.provable_iff.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_inconsistent.mp h;
    existsi Γ;
    constructor;
    · exact hΓ₁;
    · have : Γ ⊢[𝓢]! ∼φ ==> ⊥ := imp_swap'! <| and_imply_iff_imply_imply'!.mp hΓ₂;
      exact dne'! <| negEquiv'!.mpr this;
  · intro h;
    apply iff_insert_inconsistent.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    use Γ;
    constructor;
    · exact hΓ₁;
    · apply and_imply_iff_imply_imply'!.mpr;
      apply imp_swap'!;
      exact negEquiv'!.mp <| dni'! hΓ₂;

omit [DecidableEq α] in
lemma unprovable_iff_insert_neg_consistent : Consistent 𝓢 (insert (∼φ) T) ↔ T *⊬[𝓢] φ:= by classical
  simpa [not_not] using provable_iff_insert_neg_not_consistent.not;

omit [DecidableEq α] in
lemma unprovable_iff_singleton_neg_consistent : Consistent 𝓢 {∼φ} ↔ 𝓢 ⊬ φ:= by classical
  have e : insert (∼φ) ∅ = ({∼φ} : FormulaSet α) := by aesop;
  have h₂ : Consistent 𝓢 (insert (∼φ) ∅) ↔ ∅ *⊬[𝓢] φ := unprovable_iff_insert_neg_consistent;
  rw [e] at h₂;
  suffices 𝓢 ⊬ φ ↔ ∅ *⊬[𝓢] φ by tauto;
  exact Context.provable_iff_provable.not;

omit [DecidableEq α] in
lemma neg_provable_iff_insert_not_consistent : Inconsistent 𝓢 (insert (φ) T) ↔ T *⊢[𝓢]! ∼φ:= by
  classical
  constructor;
  · intro h;
    apply Context.provable_iff.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_inconsistent.mp h;
    existsi Γ;
    constructor;
    · exact hΓ₁;
    · apply negEquiv'!.mpr;
      exact imp_swap'! <| and_imply_iff_imply_imply'!.mp hΓ₂;
  · intro h;
    apply iff_insert_inconsistent.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    existsi Γ;
    constructor;
    · assumption;
    · apply and_imply_iff_imply_imply'!.mpr;
      apply imp_swap'!;
      exact negEquiv'!.mp hΓ₂;

omit [DecidableEq α] in
lemma neg_unprovable_iff_insert_consistent : Consistent 𝓢 (insert (φ) T) ↔ T *⊬[𝓢] ∼φ := by
  classical
  simpa [not_not] using neg_provable_iff_insert_not_consistent.not;

omit [DecidableEq α] in
lemma unprovable_iff_singleton_consistent : Consistent 𝓢 {φ} ↔ 𝓢 ⊬ ∼φ := by classical
  have e : insert (φ) ∅ = ({φ} : FormulaSet α) := by aesop;
  have h₂ := neg_unprovable_iff_insert_consistent (𝓢 := 𝓢) (T := ∅) (φ := φ);
  rw [e] at h₂;
  suffices 𝓢 ⊬ ∼φ ↔ ∅ *⊬[𝓢] ∼φ by tauto;
  exact Context.provable_iff_provable.not;

omit [DecidableEq α] in
lemma unprovable_either (T_consis : Consistent 𝓢 T) : ¬(T *⊢[𝓢]! φ ∧ T *⊢[𝓢]! ∼φ) := by classical
  by_contra hC;
  have ⟨hC₁, hC₂⟩ := hC;
  have := negMdp! hC₂ hC₁;
  contradiction;

omit [DecidableEq α] in
lemma not_mem_falsum_of_consistent (T_consis : Consistent 𝓢 T) : ⊥ ∉ T := by classical
  by_contra hC;
  have : 𝓢 ⊬ ⊥ ==> ⊥ := (def_consistent.mp T_consis) [⊥] (by simpa);
  have : 𝓢 ⊢! ⊥ ==> ⊥ := efq!;
  contradiction;

omit [DecidableEq α] in
lemma not_singleton_consistent [Entailment.Necessitation 𝓢] (T_consis : Consistent 𝓢 T) (h :
    ∼□φ ∈ T) :
    Consistent 𝓢 {∼φ} := by classical
  apply def_consistent.mpr;
  intro Γ hΓ;
  simp only [Set.mem_singleton_iff] at hΓ;
  by_contra hC;
  have : 𝓢 ⊢! ∼(□φ) ==> ⊥ :=
    negEquiv'!.mp <| dni'! <| nec! <| dne'! <| negEquiv'!.mpr <| replace_imply_left_conj! hΓ hC;
  have : 𝓢 ⊬ ∼(□φ) ==> ⊥ := def_consistent.mp T_consis (Γ := [∼(□φ)]) (by aesop)
  contradiction;

omit [DecidableEq α] in
lemma either_consistent (T_consis : Consistent 𝓢 T) (φ) :
    Consistent 𝓢 (insert φ T) ∨ Consistent 𝓢 (insert (∼φ) T) := by classical
  by_contra hC;
  push Not at hC;
  obtain ⟨hC₁, hC₂⟩ := hC
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_inconsistent.mp <| by simpa using hC₁;
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := iff_insert_inconsistent.mp <| by simpa using hC₂;
  replace hΓ₂ := negEquiv'!.mpr hΓ₂;
  replace hΔ₂ := negEquiv'!.mpr hΔ₂;
  have : 𝓢 ⊢! ⋀Γ ⋏ ⋀Δ ==> ⊥ :=
    negEquiv'!.mp <| demorgan₁'! <| or₃'''! (imp_trans''! (imply_of_not_or'! <|
        demorgan₄'! hΓ₂) or₁!) (imp_trans''! (imply_of_not_or'! <| demorgan₄'! hΔ₂) or₂!) lem!
  have : 𝓢 ⊬ ⋀Γ ⋏ ⋀Δ ==> ⊥ :=
    unprovable_imp_trans''! imply_left_concat_conj! <| def_consistent.mp T_consis (Γ ++ Δ) <| by
    simp only [List.mem_append];
    rintro ψ (hqΓ | hqΔ);
    · exact hΓ₁ ψ hqΓ;
    · exact hΔ₁ ψ hqΔ;
  contradiction;

omit [DecidableEq α] in
open Classical in
lemma intro_union_consistent
  (h : ∀ {Γ₁ Γ₂ : List (Formula α)}, (∀ φ ∈ Γ₁, φ ∈ T₁) ∧ (∀ φ ∈ Γ₂, φ ∈ T₂) → 𝓢 ⊬ ⋀Γ₁ ⋏ ⋀Γ₂ ==> ⊥)
  : Consistent 𝓢 (T₁ ∪ T₂) := by classical
  apply def_consistent.mpr;
  intro Δ hΔ;
  let Δ₁ := (Δ.filter (· ∈ T₁));
  let Δ₂ := (Δ.filter (· ∈ T₂));
  have : 𝓢 ⊬ ⋀Δ₁ ⋏ ⋀Δ₂ ==> ⊥ :=
    @h Δ₁ Δ₂ ⟨(by intro _ h; simpa using List.of_mem_filter h),
      (by intro _ h; simpa using List.of_mem_filter h)⟩;
  exact unprovable_imp_trans''! (by
    apply FiniteContext.deduct'!;
    apply iff_provable_list_conj.mpr;
    intro ψ hq;
    cases (hΔ ψ hq);
    · exact iff_provable_list_conj.mp (and₁'! FiniteContext.id!) ψ <|
        List.mem_filter_of_mem hq (by simpa);
    · exact iff_provable_list_conj.mp (and₂'! FiniteContext.id!) ψ <|
        List.mem_filter_of_mem hq (by simpa);
  ) this;

omit [DecidableEq α] in
open Classical in
lemma intro_triunion_consistent
  (h : ∀ {Γ₁ Γ₂ Γ₃ : List (Formula α)}, (∀ φ ∈ Γ₁, φ ∈ T₁) ∧ (∀ φ ∈ Γ₂, φ ∈ T₂) ∧
    (∀ φ ∈ Γ₃, φ ∈ T₃) → 𝓢 ⊬ ⋀Γ₁ ⋏ ⋀Γ₂ ⋏ ⋀Γ₃ ==> ⊥)
  : Consistent 𝓢 (T₁ ∪ T₂ ∪ T₃) := by classical
  apply intro_union_consistent;
  rintro Γ₁₂ Γ₃ ⟨h₁₂, h₃⟩;
  simp only [Set.mem_union] at h₁₂;
  let Γ₁ := (Γ₁₂.filter (· ∈ T₁));
  let Γ₂ := (Γ₁₂.filter (· ∈ T₂));
  apply unprovable_imp_trans''! (φ := ⋀Γ₁ ⋏ ⋀Γ₂ ⋏ ⋀Γ₃);
  · exact imp_trans''! (and₂'! <| and_assoc!) <| by
      apply and_replace_left!;
      apply imply_left_conj_concat!.mp;
        apply conjconj_subset!;
        intro φ hp;
        simp only [List.mem_append, List.mem_filter, decide_eq_true_eq, Γ₁, Γ₂];
        rcases h₁₂ φ hp with (h₁ | h₂);
      · left; exact ⟨hp, h₁⟩;
      · right; exact ⟨hp, h₂⟩;
  · apply h;
    refine ⟨?_, ?_, h₃⟩;
    · intro φ hp;
      rcases h₁₂ φ (List.mem_of_mem_filter hp) with (_ | _)
      · assumption;
      · simpa using List.of_mem_filter hp;
    · intro φ hp;
      rcases h₁₂ φ (List.mem_of_mem_filter hp) with (_ | _)
      · have := List.of_mem_filter hp; simp at this;
        simpa using List.of_mem_filter hp;
      · assumption;

omit [DecidableEq α] in
omit [Entailment.Classical 𝓢] in
lemma exists_consistent_maximal_of_consistent (T_consis : Consistent 𝓢 T)
  : ∃ Z, Consistent 𝓢 Z ∧ T ⊆ Z ∧ ∀ U, U *⊬[𝓢] ⊥ → Z ⊆ U → U = Z := by classical
  obtain ⟨Z, h₁, ⟨h₂, h₃⟩⟩ := zorn_subset_nonempty { T : FormulaSet α | Consistent 𝓢 T} (by
    intro c hc chain hnc;
    existsi (⋃₀ c);
    simp only [Set.mem_setOf_eq];
    constructor;
    · apply def_consistent.mpr;
      intro Γ hΓ; by_contra hC;
      obtain ⟨U, hUc, hUs⟩ :=
        Set.subset_mem_chain_of_finite c hnc chain
          (s := ↑Γ.toFinset) (by simp)
          (by intro φ hp; simp_all);
      simp only [List.coe_toFinset] at hUs;
      have : Consistent 𝓢 U := hc hUc;
      have : Inconsistent 𝓢 U := by
        apply def_inconsistent.mpr;
        use Γ;
        constructor;
        · intro φ hp; exact hUs hp;
        · assumption;
      contradiction;
    · intro s a;
      exact Set.subset_sUnion_of_mem a;
  ) T T_consis;
  use Z;
  simp_all only [Set.mem_setOf_eq, Set.le_eq_subset, true_and];
  constructor;
  · assumption;
  · intro U hU hZU;
    apply Set.eq_of_subset_of_subset;
    · exact h₃ hU hZU;
    · assumption;

protected alias lindenbaum := exists_consistent_maximal_of_consistent

end FormulaSet



open FormulaSet

/-- Imported declaration from the Incompleteness formalization. -/
abbrev MaximalConsistentSet (𝓢 : S) := { T :
    FormulaSet α // (Consistent 𝓢 T) ∧ (∀ {U}, T ⊂ U → Inconsistent 𝓢 U)}

namespace MaximalConsistentSet

variable {Ω Ω₁ Ω₂ : MaximalConsistentSet 𝓢}
variable {φ : Formula α}

instance : Membership (Formula α) (MaximalConsistentSet 𝓢) := ⟨fun Ω φ => φ ∈ Ω.1⟩

lemma consistent (Ω : MaximalConsistentSet 𝓢) : Consistent 𝓢 Ω.1 := Ω.2.1

lemma maximal (Ω : MaximalConsistentSet 𝓢) : Ω.1 ⊂ U → Inconsistent 𝓢 U := Ω.2.2

lemma maximal' (Ω : MaximalConsistentSet 𝓢) {φ : Formula α} (hp : φ ∉ Ω) :
    Inconsistent 𝓢 (insert φ Ω.1) :=
  Ω.maximal (Set.ssubset_insert hp)

lemma equality_def : Ω₁ = Ω₂ ↔ Ω₁.1 = Ω₂.1 := by
  constructor;
  · intro h; cases h; rfl;
  · intro h; cases Ω₁; cases Ω₂; simp_all;

variable [DecidableEq α]

omit [DecidableEq α] in
lemma exists_of_consistent (consisT : Consistent 𝓢 T) : ∃ Ω :
    MaximalConsistentSet 𝓢, (T ⊆ Ω.1) := by classical
  have ⟨Ω, hΩ₁, hΩ₂, hΩ₃⟩ := FormulaSet.lindenbaum consisT;
  use ⟨Ω, ?_, ?_⟩;
  · assumption;
  · rintro U ⟨hU₁, _⟩;
    by_contra hC;
    have := hΩ₃ U hC <| hU₁;
    subst this;
    simp_all;

alias lindenbaum := exists_of_consistent

section «lp_section_classical»

variable [Entailment.Classical 𝓢]

omit [DecidableEq α] in
instance [Entailment.Consistent 𝓢] :
    Nonempty (MaximalConsistentSet 𝓢) :=
  ⟨lindenbaum emptyset_consistent |>.choose⟩

omit [DecidableEq α] in
lemma either_mem (Ω : MaximalConsistentSet 𝓢) (φ) : φ ∈ Ω ∨ ∼φ ∈ Ω := by classical
  by_contra hC;
  push Not at hC;
  rcases either_consistent (𝓢 := 𝓢) (Ω.consistent) φ;
  · have := Ω.maximal (Set.ssubset_insert hC.1); contradiction;
  · have := Ω.maximal (Set.ssubset_insert hC.2); contradiction;

omit [DecidableEq α] in
lemma membership_iff : (φ ∈ Ω) ↔ (Ω.1 *⊢[𝓢]! φ) := by classical
  constructor;
  · intro h; exact Context.by_axm! h;
  · intro hp;
    suffices ∼φ ∉ Ω.1 by apply or_iff_not_imp_right.mp <| (either_mem Ω φ); assumption;
    by_contra hC;
    have hnp : Ω.1 *⊢[𝓢]! ∼φ := Context.by_axm! hC;
    have : Ω.1 *⊢[𝓢]! ⊥ := negMdp! hnp hp;
    have : Ω.1 *⊬[𝓢] ⊥ := Ω.consistent;
    contradiction;

omit [DecidableEq α] in
@[simp]
lemma not_mem_falsum : ⊥ ∉ Ω := by classical
  exact not_mem_falsum_of_consistent Ω.consistent

omit [DecidableEq α] in
@[simp]
lemma mem_verum : ⊤ ∈ Ω := by classical
  apply membership_iff.mpr
  apply verum!

omit [DecidableEq α] in
@[simp]
lemma iff_mem_neg : (∼φ ∈ Ω) ↔ (φ ∉ Ω) := by classical
  constructor;
  · intro hnp;
    by_contra hp;
    replace hp := membership_iff.mp hp;
    replace hnp := membership_iff.mp hnp;
    have : Ω.1 *⊢[𝓢]! ⊥ := negMdp! hnp hp;
    have : Ω.1 *⊬[𝓢] ⊥ := Ω.consistent;
    contradiction;
  · intro hp;
    have : Consistent 𝓢 (insert (∼φ) Ω.1) := by
      haveI := provable_iff_insert_neg_not_consistent.not.mpr <| membership_iff.not.mp hp;
      unfold FormulaSet.Inconsistent at this;
      push Not at this;
      exact this;
    have := not_imp_not.mpr (@maximal (Ω := Ω) (U := insert (∼φ) Ω.1)) (by simpa);
    have : insert (∼φ) Ω.1 ⊆ Ω.1 := by simpa [Set.ssubset_def] using this;
    apply this;
    tauto_set;

omit [DecidableEq α] in
@[simp 1100]
lemma iff_mem_negneg : (∼∼φ ∈ Ω) ↔ (φ ∈ Ω) := by classical
  simp

omit [DecidableEq α] in
@[simp]
lemma iff_mem_imp : ((φ ==> ψ) ∈ Ω) ↔ (φ ∈ Ω) → (ψ ∈ Ω) := by classical
  constructor;
  · intro hpq hp;
    replace dpq := membership_iff.mp hpq;
    replace dp  := membership_iff.mp hp;
    apply membership_iff.mpr;
    exact dpq ⨀ dp;
  · intro h;
    replace h : φ ∉ Ω.1 ∨ ψ ∈ Ω := or_iff_not_imp_left.mpr (fun hnn => h (not_not.mp hnn));
    cases h with
    | inl h =>
      apply membership_iff.mpr;
      exact efq_of_neg! <| membership_iff.mp <| iff_mem_neg.mpr h;
    | inr h =>
      apply membership_iff.mpr;
      exact imply₁! ⨀ (membership_iff.mp h)

omit [DecidableEq α] in
lemma mdp (hφψ : φ ==> ψ ∈ Ω) (hψ : φ ∈ Ω) : ψ ∈ Ω := by classical
  exact iff_mem_imp.mp hφψ hψ

omit [DecidableEq α] in
@[simp]
lemma iff_mem_and : ((φ ⋏ ψ) ∈ Ω) ↔ (φ ∈ Ω) ∧ (ψ ∈ Ω) := by classical
  constructor;
  · intro hpq;
    replace hpq := membership_iff.mp hpq;
    constructor;
    · apply membership_iff.mpr; exact and₁'! hpq;
    · apply membership_iff.mpr; exact and₂'! hpq;
  · rintro ⟨hp, hq⟩;
    apply membership_iff.mpr;
    exact and₃'! (membership_iff.mp hp) (membership_iff.mp hq);

omit [DecidableEq α] in
@[simp]
lemma iff_mem_or : ((φ ⋎ ψ) ∈ Ω) ↔ (φ ∈ Ω) ∨ (ψ ∈ Ω) := by classical
  constructor;
  · intro hpq;
    replace hpq := membership_iff.mp hpq;
    by_contra hC;
    push Not at hC;
    have ⟨hp, hq⟩ := hC;
    replace hp := membership_iff.mp <| iff_mem_neg.mpr hp;
    replace hq := membership_iff.mp <| iff_mem_neg.mpr hq;
    have : Ω.1 *⊢[𝓢]! ⊥ := or₃'''! (negEquiv'!.mp hp) (negEquiv'!.mp hq) hpq;
    have : Ω.1 *⊬[𝓢] ⊥ := Ω.consistent;
    contradiction;
  · rintro (hp | hq);
    · apply membership_iff.mpr;
      exact or₁'! (membership_iff.mp hp);
    · apply membership_iff.mpr;
      exact or₂'! (membership_iff.mp hq);

omit [DecidableEq α] in
lemma iff_congr : (Ω.1 *⊢[𝓢]! (φ <=> ψ)) → ((φ ∈ Ω) ↔ (ψ ∈ Ω)) := by classical
  intro hpq;
  constructor;
  · intro hp; exact iff_mem_imp.mp (membership_iff.mpr <| and₁'! hpq) hp;
  · intro hq; exact iff_mem_imp.mp (membership_iff.mpr <| and₂'! hpq) hq;


omit [DecidableEq α] in
lemma intro_equality {h : ∀ φ, φ ∈ Ω₁.1 → φ ∈ Ω₂.1} : Ω₁ = Ω₂ := by classical
  exact equality_def.mpr <| Set.eq_of_subset_of_subset
    (by intro φ hp; exact h φ hp)
    (by
      intro φ;
      contrapose;
      intro hp;
      apply iff_mem_neg.mp;
      apply h;
      apply iff_mem_neg.mpr hp;
    )

omit [DecidableEq α] in
lemma neg_imp (h : ψ ∈ Ω₂ → φ ∈ Ω₁) : (∼φ ∈ Ω₁) → (∼ψ ∈ Ω₂) := by classical
  contrapose;
  intro nhnψ hnφ;
  have : φ ∈ Ω₁ := h <| iff_mem_negneg.mp <| iff_mem_neg.mpr nhnψ;
  have : ⊥ ∈ Ω₁ := mdp hnφ this;
  simpa;

omit [DecidableEq α] in
lemma neg_iff (h : φ ∈ Ω₁ ↔ ψ ∈ Ω₂) : (∼φ ∈ Ω₁) ↔ (∼ψ ∈ Ω₂) := by classical
  exact ⟨neg_imp <| h.mpr, neg_imp <| h.mp⟩

omit [DecidableEq α] in
lemma iff_mem_conj :
    (⋀Γ ∈ Ω) ↔ (∀ φ ∈ Γ, φ ∈ Ω) := by classical
  simp [membership_iff, iff_provable_list_conj];

end «lp_section_classical»

section «lp_section_1»

variable [Entailment.K 𝓢]

omit [DecidableEq α] in
lemma iff_mem_multibox : (□^[n]φ ∈ Ω) ↔ (∀ {Ω' :
    MaximalConsistentSet 𝓢}, (□''⁻¹^[n]Ω.1 ⊆ Ω'.1) → (φ ∈ Ω')) := by classical
  constructor;
  · intro hp Ω' hΩ'; apply hΩ'; simpa;
  · contrapose;
    push Not;
    intro hp;
    obtain ⟨Ω', hΩ'⟩ := lindenbaum (𝓢 := 𝓢) (T := insert (∼φ) (□''⁻¹^[n]Ω.1)) (by
      apply unprovable_iff_insert_neg_consistent.mpr;
      by_contra hC;
      obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp hC;
      have : 𝓢 ⊢! □^[n]⋀Γ ==> □^[n]φ := imply_multibox_distribute'! hΓ₂;
      have : 𝓢 ⊬ □^[n]⋀Γ ==> □^[n]φ := by
        have := Context.provable_iff.not.mp <| membership_iff.not.mp hp;
        push Not at this;
        have : 𝓢 ⊬ ⋀□'^[n]Γ ==> □^[n]φ := FiniteContext.provable_iff.not.mp <| this (□'^[n]Γ) (by
          intro ψ hq;
          obtain ⟨χ, hr₁, rfl⟩ := by simpa using hq;
          simpa using hΓ₁ χ hr₁;
        );
        revert this;
        contrapose;
        exact imp_trans''! collect_multibox_conj!;
      contradiction;
    );
    existsi Ω';
    constructor;
    · exact Set.Subset.trans (by tauto_set) hΩ';
    · apply iff_mem_neg.mp;
      apply hΩ';
      simp only [Set.mem_insert_iff, true_or]

omit [DecidableEq α] in
lemma iff_mem_box : (□φ ∈ Ω) ↔ (∀ {Ω' :
    MaximalConsistentSet 𝓢}, (□''⁻¹Ω.1 ⊆ Ω'.1) → (φ ∈ Ω')) :=
  iff_mem_multibox (n := 1)


omit [DecidableEq α] in
lemma multibox_dn_iff : (□^[n](∼∼φ) ∈ Ω) ↔ (□^[n]φ ∈ Ω) := by classical
  simp only [iff_mem_multibox];
  constructor;
  · intro h Ω hΩ;
    exact iff_mem_negneg.mp <| h hΩ;
  · intro h Ω hΩ;
    exact iff_mem_negneg.mpr <| h hΩ;

omit [DecidableEq α] in
lemma box_dn_iff : (□(∼∼φ) ∈ Ω) ↔ (□φ ∈ Ω) := by classical
  exact multibox_dn_iff (n := 1)


omit [DecidableEq α] in
lemma mem_multibox_dual : □^[n]φ ∈ Ω ↔ ∼(◇^[n](∼φ)) ∈ Ω := by classical
  simp only [membership_iff];
  constructor;
  · intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    exact Context.provable_iff.mpr ⟨Γ, hΓ₁, FiniteContext.provable_iff.mpr <|
      imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₁'! multibox_duality!)⟩;
  · intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    exact Context.provable_iff.mpr ⟨Γ, hΓ₁, FiniteContext.provable_iff.mpr <|
      imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₂'! multibox_duality!)⟩;

omit [DecidableEq α] in
lemma mem_box_dual : □φ ∈ Ω ↔ (∼(◇(∼φ)) ∈ Ω) := by classical
  exact mem_multibox_dual (n := 1)

omit [DecidableEq α] in
lemma mem_multidia_dual : ◇^[n]φ ∈ Ω ↔ ∼(□^[n](∼φ)) ∈ Ω := by classical
  simp only [membership_iff];
  constructor;
  · intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    exact Context.provable_iff.mpr ⟨Γ, hΓ₁, FiniteContext.provable_iff.mpr <|
      imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₁'! multidia_duality!)⟩;
  · intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    exact Context.provable_iff.mpr ⟨Γ, hΓ₁, FiniteContext.provable_iff.mpr <|
      imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₂'! multidia_duality!)⟩;
omit [DecidableEq α] in
lemma mem_dia_dual : ◇φ ∈ Ω ↔ (∼(□(∼φ)) ∈ Ω) := by classical
  exact mem_multidia_dual (n := 1)

omit [DecidableEq α] in
lemma iff_mem_multidia : (◇^[n]φ ∈ Ω) ↔ (∃ Ω' :
    MaximalConsistentSet 𝓢, (□''⁻¹^[n]Ω.1 ⊆ Ω'.1) ∧ (φ ∈ Ω'.1)) := by classical
  constructor;
  · intro h;
    have := mem_multidia_dual.mp h;
    have := iff_mem_neg.mp this;
    have := iff_mem_multibox.not.mp this;
    push Not at this;
    obtain ⟨Ω', h₁, h₂⟩ := this;
    use Ω';
    constructor;
    · exact h₁;
    · exact iff_mem_negneg.mp <| iff_mem_neg.mpr h₂;
  · rintro ⟨Ω', h₁, h₂⟩;
    apply mem_multidia_dual.mpr;
    apply iff_mem_neg.mpr;
    apply iff_mem_multibox.not.mpr;
    push Not;
    use Ω';
    constructor;
    · exact h₁;
    · exact iff_mem_neg.mp <| iff_mem_negneg.mpr h₂;
omit [DecidableEq α] in
lemma iff_mem_dia : (◇φ ∈ Ω) ↔ (∃ Ω' :
    MaximalConsistentSet 𝓢, (□''⁻¹Ω.1 ⊆ Ω'.1) ∧ (φ ∈ Ω'.1)) :=
  iff_mem_multidia (n := 1)

omit [DecidableEq α] in
lemma multibox_multidia : (∀ {φ : Formula α}, (□^[n]φ ∈ Ω₁.1 → φ ∈ Ω₂.1)) ↔ (∀ {φ :
    Formula α}, (φ ∈ Ω₂.1 → ◇^[n]φ ∈ Ω₁.1)) := by classical
  constructor;
  · intro h φ;
    contrapose;
    intro h₂;
    apply iff_mem_neg.mp;
    apply h;
    apply iff_mem_negneg.mp;
    apply (neg_iff <| mem_multidia_dual).mp;
    exact iff_mem_neg.mpr h₂;
  · intro h φ;
    contrapose;
    intro h₂;
    apply iff_mem_neg.mp;
    apply (neg_iff <| mem_multibox_dual).mpr;
    apply iff_mem_negneg.mpr;
    apply h;
    exact iff_mem_neg.mpr h₂;

variable {Γ : List (Formula α)}

omit [DecidableEq α] in
lemma iff_mem_multibox_conj : (□^[n]⋀Γ ∈ Ω) ↔ (∀ φ ∈ Γ, □^[n]φ ∈ Ω) := by classical
  simp only [iff_mem_multibox, iff_mem_conj];
  constructor;
  · intro h φ hφ Ω' hΩ';
    exact h hΩ' _ hφ;
  · intro h Ω' hΩ' φ hφ;
    apply h _ hφ;
    tauto;

omit [DecidableEq α] in
lemma iff_mem_box_conj : (□⋀Γ ∈ Ω) ↔ (∀ φ ∈ Γ, □φ ∈ Ω) := by classical
  exact iff_mem_multibox_conj (n := 1)

end «lp_section_1»

end MaximalConsistentSet

end Modal
end LO
