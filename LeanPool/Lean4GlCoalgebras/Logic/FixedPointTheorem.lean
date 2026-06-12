/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/

import LeanPool.Lean4GlCoalgebras.Logic.Semantics

/-! ## Fixed-Point Theorem for Box and Diamond Formulas

Here we prove the fixed-point theorem for formulas of form `□φ` and `◇φ`.
-/

namespace Lean4GlCoalgebras

/-- Semantic Substitution Lemma for logics with transitive frames. -/
lemma semantic_substitution_lemma {α : Type} (M : Model α) (u : α) (n : ℕ) (φ ψ χ : Formula) :
  evaluate ⟨M, u⟩ (⊡ (φ ⟷ ψ)) → evaluate ⟨M, u⟩ ((single n φ χ) ⟷ (single n ψ χ)) := by
    intro mp
    induction χ generalizing u
    case bottom => simp [single]
    case top => simp [single]
    case atom k =>
      by_cases eq : k = n
      · simp_all [single]
      · simp [single, eq]
        grind
    case negAtom k =>
      by_cases eq : k = n
      · simp_all [single]
        grind
      · simp_all [single]
        grind
    case and ih1 ih2 =>
      simp_all [single]
      grind
    case or ih1 ih2 =>
      simp_all [single]
      grind
    case box χ ih1 =>
      constructor <;> simp_all only [evaluate_and, evaluate_imp, single]
      · intro h w u_w
        have := mp.2 w u_w
        simp only [evaluate_and, evaluate_imp] at this
        exact ((ih1 w) ⟨this, fun o w_o ↦ mp.2 o (M.trans u_w w_o)⟩).1 (h w u_w)
      · intro h w u_w
        have := mp.2 w u_w
        simp only [evaluate_and, evaluate_imp] at this
        exact ((ih1 w) ⟨this, fun o w_o ↦ mp.2 o (M.trans u_w w_o)⟩).2 (h w u_w)
    case diamond χ ih =>
      constructor <;> simp_all only [evaluate_and, evaluate_imp, single]
      · intro ⟨w, u_w, h⟩
        refine ⟨w, u_w, ?_⟩
        have := mp.2 w u_w
        simp only [evaluate_and, evaluate_imp] at this
        exact (ih w ⟨this, fun o w_o ↦ mp.2 o (M.trans u_w w_o)⟩).1 h
      · intro ⟨w, u_w, h⟩
        refine ⟨w, u_w, ?_⟩
        have := mp.2 w u_w
        simp only [evaluate_and, evaluate_imp] at this
        exact (ih w ⟨this, fun o w_o ↦ mp.2 o (M.trans u_w w_o)⟩).2 h

/-- On transitive and conversely well-founded frames: if `u ⊭ □ φ` then there is `w` such that
    `u R w` and `w ⊨ □ φ`. -/
lemma GL_eval_not_box_prop {α : Type} {M : Model α} {u : α} {φ : Formula} :
  ¬ evaluate ⟨M, u⟩ (□ φ) → ∃ w, M.R u w ∧ evaluate ⟨M, w⟩ (□ φ) ∧ ¬ evaluate ⟨M, w⟩ φ := by
  intro mp
  have mp := by simpa using mp
  have ⟨w, u_w, w1⟩ := mp
  by_cases w2 : evaluate (M, w) (□φ)
  · exact ⟨w, u_w, w2, w1⟩
  · have ⟨o, w_o, o1⟩ := GL_eval_not_box_prop w2
    exact ⟨o, M.trans u_w w_o, o1⟩
termination_by
  M.con_wf.wrap u
decreasing_by
  simp [WellFounded.wrap, Function.swap, u_w]

/-- Helper lemma for the fixed point theorem for `□φ`. -/
lemma FPT_box_helper (φ : Formula) (n : Nat)
  : ⊨ (⊡ (at n ⟷ single n ⊤ (□ φ))) ↣ (at n ⟷ □ φ) := by
  simp only [Formula.isValid, evaluate_imp, evaluate_and]
  intro α M u ⟨⟨mp1, mp2⟩, mp3⟩
  constructor
  · intro mp
    have claim : evaluate ⟨M, u⟩ (⊡ (at n ⟷ ⊤)) := by
      simp only [evaluate, Formula.neg, or_true, false_or, true_and]
      refine ⟨mp, fun w u_w ↦ ?_⟩
      have := (mp3 w u_w).2
      simp only [evaluate_imp] at this
      apply this
      intro o w_o
      exact mp1 mp o (M.trans u_w w_o)
    have := semantic_substitution_lemma M u n (at n) (⊤) (□ φ) claim
    simp only [evaluate_and, evaluate_imp, single, single_identity] at this
    apply this.2 (mp1 mp)
  · intro mpp
    by_contra con
    have h1 : ¬ evaluate (M, u) (single n ⊤ (□φ)) := by simp_all
    have ⟨w, u_w, w1, w2⟩ := GL_eval_not_box_prop h1
    have claim : evaluate ⟨M, w⟩ (⊡ (at n ⟷ ⊤)) := by
      simp only [evaluate, Formula.neg, or_true, false_or, true_and]
      have mp3_w := mp3 w u_w
      simp only [evaluate_and, evaluate_imp] at mp3_w
      refine ⟨mp3_w.2 w1, fun o w_o ↦ ?_⟩
      have mp3_o := mp3 o (M.trans u_w w_o)
      simp only [evaluate_and, evaluate_imp] at mp3_o
      exact mp3_o.2 (fun p o_p ↦ w1 p (M.trans w_o o_p))
    have := semantic_substitution_lemma M w n (at n) ⊤ φ claim
    simp only [evaluate_and, evaluate_imp, single_identity] at this
    exact w2 (this.1 (mpp w u_w))

/-- Helper lemma for the fixed point theorem for `◇φ`. -/
lemma FPT_diamond_helper (φ : Formula) (n : Nat)
  : ⊨ (⊡ (at n ⟷ single n ⊥ (◇ φ))) ↣ (at n ⟷ ◇ φ) := by
  simp only [Formula.isValid, evaluate_imp, evaluate_and]
  intro α M u ⟨⟨mp1, mp2⟩, mp3⟩
  constructor
  · intro mp
    have h : □(~φ) = (~(◇ φ)) := by simp
    have h' : (□(~single n ⊥ φ)) = (~◇(single n ⊥ φ)) := by simp
    have h1 := mp1 mp
    have h2 : ¬ evaluate (M, u) (single n ⊥ (□ (~ φ))) := by
      rw [h]
      simp only [single_neg, ←evaluate_neg, not_not, h1]
    have ⟨w, u_w, w1, w2⟩ := GL_eval_not_box_prop h2
    simp only [single_neg] at w1
    have claim : evaluate ⟨M, w⟩ (⊡ (at n ⟷ ⊥)) := by
      simp only [evaluate, Formula.neg, or_false, true_or, and_true]
      constructor
      · intro con
        have mp3_w := mp3 w u_w
        simp only [evaluate_and, evaluate_imp] at mp3_w
        have := mp3_w.1
        have this := by simpa [con] using this
        simp only [h', ←evaluate_neg] at w1
        exact w1 this
      · intro o w_o con
        have mp3_o := mp3 o (M.trans u_w w_o)
        simp only [evaluate_and, evaluate_imp] at mp3_o
        have := mp3_o.1
        have this := by simpa [con] using this
        have ⟨p, o_p, p1⟩ := this
        simp only [h', ←evaluate_neg] at w1
        apply w1 ⟨p, M.trans w_o o_p, p1⟩
    have := semantic_substitution_lemma M w n (at n) ⊥ φ claim
    simp only [evaluate_and, evaluate_imp, single_identity] at this
    have w2 := by simpa [single_neg, evaluate_neg] using w2
    exact ⟨w, u_w, this.2 w2⟩
  · intro mpp
    by_contra con
    have claim : evaluate ⟨M, u⟩ (⊡ (at n ⟷ ⊥)) := by
      simp only [evaluate, Formula.neg, or_false, true_or, and_true]
      refine ⟨con, fun w u_w con ↦ ?_⟩
      have mp3_w := mp3 w u_w
      simp only [evaluate_and, evaluate_imp] at mp3_w
      have ⟨o, w_o, o1⟩ := mp3_w.1 con
      have w1 : evaluate (M, u) (single n ⊥ (◇φ)) := ⟨o, M.trans u_w w_o, o1⟩
      simp_all
    have := semantic_substitution_lemma M u n (at n) ⊥ (◇ φ) claim
    simp only [evaluate_and, evaluate_imp, single_identity] at this
    simp_all

/-- Simplification lemma for the fixed point theorem. -/
lemma evaluate_box_dot_iff (φ : Formula) : ⊨ ⊡ (φ ⟷ φ) := by
  simp only [Formula.isValid, evaluate_and, evaluate_imp]
  intro α M u
  constructor
  · simp
  · intro w u_w
    simp only [evaluate_and, evaluate_imp]
    simp

/-- □ φ case of the fixed point theorem. -/
theorem FPT_box (φ : Formula) (n : Nat) :
    ⊨ (single n ⊤ (□ φ)) ⟷ (single n (□ single n ⊤ φ) (□ φ)) := by
  intro α M u
  have := FPT_box_helper φ n
  have h := single_preserves_validity n _ (single n ⊤ (□ φ)) this α M u
  simp only [single_imp, evaluate_imp, single_iff] at h
  have := h (by
    have h :
        single n (single n ⊤ (□φ)) (⊡ (at n ⟷ single n ⊤ (□ φ))) =
          (⊡ (((single n ⊤ (□φ)) ⟷ ((single n ⊤ (□ φ)))))) := by
      clear *-
      simp only [single, Formula.neg, beq_self_eq_true, if_true, Formula.and.injEq,
        Formula.or.injEq, Formula.box.injEq, Formula.diamond.injEq, true_and, and_true,
        and_self]
      constructor
      · apply not_in_single_voc
        apply not_in_single_top_voc
      · apply not_in_single_voc
        simp only [in_neg_voc_iff]
        apply not_in_single_top_voc
    rw [h]
    apply evaluate_box_dot_iff)
  simp_all [single]

/-- ◇ φ case of the fixed point theorem. -/
theorem FPT_diamond (φ : Formula) (n : Nat) :
    ⊨ (single n ⊥ (◇ φ)) ⟷ (single n (◇ single n ⊥ φ) (◇ φ)) := by
  intro α M u
  have := FPT_diamond_helper φ n
  have h := single_preserves_validity n _ (single n ⊥ (◇ φ)) this α M u
  simp only [single_imp, evaluate_imp, single_iff] at h
  have := h (by
    have h :
        single n (single n ⊥ (◇φ)) (⊡ (at n ⟷ single n ⊥ (◇ φ))) =
          (⊡ (((single n ⊥ (◇φ)) ⟷ ((single n ⊥ (◇ φ)))))) := by
      clear *-
      simp only [single, Formula.neg, beq_self_eq_true, if_true, Formula.and.injEq,
        Formula.or.injEq, Formula.box.injEq, Formula.diamond.injEq, true_and, and_true,
        and_self]
      constructor
      · apply not_in_single_voc
        apply not_in_single_bot_voc
      · apply not_in_single_voc
        simp only [in_neg_voc_iff]
        apply not_in_single_bot_voc
    rw [h]
    apply evaluate_box_dot_iff)
  simp_all [single]

/-- Vocabulary condition for □ φ case of the fixed point theorem. -/
lemma FPT_box_vocab (φ : Formula) (n : ℕ) :
    n ∉ Formula.vocab (single n ⊤ (□ φ)) ∧
      Formula.vocab (single n ⊤ (□ φ)) ⊆ Formula.vocab (□ φ) := by
  constructor
  · apply not_in_single_top_voc
  · intro m m_in
    have := in_single_voc' m_in
    simp_all [Formula.vocab]

/-- Vocabulary condition for ◇ φ case of the fixed point theorem. -/
lemma FPT_diamond_vocab (φ : Formula) (n : ℕ) :
    n ∉ Formula.vocab (single n ⊥ (◇ φ)) ∧
      Formula.vocab (single n ⊥ (◇ φ)) ⊆ Formula.vocab (◇ φ) := by
  constructor
  · apply not_in_single_bot_voc
  · intro m m_in
    have := in_single_voc' m_in
    simp_all [Formula.vocab]

/-- Fixed-point theorem for formulas `□φ` and `◇φ`. -/
theorem fixed_point_theorem_modal (φ : Formula) (n : ℕ)
    (box_or_dia : φ.isBox ∨ φ.isDiamond) :
    ∃ (ψ : Formula),
      n ∉ Formula.vocab ψ ∧ semEquiv ψ (single n ψ φ) ∧ Formula.vocab ψ ⊆ Formula.vocab φ := by
  cases φ <;> simp [Formula.isBox, Formula.isDiamond] at box_or_dia
  case box φ =>
    have FPT_box_prop := FPT_box_vocab φ n
    exact ⟨single n ⊤ (□ φ), FPT_box_prop.1, FPT_box φ n, FPT_box_prop.2⟩
  case diamond φ =>
    have FPT_diamond_prop := FPT_diamond_vocab φ n
    exact ⟨single n ⊥ (◇ φ), FPT_diamond_prop.1, FPT_diamond φ n, FPT_diamond_prop.2⟩
end Lean4GlCoalgebras
