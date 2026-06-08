/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice
import LeanPool.Lean4GlCoalgebras.Logic.Semantics
import LeanPool.Lean4GlCoalgebras.General.Proof

/-! ## Soundness of GL-proof system. -/

namespace Lean4GlCoalgebras

open Classical in
/-- Helper for soundness, Given a proof of `Γ` and a countermodel of `Γ`, find a path in the proof
    and the model -/
noncomputable def chain
  {𝕏 : Proof}
  {x : 𝕏.X}
  {Γ : Sequent}
  (prop : f (r 𝕏.α x) = Γ)
  {W : Type}
  {M : Model W}
  {w : W}
  (w_prop : ¬ evaluateSeq (M, w) Γ)
  (n : Nat) : (y : 𝕏.X) × {u : W // ¬ evaluateSeq ⟨M, u⟩ (f (r 𝕏.α y))}
    := match n with
       | 0 => ⟨x, ⟨w, by simp_all⟩⟩
       | n + 1 =>
        match chain prop w_prop n with
        | ⟨x_ih, w_ih, w_ih_prop⟩ =>
        match r_def : r 𝕏.α x_ih with
        | .top Δ in_Δ => False.elim (by
            have w_ih_prop := by simpa [r_def, f] using w_ih_prop
            have := w_ih_prop ⊤ in_Δ
            simp_all)
        | .ax Δ n in_Δ =>
          False.elim (by
            by_cases evaluate ⟨M, w_ih⟩ (at n)
            case pos w_n =>
              have w_ih_prop := by simpa [r_def, f] using w_ih_prop
              have := w_ih_prop (at n) in_Δ.1
              simp_all
            case neg not_w_n =>
              have w_ih_prop := by simpa [r_def, f] using w_ih_prop
              have := w_ih_prop (na n) in_Δ.2
              simp_all)
        | .and Δ φ₁ φ₂ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y,z] =>
            have := not_and_or.1 <| fun x ↦
              (not_exists.1 w_ih_prop) (φ₁ & φ₂) ⟨(r_def ▸ in_Δ), x⟩
            if w_ih_nφ₁ : ¬evaluate (M, w_ih) φ₁
            then
              ⟨y, w_ih, by
                have := 𝕏.step x_ih
                have this := by simpa [r_def, p_def, -Finset.union_singleton] using this
                suffices hseq : ∀ χ ∈ Δ, χ ≠ (φ₁ & φ₂) → ¬evaluate (M, w_ih) χ by
                  simpa [evaluateSeq, this.1, w_ih_nφ₁, fₙ_alternate] using hseq
                intro χ χ_in χ_not con
                apply w_ih_prop
                exact ⟨χ, r_def ▸ χ_in, con⟩
              ⟩
            else
              ⟨z, w_ih, by
                have w_ih_nφ₂ : ¬evaluate (M, w_ih) φ₂ := by simp_all
                have := 𝕏.step x_ih
                have this := by simpa [r_def, p_def, -Finset.union_singleton] using this
                suffices hseq : ∀ χ ∈ Δ, χ ≠ (φ₁ & φ₂) → ¬evaluate (M, w_ih) χ by
                  simpa [evaluateSeq, this.2, w_ih_nφ₂, fₙ_alternate] using hseq
                intro χ χ_in χ_not con
                apply w_ih_prop
                exact ⟨χ, r_def ▸ χ_in, con⟩⟩
          | [] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | [y] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | x::y::z::l => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
        | .or Δ φ₁ φ₂ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
            have := not_or.1 <| fun x ↦
              (not_exists.1 w_ih_prop) (φ₁ v φ₂) ⟨(r_def ▸ in_Δ), x⟩
            have h : ¬evaluateSeq (M, w_ih) (f (r 𝕏.α y)) := by
              have 𝕏h_x_ih := 𝕏.step x_ih
              have 𝕏h_x_ih := by simpa [r_def, p_def, -Finset.union_singleton] using 𝕏h_x_ih
              suffices hseq : ∀ χ ∈ Δ, χ ≠ (φ₁ v φ₂) → ¬evaluate (M, w_ih) χ by
                simpa [evaluateSeq, 𝕏h_x_ih, fₙ_alternate, this] using hseq
              intro χ χ_in χ_not con
              apply w_ih_prop
              exact ⟨χ, r_def ▸ χ_in, con⟩
              ⟨y, w_ih, h⟩
          | [] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | x::y::l => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
        | .box Δ φ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
              have := not_forall.1 <| fun x ↦
                (not_exists.1 w_ih_prop) (□ φ) ⟨(r_def ▸ in_Δ), x⟩
              let w_next := this.choose
              have w_next_prop := Classical.not_imp.1 this.choose_spec
              have h : ¬evaluateSeq (M, w_next) (f (r 𝕏.α y)) := by
                have 𝕏h_x_ih := 𝕏.step x_ih
                have 𝕏h_x_ih := by simpa [r_def, p_def, -Finset.union_singleton] using 𝕏h_x_ih
                suffices hseq :
                    ¬evaluate (M, w_next) φ ∧
                      ∀ χ ∈ (Δ \ {□ φ}).D, ¬evaluate (M, w_next) χ by
                  simpa [evaluateSeq, 𝕏h_x_ih, fₙ_alternate] using hseq
                constructor
                · exact w_next_prop.2
                · simp only [Sequent.D, Finset.mem_union, Finset.mem_filter,
                    Finset.mem_filterMap, Formula.opUnDi_eq, exists_eq_right,
                    Finset.mem_sdiff, Finset.mem_singleton]
                  have w_ih_prop := by simpa [evaluateSeq, r_def, f] using w_ih_prop
                  intro χ χ_in con
                  rcases χ_in with ⟨⟨χ_in, χ_not_box_φ⟩, χ_di⟩ | diχ_Δ
                  · apply w_ih_prop _ χ_in
                    cases χ <;> simp [Formula.isDiamond] at χ_di
                    case diamond χ' =>
                      have ⟨u, w_next_u, u_χ'⟩ := con
                      exact ⟨u, M.trans w_next_prop.1 w_next_u, u_χ'⟩
                  · exact w_ih_prop _ diχ_Δ.1 ⟨w_next, w_next_prop.1, con⟩
              ⟨y, w_next, h⟩
          | [] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | x::y::l => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)

/-- The left projection of `chain` is a chain in the proof. -/
lemma chain_proof_prop
  {𝕏 : Proof}
  {x : 𝕏.X}
  {Γ : Sequent}
  (prop : f (r 𝕏.α x) = Γ)
  {W : Type}
  {M : Model W}
  {w : W}
  (w_prop : ¬evaluateSeq (M, w) Γ)
  : ∀ n, edge 𝕏.α (chain prop w_prop n).1 (chain prop w_prop (n + 1)).1 := by
    intro n
    conv =>
      congr
      · skip
      · skip
      · unfold chain
    rcases chain prop w_prop n with ⟨x_ih, w_ih, w_ih_prop⟩
    cases r 𝕏.α (chain prop w_prop n).fst
    all_goals
      grind [edge]

/-- The right projection of `chain` makes progress in the model on box nodes. -/
lemma chain_model_prop {𝕏 : Proof}
  {x : 𝕏.X}
  {Γ : Sequent}
  (prop : f (r 𝕏.α x) = Γ)
  {W : Type}
  {M : Model W}
  {w : W}
  (w_prop : ¬evaluateSeq (M, w) Γ)
  : ∀ n,
      (¬ (r 𝕏.α (chain prop w_prop n).1).isBox →
        (chain prop w_prop n).2.1 = (chain prop w_prop (n + 1)).2.1) ∧
      ((r 𝕏.α (chain prop w_prop n).1).isBox →
        M.R (chain prop w_prop n).2.1 (chain prop w_prop (n + 1)).2.1)
  := by
  intro n
  constructor
  · conv =>
      congr
      · skip
      · conv =>
          congr
          · skip
          · rw [chain]
    rcases chain prop w_prop n with ⟨x_ih, w_ih, w_ih_prop⟩
    simp
    split <;> grind [RuleApp.isBox]
  · conv =>
      congr
      · skip
      · conv =>
          congr
          · skip
          · skip
          · rw [chain]
    rcases chain prop w_prop n with ⟨x_ih, w_ih, w_ih_prop⟩
    simp
    split <;> try grind [RuleApp.isBox]
    rename_i Δ φ in_Δ r_def
    intro _
    simp only
    split
    · exact (Classical.not_imp.1 (Classical.choose_spec
        (not_forall.1 (fun z ↦
          (not_exists.1 w_ih_prop) (□ φ) ⟨(r_def ▸ in_Δ), z⟩)))).1
    all_goals
      exfalso
      have step := 𝕏.step x_ih
      simp_all

/-- The right projection of `chain` eventually progresses. -/
lemma has_children_of_chain_model {𝕏 : Proof}
  {x : 𝕏.X}
  {Γ : Sequent}
  (prop : f (r 𝕏.α x) = Γ)
  {W : Type}
  {M : Model W}
  {w : W}
  (w_prop : ¬evaluateSeq (M, w) Γ) :
  ∀ n, ∃ m, M.R (chain prop w_prop n).2.1 (chain prop w_prop (n + m)).2.1 := by
  intro n
  by_contra h
  have h := by simpa using h
  have g1 : ∀ m, (chain prop w_prop n).2.1 = (chain prop w_prop (n + m)).2.1 := by
    intro m
    induction m
    · rfl
    case succ k ih =>
      simp only [ih] at *
      have h := h (k + 1)
      have chain_model_prop := chain_model_prop prop w_prop (n + k)
      by_cases (r 𝕏.α (chain prop w_prop (n + k)).fst).isBox
      case pos box =>
        have chain_model_prop := by simpa [box] using chain_model_prop
        exfalso
        exact h chain_model_prop
      case neg nbox =>
        have chain_model_prop := by simpa [nbox] using chain_model_prop
        exact chain_model_prop
  have g2 : ∀ m, ¬ (r 𝕏.α (chain prop w_prop (n + m)).fst).isBox := by
    intro m con
    have eq1 := g1 m
    have eq2 := g1 (m + 1)
    rw [eq1] at eq2
    have chain_model_prop := chain_model_prop prop w_prop (n + m)
    have chain_model_prop := by simpa [con] using chain_model_prop
    rw [eq2, add_assoc] at chain_model_prop
    apply (instModelIsIrref M).irrefl _ chain_model_prop
  have ⟨k, k_prop⟩ :=
    inf_path_has_inf_boxes (fun n ↦ (chain prop w_prop n).1) (chain_proof_prop prop w_prop) n
  apply g2 k k_prop

/-- Progressing subchain of an eventually increasing chain. -/
noncomputable def incChainEventualIncChain {β}
  {Q : β → β → Prop}
  {g : ℕ → β}
  (Q_prop : ∀ n, ∃ m, Q (g n) (g m))
  (n : ℕ) : {b : β // ∃ n, b = g n} :=
  match n with
   | 0 => ⟨g (Q_prop 0).choose, by simp⟩
   | n + 1 =>
      match incChainEventualIncChain Q_prop n with
        | ⟨ih, ih_prop⟩ => ⟨g (Q_prop ih_prop.choose).choose, by simp⟩

/-- An eventually progressing chain has an progressing subchain. -/
lemma incChainEventualIncChain_prop {β}
  {Q : β → β → Prop} {g : ℕ → β}
  (Q_prop : ∀ n, ∃ m, Q (g n) (g m)) :
  ∀ n, Q (incChainEventualIncChain Q_prop n).1
         (incChainEventualIncChain Q_prop (n + 1)).1
   := by
    intro n
    conv =>
      congr
      · skip
      · unfold incChainEventualIncChain
    rcases incChainEventualIncChain Q_prop n with ⟨ih, ih_prop⟩
    simp only
    have := (Q_prop ih_prop.choose).choose_spec
    convert this
    · exact ih_prop.choose_spec

/-- Soundness theorem for the GL-proof system. -/
theorem soundness (Γ : Sequent) : ⊢ Γ → ⊨ Γ := by
  intro mp
  have ⟨𝕏, x, prop⟩ := mp
  by_contra h
  simp only [Sequent.isValid, not_forall] at h
  have ⟨W, M, w, w_prop⟩ := h
  apply (wellFounded_iff_isEmpty_descending_chain.1 M.con_wf).false
  use fun k ↦ (@incChainEventualIncChain _ M.R (fun n ↦ (chain prop w_prop n).2.1)
    (by
      intro n
      have ⟨m, m_prop⟩ := has_children_of_chain_model prop w_prop n
      use n + m) k).1
  exact fun k ↦ @incChainEventualIncChain_prop _ M.R (fun n ↦ (chain prop w_prop n).2.1)
    (by
      intro n
      have ⟨m, m_prop⟩ := has_children_of_chain_model prop w_prop n
      use n + m) k
end Lean4GlCoalgebras
