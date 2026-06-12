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
import LeanPool.Lean4GlCoalgebras.Split.Proof
import LeanPool.Lean4GlCoalgebras.Split.CutProof

/-! ## Soundness of GL-split proof system. -/

namespace Lean4GlCoalgebras

namespace ExtSkip

-- `chain` performs a large recursive case split over all split proof rules.
open Classical in
/-- Helper for soundness, Given a proof of `Γ` and a countermodel of `Γ`, find a path in the proof
    and the model -/
noncomputable def chain
  {𝕏 : Proof}
  {x : 𝕏.X}
  {Γ : SplitSequent}
  (prop : f (r 𝕏.α x) = Γ)
  {W : Type}
  {M : Model W}
  {w : W}
  (w_prop : ¬evaluateSSeq (M, w) Γ)
  (n : Nat) : (y : 𝕏.X) × {u : W // ¬ evaluateSSeq ⟨M, u⟩ (f (r 𝕏.α y))}
    := match n with
       | 0 => ⟨x, ⟨w, by simp_all⟩⟩
       | n + 1 =>
        match chain prop w_prop n with
        | ⟨x_ih, w_ih, w_ih_prop⟩ =>
        match r_def : r 𝕏.α x_ih with
        | .skp Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
            have h : ¬evaluateSSeq (M, w_ih) (f (r 𝕏.α y)) := by
              have 𝕏h_x_ih := 𝕏.step x_ih
              have 𝕏h_x_ih := by simpa [r_def, p_def, -Finset.union_singleton] using 𝕏h_x_ih
              convert w_ih_prop using 2
              rw [𝕏h_x_ih, r_def]
              ⟨y, w_ih, h⟩
          | [] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | y :: z :: l => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
        | .cutₗ Δ φ => match p_def : p 𝕏.α x_ih with
          | [y,z] =>
            if w_ih_nφ : ¬evaluate (M, w_ih) φ
            then
              ⟨y, w_ih, by
                have := 𝕏.step x_ih
                have this := by
                  simpa [r_def, p_def, -Finset.union_singleton, fₙ_alternate] using this
                suffices hseq : ∀ χ, Sum.inr χ ∈ Δ → ¬evaluate (M, w_ih) χ by
                  simpa [evaluateSSeq, this.1, w_ih_nφ] using hseq
                intro χ χ_in con
                apply w_ih_prop
                exact ⟨Sum.inr χ, r_def ▸ χ_in, con⟩
              ⟩
            else
              ⟨z, w_ih, by
                have w_ih_nnφ : ¬evaluate (M, w_ih) (~φ) := by
                  simp [evaluate_neg]
                  tauto
                have := 𝕏.step x_ih
                have this := by simpa [r_def, p_def, -Finset.union_singleton] using this
                suffices hseq : ∀ χ, Sum.inl χ ∈ Δ → ¬evaluate (M, w_ih) χ by
                  simpa [evaluateSSeq, this.2, w_ih_nnφ, fₙ_alternate] using hseq
                intro χ χ_in con
                apply w_ih_prop
                exact ⟨Sum.inl χ, r_def ▸ χ_in, con⟩
              ⟩
          | [] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | [y] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | x::y::z::l => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
        | .cutᵣ Δ φ => match p_def : p 𝕏.α x_ih with
          | [y,z] =>
            if w_ih_nφ : ¬evaluate (M, w_ih) φ
            then
              ⟨y, w_ih, by
                have := 𝕏.step x_ih
                have this := by
                  simpa [r_def, p_def, -Finset.union_singleton, fₙ_alternate] using this
                suffices hseq : ∀ χ, Sum.inl χ ∈ Δ → ¬evaluate (M, w_ih) χ by
                  simpa [evaluateSSeq, this.1, w_ih_nφ] using hseq
                intro χ χ_in con
                apply w_ih_prop
                exact ⟨Sum.inl χ, r_def ▸ χ_in, con⟩
              ⟩
            else
              ⟨z, w_ih, by
                have w_ih_nnφ : ¬evaluate (M, w_ih) (~φ) := by
                  simp [evaluate_neg]
                  tauto
                have := 𝕏.step x_ih
                have this := by simpa [r_def, p_def, -Finset.union_singleton] using this
                suffices hseq : ∀ χ, Sum.inr χ ∈ Δ → ¬evaluate (M, w_ih) χ by
                  simpa [evaluateSSeq, this.2, w_ih_nnφ, fₙ_alternate] using hseq
                intro χ χ_in con
                apply w_ih_prop
                exact ⟨Sum.inr χ, r_def ▸ χ_in, con⟩
              ⟩
          | [] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | [y] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | x::y::z::l => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
        | .wkₗ Δ φ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
            have h : ¬evaluateSSeq (M, w_ih) (f (r 𝕏.α y)) := by
              have := 𝕏.step x_ih
              have this := by simpa [r_def, p_def, -Finset.union_singleton, fₙ_alternate] using this
              have w_ih_prop := by simpa [r_def, f] using w_ih_prop
              simp [this]
              tauto
            ⟨y, w_ih, h⟩
          | [] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | x::y::l => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
        | .wkᵣ Δ φ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
            have h : ¬evaluateSSeq (M, w_ih) (f (r 𝕏.α y)) := by
              have := 𝕏.step x_ih
              have this := by simpa [r_def, p_def, -Finset.union_singleton, fₙ_alternate] using this
              have w_ih_prop := by simpa [r_def, f] using w_ih_prop
              simp [this]
              tauto
            ⟨y, w_ih, h⟩
          | [] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | x::y::l => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
        | .topₗ Δ in_Δ => False.elim (by
            have hseq : (∀ χ, Sum.inl χ ∈ Δ → ¬evaluate (M, w_ih) χ) ∧
                ∀ χ, Sum.inr χ ∈ Δ → ¬evaluate (M, w_ih) χ := by
              simpa [r_def, f] using w_ih_prop
            have := hseq.1 ⊤ in_Δ
            simp_all)
        | .topᵣ Δ in_Δ => False.elim (by
            have hseq : (∀ χ, Sum.inl χ ∈ Δ → ¬evaluate (M, w_ih) χ) ∧
                ∀ χ, Sum.inr χ ∈ Δ → ¬evaluate (M, w_ih) χ := by
              simpa [r_def, f] using w_ih_prop
            have := hseq.2 ⊤ in_Δ
            simp_all)
        | .axₗₗ Δ n in_Δ =>
          False.elim (by
            by_cases evaluate ⟨M, w_ih⟩ (at n)
            case pos w_n =>
              have w_ih_prop := by simpa [r_def, f] using w_ih_prop
              have := w_ih_prop.1 (at n) in_Δ.1
              simp_all
            case neg not_w_n =>
              have w_ih_prop := by simpa [r_def, f] using w_ih_prop
              have := w_ih_prop.1 (na n) in_Δ.2
              simp_all)
        | .axₗᵣ Δ n in_Δ =>
          False.elim (by
            by_cases evaluate ⟨M, w_ih⟩ (at n)
            case pos w_n =>
              have w_ih_prop := by simpa [r_def, f] using w_ih_prop
              have := w_ih_prop.1 (at n) in_Δ.1
              simp_all
            case neg not_w_n =>
              have w_ih_prop := by simpa [r_def, f] using w_ih_prop
              have := w_ih_prop.2 (na n) in_Δ.2
              simp_all)
        | .axᵣₗ Δ n in_Δ =>
          False.elim (by
            by_cases evaluate ⟨M, w_ih⟩ (at n)
            case pos w_n =>
              have w_ih_prop := by simpa [r_def, f] using w_ih_prop
              have := w_ih_prop.2 (at n) in_Δ.1
              simp_all
            case neg not_w_n =>
              have w_ih_prop := by simpa [r_def, f] using w_ih_prop
              have := w_ih_prop.1 (na n) in_Δ.2
              simp_all)
        | .axᵣᵣ Δ n in_Δ =>
          False.elim (by
            by_cases evaluate ⟨M, w_ih⟩ (at n)
            case pos w_n =>
              have w_ih_prop := by simpa [r_def, f] using w_ih_prop
              have := w_ih_prop.2 (at n) in_Δ.1
              simp_all
            case neg not_w_n =>
              have w_ih_prop := by simpa [r_def, f] using w_ih_prop
              have := w_ih_prop.2 (na n) in_Δ.2
              simp_all)
        | .andₗ Δ φ₁ φ₂ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y,z] =>
              have := not_and_or.1 <| fun x ↦
                (not_exists.1 w_ih_prop) (Sum.inl (φ₁ & φ₂)) ⟨(r_def ▸ in_Δ), x⟩
            if w_ih_nφ₁ : ¬evaluate (M, w_ih) φ₁
            then
              ⟨y, w_ih, by
                have := 𝕏.step x_ih
                have this := by simpa [r_def, p_def, -Finset.union_singleton] using this
                suffices hseq :
                    (∀ χ, Sum.inl χ ∈ Δ → χ ≠ (φ₁ & φ₂) → ¬evaluate (M, w_ih) χ) ∧
                      ∀ χ, Sum.inr χ ∈ Δ → ¬evaluate (M, w_ih) χ by
                  simpa [evaluateSSeq, this.1, w_ih_nφ₁, fₙ_alternate] using hseq
                constructor
                · intro χ χ_in χ_not con
                  apply w_ih_prop
                  exact ⟨Sum.inl χ, r_def ▸ χ_in, con⟩
                · intro χ χ_in con
                  apply w_ih_prop
                  exact ⟨Sum.inr χ, r_def ▸ χ_in, con⟩
              ⟩
            else
              ⟨z, w_ih, by
                have w_ih_nφ₂ : ¬evaluate (M, w_ih) φ₂ := by simp_all
                have := 𝕏.step x_ih
                have this := by simpa [r_def, p_def, -Finset.union_singleton] using this
                suffices hseq :
                    (∀ χ, Sum.inl χ ∈ Δ → χ ≠ (φ₁ & φ₂) → ¬evaluate (M, w_ih) χ) ∧
                      ∀ χ, Sum.inr χ ∈ Δ → ¬evaluate (M, w_ih) χ by
                  simpa [evaluateSSeq, this.2, w_ih_nφ₂, fₙ_alternate] using hseq
                constructor
                · intro χ χ_in χ_not con
                  apply w_ih_prop
                  exact ⟨Sum.inl χ, r_def ▸ χ_in, con⟩
                · intro χ χ_in con
                  apply w_ih_prop
                  exact ⟨Sum.inr χ, r_def ▸ χ_in, con⟩
              ⟩
          | [] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | [y] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | x::y::z::l => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
        | .andᵣ Δ φ₁ φ₂ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y,z] =>
              have := not_and_or.1 <| fun x ↦
                (not_exists.1 w_ih_prop) (Sum.inr (φ₁ & φ₂)) ⟨(r_def ▸ in_Δ), x⟩
            if w_ih_nφ₁ : ¬evaluate (M, w_ih) φ₁
            then
              ⟨y, w_ih, by
                have := 𝕏.step x_ih
                have this := by simpa [r_def, p_def, -Finset.union_singleton] using this
                suffices hseq :
                    (∀ χ, Sum.inl χ ∈ Δ → ¬evaluate (M, w_ih) χ) ∧
                      ∀ χ, Sum.inr χ ∈ Δ → χ ≠ (φ₁ & φ₂) → ¬evaluate (M, w_ih) χ by
                  simpa [evaluateSSeq, this.1, w_ih_nφ₁, fₙ_alternate] using hseq
                constructor
                · intro χ χ_in con
                  apply w_ih_prop
                  exact ⟨Sum.inl χ, r_def ▸ χ_in, con⟩
                · intro χ χ_in _ con
                  apply w_ih_prop
                  exact ⟨Sum.inr χ, r_def ▸ χ_in, con⟩
              ⟩
            else
              ⟨z, w_ih, by
                have w_ih_nφ₂ : ¬evaluate (M, w_ih) φ₂ := by simp_all
                have := 𝕏.step x_ih
                have this := by simpa [r_def, p_def, -Finset.union_singleton] using this
                suffices hseq :
                    (∀ χ, Sum.inl χ ∈ Δ → ¬evaluate (M, w_ih) χ) ∧
                      ∀ χ, Sum.inr χ ∈ Δ → χ ≠ (φ₁ & φ₂) → ¬evaluate (M, w_ih) χ by
                  simpa [evaluateSSeq, this.2, w_ih_nφ₂, fₙ_alternate] using hseq
                constructor
                · intro χ χ_in con
                  apply w_ih_prop
                  exact ⟨Sum.inl χ, r_def ▸ χ_in, con⟩
                · intro χ χ_in _ con
                  apply w_ih_prop
                  exact ⟨Sum.inr χ, r_def ▸ χ_in, con⟩
              ⟩
          | [] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | [y] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | x::y::z::l => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
        | .orₗ Δ φ₁ φ₂ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
              have := not_or.1 <| fun x ↦
                (not_exists.1 w_ih_prop) (Sum.inl (φ₁ v φ₂)) ⟨(r_def ▸ in_Δ), x⟩
            have h : ¬evaluateSSeq (M, w_ih) (f (r 𝕏.α y)) := by
              have 𝕏h_x_ih := 𝕏.step x_ih
              have 𝕏h_x_ih := by simpa [r_def, p_def, -Finset.union_singleton] using 𝕏h_x_ih
              suffices hseq :
                  (∀ χ, Sum.inl χ ∈ Δ → χ ≠ (φ₁ v φ₂) → ¬evaluate (M, w_ih) χ) ∧
                    ∀ χ, Sum.inr χ ∈ Δ → ¬evaluate (M, w_ih) χ by
                simpa [evaluateSSeq, 𝕏h_x_ih, fₙ_alternate, this] using hseq
              constructor
              · intro χ χ_in _ con
                apply w_ih_prop
                exact ⟨Sum.inl χ, r_def ▸ χ_in, con⟩
              · intro χ χ_in con
                apply w_ih_prop
                exact ⟨Sum.inr χ, r_def ▸ χ_in, con⟩
              ⟨y, w_ih, h⟩
          | [] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | x::y::l => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
        | .orᵣ Δ φ₁ φ₂ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
              have := not_or.1 <| fun x ↦
                (not_exists.1 w_ih_prop) (Sum.inr (φ₁ v φ₂)) ⟨(r_def ▸ in_Δ), x⟩
            have h : ¬evaluateSSeq (M, w_ih) (f (r 𝕏.α y)) := by
              have 𝕏h_x_ih := 𝕏.step x_ih
              have 𝕏h_x_ih := by simpa [r_def, p_def, -Finset.union_singleton] using 𝕏h_x_ih
              suffices hseq :
                  (∀ χ, Sum.inl χ ∈ Δ → ¬evaluate (M, w_ih) χ) ∧
                    ∀ χ, Sum.inr χ ∈ Δ → χ ≠ (φ₁ v φ₂) → ¬evaluate (M, w_ih) χ by
                simpa [evaluateSSeq, 𝕏h_x_ih, fₙ_alternate, this] using hseq
              constructor
              · intro χ χ_in con
                apply w_ih_prop
                exact ⟨Sum.inl χ, r_def ▸ χ_in, con⟩
              · intro χ χ_in _ con
                apply w_ih_prop
                exact ⟨Sum.inr χ, r_def ▸ χ_in, con⟩
              ⟨y, w_ih, h⟩
          | [] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | x::y::l => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
        | .boxₗ Δ φ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
                have := not_forall.1 <| fun x ↦
                  (not_exists.1 w_ih_prop) (Sum.inl (□ φ)) ⟨(r_def ▸ in_Δ), x⟩
              let w_next := this.choose
              have w_next_prop := Classical.not_imp.1 this.choose_spec
              have h : ¬evaluateSSeq (M, w_next) (f (r 𝕏.α y)) := by
                have 𝕏h_x_ih := 𝕏.step x_ih
                have 𝕏h_x_ih := by simpa [r_def, p_def, -Finset.union_singleton] using 𝕏h_x_ih
                suffices hseq : ¬evaluate (M, w_next) φ ∧
                    ((∀ χ, Sum.inl χ ∈ (Δ \ {Sum.inl (□ φ)}).D →
                        ¬evaluate (M, w_next) χ) ∧
                      ∀ χ, Sum.inr χ ∈ (Δ \ {Sum.inl (□ φ)}).D →
                        ¬evaluate (M, w_next) χ) by
                  simpa [evaluateSSeq, 𝕏h_x_ih, fₙ_alternate] using hseq
                refine ⟨?_, ⟨?_, ?_⟩⟩
                · exact w_next_prop.2
                · suffices hD :
                      ∀ χ,
                        ((Sum.inl χ ∈ Δ ∧ χ ≠ (□ φ)) ∧
                            SplitFormula.isDiamond (Sum.inl χ) = true ∨
                          Sum.inl (◇ χ) ∈ Δ) →
                          ¬evaluate (M, w_next) χ by
                    simpa [SplitSequent.D] using hD
                  have w_ih_prop := by simpa [evaluateSSeq, r_def, f] using w_ih_prop
                  intro χ χ_in con
                  rcases χ_in with ⟨⟨χ_in, χ_not_box_φ⟩, χ_di⟩ | diχ_Δ
                  · apply w_ih_prop.1 _ χ_in
                    cases χ <;> simp [SplitFormula.isDiamond] at χ_di
                    case diamond χ' =>
                      have ⟨u, w_next_u, u_χ'⟩ := con
                      exact ⟨u, M.trans w_next_prop.1 w_next_u, u_χ'⟩
                  · exact w_ih_prop.1 _ diχ_Δ ⟨w_next, w_next_prop.1, con⟩
                · suffices hD :
                      ∀ χ,
                        (Sum.inr χ ∈ Δ ∧ SplitFormula.isDiamond (Sum.inr χ) = true ∨
                          Sum.inr (◇ χ) ∈ Δ) →
                          ¬evaluate (M, w_next) χ by
                    simpa [SplitSequent.D] using hD
                  have w_ih_prop := by simpa [evaluateSSeq, r_def, f] using w_ih_prop
                  intro χ χ_in con
                  rcases χ_in with ⟨χ_in, χ_di⟩ | diχ_Δ
                  · apply w_ih_prop.2 _ χ_in
                    cases χ <;> simp [SplitFormula.isDiamond] at χ_di
                    case diamond χ' =>
                      have ⟨u, w_next_u, u_χ'⟩ := con
                      exact ⟨u, M.trans w_next_prop.1 w_next_u, u_χ'⟩
                  · exact w_ih_prop.2 _ diχ_Δ ⟨w_next, w_next_prop.1, con⟩
              ⟨y, w_next, h⟩
          | [] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
          | x::y::l => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
        | .boxᵣ Δ φ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
                have := not_forall.1 <| fun x ↦
                  (not_exists.1 w_ih_prop) (Sum.inr (□ φ)) ⟨(r_def ▸ in_Δ), x⟩
              let w_next := this.choose
              have w_next_prop := Classical.not_imp.1 this.choose_spec
              have h : ¬evaluateSSeq (M, w_next) (f (r 𝕏.α y)) := by
                have 𝕏h_x_ih := 𝕏.step x_ih
                have 𝕏h_x_ih := by simpa [r_def, p_def, -Finset.union_singleton] using 𝕏h_x_ih
                suffices hseq : ¬evaluate (M, w_next) φ ∧
                    ((∀ χ, Sum.inl χ ∈ (Δ \ {Sum.inr (□ φ)}).D →
                        ¬evaluate (M, w_next) χ) ∧
                      ∀ χ, Sum.inr χ ∈ (Δ \ {Sum.inr (□ φ)}).D →
                        ¬evaluate (M, w_next) χ) by
                  simpa [evaluateSSeq, 𝕏h_x_ih, fₙ_alternate] using hseq
                refine ⟨?_, ⟨?_, ?_⟩⟩
                · exact w_next_prop.2
                · suffices hD :
                      ∀ χ,
                        (Sum.inl χ ∈ Δ ∧ SplitFormula.isDiamond (Sum.inl χ) = true ∨
                          Sum.inl (◇ χ) ∈ Δ) →
                          ¬evaluate (M, w_next) χ by
                    simpa [SplitSequent.D] using hD
                  have w_ih_prop := by simpa [evaluateSSeq, r_def, f] using w_ih_prop
                  intro χ χ_in con
                  rcases χ_in with ⟨χ_in, χ_di⟩ | diχ_Δ
                  · apply w_ih_prop.1 _ χ_in
                    cases χ <;> simp [SplitFormula.isDiamond] at χ_di
                    case diamond χ' =>
                      have ⟨u, w_next_u, u_χ'⟩ := con
                      exact ⟨u, M.trans w_next_prop.1 w_next_u, u_χ'⟩
                  · exact w_ih_prop.1 _ diχ_Δ ⟨w_next, w_next_prop.1, con⟩
                · suffices hD :
                      ∀ χ,
                        ((Sum.inr χ ∈ Δ ∧ χ ≠ (□ φ)) ∧
                            SplitFormula.isDiamond (Sum.inr χ) = true ∨
                          Sum.inr (◇ χ) ∈ Δ) →
                          ¬evaluate (M, w_next) χ by
                    simpa [SplitSequent.D] using hD
                  have w_ih_prop := by simpa [evaluateSSeq, r_def, f] using w_ih_prop
                  intro χ χ_in con
                  rcases χ_in with ⟨⟨χ_in, χ_not_box_φ⟩, χ_di⟩ | diχ_Δ
                  · apply w_ih_prop.2 _ χ_in
                    cases χ <;> simp [SplitFormula.isDiamond] at χ_di
                    case diamond χ' =>
                      have ⟨u, w_next_u, u_χ'⟩ := con
                      exact ⟨u, M.trans w_next_prop.1 w_next_u, u_χ'⟩
                  · exact w_ih_prop.2 _ diχ_Δ ⟨w_next, w_next_prop.1, con⟩
              ⟨y, w_next, h⟩
            | [] => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)
            | x::y::l => False.elim (by have := 𝕏.step x_ih; simp [r_def, p_def] at this)

/-- The left projection of `chain` is a chain in the proof. -/
lemma chain_proof_prop
  {𝕏 : Proof}
  {x : 𝕏.X}
  {Γ : SplitSequent}
  (prop : f (r 𝕏.α x) = Γ)
  {W : Type}
  {M : Model W}
  {w : W}
  (w_prop : ¬evaluateSSeq (M, w) Γ)
  : ∀ n, edge 𝕏.α (chain prop w_prop n).1 (chain prop w_prop (n + 1)).1 := by
    intro n
    conv =>
      congr
      · skip
      · skip
      · unfold chain
    rcases chain prop w_prop n with ⟨x_ih, w_ih, w_ih_prop⟩
    simp only
    split
    case h_1 Δ r_def =>
      split
      · rename_i y p_def
        simp [edge, p_def]
      · rename_i p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
      · rename_i y z ys p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
    case h_2 Δ φ r_def =>
      split
      · rename_i y z p_def
        by_cases h : ¬evaluate (M, w_ih) φ <;> simp [edge, p_def, h]
      · rename_i p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
      · rename_i y p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
      · rename_i x y z ys p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
    case h_3 Δ φ r_def =>
      split
      · rename_i y z p_def
        by_cases h : ¬evaluate (M, w_ih) φ <;> simp [edge, p_def, h]
      · rename_i p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
      · rename_i y p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
      · rename_i x y z ys p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
    case h_4 Δ φ in_Δ r_def =>
      split
      · rename_i y p_def
        simp [edge, p_def]
      · rename_i p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
      · rename_i y z ys p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
    case h_5 Δ φ in_Δ r_def =>
      split
      · rename_i y p_def
        simp [edge, p_def]
      · rename_i p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
      · rename_i y z ys p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
    case h_6 Δ in_Δ r_def =>
      exfalso
      apply w_ih_prop
      exact ⟨Sum.inl ⊤, by simpa [f, r_def] using in_Δ, by simp⟩
    case h_7 Δ in_Δ r_def =>
      exfalso
      apply w_ih_prop
      exact ⟨Sum.inr ⊤, by simpa [f, r_def] using in_Δ, by simp⟩
    case h_8 Δ i in_Δ r_def =>
      exfalso
      by_cases h : M.V w_ih i
      · apply w_ih_prop
        exact ⟨Sum.inl (at i), by simpa [f, r_def] using in_Δ.1, by simpa using h⟩
      · apply w_ih_prop
        exact ⟨Sum.inl (na i), by simpa [f, r_def] using in_Δ.2, by simpa using h⟩
    case h_9 Δ i in_Δ r_def =>
      exfalso
      by_cases h : M.V w_ih i
      · apply w_ih_prop
        exact ⟨Sum.inl (at i), by simpa [f, r_def] using in_Δ.1, by simpa using h⟩
      · apply w_ih_prop
        exact ⟨Sum.inr (na i), by simpa [f, r_def] using in_Δ.2, by simpa using h⟩
    case h_10 Δ i in_Δ r_def =>
      exfalso
      by_cases h : M.V w_ih i
      · apply w_ih_prop
        exact ⟨Sum.inr (at i), by simpa [f, r_def] using in_Δ.1, by simpa using h⟩
      · apply w_ih_prop
        exact ⟨Sum.inl (na i), by simpa [f, r_def] using in_Δ.2, by simpa using h⟩
    case h_11 Δ i in_Δ r_def =>
      exfalso
      by_cases h : M.V w_ih i
      · apply w_ih_prop
        exact ⟨Sum.inr (at i), by simpa [f, r_def] using in_Δ.1, by simpa using h⟩
      · apply w_ih_prop
        exact ⟨Sum.inr (na i), by simpa [f, r_def] using in_Δ.2, by simpa using h⟩
    case h_12 Δ φ ψ in_Δ r_def =>
      split
      · rename_i y z p_def
        by_cases h : ¬evaluate (M, w_ih) φ <;> simp [edge, p_def, h]
      · rename_i p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
      · rename_i y p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
      · rename_i x y z ys p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
    case h_13 Δ φ ψ in_Δ r_def =>
      split
      · rename_i y z p_def
        by_cases h : ¬evaluate (M, w_ih) φ <;> simp [edge, p_def, h]
      · rename_i p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
      · rename_i y p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
      · rename_i x y z ys p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
    case h_14 Δ φ ψ in_Δ r_def =>
      split
      · rename_i y p_def
        simp [edge, p_def]
      · rename_i p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
      · rename_i y z ys p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
    case h_15 Δ φ ψ in_Δ r_def =>
      split
      · rename_i y p_def
        simp [edge, p_def]
      · rename_i p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
      · rename_i y z ys p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
    case h_16 Δ φ in_Δ r_def =>
      split
      · rename_i y p_def
        simp [edge, p_def]
      · rename_i p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
      · rename_i y z ys p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
    case h_17 Δ φ in_Δ r_def =>
      split
      · rename_i y p_def
        simp [edge, p_def]
      · rename_i p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this
      · rename_i y z ys p_def
        exfalso
        have := 𝕏.step x_ih
        simp [r_def, p_def] at this

/-- The right projection of `chain` makes progress in the model on box nodes. -/
lemma chain_model_prop {𝕏 : Proof}
  {x : 𝕏.X}
  {Γ : SplitSequent}
  (prop : f (r 𝕏.α x) = Γ)
  {W : Type}
  {M : Model W}
  {w : W}
  (w_prop : ¬evaluateSSeq (M, w) Γ)
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
          · rw [chain] -- I think Subtype.val might be preventing from unfolding chain
    -- Splitting directly after this would recompute the recursive chain.
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
          · rw [chain] -- I think Subtype.val might be preventing from unfolding chain
    -- Splitting directly after this would recompute the recursive chain.
    rcases chain prop w_prop n with ⟨x_ih, w_ih, w_ih_prop⟩
    simp only [evaluateSSeq, Lean.Elab.WF.paramLet]
    split <;> intro box <;> try grind [RuleApp.isBox]
    case h_16 Δ φ in_Δ r_def =>
      simp only [RuleApp.isBox, r_def] at box ⊢
      split
      · exact (Classical.not_imp.1 (Classical.choose_spec
          (not_forall.1 (fun z ↦
            (not_exists.1 w_ih_prop) (Sum.inl (□ φ)) ⟨(r_def ▸ in_Δ), z⟩)))).1
      all_goals
        exfalso
        have step := 𝕏.step x_ih
        simp_all
    case h_17 Δ φ in_Δ r_def =>
      simp only [RuleApp.isBox, r_def] at box ⊢
      split
      · exact (Classical.not_imp.1 (Classical.choose_spec
          (not_forall.1 (fun z ↦
            (not_exists.1 w_ih_prop) (Sum.inr (□ φ)) ⟨(r_def ▸ in_Δ), z⟩)))).1
      all_goals
        exfalso
        have step := 𝕏.step x_ih
        simp_all

/-- The right projection of `chain` eventually progresses. -/
lemma has_children_of_chain_model {𝕏 : Proof}
  {x : 𝕏.X}
  {Γ : SplitSequent}
  (prop : f (r 𝕏.α x) = Γ)
  {W : Type}
  {M : Model W}
  {w : W}
  (w_prop : ¬evaluateSSeq (M, w) Γ) :
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
  have ⟨k, k_prop⟩ := 𝕏.path x
    ⟨(fun n ↦ (chain prop w_prop n).1),
      ⟨by simp [chain], chain_proof_prop prop w_prop⟩⟩ n
  exact g2 k k_prop

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
lemma inc_chain_eventual_inc_chain_prop {β}
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
    change Q ih (g (Q_prop ih_prop.choose).choose)
    have := (Q_prop ih_prop.choose).choose_spec
    convert this
    · exact ih_prop.choose_spec

/-- Soundness lemma for the GL-split proof system. -/
lemma soundness (Γ : SplitSequent) : SplitSequent.isTrue Γ → ⊨ Γ := by
  intro mp
  have ⟨𝕏, x, prop⟩ := mp
  by_contra h
  simp only [SplitSequent.isValid, not_forall] at h
  have ⟨W, M, w, w_prop⟩ := h
  apply (wellFounded_iff_isEmpty_descending_chain.1 M.con_wf).false
  use fun k ↦ (@incChainEventualIncChain _ M.R (fun n ↦ (chain prop w_prop n).2.1)
    (by
      intro n
      have ⟨m, m_prop⟩ := has_children_of_chain_model prop w_prop n
      use n + m) k).1
  exact fun k ↦ @inc_chain_eventual_inc_chain_prop _ M.R (fun n ↦ (chain prop w_prop n).2.1)
    (by
      intro n
      have ⟨m, m_prop⟩ := has_children_of_chain_model prop w_prop n
      use n + m) k

end ExtSkip

/-! ## Soundness of GL-split cut proof system.

This soundness lemma follows by converting any GL-split proof into a GL-split cut proof. -/

/-- Converts structure morphism for GL-split proof into one for GL-split cut proofs. -/
@[simp] def αConv (𝕏 : Split.Proof) : 𝕏.X → ExtSkip.T.obj 𝕏.X := fun x ↦
  match Split.r 𝕏.α x with
    | .topₗ Δ in_Δ => ⟨.topₗ Δ in_Δ, Split.p 𝕏.α x⟩
    | .topᵣ Δ in_Δ => ⟨.topᵣ Δ in_Δ, Split.p 𝕏.α x⟩
    | .axₗₗ Δ n in_Δ => ⟨.axₗₗ Δ n in_Δ, Split.p 𝕏.α x⟩
    | .axₗᵣ Δ n in_Δ => ⟨.axₗᵣ Δ n in_Δ, Split.p 𝕏.α x⟩
    | .axᵣₗ Δ n in_Δ => ⟨.axᵣₗ Δ n in_Δ, Split.p 𝕏.α x⟩
    | .axᵣᵣ Δ n in_Δ => ⟨.axᵣᵣ Δ n in_Δ, Split.p 𝕏.α x⟩
    | .andₗ Δ φ ψ in_Δ => ⟨.andₗ Δ φ ψ in_Δ, Split.p 𝕏.α x⟩
    | .andᵣ Δ φ ψ in_Δ => ⟨.andᵣ Δ φ ψ in_Δ, Split.p 𝕏.α x⟩
    | .orₗ Δ φ ψ in_Δ => ⟨.orₗ Δ φ ψ in_Δ, Split.p 𝕏.α x⟩
    | .orᵣ Δ φ ψ in_Δ => ⟨.orᵣ Δ φ ψ in_Δ, Split.p 𝕏.α x⟩
    | .boxₗ Δ φ in_Δ => ⟨.boxₗ Δ φ in_Δ, Split.p 𝕏.α x⟩
    | .boxᵣ Δ φ in_Δ => ⟨.boxᵣ Δ φ in_Δ, Split.p 𝕏.α x⟩

/-- If there is a GL-split proof of Γ then there is a GL-split cut proof of Γ. -/
lemma SplitProofIsExtSkipProof (Γ : SplitSequent) :
    (Split.SplitSequent.isTrue Γ) → (ExtSkip.SplitSequent.isTrue Γ) := by
  intro mp
  have ⟨𝕏, x, prop⟩ := mp
  have := 𝕏.X
  use {
    X := 𝕏.X
    α := αConv 𝕏
    step x := by
      have helper :
          ∀ x, ExtSkip.f (ExtSkip.r (αConv 𝕏) x) = Split.f (Split.r 𝕏.α x) := by
        intro x
        cases r_def : Split.r 𝕏.α x <;>
          simp_all only [αConv, ExtSkip.r, ExtSkip.f, Split.f]
      have := 𝕏.step x
      cases r_def : Split.r 𝕏.α x <;>
        simp_all only [αConv, ExtSkip.r, ExtSkip.p, Split.fₙ_alternate,
          ExtSkip.fₙ_alternate]
    path x := by
      have h : ∀ x, (ExtSkip.r (αConv 𝕏) x).isBox ↔ (Split.r 𝕏.α x).isBox := by
        intro x
        cases r_def : Split.r 𝕏.α x <;>
          simp_all only [αConv, ExtSkip.r, ExtSkip.RuleApp.isBox, Split.RuleApp.isBox]
      suffices hpath :
          ∀ (f : ℕ → 𝕏.X),
            f 0 = x →
            (∀ n, ExtSkip.edge (αConv 𝕏) (f n) (f (n + 1))) →
            ∀ n, ∃ m, (Split.r 𝕏.α (f (n + m))).isBox by
        simpa [h] using hpath
      intro f base step n
      apply Split.inf_path_has_inf_boxes f ?_ n
      convert step
      unfold ExtSkip.edge Split.edge αConv
      simp [ExtSkip.p]
      grind}
  use x
  simp [←prop]
  cases r_def : Split.r 𝕏.α x <;> simp_all only [αConv, ExtSkip.r, ExtSkip.f, Split.f]

namespace Split

/-- Soundness theorem for the GL-split cut proof system. -/
theorem soundness (Γ : SplitSequent) : SplitSequent.isTrue Γ → ⊨ Γ := by
  intro mp
  exact ExtSkip.soundness Γ (SplitProofIsExtSkipProof Γ mp)

end Split
end Lean4GlCoalgebras
