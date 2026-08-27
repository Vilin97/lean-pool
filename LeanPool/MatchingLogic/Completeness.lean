/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Theorem 14 and Corollary 15 — arXiv:2608.13306v1, Sections 4 and 5.

Corollary 15 is the paper's main positive result and the object of its
mechanization challenge. Entry point (ii) is Corollary 15 with (L) and (S)
assumed; entry point (iii) discharges (L) as well.

(L) and (S) are `Prop` hypotheses of these theorems, never Lean axioms, so the
dependence stays visible in the statement and `#print axioms` stays meaningful.

Statements pinned before any proof was attempted.
-/
import LeanPool.MatchingLogic.ProofSystem

/-!
# MatchingLogic.Completeness
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

/-! ### Theorem 14 and Corollary 15 -/

/-- **Theorem 14 (proof-theoretic localization).**  `Γ ⊢ φ ↔ Δ_Γ ⊨loc φ`. -/
theorem proof_theoretic_localization
    (hL : StrongLocalCompleteness S Var) (hS : Soundness S Var)
    {Γ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓ : ∀ γ ∈ Γ, Closed γ) (hφ : Closed φ) :
    Provable Γ φ ↔ LocalCons (localize Γ) φ := by
  constructor
  · intro hprov
    exact (semantic_localization hΓ hφ).mp (hS Γ φ hprov)
  · intro hlocal
    obtain ⟨l, hl, himp⟩ := hL (localize Γ) φ hlocal
    have hconj : Provable Γ (conj l) := by
      apply provable_conj l
      intro δ hδ
      obtain ⟨γ, hγ, p, rfl⟩ := hl δ hδ
      exact necessitation (Provable.hyp hγ) p
    exact Provable.mp hconj himp.weaken_empty

/-- **Corollary 15 (one-sorted global completeness).**  `Γ ⊨ φ ↔ Γ ⊢ φ`.

This is the paper's main positive result, and entry point (ii) of its
mechanization challenge: Corollary 15 with (L) and (S) assumed. -/
theorem global_completeness
    (hL : StrongLocalCompleteness S Var) (hS : Soundness S Var)
    {Γ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓ : ∀ γ ∈ Γ, Closed γ) (hφ : Closed φ) :
    GlobalCons Γ φ ↔ Provable Γ φ := by
  exact (semantic_localization hΓ hφ).trans
    (proof_theoretic_localization hL hS hΓ hφ).symm


end MatchingLogic
