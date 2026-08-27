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

/-- Provability is monotone in the set of hypotheses. -/
private theorem Provable.mono {Γ Δ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓΔ : Γ ⊆ Δ) (h : Provable Γ φ) : Provable Δ φ := by
  induction h with
  | hyp hφ => exact .hyp (hΓΔ hφ)
  | taut hp => exact .taut hp
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
  | exQuant hfree => exact .exQuant hfree
  | exGen _ hfree ih => exact .exGen ih hfree
  | propBot => exact .propBot
  | propOr => exact .propOr
  | propEx hfree => exact .propEx hfree
  | framing _ ih => exact .framing ih
  | existence => exact .existence
  | singleton C₁ C₂ => exact .singleton C₁ C₂

/-- Every theorem of the empty theory is available under arbitrary hypotheses. -/
private theorem Provable.weaken_empty {Γ : Set (Pattern S Var)}
    {φ : Pattern S Var} (h : Provable (∅ : Set (Pattern S Var)) φ) :
    Provable Γ φ :=
  h.mono (by simp)

/-- `⊤` is derivable in every theory. -/
private theorem provable_top (Γ : Set (Pattern S Var)) :
    Provable Γ (Pattern.tp : Pattern S Var) := by
  let p : PForm := .imp .bot .bot
  let θ : Nat → Pattern S Var := fun _ => .bot
  have hp : p.Taut := by
    intro v
    rfl
  exact Provable.taut (p := p) (θ := θ) hp

/-- Derived conjunction introduction. -/
private theorem Provable.and_intro {Γ : Set (Pattern S Var)}
    {a b : Pattern S Var} (ha : Provable Γ a) (hb : Provable Γ b) :
    Provable Γ (Pattern.and a b) := by
  let p : PForm :=
    .imp (.atom 0)
      (.imp (.atom 1)
        (.imp (.imp (.atom 0) (.imp (.atom 1) .bot)) .bot))
  let θ : Nat → Pattern S Var := fun n => if n = 0 then a else b
  have hp : p.Taut := by
    intro v
    cases h₀ : v 0 <;> cases h₁ : v 1 <;> simp [p, PForm.eval, h₀, h₁]
  have ht : Provable Γ (.imp a (.imp b (Pattern.and a b))) := by
    simpa [p, θ, PForm.subst, Pattern.and, Pattern.nt] using
      (Provable.taut (Γ := Γ) (p := p) (θ := θ) hp)
  exact Provable.mp hb (Provable.mp ha ht)

/-- Introduce the finite conjunction of a list of derivable patterns. -/
private theorem provable_conj {Γ : Set (Pattern S Var)}
    (l : List (Pattern S Var)) (hl : ∀ δ ∈ l, Provable Γ δ) :
    Provable Γ (conj l) := by
  induction l with
  | nil => exact provable_top Γ
  | cons δ l ih =>
      exact Provable.and_intro (hl δ (by simp))
        (ih (by
          intro ψ hψ
          exact hl ψ (by simp [hψ])))

/-- **Theorem 14 (proof-theoretic localization).**  `Γ ⊢ φ ⟺ Δ_Γ ⊨loc φ`. -/
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

/-- **Corollary 15 (global completeness).**  `Γ ⊨ φ ⟺ Γ ⊢ φ`.

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
