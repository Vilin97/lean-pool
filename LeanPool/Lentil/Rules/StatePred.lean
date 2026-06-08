/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.Rules.WF
import LeanPool.Lentil.Tactics.FiniteWindow

/-! Theorems specialized for state predicates.
    Their premises are typically pure Lean propositions involving
    states before/after an action, instead of being in the form of
    `|-tla-`. -/

open Classical

namespace TLA

section state_pred_specialized

variable {σ : Type u}

theorem state_preds_and (p q : σ → Prop) : (⌜ p ⌝ ∧ ⌜ q ⌝) =tla= ⌜ λ s => p s ∧ q s ⌝ := by
  funext e; tlaNontemporalSimp

theorem init_invariant {init : σ → Prop} {next : action σ} {inv : σ → Prop}
    (hinit : ∀ s, init s → inv s)
    (hnext : ∀ s s', next s s' → inv s → inv s') :
  (⌜ init ⌝ ∧ □ ⟨next⟩) |-tla- (□ ⌜ inv ⌝) := by
  have hstep : (⌜ inv ⌝ ∧ ⟨next⟩) |-tla- (◯ ⌜ inv ⌝) := by
    tlaFiniteWindow
    aesop
  rw (occs := .pos [2]) [always_induction]
  rw [and_pred_implies_split]; apply And.intro
  · intro e ⟨hinit', _⟩
    exact hinit _ hinit'
  · intro e ⟨_, hnext'⟩ k hinv
    exact hstep (e.drop k) ⟨hinv, hnext' k⟩
/-
/-- `wf1` with `p`, `q`, `init` and `inv` being state predicates. -/
theorem wf1' (p q init inv : σ → Prop) (next a : action σ)
  (hpuntilq : ∀ s s', p s → next s s' → p s' ∨ q s')
  (haq : ∀ s s', p s → next s s' → a s s' → q s')
  (henable : ∀ s, inv s → p s → enabled a s ∨ q s)
  (hinit_inv : ∀ s, init s → inv s)
  (hnext_inv : ∀ s s', next s s' → inv s → inv s') :
  (⌜ init ⌝ ∧ □ ⟨next⟩ ∧ 𝒲ℱ a) |-tla- (⌜ p ⌝ ↝ ⌜ q ⌝) := by
  have hinv := init_invariant hinit_inv hnext_inv
  apply wf1 (statePred p) (statePred q) (statePred init) (statePred inv) <;> tlaUnfoldSimp <;> aesop
-/

end state_pred_specialized

end TLA
