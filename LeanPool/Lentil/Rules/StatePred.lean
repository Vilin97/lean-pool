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

end state_pred_specialized

end TLA
