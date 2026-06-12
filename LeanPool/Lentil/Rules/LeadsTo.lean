/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import Lean
import LeanPool.Lentil.Rules.Basic
import LeanPool.Lentil.Gadgets.TheoremDeriving

/-! Theorems about the leads-to operator. -/

open Classical

namespace TLA

section leadsTo

variable {σ : Type u}

-- FIXME: any chance to make the following two lemmas more general
theorem leads_to_exists (Γ q : pred σ) (p : α → pred σ) :
  (∀ (x : α), (Γ) |-tla- ((p x) ↝ q)) ↔ (Γ) |-tla- ((tlaExists p) ↝ q) := by
  tlaUnfoldSimp; aesop

theorem leads_to_pure_pred_and (Γ p q : pred σ) (φ : Prop) :
  (φ → (Γ) |-tla- (p ↝ q)) ↔ (Γ) |-tla- (⌞ φ ⌟ ∧ p ↝ q) := by
  tlaUnfoldSimp; aesop

@[tla_derive]
theorem leads_to_conseq (p p' q q': pred σ) :
  |-tla- ((p' ⇒ p) → (q ⇒ q') → (p ↝ q) ⇒ (p' ↝ q')) := by
  tlaUnfoldSimp; intro e h1 h2 k h k' hh'
  specialize h _ (h1 _ hh'); rcases h with ⟨k1, h⟩; aesop

@[tla_derive]
theorem leads_to_trans (p q r : pred σ) :
  |-tla- ((p ↝ q) → (q ↝ r) → (p ↝ r)) := by
  tlaUnfoldSimp; intro e h1 h2 k hh
  specialize h1 _ hh; rcases h1 with ⟨k1, h1⟩
  specialize h2 _ h1; rcases h2 with ⟨k2, h2⟩
  exists (k1 + k2); rw [← Nat.add_assoc]; assumption

theorem leads_to_combine (Γ Γ' p1 q1 p2 q2 : pred σ)
  (h1 : (□ Γ ∧ Γ') |-tla- (p1 ↝ q1))
  (h2 : (□ Γ ∧ Γ') |-tla- (p2 ↝ q2))
  (h1' : (q1 ∧ □ Γ) |-tla- □ q1) (h2' : (q2 ∧ □ Γ) |-tla- □ q2) :
  (□ Γ ∧ Γ') |-tla- (p1 ∧ p2 ↝ q1 ∧ q2) := by
  -- a semantic proof
  tlaUnfoldSimp; intro e hΓ hΓ' k hp1 hp2
  specialize h1 _ hΓ hΓ' k hp1; rcases h1 with ⟨k1, h1⟩
  specialize h2 _ hΓ hΓ' k hp2; rcases h2 with ⟨k2, h2⟩
  exists k1 + k2
  specialize h1' _ h1 (by intro q; rw [exec.drop_drop]; apply hΓ) k2
  specialize h2' _ h2 (by intro q; rw [exec.drop_drop]; apply hΓ) k1
  simp [exec.drop_drop] at h1' h2'
  constructor; rw [← Nat.add_assoc]; assumption; rw [Nat.add_comm k1 k2, ← Nat.add_assoc]; assumption

@[tla_derive]
theorem leads_to_strengthen_lhs (p q inv : pred σ) :
  |-tla- (□ inv → (p ∧ inv ↝ q) → (p ↝ q)) := by
  tlaUnfoldSimp; aesop

end leadsTo

end TLA
