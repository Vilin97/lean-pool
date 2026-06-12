/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.Rules.Basic
import LeanPool.Lentil.Gadgets.TheoremDeriving
import LeanPool.Lentil.ProofMode.Tactics
import LeanPool.Lentil.ProofMode.Display

/-! Theorems about weak-fairness. -/

open Classical

namespace TLA

section wf

variable {σ : Type u}

section wf_def

variable {a : action σ}

theorem wf_as_leads_to : (𝒲ℱ a) =tla= (□ Enabled a ↝ ⟨a⟩) := rfl

theorem wf_alt1 : (𝒲ℱ a) =tla= □ ◇ ((¬ Enabled a) ∨ □ ◇ ⟨a⟩) := by
  funext e; unfold weakFairness; rw [implies_to_or]; simp [tlasimp]
  rw [← eventually_or]; (repeat rw [always_eventually_or_distrib]); simp [tlasimp]

theorem wf_alt1' : (𝒲ℱ a) =tla= □ ◇ ((¬ Enabled a) ∨ ⟨a⟩) := by
  rw [wf_alt1]; (repeat rw [always_eventually_or_distrib]); simp [tlasimp]

end wf_def

/--
A useful rule for proving `↝`. Compared with its original presentation in
the paper "The Temporal Logic of Actions", the following version contains
some changes to make it hopefully more practical.
-/
@[tla_derive]
theorem wf1 (p q : pred σ) (next a : action σ) :
  ((p ∧ ⟨next⟩ ⇒ ◯ p ∨ ◯ q) ∧
   (p ∧ ⟨next⟩ ∧ ⟨a⟩ ⇒ ◯ q) ∧
   (p ⇒ Enabled a ∨ q) ∧
   (□ ⟨next⟩ ∧ 𝒲ℱ a)) |-tla- (p ↝ q) := by
  rw [wf_alt1']
  intro e ⟨hpuntilq, haq, henable, hnext, hwf_alt⟩ k hp
  specialize hwf_alt k; rcases hwf_alt with ⟨k1, hwf_alt⟩
  -- know that: either `q` holds between `k` and `k + k1`, or `p` holds at `k1`
  -- use `henable` to know that if it is the latter case, then `q` must hold in the next step
  have htmp : (∃ k' ≤ k1, q <| e.drop (k + k')) ∨ (p <| e.drop (k + k1)) := by
    clear hwf_alt
    induction k1 with
    | zero => right; assumption
    | succ n ih => {
      rw [← Nat.add_assoc]
      rcases ih with ⟨k', hle, ih⟩ | ih
      · left; exists k'; constructor; omega; apply ih
      · specialize hpuntilq _ ⟨ih, (hnext _)⟩
        rcases hpuntilq with hq | hq <;> tlaUnfoldSimp'
        · right; apply hq
        · left; exists (n + 1); aesop
    }
  rcases htmp with ⟨k', _, hq⟩ | hq <;> tlaUnfoldSimp'
  · aesop
  · rcases hwf_alt with hq2 | hq2
    · specialize henable _ hq; aesop
    · exists (k1 + 1)
      specialize haq (k + k1) hq; rw [← Nat.add_assoc]; apply haq <;> aesop

/-- A (relatively) original presentation of the `wf1` rule. -/
theorem wf1_original (p q : pred σ) (next a : action σ) :
  ((p ∧ ⟨next⟩ ⇒ ◯ (p ∨ q)) ∧
   ((p ∧ ⟨next⟩ ∧ ⟨a⟩ ⇒ ◯ q)) ∧
   ((p ⇒ Enabled a))) |-tla- (□ ⟨next⟩ ∧ 𝒲ℱ a → p ↝ q) := by
  tla_start hpuntilq haq henable
  tla_rintro ⟨hnext, hfair⟩
  tla_apply wf1 (next := next) (a := a)
  tlaSplitAnds
  · rw [later_or]; tla_apply hpuntilq
  · tla_apply haq
  · intro e ⟨_, _, henable, _⟩ k hp
    exact Or.inl (henable k hp)
  · tla_apply hnext
  · tla_apply hfair

end wf

end TLA
