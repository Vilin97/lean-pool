/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2GevreyCalculus

@[expose] public section

/-! Pointwise factorial estimates suffice when one factor has compact
support. In particular polynomial factors need not be globally bounded. -/

noncomputable section

namespace EulerGevreyFunctions

open EulerGevrey EulerGevreyGeneratingDerivatives
open scoped ContDiff

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem product_bound_at (f g : E → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (R A B : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B) (x : E)
    (hb₁ : ∀ n, ‖iteratedFDeriv ℝ n f x‖ ≤ A*majorant R 0 n)
    (hb₂ : ∀ n, ‖iteratedFDeriv ℝ n g x‖ ≤ B*majorant R 0 n) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => f y*g y) x‖ ≤ (3*A*B)*majorant R 0 n := by
  have hp := sequence_product_majorant R A B hR hA hB 0 0
    (fun k => ‖iteratedFDeriv ℝ k f x‖) (fun k => ‖iteratedFDeriv ℝ k g x‖)
    (fun k => by simpa only [abs_norm] using hb₁ k)
    (fun k => by simpa only [abs_norm] using hb₂ k) n
  exact (norm_iteratedFDeriv_mul_le hf hg x (by simp)).trans
    ((le_abs_self _).trans (by simpa using hp))

theorem majorant_one_le (R : ℝ) (hR : 1 ≤ R) (n : ℕ) : 1 ≤ majorant R 0 n := by
  have hf : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
  simpa only [majorant,Nat.add_zero] using
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR) (by nlinarith : (1 : ℝ) ≤ (n.factorial : ℝ)^2)

theorem id_bound_on_ball (r R : ℝ) (hr : 1 ≤ r) (hR : 1 ≤ R)
    (x : E) (hx : ‖x‖ ≤ r) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (id : E → E) x‖ ≤ r*majorant R 0 n := by
  cases n with
  | zero => simpa only [norm_iteratedFDeriv_zero,id_eq,majorant,Nat.zero_add,
      pow_zero,Nat.factorial_zero,Nat.cast_one,one_pow,mul_one] using hx
  | succ n =>
    have hi := norm_iteratedFDeriv_id_le (n+1) (Nat.succ_pos _) x
    have hnorm : ‖iteratedFDeriv ℝ (n+1) (id : E → E) x‖ ≤ 1 := by
      split_ifs at hi <;> linarith
    exact hnorm.trans (one_le_mul_of_one_le_of_one_le hr (majorant_one_le R hR _))

theorem linear_bound_on_ball (L : E →L[ℝ] V) (r R : ℝ) (hr : 1 ≤ r) (hR : 1 ≤ R)
    (x : E) (hx : ‖x‖ ≤ r) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (L : E → V) x‖ ≤ (‖L‖*r)*majorant R 0 n := by
  have h := L.norm_iteratedFDeriv_comp_left (f := id) (x := x) contDiffAt_id (by simp : (n : ℕ∞ω) ≤
    ∞)
  exact h.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (id_bound_on_ball r R hr hR x hx n) (norm_nonneg L))

theorem compact_product_bound (f g : E → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (K : Set E) (hK : tsupport f ⊆ K) (R A B : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb₁ : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ A*majorant R 0 n)
    (hb₂ : ∀ x ∈ K, ∀ n, ‖iteratedFDeriv ℝ n g x‖ ≤ B*majorant R 0 n) :
    ∀ n x, ‖iteratedFDeriv ℝ n (fun y => f y*g y) x‖ ≤ (3*A*B)*majorant R 0 n := by
  intro n x
  by_cases hx : x ∈ K
  · exact product_bound_at f g hf hg R A B hR hA hB x (fun j => hb₁ j x) (hb₂ x hx) n
  · have hn : x ∉ tsupport (fun y => f y*g y) := fun h => hx (hK (tsupport_mul_subset_left h))
    have hz : iteratedFDeriv ℝ n (fun y => f y*g y) x=0 := by
      by_contra hh
      exact hn (support_iteratedFDeriv_subset n hh)
    rw [hz,norm_zero]
    exact mul_nonneg (by positivity) (majorant_nonneg R hR 0 n)

end EulerGevreyFunctions
