/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.NextStream

/-! Exact recursion identities for the selected stream increments. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem StreamIncrement.psi_zero_of_not_odd (m : ℕ) (k : ℤ) (x : Vec 2)
    (hk : ¬ Odd k) : psi β I.Λ m k x = 0 := by
  rcases Int.even_or_odd k with he | ho
  · rcases he with ⟨a, rfl⟩
    have h1 : (a + a) % 4 ≠ 1 := by omega
    have h3 : (a + a) % 4 ≠ 3 := by omega
    simp [psi, psi0, h1, h3]
  · exact (hk ho).elim

theorem StreamIncrement.tsum_eq_odd_subtype_of_even_zero (f : ℤ → ℝ)
    (hzero : ∀ k : ℤ, ¬ Odd k → f k = 0) :
    (∑' k : ℤ, f k) = ∑' k : {k : ℤ // Odd k}, f k.1 := by
  have hindicator : Set.indicator {k : ℤ | Odd k} f = f := by
    funext k
    by_cases hk : Odd k
    · simp [Set.indicator, hk]
    · simp [Set.indicator, hk, hzero k hk]
  calc
    (∑' k : ℤ, f k) = ∑' k : ℤ, Set.indicator {k : ℤ | Odd k} f k := by
      exact congrArg (fun g : ℤ → ℝ => ∑' k : ℤ, g k) hindicator.symm
    _ = ∑' k : {k : ℤ // Odd k}, f k.1 := (tsum_subtype _ _).symm

/-- The recursive increment of `Φ_m` is exactly the odd-mode
corrector coefficient `ψTilde_m`. -/
theorem streamSeq_increment_eq_psiTilde (hΦ : IsStreamSeq I Φ) (m : ℕ)
    (hm : 1 ≤ m) (t : ℝ) (x : Vec 2) :
    Φ m t x - Φ (m - 1) t x = psiTilde I hΦ m t x := by
  obtain ⟨hprev, hnext⟩ := hΦ.2 m hm
  have hnextPoint :
      Φ m t x = Φ (m - 1) t x +
        ∑' k : ℤ, I.nextStreamTerm m (Φ (m - 1)) hprev t x k := by
    have hpoint := congrFun (congrFun hnext t) x
    simpa [Ingredients.nextStream] using hpoint
  have hzero (k : ℤ) (hk : ¬ Odd k) :
      I.nextStreamTerm m (Φ (m - 1)) hprev t x k = 0 := by
    simp [Ingredients.nextStreamTerm, StreamIncrement.psi_zero_of_not_odd (β := β) I m k _ hk]
  have hoddSum :
      (∑' k : ℤ, I.nextStreamTerm m (Φ (m - 1)) hprev t x k) =
        ∑' k : {k : ℤ // Odd k},
          I.nextStreamTerm m (Φ (m - 1)) hprev t x k.1 :=
    StreamIncrement.tsum_eq_odd_subtype_of_even_zero _ hzero
  rw [hnextPoint, hoddSum]
  dsimp [psiTilde, Ingredients.nextStreamTerm, Ingredients.xFlowInv]
  ring

end AVenhance.Infra.Section5

end
