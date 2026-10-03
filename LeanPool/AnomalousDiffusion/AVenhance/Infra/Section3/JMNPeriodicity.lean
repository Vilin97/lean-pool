/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.JMN
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The explicit `j_{m,n}` coefficients have the corrected period `4τ_m`. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section3

open AVenhance

/-- Translate an odd integer index by four, preserving its parity. -/
def JMNPeriodicity.oddIndexShiftFour : {k : ℤ // Odd k} ≃ {k : ℤ // Odd k} where
  toFun k := ⟨k.1 + 4, by
    rcases k.2 with ⟨z, hz⟩
    refine ⟨z + 2, ?_⟩
    omega⟩
  invFun k := ⟨k.1 - 4, by
    rcases k.2 with ⟨z, hz⟩
    refine ⟨z - 2, ?_⟩
    omega⟩
  left_inv k := by
    apply Subtype.ext
    simp
  right_inv k := by
    apply Subtype.ext
    simp

/-- One odd-index matrix term in the cutoff-derivative moment sum. -/
def JMNPeriodicity.jMNSummand {β : ℝ} (I : Ingredients β) (m n : ℕ)
    (k : {k : ℤ // Odd k}) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (I.zetaMK m k.1 t * iteratedDeriv n (I.zetaMK m k.1) t) •
    ((if k.1 % 4 = 1 then !![0, 0; 0, 1] else 0) +
      (if k.1 % 4 = 3 then !![1, 0; 0, 0] else 0) :
        Matrix (Fin 2) (Fin 2) ℝ)

theorem JMNPeriodicity.zetaMK_add_four {β : ℝ} (I : Ingredients β) {m : ℕ}
    (k : ℤ) (t : ℝ) :
    I.zetaMK m (k + 4) (t + 4 * tau β I.Λ m) = I.zetaMK m k t := by
  have hτ : 0 < tau β I.Λ m :=
    Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  change I.zeta ((t + 4 * tau β I.Λ m -
      ((k + 4 : ℤ) : ℝ) * tau β I.Λ m) / tau β I.Λ m) =
    I.zeta ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m)
  congr 1
  push_cast
  field_simp [ne_of_gt hτ]
  ring

theorem JMNPeriodicity.iteratedDeriv_zetaMK_add_four {β : ℝ} (I : Ingredients β)
    {m n : ℕ} (k : ℤ) (t : ℝ) :
    iteratedDeriv n (I.zetaMK m (k + 4)) (t + 4 * tau β I.Λ m) =
      iteratedDeriv n (I.zetaMK m k) t := by
  let T := 4 * tau β I.Λ m
  have hfun : (fun s => I.zetaMK m (k + 4) (s + T)) = I.zetaMK m k := by
    funext s
    dsimp [T]
    exact JMNPeriodicity.zetaMK_add_four I (m := m) k s
  have h := congrFun
    (iteratedDeriv_comp_add_const n (I.zetaMK m (k + 4)) T) t
  rw [hfun] at h
  exact h.symm

theorem JMNPeriodicity.jMNSummand_shift {β : ℝ} (I : Ingredients β)
    {m n : ℕ} (k : {k : ℤ // Odd k}) (t : ℝ) :
    JMNPeriodicity.jMNSummand I m n (JMNPeriodicity.oddIndexShiftFour k) (t + 4 * tau β I.Λ m) =
      JMNPeriodicity.jMNSummand I m n k t := by
  have hz := JMNPeriodicity.zetaMK_add_four I (m := m) k.1 t
  have hd := JMNPeriodicity.iteratedDeriv_zetaMK_add_four I (m := m) (n := n) k.1 t
  have hmod : (k.1 + 4) % 4 = k.1 % 4 := by omega
  simp [JMNPeriodicity.jMNSummand, JMNPeriodicity.oddIndexShiftFour, hz, hd, hmod]

/-- Each explicit coefficient `j_{m,n}` has period `4τ_m`. -/
theorem jMN_period_four_tau {β : ℝ} (I : Ingredients β) {m : ℕ}
    (κ : ℝ) (n : ℕ) :
    Function.Periodic (I.jMN κ m n) (4 * tau β I.Λ m) := by
  intro t
  unfold Ingredients.jMN
  change
    (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
        (n.factorial : ℝ) *
      (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) •
        (∑' k : {k : ℤ // Odd k},
          JMNPeriodicity.jMNSummand I m n k (t + 4 * tau β I.Λ m)) =
    (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
        (n.factorial : ℝ) *
      (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) •
        (∑' k : {k : ℤ // Odd k}, JMNPeriodicity.jMNSummand I m n k t)
  congr 1
  calc
    (∑' k : {k : ℤ // Odd k}, JMNPeriodicity.jMNSummand I m n k (t + 4 * tau β I.Λ m)) =
        ∑' k : {k : ℤ // Odd k},
          JMNPeriodicity.jMNSummand I m n (JMNPeriodicity.oddIndexShiftFour k) (t + 4 * tau β I.Λ
              m) := by
      rw [← JMNPeriodicity.oddIndexShiftFour.tsum_eq
        (fun k : {k : ℤ // Odd k} => JMNPeriodicity.jMNSummand I m n k
          (t + 4 * tau β I.Λ m))]
    _ = ∑' k : {k : ℤ // Odd k}, JMNPeriodicity.jMNSummand I m n k t := by
      apply tsum_congr
      intro k
      exact JMNPeriodicity.jMNSummand_shift I k t

end AVenhance.Infra.Section3

end
