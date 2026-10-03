/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredDefs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsSource

/-! # Component form of the nondivergence parts

Pure algebra: termwise identities `ξ_k D_k : ∇G_k = Σ_{a,j} (fast factor) (slow factor)` and the
passage from the `tsum` over odd `k` to a finite sum over any `S` containing the support. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- Termwise component form for `twistie4`. -/
theorem sd_term4_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (k : ℤ)
    (t : ℝ) (x : Vec 2) :
    I.xiMK m k t * frob (sdDefect4 I hΦ m κm k t x) (gradG I hΦ m T (lIdx β I.Λ m k) t x) =
      ∑ a : Fin 2, ∑ j : Fin 2,
        sdFast4 I κm m k t a j (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) *
          section5SlowChoice2 I hΦ m κm T k t a j x := by
  simp only [frob, sdDefect4, sdFast4, section5SlowChoice2, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.sub_apply, Fin.sum_univ_two, smul_eq_mul]
  ring

/-- Termwise component form for `twistie5`. -/
theorem sd_term5_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (k : ℤ)
    (t : ℝ) (x : Vec 2) :
    I.xiMK m k t * frob (sdDefect5 I hΦ m κm k t x) (gradG I hΦ m T (lIdx β I.Λ m k) t x) =
      ∑ a : Fin 2, ∑ j : Fin 2,
        sdFast5 I κm m k t a j (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) *
          section5SlowChoice3 I hΦ m T k t a j x := by
  simp only [frob, sdDefect5, sdFast5, section5SlowChoice3, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.sub_apply, Matrix.add_apply, Matrix.transpose_apply, Fin.sum_univ_two, smul_eq_mul]
  ring

/-- A `tsum` over odd `k` of terms vanishing off `S` is the finite sum over `S`. -/
theorem sd_tsum_eq_sum {f : {k : ℤ // Odd k} → ℝ} (S : Finset {k : ℤ // Odd k})
    (hS : ∀ k, f k ≠ 0 → k ∈ S) : ∑' k, f k = ∑ k ∈ S, f k :=
  tsum_eq_sum fun k hk => by_contra fun h => hk (hS k h)

end AVenhance.Infra.Section5.Contracts
end
