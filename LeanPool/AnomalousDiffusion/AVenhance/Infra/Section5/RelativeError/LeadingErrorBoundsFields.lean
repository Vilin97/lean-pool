/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsPointwise

/-! # Pointwise bound for the actual remainder fields

Instantiates `flowInv_flowFwd_component_le` and `hessian_component_le` with the flow estimates
`e.Xm.bound.1`, `e.Xm.bound.2` (`LeadingErrorFlow`) and the corrector bounds `e.corrm`. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem epsilon_pos' (I : Ingredients β) (n : ℕ) : 0 < epsilon β I.Λ n :=
  Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt (by exact_mod_cast I.two_pow_seven_le)

theorem epsilon_le_one' (I : Ingredients β) (n : ℕ) : epsilon β I.Λ n ≤ 1 :=
  Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le)

theorem delta_pos' (I : Ingredients β) : 0 < delta β :=
  Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt

theorem a_nonneg' (I : Ingredients β) (n : ℕ) : 0 ≤ a β I.Λ n :=
  (Real.rpow_pos_of_pos (epsilon_pos' I n) _).le

/-- Pointwise bound on the sum of the three remainder fields at `(t, x)` with `ξ_{m,k}(t) ≠ 0`. -/
theorem leadingErr_sum_component_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ}
    (hκ : 0 < κm) (T : ℝ → Vec 2 → ℝ) {t : ℝ} (k : ℤ) (hξ : I.xiMK m k t ≠ 0) (x : Vec 2)
    {gT : ℝ} {h : Fin 2 → ℝ} (hg : ∀ p, |spaceGrad (T t) x p| ≤ gT)
    (hh : ∀ i p, |spaceHess (T t) x i p| ≤ h p) (i : Fin 2) :
    |(leadingErrFlowInv I hΦ m κm T k t x + leadingErrFlowFwd I hΦ m κm T k t x +
        leadingErrHessian I hΦ m κm T k t x) i| ≤
      20 * epsilon β I.Λ (m - 1) ^ (2 * delta β) * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) * gT +
        epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) *
          (4 * (h 0 + h 1) + 16 * (2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹) * gT) := by
  have he1 : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 :=
    Real.rpow_le_one (epsilon_pos' I _).le (epsilon_le_one' I _)
      (by linarith [delta_pos' I])
  have hA := gradMatrix_xFlowInv_sub_one_le hΦ hm k hξ x
  have hFl := flowGrad_sub_one_le hΦ hm k hξ x
  have hC : ∀ u v, |gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) u v| ≤
      a β I.Λ m * epsilon β I.Λ m ^ 2 / κm := fun u v =>
    LeftToShow.gradMatrix_chiMK_entry_abs_le I (by omega) hκ k t _ u v
  have hχ : ∀ j, |I.chiMK κm m k t (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j| ≤
      epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) := fun j =>
    (Infra.Section3.chiMK_component_abs_le I (by omega) κm hκ k t _ j).trans
      (corrector_size_le (a_nonneg' I m) (epsilon_pos' I m) hκ)
  have hA2 := abs_le_two_of_sub_one he1 (fun u v => hA u v)
  have hFl2 := abs_le_two_of_sub_one he1 (fun u v => hFl u v)
  have hg' : ∀ j, |spaceGrad (T t) x j| ≤ gT := hg
  obtain ⟨h12, h13⟩ := flowInv_flowFwd_component_le he1 (fun u v => hA u v) hC
    (fun u v => hFl u v) hg' i
  have h3 := hessian_component_le (χ := I.chiMK κm m k t (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))
    (g := spaceGrad (T t) x) (Fl := I.flowGrad hΦ m (lIdx β I.Λ m k) t x)
    (a := fun q => gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) x i q)
    (Dd := fun p j q => xFlowHess I hΦ m (lIdx β I.Λ m k) t
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) p j q)
    (Hs := fun p => spaceHess (T t) x i p) (h := h) hχ (fun j p => hFl2 j p)
    (fun q => hA2 i q) (fun p j q => abs_xFlowHess_le hΦ hm k hξ _ p j q) (fun p => hh i p) hg'
  have key := abs_add_le_of_le (abs_add_le_of_le h12 h13) h3
  exact key.trans_eq (by ring)

end AVenhance.Infra.Section5.RelativeError
