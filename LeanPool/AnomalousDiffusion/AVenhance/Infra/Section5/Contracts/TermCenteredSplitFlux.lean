/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredSplitFields
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredSplitCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredSplitAlgebra

/-! # Smoothness and periodicity of `Σ_k ξ_k D_k G_k` at a fixed time

The generic flux form with `k`-dependent matrices, a finite set of nonvanishing weights. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

theorem sd_tsum_flux_eq_sum (c : {k : ℤ // Odd k} → ℝ) (hfin : {k | c k ≠ 0}.Finite)
    (F : {k : ℤ // Odd k} → Vec 2 → Vec 2) (x : Vec 2) :
    ∑' k, c k • F k x = ∑ k ∈ hfin.toFinset, c k • F k x := by
  classical
  refine tsum_eq_sum fun k hk => ?_
  have : c k = 0 := by
    by_contra hne
    exact hk ((Set.Finite.mem_toFinset hfin).2 hne)
  simp [this]

theorem sd_flux_contDiff (c : {k : ℤ // Odd k} → ℝ) (hfin : {k | c k ≠ 0}.Finite)
    (D : {k : ℤ // Odd k} → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (W : {k : ℤ // Odd k} → Vec 2 → Vec 2)
    (hD : ∀ k i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => D k x i j))
    (hW : ∀ k j, ContDiff ℝ (⊤ : ℕ∞) (fun x => W k x j)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑' k, c k • (D k x).mulVec (W k x)) := by
  have hfun : (fun x => ∑' k, c k • (D k x).mulVec (W k x)) = fun x =>
      ∑ k ∈ hfin.toFinset, c k • (D k x).mulVec (W k x) :=
    funext fun x => sd_tsum_flux_eq_sum c hfin (fun k y => (D k y).mulVec (W k y)) x
  rw [hfun]
  refine ContDiff.sum fun k _ => ContDiff.const_smul _ ?_
  rw [← contDiffOn_univ]
  exact contDiffOn_pi.2 fun i => tf_mulVec_contDiffOn (s := Set.univ)
    (fun i j => (hD k i j).contDiffOn) (fun j => (hW k j).contDiffOn) i

theorem sd_flux_periodic (c : {k : ℤ // Odd k} → ℝ)
    (D : {k : ℤ // Odd k} → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (W : {k : ℤ // Odd k} → Vec 2 → Vec 2)
    (hD : ∀ k, IsZ2Periodic (D k)) (hW : ∀ k, IsZ2Periodic (W k)) :
    IsZ2Periodic (fun x => ∑' k, c k • (D k x).mulVec (W k x)) := by
  intro n x
  refine tsum_congr fun k => ?_
  rw [hD k n x, hW k n x]

theorem sd_tsum_eq_sum_of_support (c : {k : ℤ // Odd k} → ℝ) (hfin : {k | c k ≠ 0}.Finite)
    (f : {k : ℤ // Odd k} → ℝ) (hf : ∀ k, c k = 0 → f k = 0) :
    ∑' k, f k = ∑ k ∈ hfin.toFinset, f k := by
  classical
  refine tsum_eq_sum fun k hk => hf k ?_
  by_contra hne
  exact hk ((Set.Finite.mem_toFinset hfin).2 hne)

/-- The split `-Σ_k c_k g_k · Div D_k = Σ_k c_k D_k : ∇g_k - div (Σ_k c_k D_k g_k)` for a finite
set of nonvanishing weights and smooth data. -/
theorem sd_split_odd (c : {k : ℤ // Odd k} → ℝ) (hfin : {k | c k ≠ 0}.Finite)
    (D : {k : ℤ // Odd k} → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (g : {k : ℤ // Odd k} → Vec 2 → Vec 2)
    (hD : ∀ k i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => D k x i j))
    (hg : ∀ k j, ContDiff ℝ (⊤ : ℕ∞) (fun x => g k x j)) (x : Vec 2) :
    -∑' k, c k * vecDot (g k x) (matDiv (D k) x) =
      ∑' k, c k * frob (D k x) (Matrix.of fun i j => spaceGrad (fun y => g k y j) x i) -
        vecDiv (fun y => ∑' k, c k • (D k y).mulVec (g k y)) x := by
  have hflux : (fun y => ∑' k, c k • (D k y).mulVec (g k y)) =
      fun y => ∑ k ∈ hfin.toFinset, c k • (D k y).mulVec (g k y) :=
    funext fun y => sd_tsum_flux_eq_sum c hfin (fun k z => (D k z).mulVec (g k z)) y
  rw [hflux, sd_tsum_eq_sum_of_support c hfin _ (fun k hk => by simp [hk]),
    sd_tsum_eq_sum_of_support c hfin
      (fun k => c k * frob (D k x) (Matrix.of fun i j => spaceGrad (fun y => g k y j) x i))
      (fun k hk => by simp [hk])]
  exact sd_split_finset hfin.toFinset c D g x
    (fun k _ i j => ((hD k i j).differentiable (by simp)) x)
    (fun k _ j => ((hg k j).differentiable (by simp)) x)

theorem sd_nd_continuous (c : {k : ℤ // Odd k} → ℝ) (hfin : {k | c k ≠ 0}.Finite)
    (D A : {k : ℤ // Odd k} → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hD : ∀ k i j, Continuous (fun x => D k x i j))
    (hA : ∀ k i j, Continuous (fun x => A k x i j)) :
    Continuous (fun x => ∑' k, c k * frob (D k x) (A k x)) := by
  have hfun : (fun x => ∑' k, c k * frob (D k x) (A k x)) =
      fun x => ∑ k ∈ hfin.toFinset, c k * frob (D k x) (A k x) :=
    funext fun x => sd_tsum_eq_sum_of_support c hfin _ (fun k hk => by simp [hk])
  rw [hfun]
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  unfold frob
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (hD k i j).mul (hA k i j)

end AVenhance.Infra.Section5.Contracts
end
