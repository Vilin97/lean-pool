/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativePositiveProduct
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnalyticBridge.FlowSnorm

/-! Positive-order temperature jets and arbitrary amplitude; no zeroth-order
temperature supremum. Existing Sobolev, product and composition engines are reused. -/

@[expose] public section

noncomputable section

open scoped ContDiff
open Homogenization MeasureTheory

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.FaaDiBruno AVenhance.Infra.Section5.AnalyticBridge

/-- Pointwise bound on the ordered partials of `(∂_i f ∂_j f) ∘ X`. -/
theorem orderedPartial_comp_le {K : ℝ} (hK1 : 1 ≤ K)
    (hK : ∀ n : ℕ, ((n : ℝ) + 3) ^ 5 ≤ K * 2 ^ n)
    {A ρ e N : ℝ} (hA : 1 ≤ A) (hρ : 0 < ρ) (hρe : ρ ≤ e) (he1 : e ≤ 1) (hN : 0 < N)
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) (hp : IsZ2Periodic f)
    (hreg : ∀ (n : ℕ) (i : Fin n → Fin 2), 0 < n →
      Real.sqrt (l2NormSq (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j)))) ≤
        (A * N) * n.factorial * (A / ρ) ^ n)
    {X : Vec 2 → Vec 2} (hX : FlowForErgodicBound A e X) (hXs : ContDiff ℝ ∞ X)
    (i j : Fin 2) (n : ℕ) (x : Vec 2) (I : Fin n → Fin 2) :
    ‖orderedPartial n
        ((fun y => fderiv ℝ f y (basisVec i) * fderiv ℝ f y (basisVec j)) ∘ X) x I‖ ≤
      (4 * (3 * sobolevConst * (A * N) * K * (A / ρ) ^ 3) ^ 2) * n.factorial *
        ((2 * A / e) * (1 + ((2 : ℕ) : ℝ) * (K * e) * (2 * (A / ρ)))) ^ n := by
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA
  have he : 0 < e := lt_of_lt_of_le hρ hρe
  have ha1 : 1 ≤ A / ρ := by
    rw [le_div_iff₀ hρ]; linarith
  have ha0 : 0 < A / ρ := lt_of_lt_of_le one_pos ha1
  have hsc := sobolevConst_pos
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hB : 0 ≤ A * N := by positivity
  set h : Vec 2 → ℝ := fun y => fderiv ℝ f y (basisVec i) * fderiv ℝ f y (basisVec j) with hh
  set Cf : ℝ := 4 * (3 * sobolevConst * (A * N) * K * (A / ρ) ^ 3) ^ 2 with hCf
  have hCfpos : 0 < Cf := by positivity
  have hhs : ContDiff ℝ n h :=
    ((contDiff_fderiv_apply_basis hf i).mul (contDiff_fderiv_apply_basis hf j)).of_le
      (by exact_mod_cast le_top)
  have hXn : ContDiff ℝ n X := hXs.of_le (by exact_mod_cast le_top)
  have hCg : 0 < K * e := by positivity
  have hRh : 0 < 2 * (A / ρ) := by positivity
  have hRg : 0 < 2 * A / e := by positivity
  have hcomp := compositionEstimate10528 (d := 2) (m := n) h X hhs hXn hCfpos hCg hRh hRg
    (fun m _ => snorm_fderiv_mul_le hf hp hB ha1 hK hreg i j m)
    (fun m hm _ => snorm_flow_le hK hA0 he hX m hm) n le_rfl
  have hRpos : 0 < (2 * A / e) * (1 + ((2 : ℕ) : ℝ) * (K * e) * (2 * (A / ρ))) := by positivity
  have hpt := orderedPartial_norm_le_of_snorm_le (h ∘ X) (hhs.comp hXn) le_rfl hRpos
    hCfpos.le hcomp x I
  refine hpt.trans ?_
  have hn2 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  exact div_le_self (by positivity) hn2

end AVenhance.Infra.Section5.RelativeError

end
