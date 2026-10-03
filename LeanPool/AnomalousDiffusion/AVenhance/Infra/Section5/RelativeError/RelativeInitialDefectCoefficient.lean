/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectCutoffs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorBounds

/-! Physical coefficient bound for the twisted initial corrector. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section5.RelativeError
open AVenhance

/-- Twisting changes the evaluation point, but not the explicit coefficient bound. -/
theorem relative_initial_chiTilde_bound {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    (k : ℤ) (x : Vec 2) (i : Fin 2) :
    |I.chiTilde hΦ m κ k 0 x i| ≤
      (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ *
        |2 * Real.pi * a β I.Λ m * epsilon β I.Λ m| := by
  exact Infra.Section3.chiMK_component_abs_le I hm κ hκ k 0 _ i

/-- Actual corrector estimate with cutoff and active-flow inputs discharged.
Only the explicit coefficient and the positive derivative of the datum occur. -/
theorem relative_initial_corrector_explicit {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    {g : Vec 2 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (T : ℝ → Vec 2 → ℝ) (hT0 : T 0 = g) :
    Real.sqrt (l2NormSq (fun x => ∑' k : ℤ, I.xiMK m k 0 *
      vecDot (I.chiTilde hΦ m κ k 0 x)
        (spaceGrad (fun y => T 0 (I.xFlow hΦ m (lIdx β I.Λ m k) 0 y))
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) 0 x)))) ≤
      (24 * ((4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ *
        |2 * Real.pi * a β I.Λ m * epsilon β I.Λ m|)) *
          Real.sqrt (gradNormSq (spaceGrad g)) := by
  have h := relative_initial_corrector_bound I hΦ m κ hg T hT0
    (by positivity) (by norm_num : (0 : ℝ) ≤ 3)
    (fun k _ x i => relative_initial_chiTilde_bound I hΦ hm hκ k x i)
    (fun k hk x i j => relative_initial_active_flowGrad_le_two I hΦ hm k hk x i j)
    (relative_initial_cutoff_sum I hm)
  convert h using 1; ring
end AVenhance.Infra.Section5.RelativeError
