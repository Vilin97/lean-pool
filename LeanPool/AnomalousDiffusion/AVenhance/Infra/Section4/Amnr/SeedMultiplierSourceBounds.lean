/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowMixedEstimate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowAverageSourceBounds

/-! Full actual mixed seed-multiplier bounds from source ingredients. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Smoothness of the candidate seed through the full source order. -/
theorem amnr_seedMultiplierA0Plus_contDiff {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (n N : ℕ)
    (hN : N ≤ AVenhance.Nstar β) (j k i p : Fin 2) :
    ContDiff ℝ N (amnrSeedMultiplierA0Plus I hΦ m κ n j k i p) := by
  have hAvg := amnrFlowAverageA0Plus_contDiffOn (N := N)
    I hΦ hm isOpen_univ
    j k i p
    (fun l => (amnr_flowGrad_joint_contDiff_infty I hΦ m l j i).of_le (by simp) |>.contDiffOn)
    (fun l => (amnr_flowGrad_joint_contDiff_infty I hΦ m l k p).of_le (by simp) |>.contDiffOn)
  have hL : ContDiff ℝ N (fun z : AmnrSpace => I.LMN κ m n z.1) :=
    ((Section3.LMN_contDiff I hm hκ n).of_le (by exact_mod_cast hN)).comp contDiff_fst
  rw [amnrSeedMultiplierA0Plus_eq]
  exact (hL.neg.mul (contDiffOn_univ.mp hAvg))

/-- Smoothness of the actual seed through the source order. -/
theorem amnr_seedMultiplier_contDiff {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (n N : ℕ)
    (hN : N ≤ AVenhance.Nstar β) (j k i p : Fin 2) :
    ContDiff ℝ N (amnrSeedMultiplier I hΦ m κ n j k i p) := by
  change ContDiff ℝ N (amnrSeedMultiplierA0Plus I hΦ m κ n j k i p)
  exact amnr_seedMultiplierA0Plus_contDiff I hΦ hm hκ n N hN j k i p

end AVenhance.Infra.Section4
