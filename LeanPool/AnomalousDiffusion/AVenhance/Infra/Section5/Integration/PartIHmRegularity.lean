/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FrozenBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowAverage
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.Seed
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SpatialCommutator
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureGradientDiffusion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureIterateClassicalFamily
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TIterateSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.IteratesLMNSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.IteratesForcingSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ResidualDataRegularity

/-! # Part I: joint `C^∞` regularity of `Amnr` and `HTilde_m` on the open half space

The `Amnr` recursion differentiates in time with the two-sided `deriv`, so at `t = 0`
it sees values of `T` for `t < 0`.  On the open half space `(0,∞) × ℝ²` everything is
unconditional: the seed multiplier, the velocity, its gradient and `∇T_{N*}` are all jointly
`C^∞` there, and the recursion preserves this.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section4

/-- The primitive seed multiplier is `C^∞`, with no source-budget restriction. -/
theorem amnrSeedMultiplier_contDiff_top {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κ : ℝ}
    (hκ : 0 < κ) (n : ℕ) (j k i p : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (amnrSeedMultiplier I hΦ m κ n j k i p) := by
  refine contDiff_infty.mpr (fun N => ?_)
  have hAvg := amnrFlowAverageA0Plus_contDiffOn (N := N)
    I hΦ hm isOpen_univ
    j k i p
    (fun l => (amnr_flowGrad_joint_contDiff_infty I hΦ m l j i).of_le (by simp) |>.contDiffOn)
    (fun l => (amnr_flowGrad_joint_contDiff_infty I hΦ m l k p).of_le (by simp) |>.contDiffOn)
  have hL : ContDiff ℝ N (fun z : AmnrSpace => I.LMN κ m n z.1) :=
    ((Section5.RelativeError.LMN_contDiff_top I hm hκ n).of_le (by simp)).comp contDiff_fst
  change ContDiff ℝ N (amnrSeedMultiplierA0Plus I hΦ m κ n j k i p)
  rw [amnrSeedMultiplierA0Plus_eq]
  exact hL.neg.mul (contDiffOn_univ.mp hAvg)

/-- **Joint `C^∞` regularity of the actual `Amnr` tensors on the open half space.** -/
theorem amnr_contDiffOn_Ioi_top {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) (n r : ℕ) (i j k : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ℝ × Vec 2 => I.Amnr hΦ m κm n (T (Nstar β)) r z.1 z.2 i j k)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    isOpen_Ioi.prod isOpen_univ
  have hbInf : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2) :=
    contDiff_infty.mpr (fun N => amnr_previous_velocity_contDiff I hΦ hm N)
  obtain ⟨F, hF⟩ := amnr_tIterates_classical_family I hΦ hθprev hT (Nstar β) le_rfl
  refine contDiffOn_infty.mpr (fun a => ?_)
  exact Amnr_contDiffOn_of_factors I hΦ hm κm n (T (Nstar β)) hU (N := a + r) j k
    (hbInf.contDiffOn.of_le (by exact_mod_cast le_top))
    (fun i p => (amnrVelocityGradient_contDiffOn_infty hU hbInf.contDiffOn i p).of_le
      (by exact_mod_cast le_top))
    (fun i p => ((amnrSeedMultiplier_contDiff_top I hΦ hm hκm n j k i p).of_le
      (by exact_mod_cast le_top)).contDiffOn)
    (fun p => (amnr_classical_gradient_smooth_infty hF p).of_le
      (by exact_mod_cast le_top))
    le_rfl i

end AVenhance.Infra.Section5.Integration
