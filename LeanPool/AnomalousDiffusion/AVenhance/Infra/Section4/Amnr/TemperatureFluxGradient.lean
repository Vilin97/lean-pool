/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureGradientMaterialEquation

/-! Differentiating the actual forcing flux within its finite source order. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Two ordinary derivatives suffice to identify the forcing gradient.
No infinite regularity of the time-dependent Kmat is used. -/
theorem amnr_temperatureForcing_gradient_eq_flux
    {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {b : ℝ → Vec 2 → Vec 2} {F u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hu : AVenhance.IsClassicalSol b κprev F u₀ u)
    (B : AmnrSpace → Vec 2) (hB : ContDiff ℝ (⊤ : ℕ∞) B)
    (p : Fin 2) {z : AmnrSpace} (hz : 0 < z.1) :
    AVenhance.spaceGrad (I.TForcing hΦ m κm κprev u z.1) z.2 p =
      ∑ q : Fin 2, amnrWord B [some p, some q]
        (amnrTemperatureFlux I hΦ m κm κprev u q) z := by
  let U : Set AmnrSpace := Ioi (0 : ℝ) ×ˢ univ
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hzu : z ∈ U := ⟨hz, mem_univ _⟩
  have hN := AVenhance.Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
  have hb2 : ContDiffOn ℝ 2 B U := (hB.of_le (by simp)).contDiffOn
  have hf2 (q : Fin 2) : ContDiffOn ℝ 2
      (amnrTemperatureFlux I hΦ m κm κprev u q) U :=
    (amnr_temperatureFlux_contDiffOn I hΦ hm hκm hu q).of_le
      (by exact_mod_cast (show 2 ≤ AVenhance.Nstar β by omega))
  have hg1 (q : Fin 2) : ContDiffOn ℝ 1
      (amnrOp B (some q) (amnrTemperatureFlux I hΦ m κm κprev u q)) U :=
    amnrWord_contDiffOn hU hb2 (hf2 q) [some q] (by simp)
  have hid := amnr_temperatureForcing_eq_flux_divergence I hΦ hm hκm hu B
  have hforce : ContDiffOn ℝ 1
      (fun y : AmnrSpace => I.TForcing hΦ m κm κprev u y.1 y.2) U := by
    have hs : ContDiffOn ℝ 1
        (fun y => ∑ q : Fin 2, amnrOp B (some q)
          (amnrTemperatureFlux I hΦ m κm κprev u q) y) U :=
      ContDiffOn.sum (fun q _ => hg1 q)
    exact hs.congr (fun y hy => hid hy)
  have he := amnrWord_congr (b := B) hU hid [some p] hzu
  have hsum := amnrWord_sum hU (hb2.of_le (by norm_num)) Finset.univ
    (fun q => amnrOp B (some q) (amnrTemperatureFlux I hΦ m κm κprev u q))
    (fun q _ => hg1 q) [some p] (by simp) hzu
  change amnrOp B (some p) (fun y => I.TForcing hΦ m κm κprev u y.1 y.2) z = _ at he
  rw [amnrOp_space ((hforce.contDiffAt (hU.mem_nhds hzu)).differentiableAt (by norm_num)) p] at he
  exact he.trans hsum

end AVenhance.Infra.Section4
