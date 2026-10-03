/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermFluxesJoint
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TIterateSmooth

/-! # Joint continuity of the divergence-form terms on the open half space

`twistie3`, `normie1`, `normie2` and `R46` are divergences of fluxes that are jointly `C²` on
`(0,∞) × ℝ²` (resp. a time-continuous matrix times a jointly smooth vector for `R46`), hence jointly
continuous there.  Nothing is claimed at `t ≤ 0`: `HTilde_m` and `Amnr` use the two-sided time
derivative. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration

theorem twistie3_term_continuousOn {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (_hm : 1 ≤ m) {κm κprev : ℝ} (_hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ContinuousOn (fun p : ℝ × Vec 2 => twistie3 I hΦ m κm (T (Nstar β)) p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hTU := Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (le_refl (Nstar β))
  exact (tf_vecDiv_continuousOn (V := twistie3Flux I hΦ m κm (T (Nstar β)))
    (tf_twistie3Flux_contDiffOn I hΦ m κm hTU)).neg

theorem normie1_term_continuousOn {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (_hm : 1 ≤ m) {κm κprev : ℝ} (_hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ContinuousOn (fun p : ℝ × Vec 2 => normie1 I hΦ m κm (T (Nstar β)) p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hTU := Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (le_refl (Nstar β))
  exact (tf_vecDiv_continuousOn (V := normie1Flux I hΦ m κm (T (Nstar β)))
    (tf_normie1Flux_contDiffOn I hΦ m κm hTU)).neg

theorem normie2_term_continuousOn {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ContinuousOn (fun p : ℝ × Vec 2 => normie2 I hΦ m κm (T (Nstar β)) p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hH := Hm_contDiffOn_Ioi_top I hΦ hm hκm hθprev hT
  exact (tf_vecDiv_continuousOn (V := normie2Flux I hΦ m κm (T (Nstar β)))
    (tf_normie2Flux_contDiffOn I hΦ m κm hH)).neg

theorem R46_term_continuousOn {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (_hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ContinuousOn (fun p : ℝ × Vec 2 => R46 I hΦ m κm (T (Nstar β)) p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hTU := Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (le_refl (Nstar β))
  exact tf_R46_continuousOn I hΦ hm κm hTU

end AVenhance.Infra.Section5.Contracts
end
