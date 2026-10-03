/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermContinuityPointwiseTiny

/-! # Joint continuity of the six non-divergence §5.1 terms

For the actual iterates (`I.IsTIterates`), the terms `cutoff1`, `twistie1`, `twistie4`,
`twistie5`, `normie3` and `tiny` are jointly continuous on the open half space
`(0,∞) × ℝ²`.  Open time only: `HTilde_m` and `Amnr` use the two-sided time derivative.

* `TermContinuityPointwiseTools`: locally finite sums, spatial gradients/divergences of jointly
  smooth fields, composition with the inverse flow;
* `TermContinuityPointwiseFields`: joint regularity of the building blocks;
* `TermContinuityPointwiseTerms`: `cutoff1`, `twistie1`, `twistie4`, `twistie5`, `normie3`
  for a jointly smooth `T`;
* `TermContinuityPointwiseTiny`: `tiny`. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

/-- `cutoff1` of the terminal iterate is jointly continuous on the open half space. -/
theorem cutoff1_term_continuousOn
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ContinuousOn (fun p : ℝ × Vec 2 => cutoff1 I hΦ m κm (T (Nstar β)) p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have _hm := hm
  have _hκm := hκm
  exact tc_cutoff1_continuousOn I hΦ m κm
    (Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev le_rfl)

/-- `twistie1` of the terminal iterate is jointly continuous on the open half space. -/
theorem twistie1_term_continuousOn
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ContinuousOn (fun p : ℝ × Vec 2 => twistie1 I hΦ m κm (T (Nstar β)) p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have _hm := hm
  have _hκm := hκm
  exact tc_twistie1_continuousOn I hΦ m hm hκm
    (Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev le_rfl)

/-- `twistie4` of the terminal iterate is jointly continuous on the open half space. -/
theorem twistie4_term_continuousOn
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ContinuousOn (fun p : ℝ × Vec 2 => twistie4 I hΦ m κm (T (Nstar β)) p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have _hm := hm
  have _hκm := hκm
  exact tc_twistie4_continuousOn I hΦ m κm
    (Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev le_rfl)

/-- `twistie5` of the terminal iterate is jointly continuous on the open half space. -/
theorem twistie5_term_continuousOn
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ContinuousOn (fun p : ℝ × Vec 2 => twistie5 I hΦ m κm (T (Nstar β)) p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have _hm := hm
  have _hκm := hκm
  exact tc_twistie5_continuousOn I hΦ m κm
    (Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev le_rfl)

/-- `normie3` of the terminal iterate is jointly continuous on the open half space. -/
theorem normie3_term_continuousOn
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ContinuousOn (fun p : ℝ × Vec 2 => normie3 I hΦ m κm (T (Nstar β)) p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have _hm := hm
  have _hκm := hκm
  exact tc_normie3_continuousOn I hΦ m hm κm
    (Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev le_rfl)

/-- `tiny` (with the `d_m` and last-iterate error `e_{m-1}`) is jointly continuous on the open
half space. -/
theorem tiny_term_continuousOn
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ContinuousOn (fun p : ℝ × Vec 2 =>
      tiny I hΦ m κm (sourceErrorD I hΦ m κm (T (Nstar β)))
        (iterateError I hΦ m κm κprev T) p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have _hm := hm
  have _hκm := hκm
  exact tc_tiny_continuousOn I hΦ m hm hκm hθprev hT

end AVenhance.Infra.Section5.Contracts
