/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectActualBackward
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectSourceIntegral

/-! Actual Hm bound from its endpoint-difference L2 source on positive time.
The source estimate uses the terminal one-letter budget from EndpointPhysical. -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Homogenization AVenhance AVenhance.Infra.Section4
open AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
namespace AVenhance.Infra.Section5.RelativeError

/-- A genuine spacetime L2 source bound gives uniform Hm control on the first
positive half-cell. No source norm at any particular time is assumed. -/
theorem relative_initial_Hm_backward_of_source_L2 {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {g : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) g θprev)
    (hT : I.IsTIterates hΦ m κm κprev g θprev T)
    {B : ℝ} (hB : 0 ≤ B) (hcell : tauPP β I.Λ m / 2 < 1)
    (hsource : eLpNorm (fun z : ℝ × Vec 2 =>
      hmEndpoint I hΦ m κm (T (Nstar β)) (Jcut β) z.1 z.2 -
        hmEndpoint I hΦ m κm (T (Nstar β)) 0 z.1 z.2) 2
      (volume.restrict timeCube) ≤ ENNReal.ofReal B) :
    ∀ t ∈ Set.Ioc (0 : ℝ) (tauPP β I.Λ m / 2),
      Real.sqrt (l2NormSq (I.Hm hΦ m κm (T (Nstar β)) t)) ≤
        2 * Real.sqrt (tauPP β I.Λ m / 2) * B := by
  have hcont : ContinuousOn (fun z : ST =>
      hmEndpoint I hΦ m κm (T (Nstar β)) (Jcut β) z.1 z.2 -
        hmEndpoint I hΦ m κm (T (Nstar β)) 0 z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    (relative_initial_endpoint_contDiffOn_Ioi_top I hΦ hm hκm hθ hT (Jcut β)).continuousOn.sub
      (relative_initial_endpoint_contDiffOn_Ioi_top I hΦ hm hκm hθ hT 0).continuousOn
  have hbound := relative_initial_Hm_backward_of_source_integral I hΦ hm hκm hθ hT
    (mul_nonneg (Real.sqrt_nonneg _) hB) (fun t ht =>
      relative_initial_source_integral_of_eLpNorm hcont hB ht.1 ht.2 hcell hsource)
  intro t ht
  exact (hbound t ht).trans_eq (by ring)

end AVenhance.Infra.Section5.RelativeError
