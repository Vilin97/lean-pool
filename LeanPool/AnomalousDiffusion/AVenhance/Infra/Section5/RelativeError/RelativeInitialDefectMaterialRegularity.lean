/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectEndpointPhysical
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityPeriodic

/-! Actual endpoint regularity on positive times. No closed-time regularity
of the two-sided Amnr recursion is required. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization AVenhance AVenhance.Infra.Section4
open AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
namespace AVenhance.Infra.Section5.RelativeError

/-- Every actual endpoint is jointly smooth on the open positive half-space. -/
theorem relative_initial_endpoint_contDiffOn_Ioi_top {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec
    2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) (r : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 => hmEndpoint I hΦ m κm (T (Nstar β)) r z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hG : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ℝ × Vec 2 => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
        I.Amnr hΦ m κm n (T (Nstar β)) r z.1 z.2 i j k * I.qMNR κm m n r z.1 j k)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
    intro i
    refine ContDiffOn.sum fun n _ => ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ => ?_
    have hq : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => I.qMNR κm m n r t j k) :=
      contDiff_pi.mp (contDiff_pi.mp (residual_qMNR_contDiff I κm m n r) j) k
    exact (amnr_contDiffOn_Ioi_top I hΦ hm hκm hθprev hT n r i j k).mul
      (hq.comp contDiff_fst).contDiffOn
  unfold hmEndpoint vecDiv
  exact ContDiffOn.sum fun i _ =>
    contDiffOn_spaceGrad_slice_Ioi
      (F := fun t y => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
        I.Amnr hΦ m κm n (T (Nstar β)) r t y i j k * I.qMNR κm m n r t j k) (hG i) i

/-- Every endpoint is spatially periodic at positive times. -/
theorem relative_initial_endpoint_periodic_pos {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) {Tm1 : ℝ → Vec 2 → ℝ}
    (hTper : ∀ t : ℝ, 0 ≤ t → IsZ2Periodic (Tm1 t)) (r : ℕ) {t : ℝ} (ht : 0 < t) :
    IsZ2Periodic (hmEndpoint I hΦ m κm Tm1 r t) := by
  intro s x
  unfold hmEndpoint vecDiv
  refine Finset.sum_congr rfl fun i _ => ?_
  have hV : IsZ2Periodic (fun y => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
      I.Amnr hΦ m κm n Tm1 r t y i j k * I.qMNR κm m n r t j k) := by
    intro s' y
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    exact congrArg (· * I.qMNR κm m n r t j k)
      (Amnr_isZ2Periodic_pos I hΦ m κm n hTper r t ht i j k s' y)
  exact congrFun (Section5.RelativeError.spaceGrad_isZ2Periodic hV s x) i

end AVenhance.Infra.Section5.RelativeError
