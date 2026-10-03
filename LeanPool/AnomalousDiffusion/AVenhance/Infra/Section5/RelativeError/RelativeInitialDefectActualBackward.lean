/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectMaterialFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectPositiveExtension
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.FlowDiffeo
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmEndpoints

/-! Backward transport for the actual Hm on the first positive half-cell.
The quantitative source primitive is separate from the proved calculus. -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Homogenization AVenhance AVenhance.Infra.Section4
open AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
namespace AVenhance.Infra.Section5.RelativeError

/-- Actual positive-time Hm is controlled by the integrated endpoint source.
All flow, periodicity, continuity and material-equation premises are discharged. -/
theorem relative_initial_Hm_backward_of_source_integral {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {g : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) g θprev)
    (hT : I.IsTIterates hΦ m κm κprev g θprev T)
    {D : ℝ} (hD : 0 ≤ D)
    (hsource : ∀ t ∈ Set.Ioc (0 : ℝ) (tauPP β I.Λ m / 2),
      (∫ s in t..(tauPP β I.Λ m / 2), Real.sqrt (l2NormSq (fun x =>
        hmEndpoint I hΦ m κm (T (Nstar β)) (Jcut β) s x -
          hmEndpoint I hΦ m κm (T (Nstar β)) 0 s x))) ≤ D) :
    ∀ t ∈ Set.Ioc (0 : ℝ) (tauPP β I.Λ m / 2),
      Real.sqrt (l2NormSq (I.Hm hΦ m κm (T (Nstar β)) t)) ≤ 2 * D := by
  let X := LeftToShow.xFlowDiffeo I hΦ m 0
  let source := fun t x => hmEndpoint I hΦ m κm (T (Nstar β)) (Jcut β) t x -
    hmEndpoint I hΦ m κm (T (Nstar β)) 0 t x
  have hX : Continuous (fun z : ST => (z.1, (X z.1).toFun z.2)) := by
    simpa only [X, LeftToShow.xFlowDiffeo_toFun] using
      continuous_fst.prodMk (relative_initial_xFlow_joint_continuous I hΦ m 0)
  have hmap : Set.MapsTo (fun z : ST => (z.1, (X z.1).toFun z.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    fun _ hz => ⟨hz.1, Set.mem_univ _⟩
  have hTper := (terminalT_contDiffOn_nonneg_and_periodic I hΦ hT hθ).2
  have hsourceper (t : ℝ) (ht : 0 < t) : IsZ2Periodic (source t) := by
    intro n x
    exact congrArg₂ (· - ·)
      (relative_initial_endpoint_periodic_pos I hΦ m κm hTper (Jcut β) ht n x)
      (relative_initial_endpoint_periodic_pos I hΦ m κm hTper 0 ht n x)
  have hsourcecont : ContinuousOn (fun z : ST => source z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    (relative_initial_endpoint_contDiffOn_Ioi_top I hΦ hm hκm hθ hT (Jcut β)).continuousOn.sub
      (relative_initial_endpoint_contDiffOn_Ioi_top I hΦ hm hκm hθ hT 0).continuousOn
  have hb : 0 < tauPP β I.Λ m / 2 := by
    exact div_pos (Infra.Cutoff.tauPP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le) (by norm_num)
  have hmaterial (t : ℝ) (ht : 0 < t) (x : Vec 2) :
      HasDerivAt (fun s => I.Hm hΦ m κm (T (Nstar β)) s ((X s).toFun x))
        (source t ((X t).toFun x)) t := by
    simpa only [X, LeftToShow.xFlowDiffeo_toFun, source] using
      relative_initial_Hm_derivative_along_xFlow I hΦ hm hκm hθ hT 0 ht x
  have hzero : I.Hm hΦ m κm (T (Nstar β)) (tauPP β I.Λ m / 2) = 0 := by
    have hz := Hm_eq_zero_at_halfCell I hΦ hm κm (T (Nstar β)) 0
    have heq : ((0 : ℤ) + 1 / 2 : ℝ) * tauPP β I.Λ m = tauPP β I.Λ m / 2 := by ring
    rw [heq] at hz
    exact hz
  have hcomp : ContinuousOn (fun z : ST =>
      I.Hm hΦ m κm (T (Nstar β)) z.1 ((X z.1).toFun z.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
    simpa only [Function.comp_def] using
      (Hm_contDiffOn_Ioi_top I hΦ hm hκm hθ hT).continuousOn.comp hX.continuousOn hmap
  have hscomp : ContinuousOn (fun z : ST => source z.1 ((X z.1).toFun z.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
    simpa only [Function.comp_def] using hsourcecont.comp hX.continuousOn hmap
  exact relative_initial_backward_transport_of_positive_data
    (F := I.Hm hΦ m κm (T (Nstar β))) (source := source) X
    (fun t ht => Hm_periodic_pos I hΦ hm hκm hθ hT ht) hsourceper
    hcomp hscomp hmaterial hb hD hzero hsource

end AVenhance.Infra.Section5.RelativeError
