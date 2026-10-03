/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectMaterialEquation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.TransportCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointSmoothFromFixedStart

/-! The actual Hm material source along any flow of the previous velocity.
Only positive-time joint regularity is used. -/

@[expose] public section

noncomputable section
open Filter Topology Homogenization AVenhance AVenhance.Infra.Section4
open AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
namespace AVenhance.Infra.Section5.RelativeError

/-- Pulling actual Hm along the previous velocity differentiates to the actual
endpoint difference, with no negative-time or initial-time calculus premise. -/
theorem relative_initial_Hm_material_derivative_along_flow {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {g : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) g θprev)
    (hT : I.IsTIterates hΦ m κm κprev g θprev T)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow (streamVel (Φ (m - 1))) X)
    {t s : ℝ} (ht : 0 < t) (x : Vec 2) :
    HasDerivAt (fun r => I.Hm hΦ m κm (T (Nstar β)) r (X r x s))
      (hmEndpoint I hΦ m κm (T (Nstar β)) (Jcut β) t (X t x s) -
        hmEndpoint I hΦ m κm (T (Nstar β)) 0 t (X t x s)) t := by
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ (m - 1))
  let H : ℝ → Vec 2 → ℝ := I.Hm hΦ m κm (T (Nstar β))
  let z : Vec 2 := X t x s
  let L : (ℝ × Vec 2) →L[ℝ] ℝ := fderiv ℝ (Function.uncurry H) (t, z)
  have hHmEq := relative_initial_Hm_material_equation I hΦ hm hκm hθ hT ht z
  have hF : HasFDerivAt (Function.uncurry H) L (t, z) := by
    have hc := (Hm_contDiffOn_Ioi_top I hΦ hm hκm hθ hT).contDiffAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (show (t, z) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) from
          ⟨ht, Set.mem_univ z⟩))
    exact (hc.differentiableAt (by simp)).hasFDerivAt
  have hcurve : HasDerivAt (fun r => H r (X r x s)) (L (1, b t z)) t := by
    let γ : ℝ → ℝ × Vec 2 := fun r => (r, X r x s)
    have hγ : HasDerivAt γ (1, b t z) t := by
      exact (hasDerivAt_id t).prodMk (hX.2 x s t)
    have hc := hF.comp_hasDerivAt t hγ
    simpa [γ, Function.uncurry, Function.comp_def] using hc
  have htime : deriv (fun r => H r z) t = L (1, (0 : Vec 2)) := by
    let γ : ℝ → ℝ × Vec 2 := fun r => (r, z)
    have hγ : HasDerivAt γ (1, (0 : Vec 2)) t := by
      exact (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
    simpa [γ, Function.uncurry, Function.comp_def] using
      deriv_uncurry_comp hF hγ
  let J : Vec 2 →L[ℝ] ℝ × Vec 2 := ContinuousLinearMap.inr ℝ ℝ (Vec 2)
  have hslice : HasFDerivAt (H t) (L.comp J) z := by
    have hc := hF.comp z (hasFDerivAt_prodMk_right t z)
    simpa [Function.uncurry, Function.comp_def, J] using hc
  have hspace : fderiv ℝ (H t) z (b t z) = L (0, b t z) := by
    rw [hslice.fderiv]
    simp [J, ContinuousLinearMap.comp_apply]
  have hsplit : L (1, b t z) = L (1, (0 : Vec 2)) + L (0, b t z) := by
    calc
      L (1, b t z) = L ((1, (0 : Vec 2)) + (0, b t z)) := by simp
      _ = L (1, (0 : Vec 2)) + L (0, b t z) := by rw [L.map_add]
  have hvalue : L (1, b t z) =
      hmEndpoint I hΦ m κm (T (Nstar β))
        (Jcut β) t z -
      hmEndpoint I hΦ m κm (T (Nstar β)) 0 t z := by
    calc
      L (1, b t z) = L (1, (0 : Vec 2)) + L (0, b t z) := hsplit
      _ = deriv (fun r => H r z) t + fderiv ℝ (H t) z (b t z) := by
        rw [← htime, ← hspace]
      _ = _ := hHmEq
  exact hcurve.congr_deriv (by simpa [H, b, z] using hvalue)

/-- The actual fixed-start flow is jointly continuous in time and position. -/
theorem relative_initial_xFlow_joint_continuous {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) :
    Continuous (fun z : ST => I.xFlow hΦ m l z.1 z.2) := by
  have hflow := flow_isFlow (streamVel (Φ (m - 1)))
    (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
  have hc := (Infra.Flow.flow_joint_contDiff_infty
    (Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)) hflow).continuous
  have hemb : Continuous (fun z : ST => (z.1, z.2, (l : ℝ) * tauPP β I.Λ m)) := by fun_prop
  simpa only [Ingredients.xFlow, Function.comp_def] using hc.comp hemb

/-- The previous-scale fixed-start flow has the exact positive-time material derivative. -/
theorem relative_initial_Hm_derivative_along_xFlow {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {g : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) g θprev)
    (hT : I.IsTIterates hΦ m κm κprev g θprev T)
    (l : ℤ) {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    HasDerivAt (fun r => I.Hm hΦ m κm (T (Nstar β)) r (I.xFlow hΦ m l r x))
      (hmEndpoint I hΦ m κm (T (Nstar β)) (Jcut β) t (I.xFlow hΦ m l t x) -
        hmEndpoint I hΦ m κm (T (Nstar β)) 0 t (I.xFlow hΦ m l t x)) t := by
  exact relative_initial_Hm_material_derivative_along_flow I hΦ hm hκm hθ hT
    (flow_isFlow (streamVel (Φ (m - 1)))
      (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz) ht x

end AVenhance.Infra.Section5.RelativeError
