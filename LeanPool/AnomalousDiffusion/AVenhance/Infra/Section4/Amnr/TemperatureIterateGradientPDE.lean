/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureIterateClassicalFamily
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.DissipationCoordinateL2
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureDiffusionRates
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureMaterialWordEquation

/-! The primitive gradient PDE for every actual temperature iterate. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Temperature flux associated with a specified iterate. -/
def amnrIterateFlux {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κm κprev : ℝ) (T : ℕ → ℝ → Vec 2 → ℝ) (i : ℕ)
    (q : Fin 2) : AmnrSpace → ℝ :=
  if i = 0 then fun _ => 0 else amnrTemperatureFlux I hΦ m κm κprev (T (i - 1)) q

theorem amnr_tIterates_gradient_pde {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : AVenhance.IsClassicalSol (AVenhance.streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (i : ℕ) (hi : i ≤ AVenhance.Nstar β) (p : Fin 2) :
    EqOn (amnrOp (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) none (amnrTGradient (T i) p))
      (fun z => κprev * (∑ q : Fin 2,
          amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
            [some q, some q] (amnrTGradient (T i) p) z) +
        (∑ q : Fin 2, amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
          [some p, some q] (amnrIterateFlux I hΦ m κm κprev T i q) z) -
        ∑ q : Fin 2, amnrVelocityGradient
          (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) q p z * amnrTGradient (T i) q z)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  by_cases hz : i = 0
  · subst i
    simp only [amnrIterateFlux, ite_true, hT.1]
    intro z hz
    have hb : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) :=
      contDiff_infty.mpr (fun N => amnr_previous_velocity_contDiff I hΦ hm N)
    have hh := amnr_classical_gradient_material_equation hθprev hb p hz.1
    have hzero (q : Fin 2) : amnrWord
        (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        [some p, some q] (fun _ => 0) z = 0 :=
      congrFun (amnrWord_zero _ _) z
    simp only [hzero, Finset.sum_const_zero, add_zero]
    simpa [AVenhance.spaceGrad] using hh
  · obtain ⟨F, hv⟩ := amnr_tIterates_classical_family I hΦ hθprev hT (i - 1) (by omega)
    simpa only [amnrIterateFlux, ite_eq_right hz] using
      amnr_temperature_gradient_flux_equation I hΦ hm hκm hv (hT.2 i (by omega) hi) p

end AVenhance.Infra.Section4
