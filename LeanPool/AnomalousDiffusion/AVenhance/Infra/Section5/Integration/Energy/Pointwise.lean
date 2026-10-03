/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.Regularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.ParamIntegral
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.Duality
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.PeriodicCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsClassicalSol
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsAdmissibleStream

/-! # The differential energy identity and inequality for `w = u - v`

For `t > 0` write `w = u - v`, `f = advDiffOp b κ v`.  Then `∂ₜ w = κ Δw - b·∇w - f`, the energy
satisfies `d/dt ∫ w² = -2κ ∫ |∇w|² - 2 ∫ f w`, and (when `‖f t‖_{HDot⁻¹} < ∞`) the Young
inequality gives `d/dt ∫ w² + κ ∫ |∇w|² ≤ ‖f t‖²_{HDot⁻¹} / κ`. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Homogenization
open AVenhance.Infra.Torus AVenhance.Infra.Classical
open scoped Topology

namespace AVenhance.Infra.Section5.Integration.Energy

open AVenhance

/-- The standing hypotheses of the forced energy estimate. -/
structure ForcedSetup (φ : ℝ → Vec 2 → ℝ) (κ : ℝ) (θ₀ : Vec 2 → ℝ) (u v : ℝ → Vec 2 → ℝ) :
    Prop where
  hφ : IsAdmissibleStream φ
  hκ : 0 < κ
  hu : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) θ₀ u
  hv : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => v p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)
  hvs : ∀ t, 0 ≤ t → ContDiff ℝ (⊤ : ℕ∞) (v t)
  hvp : ∀ t, 0 ≤ t → IsZ2Periodic (v t)

variable {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ₀ : Vec 2 → ℝ} {u v : ℝ → Vec 2 → ℝ}

namespace ForcedSetup

theorem hu1 (S : ForcedSetup φ κ θ₀ u v) :
    ContDiffOn ℝ 1 (Function.uncurry u) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
  S.hu.1.of_le (by exact_mod_cast le_top)

theorem hv1 (S : ForcedSetup φ κ θ₀ u v) :
    ContDiffOn ℝ 1 (Function.uncurry v) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
  S.hv.of_le (by norm_num)

/-- The error `w = u - v` is jointly `C¹` on `[0,∞) × ℝ²`. -/
theorem hw1 (S : ForcedSetup φ κ θ₀ u v) :
    ContDiffOn ℝ 1 (Function.uncurry fun t x => u t x - v t x)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
  S.hu1.sub S.hv1

theorem hw1Open (S : ForcedSetup φ κ θ₀ u v) :
    ContDiffOn ℝ 1 (Function.uncurry fun t x => u t x - v t x) classicalPositiveTimeDomain :=
  S.hw1.mono (by
    intro p hp
    simp only [classicalPositiveTimeDomain, Set.mem_prod, Set.mem_Ioi, Set.mem_univ] at hp
    exact ⟨le_of_lt hp.1, trivial⟩)

theorem wSlice (S : ForcedSetup φ κ θ₀ u v) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => u t x - v t x) :=
  (classicalSmooth_slice_nonneg S.hu.1 ht).sub (S.hvs t ht)

theorem wPeriodic (S : ForcedSetup φ κ θ₀ u v) {t : ℝ} (ht : 0 ≤ t) :
    IsZ2Periodic (fun x => u t x - v t x) := by
  intro k x
  simp [S.hu.2.1 t ht k x, S.hvp t ht k x]

theorem drift_continuous (S : ForcedSetup φ κ θ₀ u v) :
    Continuous (Function.uncurry (streamVel φ)) :=
  (streamVel_smoothPeriodic φ S.hφ).smooth.continuous

/-- The forcing is jointly continuous on `(0,∞) × ℝ²`. -/
theorem forcing_continuousOn (S : ForcedSetup φ κ θ₀ u v) :
    ContinuousOn (fun p : ℝ × Vec 2 => advDiffOp (streamVel φ) κ v p.1 p.2)
      classicalPositiveTimeDomain :=
  continuousOn_advDiffOp S.drift_continuous κ S.hv

/-- The equation for the error `w = u - v` at positive times. -/
theorem deriv_w_eq (S : ForcedSetup φ κ θ₀ u v) {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    deriv (fun s => u s x - v s x) t =
      κ * spaceLap (fun y => u t y - v t y) x -
        vecDot (streamVel φ t x) (spaceGrad (fun y => u t y - v t y) x) -
        advDiffOp (streamVel φ) κ v t x := by
  have hOpen : ∀ {g : ℝ → Vec 2 → ℝ},
      ContDiffOn ℝ 1 (Function.uncurry g) (Set.Ici (0 : ℝ) ×ˢ Set.univ) →
      ContDiffOn ℝ 1 (Function.uncurry g) classicalPositiveTimeDomain := fun hg =>
    hg.mono (by
      intro p hp
      simp only [classicalPositiveTimeDomain, Set.mem_prod, Set.mem_Ioi, Set.mem_univ] at hp
      exact ⟨le_of_lt hp.1, trivial⟩)
  have du := timeSection_hasDerivAt_one (hOpen S.hu1) ht x
  have dv := timeSection_hasDerivAt_one (hOpen S.hv1) ht x
  have hderiv : deriv (fun s => u s x - v s x) t = deriv (fun s => u s x) t -
      deriv (fun s => v s x) t := by
    rw [(du.fun_sub dv).deriv, du.deriv, dv.deriv]
  have hus := classicalSmooth_slice_nonneg S.hu.1 ht.le
  have hvs := S.hvs t ht.le
  have hgrad := congrFun (smooth_spaceGrad_sub hus hvs) x
  have hlap := congrFun (smooth_spaceLap_sub hus hvs) x
  have hdot : vecDot (streamVel φ t x) (spaceGrad (fun y => u t y - v t y) x) =
      vecDot (streamVel φ t x) (spaceGrad (u t) x) -
        vecDot (streamVel φ t x) (spaceGrad (v t) x) := by
    simp only [vecDot]
    rw [hgrad]
    simp only [Pi.sub_apply, mul_sub]
    rw [Finset.sum_sub_distrib]
  have hu0 := S.hu.2.2.2 t ht x
  simp only [advDiffOp] at hu0 ⊢
  rw [hderiv, hlap, hdot]
  linarith

end ForcedSetup

end AVenhance.Infra.Section5.Integration.Energy

end
