/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.TimeEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.PeriodicCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.Drift
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsClassicalSol

/-! # instantaneous energy rate of a classical solution

For an admissible stream `φ` and a classical solution `θ` of the homogeneous
advection–diffusion equation, the shifted function `θ + c` (`c` constant) has
`d/dt ∫_cell (θ + c)² = -2κ ∫_cell |∇θ|²` at every positive time.  Also: joint smoothness of the
spatial gradient components up to `t = 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open AVenhance.Infra.Torus
open AVenhance.Infra.Classical
open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance

/-- `spaceGrad` ignores additive constants. -/
theorem spaceGrad_add_const (f : Vec 2 → ℝ) (c : ℝ) :
    spaceGrad (fun y => f y + c) = spaceGrad f := by
  funext x i
  simp only [spaceGrad]
  rw [fderiv_add_const]

/-- `spaceLap` ignores additive constants. -/
theorem spaceLap_add_const (f : Vec 2 → ℝ) (c : ℝ) :
    spaceLap (fun y => f y + c) = spaceLap f := by
  funext x
  simp only [spaceLap, spaceGrad_add_const]

/-- The spatial gradient components of a classical solution are jointly smooth on the closed
half-space `t ≥ 0`. -/
theorem spaceGrad_component_contDiffOn {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F θ₀ θ) (i : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry fun t x => spaceGrad (θ t) x i)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  set s : Set (ℝ × Vec 2) := Set.Ici (0 : ℝ) ×ˢ Set.univ with hs_def
  have hs : UniqueDiffOn ℝ s := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) s := hsol.1
  have hD : ContDiffOn ℝ (⊤ : ℕ∞) (fderivWithin ℝ (Function.uncurry θ) s) s :=
    hF.fderivWithin hs (by simp)
  have hE : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p => fderivWithin ℝ (Function.uncurry θ) s p ((0 : ℝ), basisVec i)) s :=
    hD.clm_apply contDiffOn_const
  refine hE.congr ?_
  rintro ⟨t, x⟩ hp
  have hdiff : DifferentiableWithinAt ℝ (Function.uncurry θ) s (t, x) :=
    (hF.differentiableOn (by simp) (t, x) hp)
  have hι : HasFDerivAt (fun y : Vec 2 => (t, y))
      ((0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2))) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hmaps : Set.MapsTo (fun y : Vec 2 => (t, y)) Set.univ s := by
    intro y _
    exact ⟨hp.1, Set.mem_univ y⟩
  have hcomp := hdiff.hasFDerivWithinAt.comp x hι.hasFDerivWithinAt hmaps
  have hcomp' : HasFDerivAt (θ t) ((fderivWithin ℝ (Function.uncurry θ) s (t, x)).comp
      ((0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2)))) x := by
    rw [← hasFDerivWithinAt_univ]
    exact hcomp
  change fderiv ℝ (θ t) x (basisVec i) = _
  rw [hcomp'.fderiv]
  simp

theorem BaseEnergyRate.continuous_spaceGrad_component {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    Continuous (fun x => spaceGrad f x i) := by
  change Continuous (fun x => fderiv ℝ f x (basisVec i))
  exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const

theorem BaseEnergyRate.continuous_spaceLap {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (spaceLap f) := by
  unfold spaceLap
  apply continuous_finsetSum
  intro i _
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fun x => spaceGrad f x i) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x (basisVec i))
    exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
  exact BaseEnergyRate.continuous_spaceGrad_component hgrad i

theorem BaseEnergyRate.continuous_vecDot' {f g : Vec 2 → Vec 2}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => vecDot (f x) (g x)) := by
  change Continuous (fun x => ∑ i : Fin 2, f x i * g x i)
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp hf).mul ((continuous_apply i).comp hg)

/-- Energy rate of a smooth periodic solution of `w_t - κΔw + b·∇w = 0` with an admissible stream
drift: `d/dt ∫_cell w² = -2κ ∫_cell |∇w|²` at positive times. -/
theorem energy_hasDerivAt_of_pde
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (κ : ℝ) (w : ℝ → Vec 2 → ℝ)
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry w) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hwper : ∀ t : ℝ, 0 ≤ t → IsZ2Periodic (w t))
    (hPDE : ∀ t : ℝ, 0 < t → ∀ x, classicalTimePartial w (t, x) - κ * spaceLap (w t) x +
        vecDot (streamVel φ t x) (spaceGrad (w t) x) = 0)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in unitCell 2, (w s x) ^ 2)
      (-(2 * κ) * ∫ x in unitCell 2, vecDot (spaceGrad (w t) x) (spaceGrad (w t) x)) t := by
  have hwOpen : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry w) classicalPositiveTimeDomain :=
    hw.mono (by
      intro p hp
      simp only [classicalPositiveTimeDomain, Set.mem_prod, Set.mem_Ioi, Set.mem_univ] at hp
      exact ⟨le_of_lt hp.1, trivial⟩)
  let dt : Vec 2 → ℝ := fun x => classicalTimePartial w (t, x)
  let lap : Vec 2 → ℝ := fun x => spaceLap (w t) x
  let drift : Vec 2 → ℝ := fun x => vecDot (streamVel φ t x) (spaceGrad (w t) x)
  let a : Vec 2 → ℝ := fun x => 2 * w t x * dt x
  let l : Vec 2 → ℝ := fun x => w t x * lap x
  let q : Vec 2 → ℝ := fun x => drift x * w t x
  have hwDiffSlice : ContDiff ℝ (⊤ : ℕ∞) (w t) := classicalSmooth_slice_nonneg hw ht.le
  have hwC : Continuous (w t) := hwDiffSlice.continuous
  have hdtCont : Continuous dt := classicalTimePartial_continuous_slice hwOpen ht
  have hlapCont : Continuous lap := BaseEnergyRate.continuous_spaceLap hwDiffSlice
  have hbJoint := streamVel_smoothPeriodic φ hφ
  have hbSlice : ContDiff ℝ 1 (streamVel φ t) :=
    (hbJoint.smooth.of_le (by simp)).comp (contDiff_const.prodMk contDiff_id)
  have hgradC : Continuous (spaceGrad (w t)) :=
    continuous_pi fun i => BaseEnergyRate.continuous_spaceGrad_component hwDiffSlice i
  have hdriftC : Continuous drift := BaseEnergyRate.continuous_vecDot' hbSlice.continuous hgradC
  have haInt : IntegrableOn a (unitCell 2) :=
    continuous_integrableOn_unitCell ((continuous_const.mul hwC).mul hdtCont)
  have hlInt : IntegrableOn l (unitCell 2) :=
    continuous_integrableOn_unitCell (hwC.mul hlapCont)
  have hqInt : IntegrableOn q (unitCell 2) :=
    continuous_integrableOn_unitCell (hdriftC.mul hwC)
  have hpoint (x : Vec 2) : a x - (2 * κ) * l x + 2 * q x = 0 := by
    have hp := hPDE t ht x
    dsimp [a, l, q, dt, lap, drift]
    calc
      2 * w t x * classicalTimePartial w (t, x) -
          (2 * κ) * (w t x * spaceLap (w t) x) +
          2 * (vecDot (streamVel φ t x) (spaceGrad (w t) x) * w t x) =
          2 * w t x * (classicalTimePartial w (t, x) - κ * spaceLap (w t) x +
            vecDot (streamVel φ t x) (spaceGrad (w t) x)) := by ring
      _ = 0 := by rw [hp]; ring
  have hsumZero : ∫ x in unitCell 2, (a x - (2 * κ) * l x + 2 * q x) = 0 := by
    calc
      ∫ x in unitCell 2, (a x - (2 * κ) * l x + 2 * q x) = ∫ _ : Vec 2 in unitCell 2, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards with x
        exact hpoint x
      _ = 0 := by simp
  have hsumZero' :
      (∫ x in unitCell 2, a x) - (2 * κ) * (∫ x in unitCell 2, l x) +
        2 * (∫ x in unitCell 2, q x) = 0 := by
    have hsplit :
        (∫ x in unitCell 2, (a x - (2 * κ) * l x + 2 * q x)) =
          (∫ x in unitCell 2, a x) - (2 * κ) * (∫ x in unitCell 2, l x) +
            2 * (∫ x in unitCell 2, q x) := by
      calc
        _ = (∫ x in unitCell 2, (fun y => a y - (2 * κ) * l y) x) +
              ∫ x in unitCell 2, (fun y => 2 * q y) x :=
          integral_add (haInt.sub (hlInt.const_mul (2 * κ))) (hqInt.const_mul 2)
        _ = _ := by
          rw [integral_sub haInt (hlInt.const_mul (2 * κ))]
          rw [integral_const_mul, integral_const_mul]
    rw [← hsplit]
    exact hsumZero
  have hwDiffSlice1 : ContDiff ℝ 1 (w t) := hwDiffSlice.of_le (by norm_num)
  have htransport := streamVel_unitCell_transport_energy_zero φ hφ t
    (w t) hwDiffSlice1 (hwper t ht.le)
  have hlapEnergy := integral_unitCell_lap_energy hwDiffSlice (hwper t ht.le)
  have henergyDeriv := unitCell_energy_hasDerivAt hw ht
  have hrate : ∫ x in unitCell 2, 2 * w t x * classicalTimePartial w (t, x) =
      -(2 * κ) * ∫ x in unitCell 2, vecDot (spaceGrad (w t) x) (spaceGrad (w t) x) := by
    rw [htransport, hlapEnergy] at hsumZero'
    change (∫ x in unitCell 2, a x) = _
    linarith
  rw [← hrate]
  exact henergyDeriv

/-- The shifted classical solution `θ + c` has the same energy rate. -/
theorem classical_shift_hasDerivAt
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) {κ : ℝ} {θ₀ : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ}
    (hsol : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) θ₀ θ) (c : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in unitCell 2, (θ s x + c) ^ 2)
      (-(2 * κ) * ∫ x in unitCell 2, vecDot (spaceGrad (θ t) x) (spaceGrad (θ t) x)) t := by
  let w : ℝ → Vec 2 → ℝ := fun s x => θ s x + c
  have hw : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry w) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    hsol.1.add contDiffOn_const
  have hwper : ∀ t : ℝ, 0 ≤ t → IsZ2Periodic (w t) := by
    intro s hs k x
    change θ s (x + latticeShift k) + c = θ s x + c
    rw [hsol.2.1 s hs k x]
  have hPDE : ∀ s : ℝ, 0 < s → ∀ x, classicalTimePartial w (s, x) - κ * spaceLap (w s) x +
        vecDot (streamVel φ s x) (spaceGrad (w s) x) = 0 := by
    intro s hs x
    have hwOpen : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry w) classicalPositiveTimeDomain :=
      hw.mono (by
        intro p hp
        simp only [classicalPositiveTimeDomain, Set.mem_prod, Set.mem_Ioi, Set.mem_univ] at hp
        exact ⟨le_of_lt hp.1, trivial⟩)
    rw [classicalTimePartial_eq_deriv hwOpen hs x]
    have hder : deriv (fun r => w r x) s = deriv (fun r => θ r x) s := by
      change deriv (fun r => θ r x + c) s = _
      exact deriv_add_const c
    have hpde := hsol.2.2.2 s hs x
    have hpde' : deriv (fun r => θ r x) s - κ * spaceLap (θ s) x +
        vecDot (streamVel φ s x) (spaceGrad (θ s) x) = 0 := by
      simpa [advDiffOp] using hpde
    have hg : spaceGrad (w s) = spaceGrad (θ s) := spaceGrad_add_const (θ s) c
    have hl : spaceLap (w s) = spaceLap (θ s) := spaceLap_add_const (θ s) c
    rw [hder, hg, hl]
    exact hpde'
  have h := energy_hasDerivAt_of_pde φ hφ κ w hw hwper hPDE ht
  rwa [spaceGrad_add_const (θ t) c] at h

end AVenhance.Infra.Section5.RelativeError
