/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LemmaU.SliceDrift
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LemmaU.LowHigh
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.DivergenceFreeEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.FiniteGalerkinEnergy

/-!
# Lemma U: a weak solution is a mode system

The real Fourier coefficients of a weak solution of the advection-diffusion equation with a
bounded divergence-free drift form a `ModeSystem` with energy density `‖Dθ(r)‖²`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Parabolic.WeakUniqueness

namespace AVenhance.Infra.FullTheorem.LemmaU

/-- Coefficient path of mode `a`. -/
def modePath (M : ℕ) (θ : ℝ → Vec 2 → ℝ) (a : RealFourierIndex M) (r : ℝ) : ℝ :=
  weakModePairing θ (realFourierModeAmbient M a) r

/-- The part of the forcing not accounted for by dissipation. -/
def modeDrift (M : ℕ) (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (θ : ℝ → Vec 2 → ℝ)
    (D : ℝ → Vec 2 → Vec 2) (a : RealFourierIndex M) (r : ℝ) : ℝ :=
  weakModeForcing b κ D (realFourierModeAmbient M a) r - κ * modeLam M a * modePath M θ a r

theorem modePath_eq_cellCoeff (M : ℕ) (θ : ℝ → Vec 2 → ℝ) (a : RealFourierIndex M) (r : ℝ) :
    modePath M θ a r = cellCoeff M (θ r) a := rfl

/-- The mode system of a weak solution. -/
theorem weak_modeSystem {b : ℝ → Vec 2 → Vec 2} {κ B : ℝ} {θ₀ : Vec 2 → ℝ}
    {Dθ₀ : Vec 2 → Vec 2} {θ : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hκ : 0 < κ) (hB0 : 0 ≤ B)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, AVenhance.IsZ2Periodic (b t))
    (hdiv : AVenhance.IsDivFree b)
    (hB : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ B)
    (hθ₀ : AVenhance.IsPeriodicH1With θ₀ Dθ₀)
    (hu : AVenhance.IsWeakSolutionGrad b κ θ₀ θ D) (M : ℕ) :
    ModeSystem κ (2 * B) (modeLam M) (modePath M θ) (modeDrift M b κ θ D)
      (fun r => AVenhance.gradNormSq (D r)) (AVenhance.l2NormSq θ₀ / (2 * κ)) := by
  have hψs : ∀ a : RealFourierIndex M, ContDiff ℝ (⊤ : ℕ∞) (realFourierModeAmbient M a) :=
    fun a => (realFourierModeAmbient_contDiff M a).of_le (by simp)
  have hcI : ∀ a, IntervalIntegrable (modePath M θ a) volume 0 1 := fun a =>
    (hu.2.2.2.2.2.2.1 _ (hψs a) (realFourierModeAmbient_periodic M a)).intervalIntegrable_of_Icc
      zero_le_one
  have hcont : ∀ a, ContinuousOn (modePath M θ a) (Icc (0 : ℝ) 1) := fun a =>
    hu.2.2.2.2.2.2.1 _ (hψs a) (realFourierModeAmbient_periodic M a)
  have hpath : ∀ a, ∀ t ∈ Icc (0 : ℝ) 1, modePath M θ a t = modePath M θ a 0 -
      ∫ r in (0 : ℝ)..t, weakModeForcing b κ D (realFourierModeAmbient M a) r := by
    intro a t ht
    have h := weak_solution_mode_integral_path hu hθ₀.2.2.1 (hψs a)
      (realFourierModeAmbient_periodic M a)
    have h0 := h 0 ⟨le_rfl, zero_le_one⟩
    simp only [intervalIntegral.integral_same, sub_zero] at h0
    have ht' := h t ht
    unfold modePath
    rw [h0]
    exact ht'
  have hdrift := hu.2.2.2.2.2.1
  have hDint := integrable_vecNormSq_timeCube hu.2.2.2.1
  have henergy := weak_solution_divFree_energy_identity hu hθ₀.2.2.1 hb_meas ⟨B, hB⟩ hb_per hdiv
    1 ⟨zero_le_one, le_rfl⟩
  refine
    { kappa_pos := hκ
      B_nonneg := by positivity
      lam_nonneg := modeLam_nonneg M
      c_cont := hcont
      G_int := fun a => ?_
      path := fun a t ht => ?_
      e_nonneg := fun r => gradNormSq_nonneg (D r)
      e_int := ?_
      e_total := ?_
      bessel_c := ?_
      bessel_G := ?_ }
  · exact (weak_solution_mode_forcing_intervalIntegrable hu (hψs a)).sub
      ((hcI a).const_mul (κ * modeLam M a))
  · have e : ∀ r, κ * modeLam M a * modePath M θ a r + modeDrift M b κ θ D a r =
        weakModeForcing b κ D (realFourierModeAmbient M a) r := by
      intro r; unfold modeDrift; ring
    simp_rw [e]
    exact hpath a t ht
  · exact intervalIntegrable_cell_of_timeCube hDint
  · have h1 : ∫ r in (0 : ℝ)..1, AVenhance.gradNormSq (D r) =
        ∫ p in AVenhance.timeCube, Homogenization.vecNormSq (D p.1 p.2) :=
      (integral_timeCube_eq_interval_cell hDint).symm
    rw [h1]
    have hl := l2NormSq_nonneg (θ 1)
    have h2 : (∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ AVenhance.unitCube,
        Homogenization.vecNormSq (D p.1 p.2)) =
        ∫ p in AVenhance.timeCube, Homogenization.vecNormSq (D p.1 p.2) := rfl
    rw [h2] at henergy
    rw [le_div_iff₀ (by positivity)]
    linarith
  · rw [← timeMeasure_Ioo_eq_Ioc]
    filter_upwards [hu.2.2.2.2.1] with t htH
    exact modeLam_sum_le htH M
  · filter_upwards [drift_slice_ae hB hu M] with t ⟨htH, hgL2, hl2, hid⟩
    have hbessel := cellCoeff_bessel M hgL2
    have hdr : ∀ a, modeDrift M b κ θ D a t =
        cellCoeff M (fun x => Homogenization.vecDot (b t x) (D t x)) a := by
      intro a
      unfold modeDrift
      rw [hid a, modePath_eq_cellCoeff]
      ring
    simp_rw [hdr]
    have he := gradNormSq_nonneg (D t)
    calc ∑ a, cellCoeff M (fun x => Homogenization.vecDot (b t x) (D t x)) a ^ 2
        ≤ AVenhance.l2NormSq (fun x => Homogenization.vecDot (b t x) (D t x)) := hbessel
      _ ≤ 2 * B ^ 2 * AVenhance.gradNormSq (D t) := hl2
      _ ≤ (2 * B) ^ 2 * AVenhance.gradNormSq (D t) := by
          apply mul_le_mul_of_nonneg_right _ he
          nlinarith [sq_nonneg B]

end AVenhance.Infra.FullTheorem.LemmaU

end
