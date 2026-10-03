/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.ZeroDataEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.FiniteGalerkinEnergy

/-!
# Forced Fourier mode calculus on the space-time cell

Support lemmas for the forced weak energy identity: the forcing seen by a smooth periodic spatial
mode, its integrability, and the finite Fourier sums attached to a weak path.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Parabolic.WeakUniqueness

local instance forcedFiniteUnitCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  unfold AVenhance.unitCube
  rw [Measure.restrict_apply_univ, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

/-- The forcing density seen by a smooth spatial mode `ψ`: transport/forcing scalar `G`,
diffusion `κ Du·∇ψ` and flux `F·∇ψ`. -/
def forcedModeIntegrand (κ : ℝ) (Du : ℝ → Vec 2 → Vec 2) (G : ℝ × Vec 2 → ℝ)
    (F : ℝ × Vec 2 → Vec 2) (ψ : Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  G p * ψ p.2 + κ * Homogenization.vecDot (Du p.1 p.2) (AVenhance.spaceGrad ψ p.2) +
    Homogenization.vecDot (F p) (AVenhance.spaceGrad ψ p.2)

/-- The time-slice integral of `forcedModeIntegrand`. -/
def forcedModeForcing (κ : ℝ) (Du : ℝ → Vec 2 → Vec 2) (G : ℝ × Vec 2 → ℝ)
    (F : ℝ × Vec 2 → Vec 2) (ψ : Vec 2 → ℝ) (s : ℝ) : ℝ :=
  ∫ x in AVenhance.unitCube, forcedModeIntegrand κ Du G F ψ (s, x)

theorem forced_timeCube_measure_eq_product :
    (volume.restrict AVenhance.timeCube) =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube) :=
  weakEnergy_timeCube_measure_eq_product

theorem forced_timeCube_measurable : MeasurableSet AVenhance.timeCube := by
  rw [AVenhance.timeCube]
  refine measurableSet_Ioo.prod ?_
  unfold AVenhance.unitCube
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

local instance forcedFiniteTimeCube : IsFiniteMeasure (volume.restrict AVenhance.timeCube) := by
  rw [forced_timeCube_measure_eq_product]
  infer_instance

/-- A continuous bounded function of the spatial variable alone is bounded on the time cell. -/
theorem forced_continuous_bound {Z : Vec 2 → ℝ} (hZ : Continuous Z) :
    ∃ C : ℝ, ∀ᵐ p ∂(volume.restrict AVenhance.timeCube), ‖Z p.2‖ ≤ C := by
  obtain ⟨C, _, hbound⟩ := weak_continuous_timeCube_bound (hZ.comp continuous_snd)
  refine ⟨C, ?_⟩
  filter_upwards [ae_restrict_mem forced_timeCube_measurable] with p hp
  exact hbound p hp

/-- A coordinatewise `L²` field paired with a continuous spatial field is integrable. -/
theorem forced_vecDot_integrable {Y : ℝ × Vec 2 → Vec 2}
    (hY : ∀ i : Fin 2, MemLp (fun p => Y p i) 2 (volume.restrict AVenhance.timeCube))
    {Z : Vec 2 → Vec 2} (hZ : Continuous Z) :
    Integrable (fun p : ℝ × Vec 2 => Homogenization.vecDot (Y p) (Z p.2))
      (volume.restrict AVenhance.timeCube) := by
  have hterm (i : Fin 2) : Integrable (fun p : ℝ × Vec 2 => Y p i * Z p.2 i)
      (volume.restrict AVenhance.timeCube) := by
    obtain ⟨C, hC⟩ := forced_continuous_bound ((continuous_apply i).comp hZ)
    exact ((hY i).integrable (by norm_num)).mul_bdd
      (((continuous_apply i).comp hZ).comp continuous_snd).measurable.aestronglyMeasurable hC
  simpa only [Homogenization.vecDot] using integrable_finsetSum Finset.univ (fun i _ => hterm i)

/-- The mode forcing density is integrable on the time cell. -/
theorem forcedModeIntegrand_integrable {κ : ℝ} {Du : ℝ → Vec 2 → Vec 2}
    {G : ℝ × Vec 2 → ℝ} {F : ℝ × Vec 2 → Vec 2}
    (hDu : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2
      (volume.restrict AVenhance.timeCube))
    (hG : MemLp G 2 (volume.restrict AVenhance.timeCube))
    (hF : ∀ i : Fin 2, MemLp (fun p => F p i) 2 (volume.restrict AVenhance.timeCube))
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Integrable (forcedModeIntegrand κ Du G F ψ) (volume.restrict AVenhance.timeCube) := by
  have hψone : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hgrad : Continuous (fun x : Vec 2 => AVenhance.spaceGrad ψ x) := by
    apply continuous_pi
    intro i
    exact (hψone.continuous_fderiv (by norm_num)).clm_apply continuous_const
  obtain ⟨C, hC⟩ := forced_continuous_bound hψ.continuous
  have h1 : Integrable (fun p : ℝ × Vec 2 => G p * ψ p.2) (volume.restrict AVenhance.timeCube) :=
    (hG.integrable (by norm_num)).mul_bdd
      (hψ.continuous.comp continuous_snd).measurable.aestronglyMeasurable hC
  have h2 := (forced_vecDot_integrable hDu hgrad).const_mul κ
  have h3 := forced_vecDot_integrable hF hgrad
  exact (h1.add h2).add h3

/-- Mode forcing is interval integrable on `[0,1]`. -/
theorem forcedModeForcing_intervalIntegrable {κ : ℝ} {Du : ℝ → Vec 2 → Vec 2}
    {G : ℝ × Vec 2 → ℝ} {F : ℝ × Vec 2 → Vec 2}
    (hDu : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2
      (volume.restrict AVenhance.timeCube))
    (hG : MemLp G 2 (volume.restrict AVenhance.timeCube))
    (hF : ∀ i : Fin 2, MemLp (fun p => F p i) 2 (volume.restrict AVenhance.timeCube))
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    IntervalIntegrable (forcedModeForcing κ Du G F ψ) volume 0 1 := by
  have hint := forcedModeIntegrand_integrable (κ := κ) hDu hG hF hψ
  have hproduct : Integrable (forcedModeIntegrand κ Du G F ψ)
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (volume.restrict AVenhance.unitCube)) := by
    rwa [← forced_timeCube_measure_eq_product]
  have htime : Integrable (fun t => ∫ x, forcedModeIntegrand κ Du G F ψ (t, x)
      ∂(volume.restrict AVenhance.unitCube)) (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    hproduct.integral_prod_left
  have htime' : Integrable (forcedModeForcing κ Du G F ψ)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [← Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Ioc)]
    exact htime
  rw [intervalIntegrable_iff, uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact htime'

end AVenhance.Infra.Section5.RelativeError

end
