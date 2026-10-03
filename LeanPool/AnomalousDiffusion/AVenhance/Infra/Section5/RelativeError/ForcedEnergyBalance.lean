/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyDifference

/-!
# Energy balance for the difference of two weak solutions

For weak solutions with the same datum and diffusivity, a bounded divergence-free drift for
the first, and a flux `F` representing the cross transport against smooth periodic tests, the
difference satisfies `‖w(t)‖² + 2κ∫∫|Dw|² = -2∫∫F·Dw`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Parabolic.WeakUniqueness

local instance balanceFiniteUnitCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  unfold AVenhance.unitCube
  rw [Measure.restrict_apply_univ, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance balanceFiniteTimeCube :
    IsFiniteMeasure (volume.restrict AVenhance.timeCube) := by
  rw [forced_timeCube_measure_eq_product]
  infer_instance

/-- Coordinatewise `L²` fields have integrable dot product on the time cell. -/
theorem forced_vecDot_integrable_fields {Y Z : ℝ × Vec 2 → Vec 2}
    (hY : ∀ i : Fin 2, MemLp (fun p => Y p i) 2 (volume.restrict AVenhance.timeCube))
    (hZ : ∀ i : Fin 2, MemLp (fun p => Z p i) 2 (volume.restrict AVenhance.timeCube)) :
    Integrable (fun p => Homogenization.vecDot (Y p) (Z p))
      (volume.restrict AVenhance.timeCube) := by
  have hterm (i : Fin 2) : Integrable (fun p => Y p i * Z p i)
      (volume.restrict AVenhance.timeCube) := weak_product_integrable_timeCube (hY i) (hZ i)
  simpa only [Homogenization.vecDot] using integrable_finsetSum Finset.univ (fun i _ => hterm i)

theorem difference_energy_identity
    {b bM : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {θ θM : ℝ → Vec 2 → ℝ} {Dθ DM : ℝ → Vec 2 → Vec 2}
    (hθ : AVenhance.IsWeakSolutionGrad b κ g θ Dθ)
    (hM : AVenhance.IsWeakSolutionGrad bM κ g θM DM)
    (hg : MemL2On AVenhance.unitCube g)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, AVenhance.IsZ2Periodic (b t))
    (hdiv : AVenhance.IsDivFree b)
    {F : ℝ × Vec 2 → Vec 2}
    (hF : ∀ i : Fin 2, MemLp (fun p => F p i) 2 (volume.restrict AVenhance.timeCube))
    (hflux : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      AVenhance.IsZ2Periodic ψ →
      Integrable (fun x => Homogenization.vecDot (b s x - bM s x) (DM s x) * ψ x)
        (volume.restrict AVenhance.unitCube) ∧
      ∫ x in AVenhance.unitCube,
          Homogenization.vecDot (b s x - bM s x) (DM s x) * ψ x =
        ∫ x in AVenhance.unitCube,
          Homogenization.vecDot (F (s, x)) (AVenhance.spaceGrad ψ x))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AVenhance.l2NormSq (fun x => θ t x - θM t x) +
      2 * κ * (∫ p in weakEnergyRegion t,
        Homogenization.vecDot (Dθ p.1 p.2 - DM p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2)) =
    -2 * ∫ p in weakEnergyRegion t,
        Homogenization.vecDot (F p) (Dθ p.1 p.2 - DM p.1 p.2) := by
  have hpath := difference_forcedModePath hθ hM hg hb_meas hb_bdd hF hflux
  obtain ⟨hproj, hprojGrad⟩ := difference_projection_tendsto hθ hM
  have hf0 : MemL2On AVenhance.unitCube (fun _ : Vec 2 => (0 : ℝ)) :=
    weak_continuous_memL2On continuous_const
  have hGE := forced_energy_of_mode_path hpath hf0 hproj hprojGrad ht
  have hDw (i : Fin 2) : MemLp (fun p : ℝ × Vec 2 => (Dθ p.1 p.2 - DM p.1 p.2) i) 2
      (volume.restrict AVenhance.timeCube) :=
    (hθ.2.2.2.1 i).sub (hM.2.2.2.1 i)
  have hw : MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2 - θM p.1 p.2) 2
      (volume.restrict AVenhance.timeCube) := hθ.2.2.1.sub hM.2.2.1
  have hH1 : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      AVenhance.IsPeriodicH1With (fun x => θ s x - θM s x) (fun x => Dθ s x - DM s x) := by
    filter_upwards [hθ.2.2.2.2.1, hM.2.2.2.2.1] with s h1 h2
    exact isPeriodicH1With_sub h1 h2
  have hzero := drift_pairing_region_zero (w := fun t x => θ t x - θM t x)
    (Dw := fun t x => Dθ t x - DM t x) hw hDw hH1 hb_meas hb_bdd hb_per hdiv ht
  have hregion : weakEnergyRegion t ⊆ AVenhance.timeCube := weakEnergy_region_subset_timeCube ht
  have hμ : volume.restrict (weakEnergyRegion t) ≤ volume.restrict AVenhance.timeCube :=
    Measure.restrict_mono hregion le_rfl
  have hGmem : MemLp (fun p : ℝ × Vec 2 =>
      Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2)) 2
      (volume.restrict AVenhance.timeCube) :=
    forced_drift_memLp_two (b := b) (Dw := fun t x => Dθ t x - DM t x) hDw hb_meas hb_bdd
  have hI1 : Integrable (fun p : ℝ × Vec 2 =>
      Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2) *
        (θ p.1 p.2 - θM p.1 p.2)) (volume.restrict (weakEnergyRegion t)) :=
    (weak_product_integrable_timeCube hGmem hw).mono_measure hμ
  have hI2 : Integrable (fun p : ℝ × Vec 2 =>
      Homogenization.vecDot (Dθ p.1 p.2 - DM p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2))
      (volume.restrict (weakEnergyRegion t)) :=
    (forced_vecDot_integrable_fields (Y := fun p => Dθ p.1 p.2 - DM p.1 p.2)
      (Z := fun p => Dθ p.1 p.2 - DM p.1 p.2) hDw hDw).mono_measure hμ
  have hI3 : Integrable (fun p : ℝ × Vec 2 =>
      Homogenization.vecDot (F p) (Dθ p.1 p.2 - DM p.1 p.2))
      (volume.restrict (weakEnergyRegion t)) :=
    (forced_vecDot_integrable_fields (Y := F) (Z := fun p => Dθ p.1 p.2 - DM p.1 p.2)
      hF hDw).mono_measure hμ
  have hsplit : ∫ p in weakEnergyRegion t,
      (Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2) *
          (θ p.1 p.2 - θM p.1 p.2) +
        κ * Homogenization.vecDot (Dθ p.1 p.2 - DM p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2) +
        Homogenization.vecDot (F p) (Dθ p.1 p.2 - DM p.1 p.2)) =
      0 + κ * (∫ p in weakEnergyRegion t,
        Homogenization.vecDot (Dθ p.1 p.2 - DM p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2)) +
      ∫ p in weakEnergyRegion t, Homogenization.vecDot (F p) (Dθ p.1 p.2 - DM p.1 p.2) := by
    have hA : Integrable (fun p : ℝ × Vec 2 =>
        Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2) *
          (θ p.1 p.2 - θM p.1 p.2) +
        κ * Homogenization.vecDot (Dθ p.1 p.2 - DM p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2))
        (volume.restrict (weakEnergyRegion t)) := hI1.add (hI2.const_mul κ)
    rw [integral_add hA hI3, integral_add hI1 (hI2.const_mul κ), integral_const_mul, hzero]
  have hl2 : AVenhance.l2NormSq (fun _ : Vec 2 => (0 : ℝ)) = 0 := by
    simp [AVenhance.l2NormSq]
  rw [hl2] at hGE
  have hGE' : AVenhance.l2NormSq (fun x => θ t x - θM t x) + 2 * (∫ p in weakEnergyRegion t,
      (Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2) *
          (θ p.1 p.2 - θM p.1 p.2) +
        κ * Homogenization.vecDot (Dθ p.1 p.2 - DM p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2) +
        Homogenization.vecDot (F p) (Dθ p.1 p.2 - DM p.1 p.2))) = 0 := hGE
  rw [hsplit] at hGE'
  linarith

end AVenhance.Infra.Section5.RelativeError

end
