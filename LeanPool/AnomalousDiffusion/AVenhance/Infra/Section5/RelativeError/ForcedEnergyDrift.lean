/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyStatic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyModes

/-!
# Divergence-free transport cancellation along a path

For a bounded measurable divergence-free periodic drift and a path that is periodic `H¹` for almost
every time, the transport pairing `∫ b·Dw w` vanishes on every truncated time cell. This is the
statement of `weak_solution_divFree_drift_pairing_zero` without the weak-equation hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Torus
open AVenhance.Infra.Parabolic.WeakUniqueness

local instance driftFiniteUnitCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  unfold AVenhance.unitCube
  rw [Measure.restrict_apply_univ, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance driftFiniteTimeCube : IsFiniteMeasure (volume.restrict AVenhance.timeCube) := by
  rw [forced_timeCube_measure_eq_product]
  infer_instance

theorem ForcedEnergyDrift.drift_openCylinder_measure :
    (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set (Vec 2)))) =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume : Measure (Vec 2)) := by
  have h := Measure.restrict_prod_eq_prod_univ
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Vec 2)))
    (s := Set.Ioo (0 : ℝ) 1)
  rw [← Measure.volume_eq_prod ℝ (Vec 2)] at h
  exact h.symm

/-- The transport density of a bounded drift against an `L²` gradient is in `L²`. -/
theorem forced_drift_memLp_two {b : ℝ → Vec 2 → Vec 2} {Dw : ℝ → Vec 2 → Vec 2}
    (hDw : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dw p.1 p.2 i) 2
      (volume.restrict AVenhance.timeCube))
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C) :
    MemLp (fun p : ℝ × Vec 2 => Homogenization.vecDot (b p.1 p.2) (Dw p.1 p.2))
      2 (volume.restrict AVenhance.timeCube) := by
  obtain ⟨C, hC⟩ := hb_bdd
  have hsub : AVenhance.timeCube ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.univ := by
    intro p hp
    exact ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, Set.mem_univ _⟩
  have hb := hb_meas.mono_set hsub
  have hcoordMeas (i : Fin 2) : AEStronglyMeasurable
      (fun p : ℝ × Vec 2 => b p.1 p.2 i) (volume.restrict AVenhance.timeCube) :=
    (continuous_apply i).comp_aestronglyMeasurable hb
  have hcoordMem (i : Fin 2) : MemLp
      (fun p : ℝ × Vec 2 => b p.1 p.2 i) ⊤ (volume.restrict AVenhance.timeCube) := by
    apply MemLp.of_bound (hcoordMeas i) C
    filter_upwards [ae_restrict_mem forced_timeCube_measurable] with p hp
    have hbound := hC p.1 ⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩ p.2
    have hi := (pi_norm_le_iff_of_nonempty (b p.1 p.2)).1 hbound i
    simpa [Real.norm_eq_abs] using hi
  have hterm (i : Fin 2) : MemLp
      (fun p : ℝ × Vec 2 => b p.1 p.2 i * Dw p.1 p.2 i) 2
      (volume.restrict AVenhance.timeCube) := (hcoordMem i).mul (hDw i)
  have hsum := (hterm 0).add (hterm 1)
  have heq : (fun p : ℝ × Vec 2 => Homogenization.vecDot (b p.1 p.2) (Dw p.1 p.2)) =
      fun p => b p.1 p.2 0 * Dw p.1 p.2 0 + b p.1 p.2 1 * Dw p.1 p.2 1 := by
    funext p
    simp [Homogenization.vecDot, Fin.sum_univ_succ]
  rw [heq]
  exact hsum

/-- Divergence-free transport cancels on every truncated time cell for an `H¹` path. -/
theorem drift_pairing_region_zero
    {b : ℝ → Vec 2 → Vec 2} {w : ℝ → Vec 2 → ℝ} {Dw : ℝ → Vec 2 → Vec 2}
    (hw : MemLp (fun p : ℝ × Vec 2 => w p.1 p.2) 2 (volume.restrict AVenhance.timeCube))
    (hDw : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dw p.1 p.2 i) 2
      (volume.restrict AVenhance.timeCube))
    (hH1 : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      AVenhance.IsPeriodicH1With (w s) (Dw s))
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, AVenhance.IsZ2Periodic (b t))
    (hdiv : AVenhance.IsDivFree b)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ p in weakEnergyRegion t,
      Homogenization.vecDot (b p.1 p.2) (Dw p.1 p.2) * w p.1 p.2 = 0 := by
  let drift : ℝ × Vec 2 → ℝ := fun p =>
    Homogenization.vecDot (b p.1 p.2) (Dw p.1 p.2)
  let value : ℝ × Vec 2 → ℝ := fun p => w p.1 p.2
  let pairing : ℝ → ℝ := fun s =>
    ∫ x in AVenhance.unitCube, drift (s, x) * value (s, x)
  have hdrift : MemLp drift 2 (volume.restrict AVenhance.timeCube) :=
    forced_drift_memLp_two hDw hb_meas hb_bdd
  have hproduct : Integrable (fun p => drift p * value p)
      (volume.restrict AVenhance.timeCube) :=
    weak_product_integrable_timeCube hdrift hw
  have hspaceMeas : AEStronglyMeasurable
      (fun p : ℝ × Vec 2 => b p.1 p.2)
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (volume : Measure (Vec 2))) := by
    have hopen : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
        (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set (Vec 2)))) :=
      hb_meas.mono_measure (Measure.restrict_mono
        (Set.prod_mono Set.Ioo_subset_Icc_self (subset_rfl)) le_rfl)
    rw [← ForcedEnergyDrift.drift_openCylinder_measure]
    exact hopen
  have hslice := hspaceMeas.prodMk_left
  have hpairingZero : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), pairing s = 0 := by
    filter_upwards [hslice, hH1, ae_restrict_mem measurableSet_Ioo]
      with s hbs hH1s hsOpen
    have hs : s ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hsOpen.1, le_of_lt hsOpen.2⟩
    obtain ⟨C, hC⟩ := hb_bdd
    have hCnonneg : 0 ≤ C := le_trans (norm_nonneg (b s 0)) (hC s hs 0)
    have hBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b s x‖ ≤ C := ⟨C, hCnonneg, hC s hs⟩
    have hperiodic : AVenhance.IsZ2Periodic (b s) := hb_per s hs
    have hdivSmooth : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
        AVenhance.IsZ2Periodic ψ →
        ∫ x in unitCell 2, Homogenization.vecDot (b s x)
          (AVenhance.spaceGrad ψ x) = 0 := by
      intro ψ hψ hψper
      exact isDivFree_integral_periodic_smooth_test hbs hBound hperiodic
        (fun φ hφ hcompact => hdiv s hs φ hφ hcompact) hψ hψper
    have hzero := static_divFree_h1_cancellation hbs hBound hdivSmooth hH1s
    change (∫ x in unitCell 2,
      Homogenization.vecDot (b s x) (Dw s x) * w s x) = 0 at hzero
    rw [integral_unitCell_eq_unitCube] at hzero
    simpa [pairing, drift, value] using hzero
  have hregionZero : ∫ s in Set.Ioo (0 : ℝ) t, pairing s = 0 := by
    have hμ : volume.restrict (Set.Ioo (0 : ℝ) t) ≤
        volume.restrict (Set.Ioo (0 : ℝ) 1) :=
      Measure.restrict_mono (by
        intro s hs
        rcases hs with ⟨hs0, hst⟩
        exact ⟨hs0, lt_of_lt_of_le hst ht.2⟩) le_rfl
    have hzero : pairing =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) t)] 0 :=
      hpairingZero.filter_mono (MeasureTheory.ae_mono hμ)
    calc
      ∫ s in Set.Ioo (0 : ℝ) t, pairing s =
          ∫ s, pairing s ∂(volume.restrict (Set.Ioo (0 : ℝ) t)) := rfl
      _ = 0 := integral_eq_zero_of_ae hzero
  have htimeZero : ∫ s in (0 : ℝ)..t, pairing s = 0 := by
    rw [← weakEnergy_Ioo_intervalIntegral ht.1]
    exact hregionZero
  rw [weakEnergy_region_integral_eq_interval hproduct ht]
  simpa [pairing, drift, value] using htimeZero

end AVenhance.Infra.Section5.RelativeError

end
