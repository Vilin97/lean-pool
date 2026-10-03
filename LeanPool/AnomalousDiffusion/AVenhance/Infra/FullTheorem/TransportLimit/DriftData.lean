/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.TransportLimit.Cancellation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.WeakEnergyPassage
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.TimeDependentFourierTest
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FullTheorem.IsTransportWeakSolution

/-!
# Measurability and bounds for the transport pairing against a test function

The hypotheses on the drift `b` (jointly measurable, bounded, periodic, divergence free) are
packaged as `DriftHyp`.  For a test function `φ`, the pairing `b·∇φ` is measurable and
bounded on the space-time cell, so it is square integrable there.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

noncomputable section

namespace AVenhance.Infra.FullTheorem.TransportLimit

open AVenhance.Infra.Parabolic.WeakUniqueness

/-- The standing hypotheses on the drift. -/
structure DriftHyp (b : ℝ → Vec 2 → Vec 2) : Prop where
  meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
    (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))
  bdd : ∃ B : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ B
  per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (b t)
  div : IsDivFree b

theorem timeCube_measurableSet' : MeasurableSet timeCube := by
  rw [timeCube]
  exact measurableSet_Ioo.prod unitCube_measurableSet'

instance transportFiniteUnitCube : IsFiniteMeasure (volume.restrict unitCube) := by
  refine ⟨?_⟩
  unfold unitCube
  rw [Measure.restrict_apply_univ, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

instance transportFiniteTimeCube : IsFiniteMeasure (volume.restrict timeCube) := by
  have hI : IsFiniteMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Ioo]⟩
  rw [weakEnergy_timeCube_measure_eq_product]
  infer_instance

theorem timeCube_subset_Icc : timeCube ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.univ :=
  fun _ hp => ⟨⟨hp.1.1.le, hp.1.2.le⟩, Set.mem_univ _⟩

theorem DriftHyp.meas_timeCube {b : ℝ → Vec 2 → Vec 2} (h : DriftHyp b) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2) (volume.restrict timeCube) :=
  h.meas.mono_set timeCube_subset_Icc

/-- Pointwise bound on the drift over the space-time cell. -/
theorem DriftHyp.bound_timeCube {b : ℝ → Vec 2 → Vec 2} (h : DriftHyp b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ timeCube, ‖b p.1 p.2‖ ≤ B := by
  obtain ⟨B, hB⟩ := h.bdd
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩ 0)
  exact ⟨B, hB0, fun p hp => hB p.1 ⟨hp.1.1.le, hp.1.2.le⟩ p.2⟩

theorem spaceGrad_spacetime_continuous {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2)) :
    Continuous (fun p : ℝ × Vec 2 => spaceGrad (φ p.1) p.2) := by
  apply continuous_pi
  intro i
  have hFderiv : Continuous (fderiv ℝ (fun p : ℝ × Vec 2 => φ p.1 p.2)) :=
    hφ.continuous_fderiv (by simp)
  have hcont : Continuous (fun p : ℝ × Vec 2 =>
      (fderiv ℝ (fun q : ℝ × Vec 2 => φ q.1 q.2) p) (0, basisVec i)) :=
    hFderiv.clm_apply continuous_const
  have heq (p : ℝ × Vec 2) :
      spaceGrad (φ p.1) p.2 i =
        (fderiv ℝ (fun q : ℝ × Vec 2 => φ q.1 q.2) p) (0, basisVec i) := by
    let F : ℝ × Vec 2 → ℝ := fun q => φ q.1 q.2
    have houter : HasFDerivAt F (fderiv ℝ F (p.1, p.2)) (p.1, p.2) :=
      (hφ.differentiable (by simp) (p.1, p.2)).hasFDerivAt
    have hline : HasFDerivAt (fun x : Vec 2 => (p.1, x))
        (ContinuousLinearMap.inr ℝ ℝ (Vec 2)) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have hcomp := HasFDerivAt.comp p.2 houter hline
    have hlineEval : ContinuousLinearMap.inr ℝ ℝ (Vec 2) (basisVec i) = (0, basisVec i) := by
      simp [ContinuousLinearMap.inr]
    change fderiv ℝ (F ∘ fun x : Vec 2 => (p.1, x)) p.2 (basisVec i) = _
    rw [hcomp.fderiv]
    simp [ContinuousLinearMap.comp_apply, hlineEval]
    rfl
  exact hcont.congr fun p => (heq p).symm

/-- Coordinatewise bound for the spatial gradient of a test function on the cell. -/
theorem grad_bound {φ : ℝ → Vec 2 → ℝ} (hφ : IsTestFunction φ) :
    ∃ Cg : Fin 2 → ℝ, ∀ i, 0 ≤ Cg i ∧
      ∀ p ∈ timeCube, |spaceGrad (φ p.1) p.2 i| ≤ Cg i := by
  have hgc := spaceGrad_spacetime_continuous hφ.1
  have h : ∀ i : Fin 2, ∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ timeCube, |spaceGrad (φ p.1) p.2 i| ≤ C := fun i => by
    obtain ⟨C, hC0, hC⟩ := weak_continuous_timeCube_bound ((continuous_apply i).comp hgc)
    exact ⟨C, hC0, fun p hp => by simpa [Real.norm_eq_abs] using hC p hp⟩
  choose Cg h0 h1 using h
  exact ⟨Cg, fun i => ⟨h0 i, h1 i⟩⟩

/-- The pairing `b·∇φ` is measurable and bounded on the space-time cell. -/
theorem transport_grad_term {b : ℝ → Vec 2 → Vec 2} (h : DriftHyp b) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsTestFunction φ) :
    ∃ Gb : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Vec 2 => vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2))
        (volume.restrict timeCube) ∧
      ∀ p ∈ timeCube, |vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2)| ≤ Gb := by
  obtain ⟨Cg, hCg⟩ := grad_bound hφ
  obtain ⟨B, hB0, hB⟩ := h.bound_timeCube
  have hgc := spaceGrad_spacetime_continuous hφ.1
  refine ⟨∑ i : Fin 2, B * Cg i, ?_, ?_⟩
  · have hmeas (i : Fin 2) : AEStronglyMeasurable
        (fun p : ℝ × Vec 2 => b p.1 p.2 i * spaceGrad (φ p.1) p.2 i)
        (volume.restrict timeCube) :=
      ((continuous_apply i).comp_aestronglyMeasurable h.meas_timeCube).mul
        ((continuous_apply i).comp hgc).aestronglyMeasurable
    exact Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin 2))
      (fun i _ => hmeas i)
  · intro p hp
    have hterm (i : Fin 2) : |b p.1 p.2 i * spaceGrad (φ p.1) p.2 i| ≤ B * Cg i := by
      rw [abs_mul]
      have h1 : |b p.1 p.2 i| ≤ B := by
        have := norm_le_pi_norm (b p.1 p.2) i
        rw [Real.norm_eq_abs] at this
        exact this.trans (hB p hp)
      exact mul_le_mul h1 ((hCg i).2 p hp) (abs_nonneg _) hB0
    calc |vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2)|
        = |∑ i : Fin 2, b p.1 p.2 i * spaceGrad (φ p.1) p.2 i| := rfl
      _ ≤ ∑ i : Fin 2, |b p.1 p.2 i * spaceGrad (φ p.1) p.2 i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 2, B * Cg i := Finset.sum_le_sum fun i _ => hterm i

/-- A measurable function bounded on the space-time cell is square integrable there. -/
theorem memLp_two_of_bdd_timeCube {F : ℝ × Vec 2 → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict timeCube)) {C : ℝ}
    (hC : ∀ p ∈ timeCube, |F p| ≤ C) : MemLp F 2 (volume.restrict timeCube) := by
  apply MemLp.of_bound hF C
  filter_upwards [ae_restrict_mem timeCube_measurableSet'] with p hp
  simpa [Real.norm_eq_abs] using hC p hp

/-- The product of a square-integrable function with a bounded measurable one is integrable. -/
theorem integrable_mul_bdd_timeCube {F G : ℝ × Vec 2 → ℝ}
    (hF : MemLp F 2 (volume.restrict timeCube))
    (hG : AEStronglyMeasurable G (volume.restrict timeCube)) {C : ℝ}
    (hC : ∀ p ∈ timeCube, |G p| ≤ C) :
    Integrable (fun p => F p * G p) (volume.restrict timeCube) := by
  have hFi : Integrable F (volume.restrict timeCube) := hF.integrable (by norm_num)
  refine hFi.mul_bdd hG (c := C) ?_
  filter_upwards [ae_restrict_mem timeCube_measurableSet'] with p hp
  simpa [Real.norm_eq_abs] using hC p hp

end AVenhance.Infra.FullTheorem.TransportLimit
