/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyBalance
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyStreamAux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyStreamReal

/-!
# The stream-difference estimate

For a weak solution `θ` of the limit drift `b = σ∇φ` and the classical solution `θ_M` for a smooth
stream `Ψ` with the same datum and diffusivity, the difference satisfies the energy balance with the
skew flux `(φ - Ψ) σ∇θ_M`; Cauchy–Schwarz then gives the `η/κ` bound on the dissipation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Parabolic.WeakUniqueness

local instance streamFiniteUnitCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  unfold AVenhance.unitCube
  rw [Measure.restrict_apply_univ, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance streamFiniteTimeCube :
    IsFiniteMeasure (volume.restrict AVenhance.timeCube) := by
  rw [forced_timeCube_measure_eq_product]
  infer_instance

/-- The gradient coordinates of a stream with bounded velocity are bounded. -/
theorem stream_grad_bound {φ : ℝ → Vec 2 → ℝ} {C : ℝ} {s : ℝ}
    (hC : ∀ x, ‖AVenhance.streamVel φ s x‖ ≤ C) (i : Fin 2) :
    ∃ C' : ℝ, ∀ x, |AVenhance.spaceGrad (φ s) x i| ≤ C' := by
  refine ⟨C, fun x => ?_⟩
  have h : ∀ j : Fin 2, |AVenhance.streamVel φ s x j| ≤ C := fun j => by
    have := norm_le_pi_norm (AVenhance.streamVel φ s x) j
    rw [Real.norm_eq_abs] at this
    exact this.trans (hC x)
  fin_cases i
  · have := h 1
    simpa [AVenhance.streamVel, sigmaMat_mulVec_apply_one] using this
  · have := h 0
    simpa [AVenhance.streamVel, sigmaMat_mulVec_apply_zero, abs_neg] using this

/-- The difference of the stream velocities is the skew gradient of the stream difference. -/
theorem streamVel_sub_eq {φ Ψ : ℝ → Vec 2 → ℝ} {s : ℝ} (hφ : Differentiable ℝ (φ s))
    (hΨ : Differentiable ℝ (Ψ s)) (x : Vec 2) :
    AVenhance.streamVel φ s x - AVenhance.streamVel Ψ s x =
      AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (fun y => φ s y - Ψ s y) x) := by
  funext i
  fin_cases i
  · change AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (φ s) x) 0 -
      AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (Ψ s) x) 0 =
        AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (fun y => φ s y - Ψ s y) x) 0
    rw [sigmaMat_mulVec_apply_zero, sigmaMat_mulVec_apply_zero, sigmaMat_mulVec_apply_zero,
      spaceGrad_sub_apply hφ hΨ]
    ring
  · change AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (φ s) x) 1 -
      AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (Ψ s) x) 1 =
        AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (fun y => φ s y - Ψ s y) x) 1
    rw [sigmaMat_mulVec_apply_one, sigmaMat_mulVec_apply_one, sigmaMat_mulVec_apply_one,
      spaceGrad_sub_apply hφ hΨ]

/-- A fixed-time slice of the stream difference satisfies the flux representation of the cross
transport against smooth periodic tests. -/
theorem stream_flux_slice {φ Ψ : ℝ → Vec 2 → ℝ} {s : ℝ} {C : ℝ}
    (hφd : Differentiable ℝ (φ s)) (hφp : AVenhance.IsZ2Periodic (φ s))
    (hC : ∀ x, ‖AVenhance.streamVel φ s x‖ ≤ C)
    (hΨ : AVenhance.IsAdmissibleStream Ψ) {θ ψ : Vec 2 → ℝ}
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθp : AVenhance.IsZ2Periodic θ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : AVenhance.IsZ2Periodic ψ) :
    IntegrableOn (fun x => vecDot (AVenhance.streamVel φ s x - AVenhance.streamVel Ψ s x)
      (AVenhance.spaceGrad θ x) * ψ x) AVenhance.unitCube ∧
    ∫ x in AVenhance.unitCube,
        vecDot (AVenhance.streamVel φ s x - AVenhance.streamVel Ψ s x)
          (AVenhance.spaceGrad θ x) * ψ x =
      ∫ x in AVenhance.unitCube, vecDot
        (fun i => (φ s x - Ψ s x) * AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad θ x) i)
        (AVenhance.spaceGrad ψ x) := by
  have hΨd : Differentiable ℝ (Ψ s) := (admissible_slice_contDiff hΨ s).differentiable (by simp)
  have hξd : Differentiable ℝ (fun y => φ s y - Ψ s y) := hφd.sub hΨd
  have hξp : AVenhance.IsZ2Periodic (fun y => φ s y - Ψ s y) := by
    intro k x
    change φ s (x + _) - Ψ s (x + _) = φ s x - Ψ s x
    rw [hφp k x, admissible_slice_periodic hΨ s k x]
  have hξb : ∀ i : Fin 2, ∃ C : ℝ, ∀ x, |AVenhance.spaceGrad (fun y => φ s y - Ψ s y) x i| ≤ C := by
    intro i
    obtain ⟨C1, h1⟩ := stream_grad_bound hC i
    obtain ⟨C2, h2⟩ := smooth_periodic_grad_bound (admissible_slice_contDiff hΨ s)
      (admissible_slice_periodic hΨ s) i
    refine ⟨C1 + C2, fun x => ?_⟩
    rw [spaceGrad_sub_apply hφd hΨd]
    exact (abs_sub _ _).trans (add_le_add (h1 x) (h2 x))
  have := skew_flux_slice hξd hξp hξb hθ hθp hψ hψp
  simp only [streamVel_sub_eq hφd hΨd]
  exact this

end AVenhance.Infra.Section5.RelativeError

end
