/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyPeriodic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergySmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinGenerator
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsAdmissibleStream
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVel

/-!
# Auxiliary facts for the stream-difference estimate

The slice identity `∫ σ∇ξ·∇θ ψ = ∫ ξ σ∇θ·∇ψ` with its integrability, and basic regularity
facts about an admissible stream.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization

namespace AVenhance.Infra.Section5.RelativeError

/-- Cross transport `σ∇ξ·∇θ ψ` is integrable on the cell, and equals the flux pairing
`ξ σ∇θ·∇ψ`. -/
theorem skew_flux_slice {ξ θ ψ : Vec 2 → ℝ}
    (hξ : Differentiable ℝ ξ) (hξp : AVenhance.IsZ2Periodic ξ)
    (hξb : ∀ i : Fin 2, ∃ C : ℝ, ∀ x, |AVenhance.spaceGrad ξ x i| ≤ C)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθp : AVenhance.IsZ2Periodic θ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : AVenhance.IsZ2Periodic ψ) :
    IntegrableOn (fun x => Homogenization.vecDot
      (AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad ξ x)) (AVenhance.spaceGrad θ x) * ψ x)
      AVenhance.unitCube ∧
    ∫ x in AVenhance.unitCube, Homogenization.vecDot
      (AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad ξ x)) (AVenhance.spaceGrad θ x) * ψ x =
    ∫ x in AVenhance.unitCube, Homogenization.vecDot
      (fun i => ξ x * AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad θ x) i)
      (AVenhance.spaceGrad ψ x) := by
  refine ⟨?_, ?_⟩
  · have hθ1 : ContDiff ℝ 1 θ := hθ.of_le (by simp)
    have hψc : Continuous ψ := hψ.continuous
    have hc (i : Fin 2) : Continuous (fun x => AVenhance.spaceGrad θ x i * ψ x) :=
      (spaceGrad_continuous_of_contDiff hθ1 i).mul hψc
    have h0 : IntegrableOn (fun x => AVenhance.spaceGrad ξ x 0 *
        (AVenhance.spaceGrad θ x 1 * ψ x)) AVenhance.unitCube := by
      obtain ⟨C, hC⟩ := hξb 0
      exact integrableOn_unitCube_mul_continuous (measurable_spaceGrad_component ξ 0) hC (hc 1)
    have h1 : IntegrableOn (fun x => AVenhance.spaceGrad ξ x 1 *
        (AVenhance.spaceGrad θ x 0 * ψ x)) AVenhance.unitCube := by
      obtain ⟨C, hC⟩ := hξb 1
      exact integrableOn_unitCube_mul_continuous (measurable_spaceGrad_component ξ 1) hC (hc 0)
    have := h0.sub h1
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Homogenization.vecDot, Fin.sum_univ_two, sigmaMat_mulVec_apply_zero,
      sigmaMat_mulVec_apply_one, Pi.sub_apply]
    ring
  · rw [skew_flux_cell_identity hξ hξp hξb (hθ.of_le (by simp)) hθp (hψ.of_le (by simp)) hψp]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Homogenization.vecDot, Fin.sum_univ_two]
    ring

/-- The coordinates of the gradient of a difference. -/
theorem spaceGrad_sub_apply {f h : Vec 2 → ℝ} (hf : Differentiable ℝ f) (hh : Differentiable ℝ h)
    (x : Vec 2) (i : Fin 2) :
    AVenhance.spaceGrad (fun y => f y - h y) x i =
      AVenhance.spaceGrad f x i - AVenhance.spaceGrad h x i := by
  unfold AVenhance.spaceGrad
  rw [fderiv_fun_sub (hf x) (hh x)]
  rfl

/-- Time slices of an admissible stream are smooth. -/
theorem admissible_slice_contDiff {Ψ : ℝ → Vec 2 → ℝ} (hΨ : AVenhance.IsAdmissibleStream Ψ)
    (s : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (Ψ s) :=
  hΨ.1.comp (contDiff_const.prodMk contDiff_id)

/-- Time slices of an admissible stream are space periodic. -/
theorem admissible_slice_periodic {Ψ : ℝ → Vec 2 → ℝ} (hΨ : AVenhance.IsAdmissibleStream Ψ)
    (s : ℝ) : AVenhance.IsZ2Periodic (Ψ s) := by
  intro k x
  simpa using hΨ.2 0 k s x

/-- Gradient coordinates of a smooth periodic function are globally bounded. -/
theorem smooth_periodic_grad_bound {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f) (i : Fin 2) :
    ∃ C : ℝ, ∀ x, |AVenhance.spaceGrad f x i| ≤ C := by
  obtain ⟨C, _, hC⟩ := AVenhance.Infra.Classical.exists_uniform_bound_of_continuous_periodic
    (fun x => AVenhance.spaceGrad f x i)
    (spaceGrad_continuous_of_contDiff (hf.of_le (by simp)) i)
    (AVenhance.Infra.Classical.periodic_spaceGrad_component hp i)
  exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩

end AVenhance.Infra.Section5.RelativeError

end
