/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.TransportLimit.SolutionForm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.TransportLimit.KappaBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.DivergenceFreeEnergy

/-!
# Quantitative viscous error for weak solutions

For a weak solution with divergence-free drift and diffusivity `κ > 0`,
`|∫∫ (-θ ∂ₜφ - θ b·∇φ) - ∫ θ₀ φ(0)| ≤ (√κ/2) (‖θ₀‖²/2 + ∑ᵢ V Cᵢ²)`, where `Cᵢ` bounds `∂ᵢφ`
on the cell and `V` is the volume of the space-time cell.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

noncomputable section

namespace AVenhance.Infra.FullTheorem.TransportLimit

open AVenhance.Infra.Parabolic.WeakUniqueness

theorem solution_viscous_error {b : ℝ → Vec 2 → Vec 2} (h : DriftHyp b)
    {κ : ℝ} (hκ : 0 < κ) {θ₀ : Vec 2 → ℝ} (hθ₀ : MemL2On unitCube θ₀)
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hu : IsWeakSolutionGrad b κ θ₀ θ Dθ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsTestFunction φ)
    {Cg : Fin 2 → ℝ}
    (hCg : ∀ i, ∀ p ∈ timeCube, |spaceGrad (φ p.1) p.2 i| ≤ Cg i) :
    |(∫ p in timeCube,
      (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
        - θ p.1 p.2 * vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2))) -
        ∫ x in unitCube, θ₀ x * φ 0 x| ≤
      Real.sqrt κ / 2 * (l2NormSq θ₀ / 2 +
        ∑ i : Fin 2, (volume.restrict timeCube).real Set.univ * Cg i ^ 2) := by
  rw [solution_transport_form h hu hφ]
  have hgc := spaceGrad_spacetime_continuous hφ.1
  have hG (i : Fin 2) : MemLp (fun p : ℝ × Vec 2 => spaceGrad (φ p.1) p.2 i) 2
      (volume.restrict timeCube) :=
    weak_continuous_memLp_two_timeCube ((continuous_apply i).comp hgc)
  have hk := kappa_term_bound (D := fun p => Dθ p.1 p.2) (G := fun p => spaceGrad (φ p.1) p.2)
    hu.2.2.2.1 hG hκ
  have henergy := weak_solution_divFree_energy_identity hu hθ₀ h.meas h.bdd h.per h.div
    1 ⟨zero_le_one, le_rfl⟩
  have hnn : 0 ≤ l2NormSq (θ 1) := integral_nonneg fun x => sq_nonneg _
  have hE : κ * ∫ p in timeCube, vecNormSq (Dθ p.1 p.2) ≤ l2NormSq θ₀ / 2 := by
    change l2NormSq (θ 1) + 2 * κ * (∫ p in timeCube, vecNormSq (Dθ p.1 p.2)) = _ at henergy
    linarith
  have hGint (i : Fin 2) : ∫ p in timeCube, spaceGrad (φ p.1) p.2 i ^ 2 ≤
      (volume.restrict timeCube).real Set.univ * Cg i ^ 2 := by
    have hi : Integrable (fun p : ℝ × Vec 2 => spaceGrad (φ p.1) p.2 i ^ 2)
        (volume.restrict timeCube) :=
      (memLp_two_iff_integrable_sq (hG i).aestronglyMeasurable).1 (hG i)
    calc ∫ p in timeCube, spaceGrad (φ p.1) p.2 i ^ 2
        ≤ ∫ _p in timeCube, Cg i ^ 2 := by
          refine integral_mono_ae hi (integrable_const _) ?_
          filter_upwards [ae_restrict_mem timeCube_measurableSet'] with p hp
          exact sq_le_sq' (abs_le.1 (hCg i p hp)).1 (abs_le.1 (hCg i p hp)).2
      _ = _ := by simp
  have hsum : ∑ i : Fin 2, ∫ p in timeCube, spaceGrad (φ p.1) p.2 i ^ 2 ≤
      ∑ i : Fin 2, (volume.restrict timeCube).real Set.univ * Cg i ^ 2 :=
    Finset.sum_le_sum fun i _ => hGint i
  have hs0 : 0 ≤ Real.sqrt κ / 2 := by positivity
  calc |((∫ x in unitCube, θ₀ x * φ 0 x) -
        κ * ∫ p in timeCube, vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2)) -
        ∫ x in unitCube, θ₀ x * φ 0 x|
      = |κ * ∫ p in timeCube, vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2)| := by
        rw [sub_sub_cancel_left, abs_neg]
    _ ≤ _ := hk.trans (mul_le_mul_of_nonneg_left
      (by linarith : (κ * ∫ p in timeCube, vecNormSq (Dθ p.1 p.2)) +
        ∑ i : Fin 2, ∫ p in timeCube, spaceGrad (φ p.1) p.2 i ^ 2 ≤ l2NormSq θ₀ / 2 +
          ∑ i : Fin 2, (volume.restrict timeCube).real Set.univ * Cg i ^ 2) hs0)

end AVenhance.Infra.FullTheorem.TransportLimit
