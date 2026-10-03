/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.TransportLimit.Passage

/-!
# The limit satisfies the transport weak form
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

noncomputable section

namespace AVenhance.Infra.FullTheorem.TransportLimit

open AVenhance.Infra.Parabolic.WeakUniqueness

theorem limit_weak_form {b : ℝ → Vec 2 → Vec 2} (h : DriftHyp b)
    {θ₀ : Vec 2 → ℝ} (hθ₀ : MemL2On unitCube θ₀)
    {κ : ℕ → ℝ} (hκ : ∀ j, 0 < κ j) (hκ0 : Tendsto κ atTop (𝓝 0))
    {θ : ℕ → ℝ → Vec 2 → ℝ} {Dθ : ℕ → ℝ → Vec 2 → Vec 2}
    (hu : ∀ j, IsWeakSolutionGrad b (κ j) θ₀ (θ j) (Dθ j))
    {Θ : ℝ → Vec 2 → ℝ} (hΘ : MemLp (fun p : ℝ × Vec 2 => Θ p.1 p.2) 2 (volume.restrict timeCube))
    (hunif : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j ≥ N, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θ j t x - Θ t x)) ≤ η)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsTestFunction φ) :
    Integrable (fun p : ℝ × Vec 2 =>
      Θ p.1 p.2 * vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2)) (volume.restrict timeCube) ∧
    ∫ p in timeCube,
      (-(Θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
        - Θ p.1 p.2 * vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2))
      = ∫ x in unitCube, θ₀ x * φ 0 x := by
  obtain ⟨Cg, hCg⟩ := grad_bound hφ
  obtain ⟨Gb, hGm, hGb⟩ := transport_grad_term h hφ
  refine ⟨integrable_mul_bdd_timeCube hΘ hGm hGb, ?_⟩
  have hq := time_derivative_continuous hφ
  let hh : ℝ × Vec 2 → ℝ := fun p =>
    deriv (fun s => φ s p.2) p.1 + vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2)
  have hhL : MemLp hh 2 (volume.restrict timeCube) :=
    (weak_continuous_memLp_two_timeCube hq).add (memLp_two_of_bdd_timeCube hGm hGb)
  have lhs_eq : ∀ f : ℝ → Vec 2 → ℝ, ∫ p in timeCube,
      (-(f p.1 p.2) * deriv (fun s => φ s p.2) p.1
        - f p.1 p.2 * vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2)) =
      -∫ p in timeCube, f p.1 p.2 * hh p := by
    intro f
    rw [← integral_neg]
    congr 1; funext p
    simp only [hh]; ring
  set Mh := Real.sqrt (∫ p in timeCube, hh p ^ 2) with hMh
  have hMh0 : 0 ≤ Mh := Real.sqrt_nonneg _
  -- convergence of the pairings against `hh`
  have hconv : Tendsto (fun j => ∫ p in timeCube, θ j p.1 p.2 * hh p) atTop
      (𝓝 (∫ p in timeCube, Θ p.1 p.2 * hh p)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hunif (ε / (2 * (Mh + 1))) (by positivity)
    refine ⟨N, fun j hj => ?_⟩
    have hθj : MemLp (fun p : ℝ × Vec 2 => θ j p.1 p.2) 2 (volume.restrict timeCube) :=
      (hu j).2.2.1
    have hdm : MemLp (fun p : ℝ × Vec 2 => θ j p.1 p.2 - Θ p.1 p.2) 2
        (volume.restrict timeCube) := hθj.sub hΘ
    have hdiff : (∫ p in timeCube, θ j p.1 p.2 * hh p) - ∫ p in timeCube, Θ p.1 p.2 * hh p =
        ∫ p in timeCube, (θ j p.1 p.2 - Θ p.1 p.2) * hh p := by
      rw [← integral_sub (weak_product_integrable_timeCube hθj hhL)
        (weak_product_integrable_timeCube hΘ hhL)]
      congr 1; funext p; ring
    have hnorm : Real.sqrt (∫ p in timeCube, (θ j p.1 p.2 - Θ p.1 p.2) ^ 2) ≤
        ε / (2 * (Mh + 1)) := by
      apply sqrt_integral_sq_le_of_eLpNorm_le hdm (by positivity)
      apply joint_eLpNorm_le hdm (by positivity)
      intro t ht
      exact hN j hj t ⟨ht.1.le, ht.2.le⟩
    rw [Real.dist_eq, hdiff]
    calc |∫ p in timeCube, (θ j p.1 p.2 - Θ p.1 p.2) * hh p|
        ≤ Real.sqrt (∫ p in timeCube, (θ j p.1 p.2 - Θ p.1 p.2) ^ 2) * Mh :=
          l2_pairing_bound hdm hhL
      _ ≤ ε / (2 * (Mh + 1)) * Mh := mul_le_mul_of_nonneg_right hnorm hMh0
      _ ≤ ε / (2 * (Mh + 1)) * (Mh + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  -- convergence of the left-hand sides to the initial datum
  have hvisc : Tendsto (fun j => ∫ p in timeCube,
      (-(θ j p.1 p.2) * deriv (fun s => φ s p.2) p.1
        - θ j p.1 p.2 * vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2))) atTop
      (𝓝 (∫ x in unitCube, θ₀ x * φ 0 x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hs : Tendsto (fun j => Real.sqrt (κ j) / 2 * (l2NormSq θ₀ / 2 +
        ∑ i : Fin 2, (volume.restrict timeCube).real Set.univ * Cg i ^ 2)) atTop (𝓝 0) := by
      have := ((Real.continuous_sqrt.tendsto 0).comp hκ0).div_const 2 |>.mul_const
        (l2NormSq θ₀ / 2 + ∑ i : Fin 2, (volume.restrict timeCube).real Set.univ * Cg i ^ 2)
      simpa using this
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hs
    rw [Real.norm_eq_abs]
    exact solution_viscous_error h (hκ j) hθ₀ (hu j) hφ (fun i p hp => (hCg i).2 p hp)
  have hneg := hconv.neg
  have hvisc' : Tendsto (fun j => -∫ p in timeCube, θ j p.1 p.2 * hh p) atTop
      (𝓝 (∫ x in unitCube, θ₀ x * φ 0 x)) := by
    refine hvisc.congr fun j => ?_
    exact lhs_eq (θ j)
  rw [lhs_eq Θ]
  exact tendsto_nhds_unique hneg hvisc'

end AVenhance.Infra.FullTheorem.TransportLimit
