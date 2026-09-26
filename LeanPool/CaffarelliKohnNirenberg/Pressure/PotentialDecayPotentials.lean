/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecay
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecayFarField

/-!
# Linear growth of the pressure potentials

Combining the far-field decay of Newtonian potentials of compactly supported
data with the ball estimate for the radial weight `‖x‖ ^ (-3/2)` gives, for each
of the three potential shapes `N * g`, `∂ⱼN * g` and `∂ᵢ∂ⱼN * g`, exactly the
pair of hypotheses consumed by the Liouville theorem
`CKN.Foundation.Heat.weaklyHarmonicOn_eq_zero_of_lpNorm_linear_growth`: local
`L^{3/2}` membership on every round ball about the origin, and a growth bound of
the form `C * (1 + ρ)`.  This is the decay-at-infinity input to the uniqueness
half of the Newtonian representation `ext:newtonian` of the paper.

The local `L^{3/2}` hypothesis near the origin is left to the consumer: for the
zeroth-order potential it follows from local integrability of the kernel, and for
the derivative potentials it is the Calderón–Zygmund bound.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat


noncomputable section

namespace CKN

/-- The first-derivative Newtonian potential of integrable data supported in the
closed ball of radius `R` about `x₀` satisfies the Liouville growth hypotheses. -/
theorem memLp_and_lpNorm_linear_growth_pressureNewtonianDerivativePotential
    {g : Vec3 → ℝ} (hg : Integrable g volume) {x₀ : Vec3} {R : ℝ} (hR : 0 < R)
    (hSupp : tsupport g ⊆ Metric.closedBall x₀ R) (i : Fin 3)
    (hmeas : AEStronglyMeasurable (pressureNewtonianDerivativePotential i g)
      volume)
    (hnear : MemLp (pressureNewtonianDerivativePotential i g)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (Metric.ball (0 : Vec3) (2 * (2 * R + 2 * ‖x₀‖))))) :
    (∀ ρ : ℝ, 0 < ρ → MemLp (pressureNewtonianDerivativePotential i g)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ →
        lpNorm (pressureNewtonianDerivativePotential i g)
            (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
          invNormGrowthConstant (pressureNewtonianDerivativePotential i g)
              (2 * (4 * (4 * Real.pi)⁻¹ * (∫ y, |g y|) / (2 * R)))
              (2 * R + 2 * ‖x₀‖) * (1 + ρ) := by
  have hmass : (0 : ℝ) ≤ ∫ y, |g y| :=
    integral_nonneg (fun y => abs_nonneg (g y))
  have hA : (0 : ℝ) ≤ 4 * (4 * Real.pi)⁻¹ * ∫ y, |g y| :=
    mul_nonneg (by positivity) hmass
  have hM : (0 : ℝ) ≤ 4 * (4 * Real.pi)⁻¹ * (∫ y, |g y|) / (2 * R) := by
    have h2R : (0 : ℝ) < 2 * R := by linarith only [hR]
    exact div_nonneg hA h2R.le
  have hdiv : ∀ x : Vec3, 2 * R ≤ ‖x - x₀‖ →
      |pressureNewtonianDerivativePotential i g x| ≤
        4 * (4 * Real.pi)⁻¹ * (∫ y, |g y|) / ‖x - x₀‖ ^ 2 := by
    intro x hx
    refine (pressureNewtonianDerivativePotential_tail_bound_centre hg hR hSupp i
      hx).trans_eq ?_
    rw [div_mul_eq_mul_div]
  exact memLp_and_lpNorm_linear_growth_of_inv_norm_decay_centre hM hR hmeas hnear
    (inv_norm_decay_of_div_norm_sq hR hA hdiv)

end CKN
