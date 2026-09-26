/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpKernel
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpExponents
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpMeasure

/-!
# Local `L^{3/2}` bounds for Newtonian potentials of compactly supported data

The Newtonian representation `ext:newtonian` of the paper writes the local pressure as a sum of
Newtonian potentials `N * g` and first-derivative potentials `∂ⱼN * g` of compactly supported
data `g`.  The Liouville step needs each of these to be `L^{3/2}` on every ball of
three-dimensional space.

This file supplies the *near-field* half of that statement: Young's inequality on a ball, with
the kernel truncated at the radius `R + ρ` beyond which it cannot be seen by data supported in
the closed ball of radius `R`.

## Exponent arithmetic

Young's inequality `1 + 1/r = 1/q + 1/s` with target `r = 3/2` reads `1/q + 1/s = 5/3`.
The kernel `N` has the size `‖z‖⁻¹`, so its truncation lies in `L^s` exactly for `s < 3`; this
allows every `q ≥ 1`.  The kernel `∂ⱼN` has the size `‖z‖⁻²`, so its truncation lies in `L^s`
exactly for `s < 3/2`; this allows exactly `q > 1`.  Both ranges contain the symmetric choice
`q = s = 6/5`, which is the Young instance available as
`eLpNorm_scalarConvolution_six_fifths_three_halves`.  Since the data is compactly supported,
`L^q ⊆ L^{6/5}` for every `q ≥ 6/5`, so all the estimates below are routed through `q = 6/5`
and therefore cover every exponent `q ≥ 6/5`; in particular `q = 3/2` and the exponents
`q > 5/2` of `def:sws`.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-! ### A measurable representative supported in the same ball

The force datum of a suitable weak solution is only almost everywhere strongly measurable, while
Young's inequality is stated for measurable data.  Replacing the datum by the indicator of the
support ball of a strongly measurable representative changes neither its `L^p` sizes nor any of
its Newtonian potentials. -/

/-- Data that vanishes off a closed ball and is almost everywhere strongly measurable agrees
almost everywhere with measurable data that vanishes off the same ball. -/
theorem exists_measurable_representative_of_support_closedBall
    {G : Vec3 → ℝ} {R : ℝ} (hG : AEStronglyMeasurable G volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    ∃ G' : Vec3 → ℝ, Measurable G' ∧ G =ᵐ[volume] G' ∧
      (∀ y, y ∉ closedBall (0 : Vec3) R → G' y = 0) := by
  classical
  refine ⟨(closedBall (0 : Vec3) R).indicator (hG.mk G), ?_, ?_, ?_⟩
  · exact (hG.stronglyMeasurable_mk.measurable).indicator isClosed_closedBall.measurableSet
  · filter_upwards [hG.ae_eq_mk] with y hy
    by_cases hyB : y ∈ closedBall (0 : Vec3) R
    · rw [Set.indicator_of_mem hyB, hy]
    · rw [Set.indicator_of_notMem hyB, hGzero y hyB]
  · intro y hy
    rw [Set.indicator_of_notMem hy]

/-! ### Young's inequality on a ball

Data supported in the closed ball of radius `R` only sees the kernel on the ball of radius
`R + ρ` when the potential is evaluated on the ball of radius `ρ`, so the potential agrees there
with the convolution against the truncated kernel, to which the `L^{6/5} * L^{6/5} → L^{3/2}`
Young estimate applies. -/

/-- Young's estimate on a ball for the Newtonian potential of data supported in the closed ball
of radius `R`: the near-field kernel is the Newtonian kernel truncated at radius `R + ρ`. -/
theorem pressureNewtonianPotential_eLpNorm_three_halves_restrict_ball_le
    {G : Vec3 → ℝ} {R ρ : ℝ} (hGmeas : Measurable G)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    eLpNorm (pressureNewtonianPotential G) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (ball (0 : Vec3) ρ)) ≤
      eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume *
        eLpNorm (truncatedNewtonianPotentialKernel (R + ρ))
          (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  have hkm : Measurable (fun z : Vec3 => -truncatedNewtonianPotentialKernel (R + ρ) z) :=
    (measurable_truncatedNewtonianPotentialKernel (R + ρ)).neg
  have heq : pressureNewtonianPotential G =ᵐ[volume.restrict (ball (0 : Vec3) ρ)]
      scalarConvolution G (fun z => -truncatedNewtonianPotentialKernel (R + ρ) z) := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
    have hxnorm : ‖x‖ < ρ := mem_ball_zero_iff.mp hx
    rw [pressureNewtonianPotential, scalarConvolution]
    refine integral_congr_ae ?_
    filter_upwards [] with y
    by_cases hGy : G y = 0
    · simp [hGy]
    · have hy : y ∈ closedBall (0 : Vec3) R := by
        by_contra hy
        exact hGy (hGzero y hy)
      have hynorm : ‖y‖ ≤ R := mem_closedBall_zero_iff.mp hy
      have hxy : ‖x - y‖ < R + ρ := by
        have hsum : ‖x‖ + ‖y‖ < ρ + R := add_lt_add_of_lt_of_le hxnorm hynorm
        exact (lt_of_le_of_lt (norm_sub_le x y) hsum).trans_eq (by ring)
      simp only [truncatedNewtonianPotentialKernel, hxy, ite_true]
      ring
  calc
    eLpNorm (pressureNewtonianPotential G) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (ball (0 : Vec3) ρ)) =
        eLpNorm (scalarConvolution G
            (fun z => -truncatedNewtonianPotentialKernel (R + ρ) z))
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (ball (0 : Vec3) ρ)) := eLpNorm_congr_ae heq
    _ ≤ eLpNorm (scalarConvolution G
            (fun z => -truncatedNewtonianPotentialKernel (R + ρ) z))
          (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume *
        eLpNorm (fun z => -truncatedNewtonianPotentialKernel (R + ρ) z)
          (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
      eLpNorm_scalarConvolution_six_fifths_three_halves hGmeas hkm
    _ = eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume *
        eLpNorm (truncatedNewtonianPotentialKernel (R + ρ))
          (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
      rw [show (fun z : Vec3 => -truncatedNewtonianPotentialKernel (R + ρ) z) =
        -(truncatedNewtonianPotentialKernel (R + ρ)) from rfl, eLpNorm_neg]

/-- Young's estimate on a ball for the first-derivative Newtonian potential of data supported in
the closed ball of radius `R`. -/
theorem pressureNewtonianDerivativePotential_eLpNorm_three_halves_restrict_ball_le
    {G : Vec3 → ℝ} (i : Fin 3) {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (hGmeas : Measurable G) (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    eLpNorm (pressureNewtonianDerivativePotential i G) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (ball (0 : Vec3) ρ)) ≤
      eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume *
        eLpNorm (truncatedNewtonianDerivative (R + ρ) i)
          (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
  newtonianDerivativePotential_eLpNorm_three_halves_restrict_ball_le i hR hρ hGmeas hG hGzero

/-! ### Local `L^{3/2}` membership on the ambient balls -/

/-- The Newtonian potential of compactly supported `L^{6/5}` data is `L^{3/2}` on every ambient
ball about the origin. -/
theorem pressureNewtonianPotential_memLp_ball
    {G : Vec3 → ℝ} {R ρ : ℝ} (hRρ : 0 < R + ρ) (hGmeas : Measurable G)
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    MemLp (pressureNewtonianPotential G) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (ball (0 : Vec3) ρ)) := by
  have hkernel : MemLp (truncatedNewtonianPotentialKernel (R + ρ))
      (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
    truncatedNewtonianPotentialKernel_memLp hRρ (by norm_num) (by norm_num)
  rw [memLp_iff]
  refine lt_of_le_of_lt
    (pressureNewtonianPotential_eLpNorm_three_halves_restrict_ball_le hGmeas hGzero) ?_
  exact ENNReal.mul_lt_top hG.eLpNorm_lt_top hkernel.eLpNorm_lt_top

/-- The first-derivative Newtonian potential of compactly supported `L^{6/5}` data is `L^{3/2}`
on every ambient ball about the origin. -/
theorem pressureNewtonianDerivativePotential_memLp_ball
    {G : Vec3 → ℝ} (i : Fin 3) {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (hGmeas : Measurable G) (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    MemLp (pressureNewtonianDerivativePotential i G) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (ball (0 : Vec3) ρ)) := by
  have hRρ : 0 < R + ρ := by linarith only [hR, hρ]
  have hkernel : MemLp (truncatedNewtonianDerivative (R + ρ) i)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
    truncatedNewtonianDerivative_memLp_of_lt_three_halves hRρ (by norm_num) (by norm_num) i
  rw [memLp_iff]
  refine lt_of_le_of_lt
    (pressureNewtonianDerivativePotential_eLpNorm_three_halves_restrict_ball_le
      i hR hρ hGmeas hG hGzero) ?_
  exact ENNReal.mul_lt_top hG.eLpNorm_lt_top hkernel.eLpNorm_lt_top

end CKN.Foundation.Euclidean
