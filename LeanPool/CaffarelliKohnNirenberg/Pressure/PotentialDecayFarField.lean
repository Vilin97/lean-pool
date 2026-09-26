/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsBasic
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecayGeometry

/-!
# Far-field decay of Newtonian potentials about a general centre

The tail estimates of the Newtonian potential and of its first derivative are stated here for
data supported in a closed ball centred at an arbitrary point `x₀`, rather than at the origin:
on the support of the data a far point `x` with `2 * R ≤ ‖x - x₀‖` satisfies
`‖x - y‖ ≥ ‖x - x₀‖ / 2`, so the Newtonian kernel bounds of `CKN.Foundation.Heat` supply the
same decay with `‖x - x₀‖` in place of `‖x‖`.

These tail estimates are the decay-at-infinity input to the uniqueness half of the
Newtonian representation `ext:newtonian` of the paper, where the difference of two
representations is harmonic on all of space and tends to zero in the `L^{3/2}` average sense.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
noncomputable section
namespace CKN

private theorem compact_kernel_mul_integrable
    {k g : Vec3 → ℝ} {x : Vec3} {A : ℝ}
    (hk : Measurable k) (hg : Integrable g volume)
    (hpoint : ∀ y, g y ≠ 0 → |k (x - y)| ≤ A) :
    Integrable (fun y => k (x - y) * g y) volume := by
  have hmeas : AEStronglyMeasurable (fun y => k (x - y) * g y) volume := by
    exact (hk.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
      hg.aestronglyMeasurable
  refine (hg.norm.const_mul A).mono' hmeas ?_
  filter_upwards [] with y
  by_cases hgy : g y = 0
  · simp [hgy]
  · simpa only [Real.norm_eq_abs, abs_mul, mul_comm] using
      (mul_le_mul_of_nonneg_right (hpoint y hgy) (abs_nonneg (g y)))

private lemma potential_kernel_meas :
    Measurable (fun z : Vec3 => -newtonianKernel z) := by
  have hnorm : Measurable (fun z : Vec3 => vec3EuclideanNorm z) := by
    unfold vec3EuclideanNorm
    fun_prop
  have hk : Measurable (newtonianKernel : Vec3 → ℝ) := by
    unfold newtonianKernel
    exact measurable_const.div (measurable_const.mul hnorm)
  exact hk.neg

private lemma derivative_kernel_meas (i : Fin 3) : Measurable
    (fun z : Vec3 => CKN.spatialDeriv newtonianKernel i z) := by
  unfold CKN.spatialDeriv
  exact measurable_fderiv_apply_const ℝ newtonianKernel (CKN.basisVec i)

/-- On the support of data carried by the closed ball of radius `R` about `x₀`, a far point `x`
with `2 * R ≤ ‖x - x₀‖` is at distance at least `‖x - x₀‖ / 2` from every such support point, is
distinct from every such point, and is itself distinct from `x₀`. -/
private lemma tail_geometry_centre
    {g : Vec3 → ℝ} {x₀ : Vec3} {R : ℝ}
    (hR : 0 < R) (hSupp : tsupport g ⊆ Metric.closedBall x₀ R)
    {x : Vec3} (hx : 2 * R ≤ ‖x - x₀‖) {y : Vec3} (hy : y ∈ tsupport g) :
    ‖x - x₀‖ / 2 ≤ ‖x - y‖ ∧ x - y ≠ 0 ∧ x - x₀ ≠ 0 := by
  have hy' : ‖y - x₀‖ ≤ R := by
    have hmem := hSupp hy
    rwa [Metric.mem_closedBall, dist_eq_norm] at hmem
  have hx₀ : x - x₀ ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hx
    linarith only [hx, hR]
  exact ⟨far_field_norm_sub_ge hx hy', far_field_sub_ne_zero hR hx hy', hx₀⟩

/-- Far-field decay of the Newtonian potential of data supported in the closed ball of radius `R`
about `x₀`.  Decay-at-infinity input to `ext:newtonian` of the paper, at a general centre. -/
theorem pressureNewtonianPotential_tail_bound_centre
    {g : Vec3 → ℝ} (hg : Integrable g volume) {x₀ : Vec3} {R : ℝ} (hR : 0 < R)
    (hSupp : tsupport g ⊆ Metric.closedBall x₀ R)
    {x : Vec3} (hx : 2 * R ≤ ‖x - x₀‖) :
    |pressureNewtonianPotential g x| ≤
      (2 * (4 * Real.pi)⁻¹ / ‖x - x₀‖) * ∫ y, |g y| := by
  let K : ℝ := 2 * (4 * Real.pi)⁻¹ / ‖x - x₀‖
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpoint : ∀ y, g y ≠ 0 →
      |newtonianKernel (x - y)| ≤ K := by
    intro y hgy
    have hy : y ∈ tsupport g :=
      subset_tsupport (f := g) (Function.mem_support.mpr hgy)
    obtain ⟨hdist, hxy, hx₀⟩ := tail_geometry_centre hR hSupp hx hy
    have hxypos : 0 < ‖x - y‖ := norm_pos_iff.mpr hxy
    have hhalfpos : 0 < ‖x - x₀‖ / 2 := half_pos (norm_pos_iff.mpr hx₀)
    have hinv : ‖x - y‖⁻¹ ≤ (‖x - x₀‖ / 2)⁻¹ := by
      exact (inv_le_inv₀ hxypos hhalfpos).2 hdist
    have hb := Foundation.Heat.newtonianKernel_size_bound hxy
    have hc : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
    calc
      |newtonianKernel (x - y)| ≤ (4 * Real.pi)⁻¹ * ‖x - y‖⁻¹ := hb
      _ ≤ (4 * Real.pi)⁻¹ * (‖x - x₀‖ / 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hc
      _ = K := by
        dsimp [K]
        field_simp [norm_ne_zero_iff.mpr hx₀, ne_of_gt Real.pi_pos]
  have hprod : Integrable
      (fun y => (-newtonianKernel (x - y)) * g y) volume := by
    have hneg : ∀ y, g y ≠ 0 →
        |-newtonianKernel (x - y)| ≤ K := by
      intro y hgy
      simpa only [abs_neg] using hpoint y hgy
    exact compact_kernel_mul_integrable potential_kernel_meas hg hneg
  exact pressure_newtonian_potential_bound hK hg hprod hpoint

/-- Far-field decay of the first-derivative Newtonian potential of data supported in the closed
ball of radius `R` about `x₀`.  Decay-at-infinity input to `ext:newtonian` of the paper,
at a general centre. -/
theorem pressureNewtonianDerivativePotential_tail_bound_centre
    {g : Vec3 → ℝ} (hg : Integrable g volume) {x₀ : Vec3} {R : ℝ} (hR : 0 < R)
    (hSupp : tsupport g ⊆ Metric.closedBall x₀ R)
    (i : Fin 3) {x : Vec3} (hx : 2 * R ≤ ‖x - x₀‖) :
    |pressureNewtonianDerivativePotential i g x| ≤
      (4 * (4 * Real.pi)⁻¹ / ‖x - x₀‖ ^ 2) * ∫ y, |g y| := by
  let K : ℝ := 4 * (4 * Real.pi)⁻¹ / ‖x - x₀‖ ^ 2
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpoint : ∀ y, g y ≠ 0 →
      |CKN.spatialDeriv newtonianKernel i (x - y)| ≤ K := by
    intro y hgy
    have hy : y ∈ tsupport g :=
      subset_tsupport (f := g) (Function.mem_support.mpr hgy)
    obtain ⟨hdist, hxy, hx₀⟩ := tail_geometry_centre hR hSupp hx hy
    have hxypos : 0 < ‖x - y‖ := norm_pos_iff.mpr hxy
    have hhalfpos : 0 < ‖x - x₀‖ / 2 := half_pos (norm_pos_iff.mpr hx₀)
    have hsq : (‖x - x₀‖ / 2) ^ 2 ≤ ‖x - y‖ ^ 2 := by
      nlinarith only [hdist, norm_nonneg (x - x₀), norm_nonneg (x - y)]
    have hinv : (‖x - y‖ ^ 2)⁻¹ ≤ ((‖x - x₀‖ / 2) ^ 2)⁻¹ := by
      exact (inv_le_inv₀ (sq_pos_of_pos hxypos)
        (sq_pos_of_pos hhalfpos)).2 hsq
    have hb := Foundation.Heat.newtonianKernel_spatialDeriv_size_bound hxy i
    have hc : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
    calc
      |CKN.spatialDeriv newtonianKernel i (x - y)| ≤
          (4 * Real.pi)⁻¹ * (‖x - y‖ ^ 2)⁻¹ := hb
      _ ≤ (4 * Real.pi)⁻¹ * ((‖x - x₀‖ / 2) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hc
      _ = K := by
        dsimp [K]
        field_simp [norm_ne_zero_iff.mpr hx₀, ne_of_gt Real.pi_pos]
        ring
  have hprod : Integrable
      (fun y => CKN.spatialDeriv newtonianKernel i (x - y) * g y) volume :=
    compact_kernel_mul_integrable (derivative_kernel_meas i) hg hpoint
  exact pressure_newtonian_derivative_potential_bound hK i hg hprod hpoint

end CKN
