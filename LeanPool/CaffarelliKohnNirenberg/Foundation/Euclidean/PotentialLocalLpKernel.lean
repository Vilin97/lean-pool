/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.NewtonianDerivativeLocalLp

/-!
# Potential Local Lp Kernel

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-- The Newtonian kernel truncated to the ball of radius `R` about the origin. -/
@[expose]
def truncatedNewtonianPotentialKernel (R : ℝ) : Vec3 → ℝ := fun z =>
  if ‖z‖ < R then newtonianKernel z else 0

/-- The truncated Newtonian kernel is measurable. -/
theorem measurable_truncatedNewtonianPotentialKernel (R : ℝ) :
    Measurable (truncatedNewtonianPotentialKernel R) := by
  unfold truncatedNewtonianPotentialKernel
  have hk : Measurable (newtonianKernel : Vec3 → ℝ) := by
    unfold newtonianKernel
    have hnorm : Measurable (fun z : Vec3 => vec3EuclideanNorm z) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact measurable_const.div (measurable_const.mul hnorm)
  exact hk.piecewise (measurableSet_lt measurable_norm measurable_const) measurable_const

/-- The Newtonian kernel `|z|⁻¹` truncated to a ball lies in `L^s` for every `0 < s < 3`. -/
theorem truncatedNewtonianPotentialKernel_memLp {R s : ℝ} (_ : 0 < R)
    (hs : 0 < s) (hs3 : s < 3) :
    MemLp (truncatedNewtonianPotentialKernel R) (ENNReal.ofReal s) volume := by
  let k := truncatedNewtonianPotentialKernel R
  have hkmeas : AEStronglyMeasurable k volume :=
    (measurable_truncatedNewtonianPotentialKernel R).aestronglyMeasurable
  let kp : Vec3 → ℝ := fun z => ‖k z‖ ^ s
  have hkpmeas : AEStronglyMeasurable kp volume := by
    exact ((Real.continuous_rpow_const hs.le).measurable.comp_aemeasurable
      hkmeas.norm.aemeasurable).aestronglyMeasurable
  have hz0 : ∀ᵐ z ∂volume.restrict (ball (0 : Vec3) R), z ≠ 0 :=
    ae_restrict_of_ae (Measure.ae_ne volume (0 : Vec3))
  have hdecay : ∀ᵐ z ∂volume.restrict (ball (0 : Vec3) R),
      ‖kp z‖ ≤ ((4 * Real.pi)⁻¹) ^ s * ‖z‖ ^ (-s) := by
    filter_upwards [ae_restrict_mem (isOpen_ball.measurableSet), hz0]
      with z hz hzero
    have hbound := newtonianKernel_size_bound hzero
    have hkval : k z = newtonianKernel z := by
      dsimp [k, truncatedNewtonianPotentialKernel]
      simp only [mem_ball_zero_iff] at hz
      simp only [hz, ite_true]
    dsimp [kp]
    rw [hkval, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have hpow := Real.rpow_le_rpow (abs_nonneg _) hbound hs.le
    have hright : ((4 * Real.pi)⁻¹) ^ s * ‖z‖ ^ (-s) =
        ((4 * Real.pi)⁻¹ * ‖z‖ ^ (-1 : ℝ)) ^ s := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
      rw [neg_one_mul]
    calc
      |newtonianKernel z| ^ s ≤
          ((4 * Real.pi)⁻¹ * ‖z‖ ^ (-1 : ℝ)) ^ s := by
        simpa only [Real.norm_eq_abs, Real.rpow_neg (norm_nonneg _), Real.rpow_one] using hpow
      _ = _ := hright.symm
  have hintOn : IntegrableOn kp (ball (0 : Vec3) R) volume := by
    apply integrableOn_ball_of_norm_le_rpow (E := Vec3) (F := ℝ)
      (by change 1 ≤ Module.finrank ℝ (Fin 3 → ℝ); rw [Module.finrank_fin_fun]; norm_num)
      (by
        change s < (Module.finrank ℝ Vec3 : ℝ)
        rw [Module.finrank_fin_fun]
        exact hs3)
      hdecay hkpmeas
  have hint : Integrable kp volume := by
    exact hintOn.integrable_of_forall_notMem_eq_zero (by
      intro z hz
      have hz' : ¬ ‖z‖ < R := by simpa [mem_ball_zero_iff] using hz
      simp [kp, k, truncatedNewtonianPotentialKernel, hz', Real.zero_rpow hs.ne'])
  have hzero : ENNReal.ofReal s ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hs
  rw [← (integrable_norm_rpow_iff hkmeas hzero ENNReal.ofReal_ne_top)]
  convert hint using 1
  simp [kp, ENNReal.toReal_ofReal hs.le]

/-- The Newtonian derivative kernel `|z|⁻²` truncated to a ball lies in `L^s` for every
`0 < s < 3 / 2`. -/
theorem truncatedNewtonianDerivative_memLp_of_lt_three_halves {R s : ℝ} (_ : 0 < R)
    (hs : 0 < s) (hs3 : s < 3 / 2) (i : Fin 3) :
    MemLp (truncatedNewtonianDerivative R i) (ENNReal.ofReal s) volume := by
  let k := truncatedNewtonianDerivative R i
  have hkmeas : AEStronglyMeasurable k volume :=
    (measurable_truncatedNewtonianDerivative R i).aestronglyMeasurable
  let kp : Vec3 → ℝ := fun z => ‖k z‖ ^ s
  have hkpmeas : AEStronglyMeasurable kp volume := by
    exact ((Real.continuous_rpow_const hs.le).measurable.comp_aemeasurable
      hkmeas.norm.aemeasurable).aestronglyMeasurable
  have hz0 : ∀ᵐ z ∂volume.restrict (ball (0 : Vec3) R), z ≠ 0 :=
    ae_restrict_of_ae (Measure.ae_ne volume (0 : Vec3))
  have hdecay : ∀ᵐ z ∂volume.restrict (ball (0 : Vec3) R),
      ‖kp z‖ ≤ ((4 * Real.pi)⁻¹) ^ s * ‖z‖ ^ (-(2 * s)) := by
    filter_upwards [ae_restrict_mem (isOpen_ball.measurableSet), hz0]
      with z hz hzero
    have hbound := newtonianKernel_spatialDeriv_size_bound hzero i
    have hkval : k z = spatialDeriv newtonianKernel i z := by
      dsimp [k, truncatedNewtonianDerivative]
      simp only [mem_ball_zero_iff] at hz
      simp only [hz, ite_true]
    dsimp [kp]
    rw [hkval, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have hpow := Real.rpow_le_rpow (abs_nonneg _) hbound hs.le
    have hright : ((4 * Real.pi)⁻¹) ^ s * ‖z‖ ^ (-(2 * s)) =
        ((4 * Real.pi)⁻¹ * (‖z‖ ^ (-2 : ℝ))) ^ s := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
      rw [neg_mul]
    calc
      |spatialDeriv newtonianKernel i z| ^ s ≤
          ((4 * Real.pi)⁻¹ * (‖z‖ ^ (-2 : ℝ))) ^ s := by
        simpa only [Real.norm_eq_abs, Real.rpow_neg (norm_nonneg _), Real.rpow_two] using hpow
      _ = _ := hright.symm
  have hintOn : IntegrableOn kp (ball (0 : Vec3) R) volume := by
    apply integrableOn_ball_of_norm_le_rpow (E := Vec3) (F := ℝ)
      (by change 1 ≤ Module.finrank ℝ (Fin 3 → ℝ); rw [Module.finrank_fin_fun]; norm_num)
      (by
        change (2 * s) < (Module.finrank ℝ Vec3 : ℝ)
        rw [Module.finrank_fin_fun]
        norm_num
        linarith only [hs3])
      hdecay hkpmeas
  have hint : Integrable kp volume := by
    exact hintOn.integrable_of_forall_notMem_eq_zero (by
      intro z hz
      have hz' : ¬ ‖z‖ < R := by simpa [mem_ball_zero_iff] using hz
      simp [kp, k, truncatedNewtonianDerivative, hz', Real.zero_rpow hs.ne'])
  have hzero : ENNReal.ofReal s ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hs
  rw [← (integrable_norm_rpow_iff hkmeas hzero ENNReal.ofReal_ne_top)]
  convert hint using 1
  simp [kp, ENNReal.toReal_ofReal hs.le]

end CKN.Foundation.Euclidean
