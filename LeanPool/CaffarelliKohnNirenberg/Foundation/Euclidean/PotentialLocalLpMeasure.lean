/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Potentials

/-!
# Potential Local Lp Measure

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-- The Newtonian kernel `newtonianKernel : Vec3 → ℝ` is Borel measurable; this is the
kernel-measurability input for the measurability of the Newtonian potentials below. -/
private lemma pressureNewtonianKernel_meas :
    Measurable (newtonianKernel : Vec3 → ℝ) := by
  have hnorm : Measurable (fun z : Vec3 => vec3EuclideanNorm z) := by
    unfold vec3EuclideanNorm
    fun_prop
  unfold newtonianKernel
  exact measurable_const.div (measurable_const.mul hnorm)

/-- Each first partial derivative `∂ᵢ newtonianKernel : Vec3 → ℝ` is Borel measurable; this is
the kernel-measurability input for the measurability of the derivative potentials below. -/
private lemma pressureNewtonianKernel_deriv_meas (i : Fin 3) :
    Measurable (fun z : Vec3 => CKN.spatialDeriv newtonianKernel i z) := by
  unfold CKN.spatialDeriv
  exact measurable_fderiv_apply_const ℝ newtonianKernel (CKN.basisVec i)

/-- The Newtonian potential of measurable data is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_pressureNewtonianPotential {G : Vec3 → ℝ}
    (hG : Measurable G) :
    AEStronglyMeasurable (pressureNewtonianPotential G) volume := by
  change AEStronglyMeasurable
    (fun x : Vec3 => ∫ y, (-newtonianKernel (x-y)) * G y) volume
  have hF : AEStronglyMeasurable
      (fun p : Vec3 × Vec3 => (-newtonianKernel (p.1-p.2)) * G p.2)
      (volume.prod volume) :=
    (((pressureNewtonianKernel_meas.comp
        (measurable_fst.sub measurable_snd)).neg).mul
      (hG.comp measurable_snd)).aestronglyMeasurable
  exact hF.integral_prod_right'

/-- The first-derivative Newtonian potential of measurable data is almost everywhere strongly
measurable. -/
theorem aestronglyMeasurable_pressureNewtonianDerivativePotential (i : Fin 3) {G : Vec3 → ℝ}
    (hG : Measurable G) :
    AEStronglyMeasurable (pressureNewtonianDerivativePotential i G) volume := by
  change AEStronglyMeasurable
    (fun x : Vec3 => ∫ y, CKN.spatialDeriv newtonianKernel i (x-y) * G y) volume
  have hF : AEStronglyMeasurable
      (fun p : Vec3 × Vec3 => CKN.spatialDeriv newtonianKernel i (p.1-p.2) * G p.2)
      (volume.prod volume) :=
    (((pressureNewtonianKernel_deriv_meas i).comp
        (measurable_fst.sub measurable_snd)).mul
      (hG.comp measurable_snd)).aestronglyMeasurable
  exact hF.integral_prod_right'

/-- The Newtonian potential only sees the data up to a null set, so it is unchanged when the
data is replaced by an almost-everywhere equal function. -/
theorem pressureNewtonianPotential_congr_of_ae_eq {G G' : Vec3 → ℝ}
    (h : G =ᵐ[volume] G') :
    pressureNewtonianPotential G = pressureNewtonianPotential G' := by
  funext x
  change (∫ y, (-newtonianKernel (x-y)) * G y) =
    ∫ y, (-newtonianKernel (x-y)) * G' y
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

/-- The same statement for the first-derivative Newtonian potential. -/
theorem pressureNewtonianDerivativePotential_congr_of_ae_eq (i : Fin 3) {G G' : Vec3 → ℝ}
    (h : G =ᵐ[volume] G') :
    pressureNewtonianDerivativePotential i G = pressureNewtonianDerivativePotential i G' := by
  funext x
  change (∫ y, CKN.spatialDeriv newtonianKernel i (x-y) * G y) =
    ∫ y, CKN.spatialDeriv newtonianKernel i (x-y) * G' y
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

end CKN.Foundation.Euclidean
