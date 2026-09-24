/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceLocalForce

/-!
# Measurability of time-dependent force potentials

Spatial integration against a measurable kernel preserves measurability
of the potential norm in time. This applies to the force-growth constants
in `eq:pressure-gradient-morrey` without assuming temporal regularity.
-/

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

/-- The spatial norm of a time-dependent convolution is measurable in time. -/
theorem origin_convolution_norm_time_aemeasurable
    {G : Vec3 × ℝ → ℝ} {J : Set ℝ} {k : Vec3 → ℝ}
    (hG : AEStronglyMeasurable G ((volume : Measure Vec3).prod (volume.restrict J)))
    (hk : Measurable k) {P : ℝ} (hP : 0 < P) (B : Set Vec3) :
    AEMeasurable (fun s => eLpNorm (fun x => ∫ y, k (x - y) * G (y, s))
      (ENNReal.ofReal P) (volume.restrict B)) (volume.restrict J) := by
  let G' := hG.mk G
  have hG'm : Measurable G' := hG.stronglyMeasurable_mk.measurable
  have hpot : Measurable (fun w : Vec3 × ℝ => ∫ y, k (w.1 - y) * G' (y, w.2)) := by
    have hm : Measurable (fun v : (Vec3 × ℝ) × Vec3 =>
        k (v.1.1 - v.2) * G' (v.2, v.1.2)) :=
      (hk.comp (measurable_fst.fst.sub measurable_snd)).mul
        (hG'm.comp (measurable_snd.prodMk measurable_fst.snd))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  have hn := origin_time_slice_norm_aemeasurable hP hpot.aemeasurable.restrict (E := B) (J := J)
  apply hn.congr
  filter_upwards [ae_ae_of_ae_prod_snd hG.ae_eq_mk] with s hs
  apply eLpNorm_congr_ae
  exact Eventually.of_forall fun x => integral_congr_ae
    (hs.mono fun y hy => congrArg (fun a => k (x - y) * a) hy.symm)

/-- Both Newtonian force-growth constants are measurable functions of time
for a jointly measurable source supported on the full spatial space. -/
theorem origin_force_growth_constants_time_aemeasurable
    {G : Vec3 × ℝ → ℝ} {J : Set ℝ}
    (hG : AEStronglyMeasurable G ((volume : Measure Vec3).prod (volume.restrict J)))
    (R : ℝ) :
    AEMeasurable (fun s => newtonianPotentialGrowthConstant (fun y => G (y, s)) R)
      (volume.restrict J) ∧
      ∀ i : Fin 3, AEMeasurable
        (fun s => newtonianDerivativePotentialGrowthConstant i (fun y => G (y, s)) R)
        (volume.restrict J) := by
  have hmass : AEMeasurable (fun s => ∫ y, |G (y, s)|) (volume.restrict J) :=
    hG.norm.prod_swap.integral_prod_right'.aemeasurable
  have hk : Measurable (fun x : Vec3 => -newtonianKernel x) := by
    unfold newtonianKernel vec3EuclideanNorm
    fun_prop
  have hd (i : Fin 3) : Measurable (spatialDeriv newtonianKernel i) :=
    measurable_fderiv_apply_const ℝ newtonianKernel (basisVec i)
  have hp := origin_convolution_norm_time_aemeasurable hG hk (by norm_num : (0 : ℝ) < 3 / 2)
    (ball (0 : Vec3) (2 * R))
  have hdp (i : Fin 3) := origin_convolution_norm_time_aemeasurable hG (hd i)
    (by norm_num : (0 : ℝ) < 3 / 2) (ball (0 : Vec3) (2 * R))
  constructor
  · unfold newtonianPotentialGrowthConstant invNormGrowthConstant
    simp_rw [← toReal_eLpNorm]
    exact hp.ennreal_toReal.add ((aemeasurable_const.mul hmass).mul_const _)
  · intro i
    unfold newtonianDerivativePotentialGrowthConstant invNormGrowthConstant
    simp_rw [← toReal_eLpNorm]
    exact (hdp i).ennreal_toReal.add (((aemeasurable_const.mul hmass).div_const _).mul_const _)

end CKN.Core.Step4
