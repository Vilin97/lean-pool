/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.ExcessComparisonCore

/-!
# Lin34 Slice Mean Free

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-!
# Integrability of the mean-free velocity cube on a parabolic cylinder

This file supplies the integrability of the integrand of the local quantity
`C_hat(z,ρ)` on a contained parabolic cylinder, the estimate used in
`prop:lin34` of `paper/ckn.tex` (equation `eq:Chat`).  Concretely, if the
velocity `u` and its cube `|u|^3` are integrable on the one-sided parabolic
cylinder `parabolicCylinder x t r`, then so is the cube of the mean-free
velocity `meanFreeVec u x r w.2 w.1`, the spatial mean-free part of `u` at
time `w.2` over the ball `vec3Ball x r`.

The proof converts the cylinder integral to the product measure on
`vec3Ball x r ×ˢ Ioc (t - r^2) t`, uses the pointwise mean-oscillation bound
on almost every spatial slice, and applies Tonelli's theorem.  The two helper
lemmas below are private.
-/

/-- The mean-free velocity `meanFreeVec u x r s ·` is measurable whenever `u` is
measurable as a function of the product variable `(y,s)`.  This is the
measurability input for the integrand of `eq:Chat` in `paper/ckn.tex`. -/
private lemma local_meanFreeVec_aemeasurable
    {u : ParabolicPoint → Vec3} {x : Vec3} {r : ℝ} {T : Set ℝ}
    (hU : AEStronglyMeasurable u
      ((volume.restrict (vec3Ball x r)).prod (volume.restrict T))) :
    AEStronglyMeasurable (fun w : Vec3 × ℝ => meanFreeVec u x r w.2 w.1)
      ((volume.restrict (vec3Ball x r)).prod (volume.restrict T)) := by
  let μ := (volume.restrict (vec3Ball x r)).prod (volume.restrict T)
  have hcomp : ∀ i : Fin 3, AEStronglyMeasurable (fun w : Vec3 × ℝ => u w i) μ := by
    intro i
    exact (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hU
  have havg : ∀ i : Fin 3, AEStronglyMeasurable
      (fun s : ℝ => average (volume.restrict (vec3Ball x r))
        (fun y : Vec3 => u (y,s) i)) (volume.restrict T) := by
    intro i
    have hi := (hcomp i).prod_swap.integral_prod_right'
    convert hi.const_smul ((volume (vec3Ball x r)).toReal⁻¹) using 1
    · funext s
      rw [MeasureTheory.average_eq (μ := volume.restrict (vec3Ball x r))]
      simp only [MeasureTheory.measureReal_restrict_apply_univ]
      rfl
  have hcoord : ∀ i : Fin 3, AEStronglyMeasurable
      (fun w : Vec3 × ℝ => u w i - average (volume.restrict (vec3Ball x r))
        (fun y : Vec3 => u (y,w.2) i)) μ := by
    intro i
    have hsnd := Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (vec3Ball x r)) (ν := volume.restrict T)
    have hm := (havg i).comp_quasiMeasurePreserving hsnd
    change AEStronglyMeasurable ((fun w : Vec3 × ℝ => u w i) -
      (fun w : Vec3 × ℝ => average (volume.restrict (vec3Ball x r))
        (fun y : Vec3 => u (y,w.2) i))) μ
    simpa [Function.comp_def, Prod.swap_prod_mk] using (hcomp i).sub hm
  change AEStronglyMeasurable (fun w : Vec3 × ℝ => fun i =>
    u w i - average (volume.restrict (vec3Ball x r))
      (fun y : Vec3 => u (y,w.2) i)) μ
  apply aestronglyMeasurable_iff_aemeasurable.mpr
  apply aemeasurable_pi_iff.mpr
  intro i
  exact (hcoord i).aemeasurable

/-- On a spatial slice at time `s` on which `u(·,s)` and `|u(·,s)|^3` are
integrable, the `L³` mean oscillation of `u(·,s)` over the ball `vec3Ball x r`
is bounded by `8` times the `L³` norm of `u(·,s)`.  This is the slicewise
form of the mean-oscillation estimate behind `eq:Chat` in `paper/ckn.tex`. -/
private lemma local_ball_meanFree_lintegral_bound
    {u : ParabolicPoint → Vec3} {x : Vec3} {r s : ℝ}
    (hr : 0 < r)
    (hu : IntegrableOn (fun y : Vec3 => u (y,s)) (vec3Ball x r) volume)
    (hu3 : IntegrableOn (fun y : Vec3 => vec3EuclideanNorm (u (y,s)) ^ (3 : ℕ))
      (vec3Ball x r) volume) :
    (∫⁻ y in vec3Ball x r, ENNReal.ofReal
      (vec3EuclideanNorm (u (y,s) - ⨍ z in vec3Ball x r, u (z,s))) ^ (3 : ℝ)) ≤
      8 * (∫⁻ y in vec3Ball x r, ENNReal.ofReal
        (vec3EuclideanNorm (u (y,s))) ^ (3 : ℝ)) := by
  let L := (PiLp.continuousLinearEquiv (2 : ℝ≥0∞) ℝ
    (fun _ : Fin 3 => ℝ)).symm
  have hLint : IntegrableOn (fun y : Vec3 => L (u (y,s)))
      (vec3Ball x r) volume := L.toContinuousLinearMap.integrable_comp hu.integrable
  have hL3 : IntegrableOn (fun y : Vec3 => ‖L (u (y,s))‖ ^ (3 : ℕ))
      (vec3Ball x r) volume := by
    simpa only [vec3EuclideanNorm_eq_l2,
      show (L : Vec3 → L2Vec3) = WithLp.toLp 2 by rfl] using hu3
  have h := CKN.Foundation.Parabolic.Integration.setLaverage_norm_sub_setAverage_rpow_le
    (f := fun y : Vec3 => L (u (y,s))) (p := (3 : ℝ)) (c := (0 : L2Vec3))
    (by norm_num) (CKN.Foundation.Parabolic.Integration.volume_vec3Ball_pos hr)
    (CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top (x := x) (r := r))
    hLint (by simpa using hL3)
  have hmap : L (⨍ y in vec3Ball x r, u (y,s)) =
      ⨍ y in vec3Ball x r, L (u (y,s)) := by
    rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
    change L ((volume (vec3Ball x r)).toReal⁻¹ • ∫ y in vec3Ball x r, u (y,s)) =
      (volume (vec3Ball x r)).toReal⁻¹ • ∫ y in vec3Ball x r, L (u (y,s))
    rw [map_smul, L.integral_comp_comm]
  rw [← hmap] at h
  simp only [← map_sub] at h
  rw [MeasureTheory.setLAverage_eq, MeasureTheory.setLAverage_eq] at h
  have h' := h
  norm_num [ENNReal.rpow_natCast] at h'
  have h'' :
      (∫⁻ y in vec3Ball x r, ‖L (u (y,s) - ⨍ z in vec3Ball x r, u (z,s))‖ₑ ^ (3 : ℝ)) /
        volume (vec3Ball x r) ≤
      (8 * (∫⁻ y in vec3Ball x r, ‖L (u (y,s))‖ₑ ^ (3 : ℝ))) /
        volume (vec3Ball x r) := by
    simpa [map_sub, sub_zero, mul_div_assoc, Real.rpow_natCast] using h'
  have hp := CKN.Foundation.Parabolic.Integration.volume_vec3Ball_pos (x := x) (r := r) hr
  have ht := CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top (x := x) (r := r)
  have hraw :
      (∫⁻ y in vec3Ball x r, ‖L (u (y,s) - ⨍ z in vec3Ball x r, u (z,s))‖ₑ ^ (3 : ℝ)) ≤
      8 * (∫⁻ y in vec3Ball x r, ‖L (u (y,s))‖ₑ ^ (3 : ℝ)) := by
    calc
      _ = ((∫⁻ y in vec3Ball x r, ‖L (u (y,s) - ⨍ z in vec3Ball x r, u (z,s))‖ₑ ^ (3 : ℝ)) /
          volume (vec3Ball x r)) * volume (vec3Ball x r) := by rw [ENNReal.div_mul_cancel hp.ne'
            ht.ne]
      _ ≤ ((8 : ℝ≥0∞) * (∫⁻ y in vec3Ball x r, ‖L (u (y,s))‖ₑ ^ (3 : ℝ)) /
          volume (vec3Ball x r)) * volume (vec3Ball x r) := mul_le_mul_of_nonneg_right h'' (by
            positivity)
      _ = 8 * (∫⁻ y in vec3Ball x r, ‖L (u (y,s))‖ₑ ^ (3 : ℝ)) := ENNReal.div_mul_cancel hp.ne'
        ht.ne
  convert hraw using 1 <;> simp [vec3EuclideanNorm_eq_l2,
    show (L : Vec3 → L2Vec3) = WithLp.toLp 2 by rfl, ofReal_norm]

/-- The cube of the mean-free velocity is integrable on a parabolic cylinder
`parabolicCylinder x t r` whenever the velocity and its cube are.  This is the
integrability of the integrand of `C_hat(z,ρ)` used in `prop:lin34` of
`paper/ckn.tex` (equation `eq:Chat`). -/
theorem lin34_integrableOn_meanFree_cube
    {u : ParabolicPoint → Vec3} {x : Vec3} {t r : ℝ} (hr : 0 < r)
    (hu : IntegrableOn u (parabolicCylinder x t r) volume)
    (hu3 : IntegrableOn (fun w => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      (parabolicCylinder x t r) volume) :
    IntegrableOn (fun w : ParabolicPoint =>
        vec3EuclideanNorm (meanFreeVec u x r w.2 w.1) ^ (3 : ℕ))
      (parabolicCylinder x t r) volume := by
  let B : Set Vec3 := vec3Ball x r
  let T : Set ℝ := Ioc (t - r ^ 2) t
  have hu' : Integrable u ((volume.restrict B).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict]
    change IntegrableOn u (vec3Ball x r ×ˢ Ioc (t-r^2) t)
      ((volume : Measure Vec3).prod (volume : Measure ℝ))
    exact hu
  have hu3' : Integrable (fun w => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      ((volume.restrict B).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict]
    change IntegrableOn (fun w => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      (vec3Ball x r ×ˢ Ioc (t-r^2) t)
      ((volume : Measure Vec3).prod (volume : Measure ℝ))
    exact hu3
  have hUmeas := hu'.aestronglyMeasurable
  have hmeanfree := local_meanFreeVec_aemeasurable hUmeas
  have hFmeas : AEMeasurable (fun w : Vec3 × ℝ => ENNReal.ofReal
      (vec3EuclideanNorm (meanFreeVec u x r w.2 w.1)) ^ (3 : ℝ))
      ((volume.restrict B).prod (volume.restrict T)) := by
    have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact (hc.comp_aestronglyMeasurable hmeanfree).aemeasurable.ennreal_ofReal.pow_const _
  have hU3meas : AEMeasurable (fun w : Vec3 × ℝ => ENNReal.ofReal
      (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ((volume.restrict B).prod (volume.restrict T)) := by
    have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact (hc.comp_aestronglyMeasurable hUmeas).aemeasurable.ennreal_ofReal.pow_const _
  have hsliceU := hu'.prod_left_ae
  have hsliceU3 := hu3'.prod_left_ae
  have hgood : ∀ᵐ s ∂volume.restrict T, (∫⁻ v in B, ENNReal.ofReal
      (vec3EuclideanNorm (u (v,s) - ⨍ w in B, u (w,s))) ^ (3 : ℝ)) ≤
      8 * (∫⁻ v in B, ENNReal.ofReal (vec3EuclideanNorm (u (v,s))) ^ (3 : ℝ)) := by
    filter_upwards [hsliceU, hsliceU3] with s hs hs3
    have hh := local_ball_meanFree_lintegral_bound hr hs hs3
    exact hh
  have hgood' : ∀ᵐ s ∂volume.restrict T, (∫⁻ v in B,
      ENNReal.ofReal (vec3EuclideanNorm (meanFreeVec u x r s v)) ^ (3 : ℝ)) ≤
      8 * (∫⁻ v in B, ENNReal.ofReal (vec3EuclideanNorm (u (v,s))) ^ (3 : ℝ)) := by
    filter_upwards [hgood, hsliceU] with s hs hsU
    have heq := meanFreeVec_eq_sub_spatialAverage hsU
    convert hs using 1
    · apply lintegral_congr
      intro v
      rw [congrFun heq v]
  have hFmeas' : AEMeasurable (fun w : Vec3 × ℝ => ENNReal.ofReal
      (vec3EuclideanNorm (meanFreeVec u x r w.2 w.1)) ^ (3 : ℝ))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict (B ×ˢ T)) := by
    rw [← Measure.prod_restrict]
    exact hFmeas
  have hU3meas' : AEMeasurable (fun w : Vec3 × ℝ => ENNReal.ofReal
      (vec3EuclideanNorm (u w)) ^ (3 : ℝ))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict (B ×ˢ T)) := by
    rw [← Measure.prod_restrict]
    exact hU3meas
  have hrawprod : (∫⁻ w in B ×ˢ T, ENNReal.ofReal
      (vec3EuclideanNorm (meanFreeVec u x r w.2 w.1)) ^ (3 : ℝ)) ≤
      8 * (∫⁻ w in B ×ˢ T, ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) := by
    change (∫⁻ w in B ×ˢ T, ENNReal.ofReal
      (vec3EuclideanNorm (meanFreeVec u x r w.2 w.1)) ^ (3 : ℝ) ∂
        ((volume : Measure Vec3).prod (volume : Measure ℝ))) ≤
      8 * (∫⁻ w in B ×ˢ T, ENNReal.ofReal
        (vec3EuclideanNorm (u w)) ^ (3 : ℝ) ∂
        ((volume : Measure Vec3).prod (volume : Measure ℝ)))
    have hFub := setLIntegral_prod_symm
      (fun w : Vec3 × ℝ => ENNReal.ofReal
        (vec3EuclideanNorm (meanFreeVec u x r w.2 w.1)) ^ (3 : ℝ)) hFmeas'
    have hU3ub := setLIntegral_prod_symm
      (fun w : Vec3 × ℝ => ENNReal.ofReal
        (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) hU3meas'
    have hFub' : (∫⁻ w in B ×ˢ T, ENNReal.ofReal
        (vec3EuclideanNorm (meanFreeVec u x r w.2 w.1)) ^ (3 : ℝ) ∂
          ((volume : Measure Vec3).prod (volume : Measure ℝ))) =
        ∫⁻ s in T, ∫⁻ v in B, ENNReal.ofReal
          (vec3EuclideanNorm (meanFreeVec u x r s v)) ^ (3 : ℝ) := by
      simpa only [Prod.fst, Prod.snd] using hFub
    have hU3ub' : (∫⁻ w in B ×ˢ T, ENNReal.ofReal
        (vec3EuclideanNorm (u w)) ^ (3 : ℝ) ∂
          ((volume : Measure Vec3).prod (volume : Measure ℝ))) =
        ∫⁻ s in T, ∫⁻ v in B, ENNReal.ofReal
          (vec3EuclideanNorm (u (v,s))) ^ (3 : ℝ) := by
      simpa only [Prod.fst, Prod.snd] using hU3ub
    calc
      _ = ∫⁻ s in T, ∫⁻ v in B, ENNReal.ofReal
          (vec3EuclideanNorm (meanFreeVec u x r s v)) ^ (3 : ℝ) := by
            exact hFub'
      _ ≤ ∫⁻ s in T, 8 * (∫⁻ v in B, ENNReal.ofReal
          (vec3EuclideanNorm (u (v,s))) ^ (3 : ℝ)) := lintegral_mono_ae hgood'
      _ = 8 * (∫⁻ s in T, ∫⁻ v in B, ENNReal.ofReal
          (vec3EuclideanNorm (u (v,s))) ^ (3 : ℝ)) := by rw [lintegral_const_mul' 8 _ (by norm_num)]
      _ = 8 * (∫⁻ w in B ×ˢ T, ENNReal.ofReal
          (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) := by
            exact congrArg (fun x => 8 * x) hU3ub'.symm
  have hraw : (∫⁻ w in parabolicCylinder x t r, ENNReal.ofReal
      (vec3EuclideanNorm (meanFreeVec u x r w.2 w.1)) ^ (3 : ℝ)) ≤
      8 * (∫⁻ w in parabolicCylinder x t r, ENNReal.ofReal
        (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) := by
    rw [parabolicCylinder, CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    change (∫⁻ w in B ×ˢ T, ENNReal.ofReal
      (vec3EuclideanNorm (meanFreeVec u x r w.2 w.1)) ^ (3 : ℝ) ∂
        ((volume : Measure Vec3).prod (volume : Measure ℝ))) ≤
      8 * (∫⁻ w in B ×ˢ T, ENNReal.ofReal
        (vec3EuclideanNorm (u w)) ^ (3 : ℝ) ∂
        ((volume : Measure Vec3).prod (volume : Measure ℝ)))
    exact hrawprod
  have hChatMeas : AEStronglyMeasurable
      (fun w : ParabolicPoint => vec3EuclideanNorm
        (meanFreeVec u x r w.2 w.1) ^ (3 : ℕ))
      (volume.restrict (parabolicCylinder x t r)) := by
    rw [parabolicCylinder, CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    change AEStronglyMeasurable
      (fun w : Vec3 × ℝ => vec3EuclideanNorm
        (meanFreeVec u x r w.2 w.1) ^ (3 : ℕ))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (B ×ˢ T))
    rw [← Measure.prod_restrict]
    simpa [B, T] using (by
      have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
        unfold vec3EuclideanNorm
        fun_prop
      exact (hc.comp_aestronglyMeasurable hmeanfree).pow 3)
  have hU3MeasCyl : AEStronglyMeasurable
      (fun w : ParabolicPoint => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      (volume.restrict (parabolicCylinder x t r)) := by
    rw [parabolicCylinder, CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    change AEStronglyMeasurable
      (fun w : Vec3 × ℝ => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (B ×ˢ T))
    rw [← Measure.prod_restrict]
    simpa [B, T] using (by
      have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
        unfold vec3EuclideanNorm
        fun_prop
      exact (hc.comp_aestronglyMeasurable hUmeas).pow 3)
  have hU3Top : (∫⁻ w in parabolicCylinder x t r,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ⊤ := by
    have h := (lintegral_ofReal_ne_top_iff_integrable hU3MeasCyl
      (Eventually.of_forall fun w =>
        pow_nonneg (vec3EuclideanNorm_nonneg (u w)) 3)).2 hu3
    convert h using 1
    apply lintegral_congr
    intro w
    rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 3]
    norm_num [ENNReal.rpow_natCast]
  have hChatTop : (∫⁻ w in parabolicCylinder x t r,
      ENNReal.ofReal (vec3EuclideanNorm
        (meanFreeVec u x r w.2 w.1) ^ (3 : ℕ))) ≠ ⊤ := by
    have hlt := lt_of_le_of_lt hraw
      (ENNReal.mul_lt_top (by norm_num) hU3Top.lt_top)
    convert ne_of_lt hlt using 1
    apply lintegral_congr
    intro w
    rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 3]
    norm_num [ENNReal.rpow_natCast]
  exact (lintegral_ofReal_ne_top_iff_integrable hChatMeas
    (Eventually.of_forall fun w =>
      pow_nonneg (vec3EuclideanNorm_nonneg (meanFreeVec u x r w.2 w.1)) 3)).mp hChatTop

end CKN
