/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambda
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.WeightedLayerCake

/-!
# Integration of an untruncated weighted good-`lambda` inequality

This module closes the natural one-level estimate under the untruncated measures
`nu_f = ‖f‖^2 dmu` and `nu_g = ‖g‖^2 dmu`.  The self term is integrated only up to a
finite level `R`.  The substitution `t = 2 M s` produces the smaller cutoff `R / (2 M)`,
which is bounded by `R` when `1 / 2 < M`.  Reabsorption is therefore legitimate at every
finite cutoff, and monotone convergence then removes the cutoff without assuming `f` is in
`L^p`.
-/

@[expose] public section

namespace Homogenization

open scoped ENNReal NNReal BigOperators

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory

/-- Exact layer cake for the untruncated square weight.  This is an `ENNReal` identity, so
it does not require a finiteness assumption. -/
private theorem untruncated_weighted_layercake
    {alpha E : Type*} [MeasurableSpace alpha] [NormedAddCommGroup E]
    {mu : Measure alpha} {f : alpha -> E} {p a : Real}
    (hf : AEStronglyMeasurable f mu) (hp : 2 < p) (ha : 0 < a) :
    ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p / a ^ (p - 2)) ∂mu =
      ENNReal.ofReal (p - 2) * ∫⁻ t in Set.Ioi (0 : Real),
        sqWeightedMeasure f mu {x | a * t < ‖f x‖} *
          ENNReal.ofReal (t ^ (p - 3)) := by
  let u : alpha -> Real := fun x => ‖f x‖
  have hu : AEMeasurable u mu := hf.norm.aemeasurable
  have hdensity : AEMeasurable (fun x => ENNReal.ofReal (u x ^ (2 : Nat))) mu :=
    (hu.pow aemeasurable_const).ennreal_ofReal
  have hpower : AEMeasurable (fun x => ENNReal.ofReal ((u x / a) ^ (p - 2))) mu :=
    ((hu.div_const a).pow aemeasurable_const).ennreal_ofReal
  have hmoment :
      ∫⁻ x, ENNReal.ofReal (u x ^ p / a ^ (p - 2)) ∂mu =
        ∫⁻ x, ENNReal.ofReal ((u x / a) ^ (p - 2)) ∂sqWeightedMeasure f mu := by
    rw [sqWeightedMeasure, lintegral_withDensity_eq_lintegral_mul₀ hdensity hpower]
    apply lintegral_congr
    intro x
    have hu0 : 0 <= u x := norm_nonneg _
    have hpow : u x ^ p = u x ^ (p - 2) * u x ^ (2 : Real) := by
      calc
        u x ^ p = u x ^ (p - 2 + 2) := by ring_nf
        _ = u x ^ (p - 2) * u x ^ (2 : Real) :=
          Real.rpow_add_of_nonneg hu0 (by linarith) (by norm_num)
    have hpow_nat : u x ^ p = u x ^ (p - 2) * u x ^ (2 : Nat) := by
      rw [← Real.rpow_natCast]
      exact hpow
    have hreal : u x ^ p / a ^ (p - 2) =
        (u x / a) ^ (p - 2) * u x ^ (2 : Nat) := by
      calc
        u x ^ p / a ^ (p - 2) =
            (u x ^ (p - 2) * u x ^ (2 : Nat)) / a ^ (p - 2) :=
          congr_arg (fun z => z / a ^ (p - 2)) hpow_nat
        _ = (u x ^ (p - 2) / a ^ (p - 2)) * u x ^ (2 : Nat) := by ring
        _ = (u x / a) ^ (p - 2) * u x ^ (2 : Nat) := by
          rw [← Real.div_rpow hu0 ha.le]
    simp only [Pi.mul_apply, u]
    rw [show ‖f x‖ ^ p / a ^ (p - 2) =
      (‖f x‖ / a) ^ (p - 2) * ‖f x‖ ^ (2 : Nat) by exact hreal]
    rw [mul_comm]
    exact ENNReal.ofReal_mul (sq_nonneg ‖f x‖)
  have hu_nonneg : 0 ≤ᵐ[sqWeightedMeasure f mu] (fun x => u x / a) :=
    (withDensity_absolutelyContinuous mu _).ae_le
      (ae_of_all _ fun x => div_nonneg (norm_nonneg _) ha.le)
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul
    (sqWeightedMeasure f mu) hu_nonneg
    ((hu.div_const a).mono' (withDensity_absolutelyContinuous mu _))
    (p := p - 2) (by linarith)
  have hpow : p - 2 - 1 = p - 3 := by ring
  have hthreshold (t : Real) : {x | t < u x / a} = {x | a * t < u x} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [lt_div_iff₀ ha]
    ring_nf
  rw [hpow] at hlayer
  simpa only [u, hthreshold] using hmoment.trans hlayer

/-- The low-level portion of a weighted layer-cake integral is controlled by the total
weighted mass. -/
lemma low_weighted_layercake_le
    {alpha : Type*} [MeasurableSpace alpha] (nu : Measure alpha) {u : alpha -> Real}
    {p M lambda0 : Real} (hp : 2 < p) (hlambda0 : 0 <= lambda0) :
    ENNReal.ofReal (p - 2) *
        ∫⁻ t in Set.Ioo (0 : Real) lambda0,
          nu {x | M * t < u x} * ENNReal.ofReal (t ^ (p - 3)) <=
      nu Set.univ * ENNReal.ofReal (lambda0 ^ (p - 2)) := by
  have hr : 0 < p - 2 := by linarith
  have hconst := lintegral_rpow_eq_lintegral_meas_lt_mul nu
    (ae_of_all _ fun _ => hlambda0)
    (aemeasurable_const : AEMeasurable (fun _ : alpha => lambda0) nu)
    (p := p - 2) hr
  have htail :
      ∫⁻ t in Set.Ioo (0 : Real) lambda0,
          nu {x | M * t < u x} * ENNReal.ofReal (t ^ (p - 3)) <=
        ∫⁻ t in Set.Ioo (0 : Real) lambda0,
          nu Set.univ * ENNReal.ofReal (t ^ (p - 3)) := by
    apply lintegral_mono
    intro t
    simpa only [mul_comm] using
      mul_le_mul_right (measure_mono (Set.subset_univ _))
        (ENNReal.ofReal (t ^ (p - 3)))
  have hconst_tail :
      ∫⁻ t in Set.Ioo (0 : Real) lambda0,
          nu Set.univ * ENNReal.ofReal (t ^ (p - 3)) <=
        ∫⁻ t in Set.Ioi (0 : Real),
          nu {x | t < lambda0} * ENNReal.ofReal (t ^ (p - 3)) := by
    calc
      ∫⁻ t in Set.Ioo (0 : Real) lambda0,
          nu Set.univ * ENNReal.ofReal (t ^ (p - 3)) <=
          ∫⁻ t in Set.Ioo (0 : Real) lambda0,
            nu {x | t < lambda0} * ENNReal.ofReal (t ^ (p - 3)) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
        have hset : {x : alpha | t < lambda0} = Set.univ := by
          ext x
          simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          exact ht.2
        rw [hset]
      _ <= ∫⁻ t in Set.Ioi (0 : Real),
          nu {x | t < lambda0} * ENNReal.ofReal (t ^ (p - 3)) :=
        lintegral_mono_set (fun _ ht => ht.1)
  have hpow : p - 2 - 1 = p - 3 := by ring
  rw [hpow] at hconst
  calc
    ENNReal.ofReal (p - 2) *
        ∫⁻ t in Set.Ioo (0 : Real) lambda0,
          nu {x | M * t < u x} * ENNReal.ofReal (t ^ (p - 3)) <=
        ENNReal.ofReal (p - 2) *
          ∫⁻ t in Set.Ioi (0 : Real),
            nu {x | t < lambda0} * ENNReal.ofReal (t ^ (p - 3)) := by
      exact mul_le_mul_right (htail.trans hconst_tail) (ENNReal.ofReal (p - 2))
    _ = nu Set.univ * ENNReal.ofReal (lambda0 ^ (p - 2)) := by
      rw [← hconst, lintegral_const]
      ring

/-- The finite layer-cutoff integral used in the reabsorption argument. -/
private def cutoffTailMoment
    {alpha : Type*} [MeasurableSpace alpha]
    (nu : Measure alpha) (u : alpha -> Real) (p a R : Real) : ENNReal :=
  ENNReal.ofReal (p - 2) * ∫⁻ t in Set.Ioo (0 : Real) R,
    nu {x | a * t < u x} * ENNReal.ofReal (t ^ (p - 3))

/-- Change variables in a finite Lebesgue integral by a positive dilation. -/
private theorem setLIntegral_comp_mul_left
    {H : Real -> ENNReal} (hH : Measurable H) {c R : Real} (hc : 0 < c) :
    ∫⁻ t in Set.Ioo (0 : Real) R, H t =
      ENNReal.ofReal c * ∫⁻ s in Set.Ioo (0 : Real) (R / c), H (c * s) := by
  calc
    ∫⁻ t in Set.Ioo (0 : Real) R, H t ∂volume =
        ∫⁻ t in Set.Ioo (0 : Real) R, H t
          ∂(ENNReal.ofReal c • Measure.map (c * ·) volume) := by
      have hm : ENNReal.ofReal c • Measure.map (c * ·) volume = volume := by
        simpa only [abs_of_pos hc] using Real.smul_map_volume_mul_left hc.ne'
      rw [hm]
    _ = ENNReal.ofReal c *
        ∫⁻ t in Set.Ioo (0 : Real) R, H t ∂Measure.map (c * ·) volume := by
      rw [setLIntegral_smul_measure]
      rfl
    _ = ENNReal.ofReal c *
        ∫⁻ s in (c * ·) ⁻¹' Set.Ioo (0 : Real) R, H (c * s) := by
      rw [setLIntegral_map measurableSet_Ioo hH (measurable_const_mul c)]
    _ = ENNReal.ofReal c *
        ∫⁻ s in Set.Ioo (0 : Real) (R / c), H (c * s) := by
      rw [Set.preimage_const_mul_Ioo₀ (0 : Real) R hc, zero_div]

/-- With `t = 2 M s`, the finite self-tail integral scales by `(2 M)^(p - 2)` and
acquires the smaller cutoff `R / (2 M)`. -/
private theorem cutoff_self_tail_eq
    {alpha : Type*} [MeasurableSpace alpha] (nu : Measure alpha) (u : alpha -> Real)
    {p M R : Real} (hM : 0 < M) :
    ENNReal.ofReal (p - 2) * ∫⁻ t in Set.Ioo (0 : Real) R,
        nu {x | t / 2 < u x} * ENNReal.ofReal (t ^ (p - 3)) =
      ENNReal.ofReal ((2 * M) ^ (p - 2)) * cutoffTailMoment nu u p M (R / (2 * M)) := by
  let k : Real := 2 * M
  let F : Real -> ENNReal := fun t => nu {x | t / 2 < u x}
  let w : Real -> ENNReal := fun t => ENNReal.ofReal (t ^ (p - 3))
  have hk : 0 < k := mul_pos (by norm_num) hM
  have hF : Measurable F := by
    refine Antitone.measurable (show Antitone F from ?_)
    intro s t hst
    exact measure_mono fun x hx =>
      lt_of_le_of_lt (div_le_div_of_nonneg_right hst (by norm_num)) hx
  have hw : Measurable w :=
    (measurable_id.pow measurable_const).ennreal_ofReal
  have hscale := setLIntegral_comp_mul_left (H := fun t => F t * w t)
    (hF.mul hw) (R := R) hk
  have hintegrand :
      ∫⁻ s in Set.Ioo (0 : Real) (R / k), F (k * s) * w (k * s) =
        ENNReal.ofReal (k ^ (p - 3)) *
          ∫⁻ s in Set.Ioo (0 : Real) (R / k),
            nu {x | M * s < u x} * w s := by
    rw [← lintegral_const_mul'' _
      (show AEMeasurable (fun s => nu {x : alpha | M * s < u x} * w s)
          (volume.restrict (Set.Ioo (0 : Real) (R / k))) from
        (((Antitone.measurable (show Antitone
          (fun s : Real => nu {x : alpha | M * s < u x}) from by
            intro s t hst
            exact measure_mono fun x hx =>
              lt_of_le_of_lt (mul_le_mul_of_nonneg_left hst hM.le) hx)).aemeasurable).mul
          hw.aemeasurable).restrict)]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with s hs
    have hset : {x : alpha | k * s / 2 < u x} = {x | M * s < u x} := by
      ext x
      simp only [k, Set.mem_ofPred_eq]
      ring_nf
    have hrpow : (k * s) ^ (p - 3) = k ^ (p - 3) * s ^ (p - 3) :=
      Real.mul_rpow hk.le hs.1.le
    simp only [F, w, hset, hrpow]
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hk.le _)]
    ring
  have hkp : k ^ (p - 2) = k * k ^ (p - 3) := by
    calc
      k ^ (p - 2) = k ^ ((1 : Real) + (p - 3)) := by ring_nf
      _ = k ^ (1 : Real) * k ^ (p - 3) := Real.rpow_add hk _ _
      _ = k * k ^ (p - 3) := by rw [Real.rpow_one]
  simp only [F, w] at hscale
  rw [hscale]
  simp only [k, cutoffTailMoment] at hintegrand ⊢
  rw [hintegrand]
  rw [hkp, ENNReal.ofReal_mul hk.le]
  ring

/-- Scalar integration of a pointwise inequality on the finite high-level interval. -/
private theorem lintegral_Ico_mul_le_of_pointwise
    {L F G w : Real -> ENNReal} {lambda0 R : Real} {c theta B : ENNReal}
    (hlambda0 : 0 < lambda0)
    (hpoint : ∀ t ∈ Set.Ico lambda0 R, L t <= theta * F t + B * G t)
    (hF : AEMeasurable F volume) (hG : AEMeasurable G volume)
    (hw : Measurable w) :
    c * ∫⁻ t in Set.Ico lambda0 R, L t * w t <=
      theta * (c * ∫⁻ t in Set.Ioo (0 : Real) R, F t * w t) +
        B * (c * ∫⁻ t in Set.Ioi (0 : Real), G t * w t) := by
  have hFw : AEMeasurable (fun t => F t * w t) volume := hF.mul hw.aemeasurable
  have hGw : AEMeasurable (fun t => G t * w t) volume := hG.mul hw.aemeasurable
  have hmono : ∀ᵐ t ∂volume.restrict (Set.Ico lambda0 R),
      L t * w t <= (theta * F t + B * G t) * w t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ico] with t ht
    simpa only [mul_comm] using mul_le_mul_right (hpoint t ht) (w t)
  have hsplit :
      ∫⁻ t in Set.Ico lambda0 R, (theta * F t + B * G t) * w t =
        (∫⁻ t in Set.Ico lambda0 R, theta * (F t * w t)) +
          ∫⁻ t in Set.Ico lambda0 R, B * (G t * w t) := by
    calc
      ∫⁻ t in Set.Ico lambda0 R, (theta * F t + B * G t) * w t =
          ∫⁻ t in Set.Ico lambda0 R, theta * (F t * w t) + B * (G t * w t) := by
        apply lintegral_congr_ae
        filter_upwards with t
        ring
      _ = (∫⁻ t in Set.Ico lambda0 R, theta * (F t * w t)) +
          ∫⁻ t in Set.Ico lambda0 R, B * (G t * w t) := by
        rw [lintegral_add_left' (hFw.restrict.const_mul theta)]
  have hF_restrict :
      ∫⁻ t in Set.Ico lambda0 R, F t * w t <=
        ∫⁻ t in Set.Ioo (0 : Real) R, F t * w t :=
    lintegral_mono_set fun _ ht => ⟨lt_of_lt_of_le hlambda0 ht.1, ht.2⟩
  have hG_restrict :
      ∫⁻ t in Set.Ico lambda0 R, G t * w t <=
        ∫⁻ t in Set.Ioi (0 : Real), G t * w t :=
    lintegral_mono_set fun _ ht => lt_of_lt_of_le hlambda0 ht.1
  calc
    c * ∫⁻ t in Set.Ico lambda0 R, L t * w t <=
        c * ∫⁻ t in Set.Ico lambda0 R, (theta * F t + B * G t) * w t :=
      mul_le_mul_right (lintegral_mono_ae hmono) c
    _ = c * ((∫⁻ t in Set.Ico lambda0 R, theta * (F t * w t)) +
          ∫⁻ t in Set.Ico lambda0 R, B * (G t * w t)) := by rw [hsplit]
    _ <= c * (theta * (∫⁻ t in Set.Ioo (0 : Real) R, F t * w t) +
          B * (∫⁻ t in Set.Ioi (0 : Real), G t * w t)) := by
      apply mul_le_mul_right
      apply add_le_add
      · rw [lintegral_const_mul'' theta hFw.restrict]
        exact mul_le_mul_right hF_restrict theta
      · rw [lintegral_const_mul'' B hGw.restrict]
        exact mul_le_mul_right hG_restrict B
    _ = theta * (c * ∫⁻ t in Set.Ioo (0 : Real) R, F t * w t) +
        B * (c * ∫⁻ t in Set.Ioi (0 : Real), G t * w t) := by
      rw [mul_add]
      ac_rfl

/-- The exact untruncated data moment with the threshold written as `eps * t / 2`. -/
private theorem data_weighted_layercake
    {alpha E : Type*} [MeasurableSpace alpha] [NormedAddCommGroup E]
    {mu : Measure alpha} {g : alpha -> E} {p eps : Real}
    (hg : AEStronglyMeasurable g mu) (hp : 2 < p) (heps : 0 < eps) :
    ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p / (eps / 2) ^ (p - 2)) ∂mu =
      ENNReal.ofReal (p - 2) * ∫⁻ t in Set.Ioi (0 : Real),
        sqWeightedMeasure g mu {x | eps * t / 2 < ‖g x‖} *
          ENNReal.ofReal (t ^ (p - 3)) := by
  have hlayer := untruncated_weighted_layercake hg hp
    (by positivity : (0 : Real) < eps / 2)
  have hthreshold (t : Real) :
      {x | eps / 2 * t < ‖g x‖} = {x | eps * t / 2 < ‖g x‖} := by
    ext x
    ring_nf
  simpa only [hthreshold] using hlayer

/-- The natural one-level estimate integrated up to a finite cutoff `R`. -/
private theorem cutoffTailMoment_le
    {alpha E F : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {mu : Measure alpha} {f : alpha -> E} {g : alpha -> F}
    {p M eps lambda0 R : Real} {theta B : ENNReal}
    (hg : AEStronglyMeasurable g mu)
    (hp : 2 < p) (hM : 0 < M) (hhalfM : (1 / 2 : Real) < M) (heps : 0 < eps)
    (hlambda0 : 0 < lambda0) (hR : lambda0 < R)
    (h_tail : forall t, lambda0 <= t ->
      sqWeightedMeasure f mu {x | M * t < ‖f x‖} <=
        theta * sqWeightedMeasure f mu {x | t / 2 < ‖f x‖} +
          B * sqWeightedMeasure g mu {x | eps * t / 2 < ‖g x‖}) :
    cutoffTailMoment (sqWeightedMeasure f mu) (fun x => ‖f x‖) p M R <=
      sqWeightedMeasure f mu Set.univ * ENNReal.ofReal (lambda0 ^ (p - 2)) +
        theta * ENNReal.ofReal ((2 * M) ^ (p - 2)) *
          cutoffTailMoment (sqWeightedMeasure f mu) (fun x => ‖f x‖) p M R +
        B * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p / (eps / 2) ^ (p - 2)) ∂mu := by
  let nuf := sqWeightedMeasure f mu
  let nug := sqWeightedMeasure g mu
  let u : alpha -> Real := fun x => ‖f x‖
  let v : alpha -> Real := fun x => ‖g x‖
  let w : Real -> ENNReal := fun t => ENNReal.ofReal (t ^ (p - 3))
  let c : ENNReal := ENNReal.ofReal (p - 2)
  have hR0 : 0 < R := hlambda0.trans hR
  have hself_meas : AEMeasurable (fun t => nuf {x | t / 2 < u x}) volume := by
    refine (Antitone.measurable (show Antitone
      (fun t : Real => nuf {x : alpha | t / (2 : Real) < u x}) from ?_)).aemeasurable
    intro s t hst
    exact measure_mono fun x hx =>
      lt_of_le_of_lt (div_le_div_of_nonneg_right hst (by norm_num)) hx
  have hdata_meas : AEMeasurable (fun t => nug {x | eps * t / 2 < v x}) volume := by
    refine (Antitone.measurable (show Antitone
      (fun t : Real => nug {x : alpha | eps * t / (2 : Real) < v x}) from ?_)).aemeasurable
    intro s t hst
    exact measure_mono fun x hx => lt_of_le_of_lt
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hst heps.le) (by norm_num)) hx
  have hpoint (t : Real) (ht : t ∈ Set.Ico lambda0 R) :
      nuf {x | M * t < u x} <= theta * nuf {x | t / 2 < u x} +
        B * nug {x | eps * t / 2 < v x} := by
    simpa only [nuf, nug, u, v] using h_tail t ht.1
  have hhigh := lintegral_Ico_mul_le_of_pointwise
    (L := fun t => nuf {x | M * t < u x})
    (F := fun t => nuf {x | t / 2 < u x})
    (G := fun t => nug {x | eps * t / 2 < v x}) (w := w)
    (lambda0 := lambda0) (R := R) (c := c) (theta := theta) (B := B)
    hlambda0 hpoint hself_meas hdata_meas
    (measurable_id.pow measurable_const).ennreal_ofReal
  have hscale := cutoff_self_tail_eq nuf u (p := p) (R := R) hM
  have hkpos : 0 < 2 * M := mul_pos (by norm_num) hM
  have hRdiv : R / (2 * M) <= R := by
    rw [div_le_iff₀ hkpos]
    nlinarith [hhalfM]
  have hcut_mono :
      cutoffTailMoment nuf u p M (R / (2 * M)) <= cutoffTailMoment nuf u p M R := by
    apply mul_le_mul_right
    apply lintegral_mono_set
    intro t ht
    exact ⟨ht.1, ht.2.trans_le hRdiv⟩
  have hdata_layer := data_weighted_layercake hg hp heps
  have hhigh' :
      c * ∫⁻ t in Set.Ico lambda0 R, nuf {x | M * t < u x} * w t <=
        theta * ENNReal.ofReal ((2 * M) ^ (p - 2)) * cutoffTailMoment nuf u p M R +
          B * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p / (eps / 2) ^ (p - 2)) ∂mu := by
    rw [hscale] at hhigh
    rw [← hdata_layer] at hhigh
    calc
      c * ∫⁻ t in Set.Ico lambda0 R, nuf {x | M * t < u x} * w t <=
          theta * (ENNReal.ofReal ((2 * M) ^ (p - 2)) *
            cutoffTailMoment nuf u p M (R / (2 * M))) +
            B * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p / (eps / 2) ^ (p - 2)) ∂mu := hhigh
      _ <= theta * (ENNReal.ofReal ((2 * M) ^ (p - 2)) *
            cutoffTailMoment nuf u p M R) +
            B * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p / (eps / 2) ^ (p - 2)) ∂mu := by
        gcongr
      _ = theta * ENNReal.ofReal ((2 * M) ^ (p - 2)) *
            cutoffTailMoment nuf u p M R +
            B * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p / (eps / 2) ^ (p - 2)) ∂mu := by
        rw [mul_assoc]
  have hlow := low_weighted_layercake_le nuf (u := u) (p := p) (M := M)
    hp hlambda0.le
  have hsplit_sets :
      Set.Ioo (0 : Real) lambda0 ∪ Set.Ico lambda0 R = Set.Ioo 0 R := by
    ext t
    constructor
    · intro ht
      rcases ht with ht | ht
      · exact ⟨ht.1, ht.2.trans hR⟩
      · exact ⟨hlambda0.trans_le ht.1, ht.2⟩
    · intro ht
      by_cases htl : t < lambda0
      · exact Or.inl ⟨ht.1, htl⟩
      · exact Or.inr ⟨le_of_not_gt htl, ht.2⟩
  have hdisjoint : Disjoint (Set.Ioo (0 : Real) lambda0) (Set.Ico lambda0 R) :=
    Set.disjoint_left.2 fun _ ht ht' => (not_lt_of_ge ht'.1) ht.2
  have hsplit :
      ∫⁻ t in Set.Ioo (0 : Real) R, nuf {x | M * t < u x} * w t =
        (∫⁻ t in Set.Ioo (0 : Real) lambda0, nuf {x | M * t < u x} * w t) +
          ∫⁻ t in Set.Ico lambda0 R, nuf {x | M * t < u x} * w t := by
    rw [← hsplit_sets]
    exact lintegral_union measurableSet_Ico hdisjoint
  simp only [cutoffTailMoment, nuf, u, w, c] at hlow hhigh' hsplit ⊢
  calc
    ENNReal.ofReal (p - 2) * ∫⁻ t in Set.Ioo (0 : Real) R,
        sqWeightedMeasure f mu {x | M * t < ‖f x‖} * ENNReal.ofReal (t ^ (p - 3)) =
      (ENNReal.ofReal (p - 2) * ∫⁻ t in Set.Ioo (0 : Real) lambda0,
        sqWeightedMeasure f mu {x | M * t < ‖f x‖} * ENNReal.ofReal (t ^ (p - 3))) +
      ENNReal.ofReal (p - 2) * ∫⁻ t in Set.Ico lambda0 R,
        sqWeightedMeasure f mu {x | M * t < ‖f x‖} * ENNReal.ofReal (t ^ (p - 3)) := by
      rw [hsplit, mul_add]
    _ <= sqWeightedMeasure f mu Set.univ * ENNReal.ofReal (lambda0 ^ (p - 2)) +
        (theta * ENNReal.ofReal ((2 * M) ^ (p - 2)) *
          (ENNReal.ofReal (p - 2) * ∫⁻ t in Set.Ioo (0 : Real) R,
            sqWeightedMeasure f mu {x | M * t < ‖f x‖} * ENNReal.ofReal (t ^ (p - 3))) +
          B * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p / (eps / 2) ^ (p - 2)) ∂mu) :=
      add_le_add hlow hhigh'
    _ = _ := by rw [add_assoc]

/-- Reabsorption in `ENNReal`, performed through `toReal` after both sides have been shown
finite. -/
private theorem ennreal_reabsorb {rho X K : ENNReal}
    (hrho : rho < 1) (hX : X ≠ ∞) (hK : K ≠ ∞)
    (h : X <= K + rho * X) :
    X <= K / (1 - rho) := by
  have hrho_top : rho ≠ ∞ := ne_top_of_lt (hrho.trans_le le_top)
  have hrhs : K + rho * X ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hK, ENNReal.mul_ne_top hrho_top hX⟩
  have hrho_real : rho.toReal < 1 := by
    rw [← ENNReal.toReal_one, ENNReal.toReal_lt_toReal hrho_top ENNReal.one_ne_top]
    exact hrho
  have hreal : X.toReal <= rho.toReal * X.toReal + K.toReal := by
    have ht := (ENNReal.toReal_le_toReal hX hrhs).2 h
    rw [ENNReal.toReal_add hK (ENNReal.mul_ne_top hrho_top hX), ENNReal.toReal_mul] at ht
    linarith
  have hreabsorbed := goodLambda_reabsorb
    (θ := rho.toReal) (X := X.toReal) (C := (1 : Real)) (Y := K.toReal)
      hrho_real (by simpa only [one_mul] using hreal)
  have hdenom_ne : 1 - rho ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hrho)
  rw [← ENNReal.toReal_le_toReal hX (ENNReal.div_ne_top hK hdenom_ne)]
  rw [ENNReal.toReal_div, ENNReal.toReal_sub_of_le (le_of_lt hrho) ENNReal.one_ne_top,
    ENNReal.toReal_one]
  simpa only [one_div, one_mul, div_eq_inv_mul, mul_comm] using hreabsorbed

/-- Every finite layer cutoff obeys the same reabsorbed estimate. -/
private theorem cutoffTailMoment_reabsorbed
    {alpha E F : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {mu : Measure alpha} {f : alpha -> E} {g : alpha -> F}
    {p M eps lambda0 R : Real} {theta B : ENNReal}
    (hg : AEStronglyMeasurable g mu)
    (hp : 2 < p) (hM : 0 < M) (hhalfM : (1 / 2 : Real) < M) (heps : 0 < eps)
    (hlambda0 : 0 < lambda0) (hR : lambda0 < R)
    (hnuf : sqWeightedMeasure f mu Set.univ ≠ ∞)
    (hB : B ≠ ∞)
    (hdata : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p / (eps / 2) ^ (p - 2)) ∂mu) ≠ ∞)
    (hsmall : theta * ENNReal.ofReal ((2 * M) ^ (p - 2)) < 1)
    (h_tail : forall t, lambda0 <= t ->
      sqWeightedMeasure f mu {x | M * t < ‖f x‖} <=
        theta * sqWeightedMeasure f mu {x | t / 2 < ‖f x‖} +
          B * sqWeightedMeasure g mu {x | eps * t / 2 < ‖g x‖}) :
    cutoffTailMoment (sqWeightedMeasure f mu) (fun x => ‖f x‖) p M R <=
      (sqWeightedMeasure f mu Set.univ * ENNReal.ofReal (lambda0 ^ (p - 2)) +
          B * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p / (eps / 2) ^ (p - 2)) ∂mu) /
        (1 - theta * ENNReal.ofReal ((2 * M) ^ (p - 2))) := by
  let X := cutoffTailMoment (sqWeightedMeasure f mu) (fun x => ‖f x‖) p M R
  let A := sqWeightedMeasure f mu Set.univ * ENNReal.ofReal (lambda0 ^ (p - 2))
  let D := ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p / (eps / 2) ^ (p - 2)) ∂mu
  let rho := theta * ENNReal.ofReal ((2 * M) ^ (p - 2))
  let K := A + B * D
  have hR0 : 0 < R := hlambda0.trans hR
  have hX_le := low_weighted_layercake_le (sqWeightedMeasure f mu)
    (u := fun x => ‖f x‖) (p := p) (M := M) hp hR0.le
  have hX : X ≠ ∞ := by
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hnuf ENNReal.ofReal_ne_top)
    simpa only [X, cutoffTailMoment] using hX_le
  have hA : A ≠ ∞ := ENNReal.mul_ne_top hnuf ENNReal.ofReal_ne_top
  have hK : K ≠ ∞ := by
    exact ENNReal.add_ne_top.2 ⟨hA, ENNReal.mul_ne_top hB hdata⟩
  have hfinite := cutoffTailMoment_le hg hp hM hhalfM heps hlambda0 hR h_tail
  have hineq : X <= K + rho * X := by
    calc
      X <= A + rho * X + B * D := by
        simpa only [X, A, D, rho] using hfinite
      _ = K + rho * X := by
        change (A + rho * X) + B * D = (A + B * D) + rho * X
        calc
          (A + rho * X) + B * D = A + (rho * X + B * D) := add_assoc _ _ _
          _ = A + (B * D + rho * X) := congr_arg (fun z : ENNReal => A + z)
            (add_comm (rho * X) (B * D))
          _ = (A + B * D) + rho * X := (add_assoc _ _ _).symm
  simpa only [X, A, D, rho, K] using ennreal_reabsorb hsmall hX hK hineq

/-- Increasing finite intervals exhaust the positive half-line. -/
private theorem setLIntegral_Ioo_iSup
    (H : Real -> ENNReal) (hH : Measurable H) {lambda0 : Real} :
    ∫⁻ t in Set.Ioi (0 : Real), H t =
      ⨆ n : Nat, ∫⁻ t in Set.Ioo (0 : Real) (lambda0 + n + 1), H t := by
  let S : Nat -> Set Real := fun n => Set.Ioo (0 : Real) (lambda0 + n + 1)
  let hfun : Nat -> Real -> ENNReal := fun n => (S n).indicator H
  have hS_mono : Monotone S := by
    intro n m hnm t ht
    have hcast : (n : Real) <= (m : Real) := by exact_mod_cast hnm
    exact ⟨ht.1, lt_of_lt_of_le ht.2 (by linarith)⟩
  have hh_meas : forall n, AEMeasurable (hfun n) volume := fun n =>
    (hH.indicator measurableSet_Ioo).aemeasurable
  have hh_mono : forall t, Monotone fun n => hfun n t := by
    intro t n m hnm
    by_cases hnt : t ∈ S n
    · simp only [hfun, Set.indicator_of_mem hnt,
        Set.indicator_of_mem (hS_mono hnm hnt)]
      exact le_rfl
    · simp only [hfun, Set.indicator_of_notMem hnt]
      exact bot_le
  have hiSup_h : (fun t => ⨆ n, hfun n t) = (Set.Ioi (0 : Real)).indicator H := by
    funext t
    apply le_antisymm
    · refine iSup_le fun n => ?_
      by_cases hnt : t ∈ S n
      · simp only [hfun, Set.indicator_of_mem hnt]
        have htarget : (Set.Ioi (0 : Real)).indicator H t = H t :=
          Set.indicator_of_mem hnt.1 H
        rw [htarget]
      · simp only [hfun, Set.indicator_of_notMem hnt]
        exact bot_le
    · by_cases ht : t ∈ Set.Ioi (0 : Real)
      · rw [Set.indicator_of_mem ht]
        obtain ⟨n, hn⟩ := exists_nat_gt (t - lambda0 - 1)
        have hnt : t ∈ S n := by
          exact ⟨ht, by exact_mod_cast (show t < lambda0 + (n : Real) + 1 by linarith)⟩
        exact le_iSup_of_le n (by
          simp only [hfun, Set.indicator_of_mem hnt]
          exact le_rfl)
      · rw [Set.indicator_of_notMem ht]
        exact bot_le
  calc
    ∫⁻ t in Set.Ioi (0 : Real), H t =
        ∫⁻ t, (Set.Ioi (0 : Real)).indicator H t := by
      rw [lintegral_indicator measurableSet_Ioi]
    _ = ∫⁻ t, ⨆ n, hfun n t := by rw [hiSup_h]
    _ = ⨆ n, ∫⁻ t, hfun n t := lintegral_iSup' hh_meas (ae_of_all _ hh_mono)
    _ = ⨆ n : Nat, ∫⁻ t in Set.Ioo (0 : Real) (lambda0 + n + 1), H t := by
      congr with n
      simp only [hfun, S]
      rw [lintegral_indicator measurableSet_Ioo]

/-- Integrate and reabsorb the natural untruncated weighted good-`lambda` estimate.

The only finiteness assumptions used before the conclusion are the finite square-weighted
mass of `f`, the finite displayed data moment, and the finiteness of the scalar coefficient
`B`.  In particular, there is no `L^p` hypothesis on `f`. -/
theorem lp_le_of_oneLevel_weighted_tail
    {alpha E F : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {mu : Measure alpha} {f : alpha -> E} {g : alpha -> F}
    {p M eps lambda0 : Real} {theta B : ENNReal}
    (hf : AEStronglyMeasurable f mu) (hg : AEStronglyMeasurable g mu)
    (hp : 2 < p) (hM : 0 < M) (hhalfM : (1 / 2 : Real) < M) (heps : 0 < eps)
    (hlambda0 : 0 < lambda0)
    (hnuf : sqWeightedMeasure f mu Set.univ ≠ ∞)
    (hB : B ≠ ∞)
    (hdata : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p / (eps / 2) ^ (p - 2)) ∂mu) ≠ ∞)
    (hsmall : theta * ENNReal.ofReal ((2 * M) ^ (p - 2)) < 1)
    (h_tail : forall t, lambda0 <= t ->
      sqWeightedMeasure f mu {x | M * t < ‖f x‖} <=
        theta * sqWeightedMeasure f mu {x | t / 2 < ‖f x‖} +
          B * sqWeightedMeasure g mu {x | eps * t / 2 < ‖g x‖}) :
    ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p / M ^ (p - 2)) ∂mu <=
      (sqWeightedMeasure f mu Set.univ * ENNReal.ofReal (lambda0 ^ (p - 2)) +
          B * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p / (eps / 2) ^ (p - 2)) ∂mu) /
        (1 - theta * ENNReal.ofReal ((2 * M) ^ (p - 2))) := by
  let nuf := sqWeightedMeasure f mu
  let u : alpha -> Real := fun x => ‖f x‖
  let H : Real -> ENNReal := fun t =>
    nuf {x | M * t < u x} * ENNReal.ofReal (t ^ (p - 3))
  let K : ENNReal :=
    (sqWeightedMeasure f mu Set.univ * ENNReal.ofReal (lambda0 ^ (p - 2)) +
        B * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p / (eps / 2) ^ (p - 2)) ∂mu) /
      (1 - theta * ENNReal.ofReal ((2 * M) ^ (p - 2)))
  have hH : Measurable H := by
    have htail_meas : Measurable (fun t => nuf {x | M * t < u x}) := by
      refine Antitone.measurable (show Antitone
        (fun t : Real => nuf {x : alpha | M * t < u x}) from ?_)
      intro s t hst
      exact measure_mono fun x hx =>
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left hst hM.le) hx
    exact htail_meas.mul (measurable_id.pow measurable_const).ennreal_ofReal
  have hexhaust := setLIntegral_Ioo_iSup H hH (lambda0 := lambda0)
  have hfull : ENNReal.ofReal (p - 2) * ∫⁻ t in Set.Ioi (0 : Real), H t <= K := by
    rw [hexhaust, ENNReal.mul_iSup]
    apply iSup_le
    intro n
    have hR : lambda0 < lambda0 + (n : Real) + 1 := by
      have hn0 : 0 ≤ (n : Real) := Nat.cast_nonneg n
      linarith
    have hn := cutoffTailMoment_reabsorbed hg hp hM hhalfM heps hlambda0 hR
      hnuf hB hdata hsmall h_tail
    simpa only [K, cutoffTailMoment, nuf, u, H] using hn
  have hlayer := untruncated_weighted_layercake hf hp hM
  calc
    ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p / M ^ (p - 2)) ∂mu =
        ENNReal.ofReal (p - 2) * ∫⁻ t in Set.Ioi (0 : Real), H t := by
      simpa only [H, nuf, u] using hlayer
    _ <= K := hfull
    _ = _ := rfl

end CubeCalderonZygmund

end

end Homogenization
