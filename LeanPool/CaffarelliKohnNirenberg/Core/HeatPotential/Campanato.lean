/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.Exponents
public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.Kernel
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.CampanatoHolderCorollaries
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Campanato

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter


noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Heat CKN.Foundation.Parabolic



def heatPotentialShellValue (F : ParabolicPoint → ℝ)
    (G : Fin 3 → ParabolicPoint → ℝ) (S : Set ParabolicPoint)
    (w : ParabolicPoint) : ℝ :=
  (∫ v in S, heatPotentialKernel w v * F v) +
    ∑ i, ∫ v in S, heatPotentialSpatialKernel i w v * G i v

lemma heatPotential_single_kernel_shell_bound {K : ParabolicPoint → ParabolicPoint → ℝ}
    {f : ParabolicPoint → ℝ} {S : Set ParabolicPoint}
    {p p' : ParabolicPoint} {C : ℝ}
    (_ : 0 ≤ C)
    (hS : MeasurableSet S)
    (hwi : IntegrableOn (fun v => K p v * f v) S volume)
    (hwi' : IntegrableOn (fun v => K p' v * f v) S volume)
    (hmajor : IntegrableOn (fun v => C * |f v|) S volume)
    (hpoint : ∀ v ∈ S, |K p v - K p' v| ≤ C) :
    |(∫ v in S, K p v * f v) - ∫ v in S, K p' v * f v| ≤
      C * ∫ v in S, |f v| := by
  have hdiff : IntegrableOn
      (fun v => K p v * f v - K p' v * f v) S volume := hwi.sub hwi'
  have hbound : ∀ᵐ v ∂(volume.restrict S),
      |K p v * f v - K p' v * f v| ≤ C * |f v| := by
    filter_upwards [MeasureTheory.ae_restrict_mem hS] with v hv
    rw [show K p v * f v - K p' v * f v = (K p v - K p' v) * f v by ring,
      abs_mul]
    exact mul_le_mul_of_nonneg_right (hpoint v hv) (abs_nonneg _)
  calc
    |(∫ v in S, K p v * f v) - ∫ v in S, K p' v * f v| =
        |∫ v in S, (K p v * f v - K p' v * f v)| := by
      rw [integral_sub hwi hwi']
    _ ≤ ∫ v in S, |K p v * f v - K p' v * f v| :=
      by simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (μ := volume.restrict S)
          (fun v => K p v * f v - K p' v * f v)).trans_eq rfl
    _ ≤ ∫ v in S, C * |f v| :=
      MeasureTheory.integral_mono_ae hdiff.norm hmajor hbound
    _ = C * ∫ v in S, |f v| := by rw [integral_const_mul]



lemma heatPotential_campanato_bound_of_pairwise
    {h : ParabolicPoint → ℝ} {z : ParabolicPoint} {r α K p : ℝ}
    (hr : 0 < r) (_ : 0 ≤ α) (hp : 1 ≤ p) (hK : 0 ≤ K)
    (hint : IntegrableOn h
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) volume)
    (hfp : IntegrableOn
      (fun q => |h q - ⨍ x in
        @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r, h x| ^ p)
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) volume)
    (hpair : ∀ w ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r,
      ∀ w' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r,
        |h w - h w'| ≤ K * r ^ α) :
    ParabolicBallLpOscillation h z r p ≤ K * r ^ α := by
  let B : Set ParabolicPoint :=
    @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r
  let C : ℝ := K * r ^ α
  have hBpos : 0 < volume B := by
    dsimp [B]
    exact parabolicBall_closedBall_pos hr
  have hBtop : volume B < ∞ := by
    dsimp [B]
    exact parabolicBall_closedBall_top hr
  have hB : MeasurableSet B := by
    dsimp [B]
    exact measurableSet_closedBall
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg hK (Real.rpow_nonneg hr.le _)
  have hp0lt : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpoint : ∀ w ∈ B,
      |h w - ⨍ v in B, h v| ≤ C := by
    intro w hw
    have hconst : IntegrableOn (fun _ : ParabolicPoint => h w) B volume :=
      integrableOn_const hBtop.ne
    have hsub : IntegrableOn (fun v => h w - h v) B volume := hconst.sub hint
    have havgsub : (⨍ v in B, h w - h v) = h w - ⨍ v in B, h v := by
      rw [show (fun v => h w - h v) = (fun v => h w) - h by
        funext v
        rfl,
        MeasureTheory.setAverage_sub hconst hint,
        MeasureTheory.setAverage_const hBpos.ne' hBtop.ne]
    have havgnorm := Integration.setAverage_norm_le volume B
      (fun v => h w - h v)
    rw [havgsub] at havgnorm
    have havgabs : |h w - ⨍ v in B, h v| ≤
        ⨍ v in B, |h w - h v| := by
      simpa only [Real.norm_eq_abs] using havgnorm
    have hmono : (⨍ v in B, |h w - h v|) ≤ C := by
      calc
        (⨍ v in B, |h w - h v|) ≤ ⨍ v in B, C := by
          apply Integration.setAverage_mono_of_ae hsub.norm
            (integrableOn_const hBtop.ne)
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_closedBall] with v hv
          exact hpair w (by simpa [B] using hw) v (by simpa [B] using hv)
        _ = C := MeasureTheory.setAverage_const hBpos.ne' hBtop.ne _
    exact havgabs.trans hmono
  have hpow : ∀ᵐ w ∂(volume.restrict B),
      |h w - ⨍ v in B, h v| ^ p ≤ C ^ p := by
    filter_upwards [MeasureTheory.ae_restrict_mem hB] with w hw
    exact Real.rpow_le_rpow (abs_nonneg _) (hpoint w hw) hp0lt.le
  have hpow_int : IntegrableOn
      (fun w => C ^ p) B volume := integrableOn_const hBtop.ne
  have hpow_avg : (⨍ w in B,
      |h w - ⨍ v in B, h v| ^ p) ≤ C ^ p := by
    calc
      (⨍ w in B, |h w - ⨍ v in B, h v| ^ p) ≤
          ⨍ w in B, C ^ p :=
        Integration.setAverage_mono_of_ae hfp hpow_int hpow
      _ = C ^ p := MeasureTheory.setAverage_const hBpos.ne' hBtop.ne _
  have hroot : 0 ≤ (1 / p : ℝ) := by positivity
  have hpow_nonneg : 0 ≤
      ⨍ w in B, |h w - ⨍ v in B, h v| ^ p := by
    exact Integration.setAverage_nonneg_of_ae
      (Filter.Eventually.of_forall fun w => Real.rpow_nonneg (abs_nonneg _) _)
  have hroot' := Real.rpow_le_rpow hpow_nonneg hpow_avg hroot
  have hp0 : p ≠ 0 := by linarith only [hp]
  have hCp : (C ^ p) ^ (1 / p) = C := by
    rw [← Real.rpow_mul hC]
    field_simp [hp0]
    simp
  change (⨍ w in B, |h w - ⨍ v in B, h v| ^ p) ^ (1 / p) ≤ C
  exact hroot'.trans_eq hCp


lemma heatPotential_far_shell_bound {γ : ℝ} (hγ : γ < 1) {A : ℕ → ℝ}
    {C r : ℝ} (_ : 0 ≤ C) (_ : 0 ≤ r)
    (hA : ∀ j : ℕ, 0 ≤ A j)
    (hAj : ∀ j : ℕ, A j ≤ C * (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ) :
    ∑' j : ℕ, A j ≤
      C * (1 - (2 : ℝ) ^ (γ - 1))⁻¹ * r ^ γ := by
  have hq0 : 0 ≤ (2 : ℝ) ^ (γ - 1) := heat_morrey_geometric_ratio_nonneg
  have hq1 : (2 : ℝ) ^ (γ - 1) < 1 :=
    heat_morrey_geometric_ratio_lt_one hγ
  let g : ℕ → ℝ := fun j => C * r ^ γ *
    (2 : ℝ) ^ ((j : ℝ) * (γ - 1))
  have hg : Summable g := by
    let hgeo : Summable (fun j : ℕ =>
        (2 : ℝ) ^ ((j : ℝ) * (γ - 1))) := by
      rw [show (fun j : ℕ => (2 : ℝ) ^ ((j : ℝ) * (γ - 1))) =
          (fun j : ℕ => ((2 : ℝ) ^ (γ - 1)) ^ j) by
            funext j
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
            congr 1
            ring]
      exact summable_geometric_of_lt_one hq0 hq1
    simpa only [g] using hgeo.mul_left (C * r ^ γ)
  have hterm : ∀ j : ℕ,
      A j ≤ (C * r ^ γ) * (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) := by
    intro j
    convert hAj j using 1
    ring
  have hsum : Summable A := by
    apply Summable.of_norm_bounded hg
    intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (hA j)]
    exact hterm j
  have hsum_le : ∑' j : ℕ, A j ≤ ∑' j : ℕ, g j := by
    exact (le_abs_self _).trans
      (hsum.hasSum.norm_le_of_bounded hg.hasSum (fun j => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hA j)]
        exact hterm j))
  calc
    ∑' j : ℕ, A j ≤ ∑' j : ℕ, g j := hsum_le
    _ = (C * r ^ γ) *
          (1 - (2 : ℝ) ^ (γ - 1))⁻¹ := by
      rw [show (fun j : ℕ => g j) =
          (fun j : ℕ => (C * r ^ γ) *
            (2 : ℝ) ^ ((j : ℝ) * (γ - 1))) by
            funext j
            rfl]
      rw [tsum_mul_left]
      rw [heat_morrey_geometric_series hγ]
    _ = C * (1 - (2 : ℝ) ^ (γ - 1))⁻¹ * r ^ γ := by ring

lemma heatPotential_near_far_sum_bound {γ : ℝ} (hγ : γ < 1)
    {Anear : ℝ} {A : ℕ → ℝ} {Cnear Cfar r : ℝ}
    (hnear : Anear ≤ Cnear * r ^ γ)
    (hA : ∀ j : ℕ, 0 ≤ A j)
    (hfar : ∀ j : ℕ,
      A j ≤ Cfar * (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ)
    (hCfar : 0 ≤ Cfar) (hr : 0 ≤ r) :
    Anear + ∑' j : ℕ, A j ≤
      (Cnear + Cfar * (1 - (2 : ℝ) ^ (γ - 1))⁻¹) * r ^ γ := by
  have hfar' := heatPotential_far_shell_bound hγ hCfar hr hA hfar
  calc
    Anear + ∑' j : ℕ, A j ≤
        Cnear * r ^ γ + Cfar * (1 - (2 : ℝ) ^ (γ - 1))⁻¹ * r ^ γ :=
      add_le_add hnear hfar'
    _ = (Cnear + Cfar * (1 - (2 : ℝ) ^ (γ - 1))⁻¹) * r ^ γ := by ring

lemma heatPotential_far_shell_sum_from_six {γ : ℝ} (hγ : γ < 1)
    {A : ℕ → ℝ} {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hA : ∀ j : ℕ, 0 ≤ A j)
    (hAj : ∀ j : ℕ,
      A (j + 6) ≤ C * (2 : ℝ) ^ (((j + 6 : ℕ) : ℝ) * (γ - 1)) * r ^ γ) :
    ∑' j : ℕ, A (j + 6) ≤
      C * (2 : ℝ) ^ ((6 : ℝ) * (γ - 1)) *
        (1 - (2 : ℝ) ^ (γ - 1))⁻¹ * r ^ γ := by
  let C₆ : ℝ := C * (2 : ℝ) ^ ((6 : ℝ) * (γ - 1))
  have hC₆ : 0 ≤ C₆ := by
    dsimp [C₆]
    exact mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
  have hAj' : ∀ j : ℕ,
      A (j + 6) ≤ C₆ * (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ := by
    intro j
    have hsplit :
        (2 : ℝ) ^ (((j + 6 : ℕ) : ℝ) * (γ - 1)) =
          (2 : ℝ) ^ ((6 : ℝ) * (γ - 1)) *
            (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) := by
      rw [Nat.cast_add, add_mul, Real.rpow_add (by norm_num)]
      ring_nf
    calc
      A (j + 6) ≤ C * (2 : ℝ) ^ (((j + 6 : ℕ) : ℝ) * (γ - 1)) * r ^ γ := hAj j
      _ = C₆ * (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ := by
        rw [hsplit]
        dsimp [C₆]
        ring
  have hsum := heatPotential_far_shell_bound hγ hC₆ hr
    (fun j => hA (j + 6)) hAj'
  simpa [C₆, mul_assoc, mul_left_comm, mul_comm] using hsum

lemma heatPotential_campanato_bound
    {h : ParabolicPoint → ℝ} {z : ParabolicPoint} {r γ p Cnear Cfar : ℝ}
    {Anear : ℝ} {A : ℕ → ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hr : 0 < r) (hp : 1 ≤ p)
    (hCnear : 0 ≤ Cnear) (hCfar : 0 ≤ Cfar)
    (hint : IntegrableOn h
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) volume)
    (hfp : IntegrableOn
      (fun q => |h q - ⨍ x in
        @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r, h x| ^ p)
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) volume)
    (hnear : Anear ≤ Cnear * r ^ γ)
    (hA : ∀ j : ℕ, 0 ≤ A j)
    (hfar : ∀ j : ℕ,
      A j ≤ Cfar * (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ)
    (hpair : ∀ w ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r,
      ∀ w' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r,
        |h w - h w'| ≤ Anear + ∑' j : ℕ, A j) :
    ParabolicBallLpOscillation h z r p ≤
      (Cnear + Cfar * (1 - (2 : ℝ) ^ (γ - 1))⁻¹) * r ^ γ := by
  have hsum := heatPotential_near_far_sum_bound hγ1 hnear hA hfar hCfar hr.le
  let K : ℝ := Cnear + Cfar * (1 - (2 : ℝ) ^ (γ - 1))⁻¹
  have hden : 0 ≤ (1 - (2 : ℝ) ^ (γ - 1))⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr
      (heat_morrey_geometric_ratio_lt_one hγ1).le)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg hCnear (mul_nonneg hCfar hden)
  have hpair' : ∀ w ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r,
      ∀ w' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r,
        |h w - h w'| ≤ K * r ^ γ := by
    intro w hw w' hw'
    exact (hpair w hw w' hw').trans (by
      dsimp [K]
      exact hsum)
  have hcamp := heatPotential_campanato_bound_of_pairwise hr hγ0 hp hK hint hfp hpair'
  simpa [K] using hcamp


end CKN.Core.HeatPotential
