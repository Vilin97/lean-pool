/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Bounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.TestFunction
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.PolyExpBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrability

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set


noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic



private lemma abs_mul_exp_neg_sq_le {b y : ℝ} (hb : 0 < b) :
    |y| * Real.exp (-b * y ^ 2) ≤
      4 / Real.sqrt b * Real.exp (-(b / 2) * y ^ 2) := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  let q : ℝ := b * y ^ 2
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hsq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq
  have hroot : Real.sqrt q ≤ 1 + q := by
    have hnonneg : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
    nlinarith only [sq_nonneg (Real.sqrt q - 1), hsq]
  have hhalf : (1 + q) * Real.exp (-q / 2) ≤ 4 := by
    have hhalf' : (1 + q / 2) * Real.exp (-(q / 2)) ≤
        (2 : ℝ) ^ (1 - 1) * (1 + (Nat.factorial 1 : ℝ)) :=
      by simpa only [pow_one] using
        (one_add_pow_exp_neg_le (n := 1) (a := q / 2) (by positivity))
    calc
      (1 + q) * Real.exp (-q / 2) ≤
          2 * (1 + q / 2) * Real.exp (-q / 2) := by
        gcongr
        nlinarith only [hq]
      _ ≤ 4 := by
        calc
          2 * (1 + q / 2) * Real.exp (-q / 2) =
              2 * ((1 + q / 2) * Real.exp (-q / 2)) := by ring_nf
          _ ≤ 4 := by
            calc
              2 * ((1 + q / 2) * Real.exp (-q / 2)) ≤ 2 * 2 := by
                apply mul_le_mul_of_nonneg_left _ (show 0 ≤ (2 : ℝ) by norm_num)
                convert hhalf' using 1 <;> ring_nf
              _ = 4 := by norm_num
  have hscaled : Real.sqrt b * |y| * Real.exp (-q) ≤
      4 * Real.exp (-q / 2) := by
    have hsqrt : Real.sqrt b * |y| = Real.sqrt q := by
      rw [← Real.sqrt_sq_eq_abs y, ← Real.sqrt_mul (by positivity : 0 ≤ b)]
    rw [hsqrt]
    calc
      Real.sqrt q * Real.exp (-q) =
          (Real.sqrt q * Real.exp (-q / 2)) * Real.exp (-q / 2) := by
        rw [show -q = (-q / 2) + (-q / 2) by ring_nf, Real.exp_add]
        ring_nf
      _ ≤ (1 + q) * Real.exp (-q / 2) * Real.exp (-q / 2) := by
        gcongr
      _ ≤ 4 * Real.exp (-q / 2) := by
        gcongr
  rw [show 4 / Real.sqrt b * Real.exp (-(b / 2) * y ^ 2) =
      (4 * Real.exp (-(b / 2) * y ^ 2)) / Real.sqrt b by ring_nf]
  apply (le_div_iff₀ hsb).2
  calc
    |y| * Real.exp (-b * y ^ 2) * Real.sqrt b =
        Real.sqrt b * |y| * Real.exp (-q) := by dsimp [q]; ring_nf
    _ ≤ 4 * Real.exp (-q / 2) := hscaled
    _ = 4 * Real.exp (-(b / 2) * y ^ 2) := by
      dsimp [q]
      congr 2
      ring_nf

/-- Wider Gaussian majorant for the spatial heat-kernel gradient. -/
def heatKernelGradientMajorant (x : Vec3) (t : ℝ) : ℝ :=
  if 0 < t then
    (Real.sqrt t)⁻¹ * (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
      Real.exp (-(∑ i, x i ^ 2) / (8 * t))
  else 0

lemma heatKernelGradientNorm_le_majorant {x : Vec3} {t : ℝ} (ht : 0 < t) :
    heatKernelGradientNorm x t ≤ 100 * heatKernelGradientMajorant x t := by
  let s : ℝ := ∑ j, x j ^ 2
  let p : ℝ := (4 * Real.pi * t) ^ (-(3 : ℝ) / 2)
  have hs : 0 ≤ s := by
    dsimp [s]
    positivity
  have hp : 0 ≤ p := by
    dsimp [p]
    positivity
  have hst : 0 < 4 * t := by positivity
  have hcomponent : ∀ i : Fin 3,
      |heatKernelSpaceDerivative x t i| ≤
        4 / Real.sqrt t * p * Real.exp (-s / (8 * t)) := by
    intro i
    have hxi : (x i) ^ 2 ≤ s := by
      dsimp [s]
      exact Finset.single_le_sum (fun j _hj => sq_nonneg (x j)) (Finset.mem_univ i)
    have hother : 0 ≤ s - (x i) ^ 2 := sub_nonneg.mpr hxi
    have hexp_other : Real.exp (-(s - (x i) ^ 2) / (4 * t)) ≤
        Real.exp (-(s - (x i) ^ 2) / (8 * t)) := by
      apply Real.exp_le_exp.mpr
      have hdiv : (s - (x i) ^ 2) / (8 * t) ≤
          (s - (x i) ^ 2) / (4 * t) := by
        exact div_le_div_of_nonneg_left hother (by positivity : 0 < (4 * t : ℝ))
          (by nlinarith only [ht])
      simpa only [neg_div] using (neg_le_neg hdiv)
    have hexp_split : Real.exp (-s / (4 * t)) ≤
        Real.exp (-((x i) ^ 2) / (4 * t)) *
          Real.exp (-(s - (x i) ^ 2) / (8 * t)) := by
      have hsplit : Real.exp (-s / (4 * t)) =
          Real.exp (-((x i) ^ 2) / (4 * t)) *
            Real.exp (-(s - (x i) ^ 2) / (4 * t)) := by
        rw [← Real.exp_add]
        congr 1
        field_simp
        ring_nf
      calc
        Real.exp (-s / (4 * t)) =
            Real.exp (-((x i) ^ 2) / (4 * t)) *
              Real.exp (-(s - (x i) ^ 2) / (4 * t)) := hsplit
        _ ≤ Real.exp (-((x i) ^ 2) / (4 * t)) *
              Real.exp (-(s - (x i) ^ 2) / (8 * t)) := by
          exact mul_le_mul_of_nonneg_left hexp_other (Real.exp_nonneg _)
    have hscalar := abs_mul_exp_neg_sq_le (b := 1 / (4 * t)) (y := x i) (by positivity)
    have hscalar' : |x i| * Real.exp (-((x i) ^ 2) / (4 * t)) ≤
        8 * Real.sqrt t * Real.exp (-((x i) ^ 2) / (8 * t)) := by
      calc
        |x i| * Real.exp (-((x i) ^ 2) / (4 * t)) ≤
              4 / Real.sqrt (1 / (4 * t)) *
              Real.exp (-(1 / (4 * t) / 2) * (x i) ^ 2) := by
          convert hscalar using 1
          ring_nf
        _ = 8 * Real.sqrt t * Real.exp (-((x i) ^ 2) / (8 * t)) := by
          have hsqrtinv : Real.sqrt (1 / (4 * t)) = (2 * Real.sqrt t)⁻¹ := by
            rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
            have hsqrt4 : Real.sqrt (4 * t) = 2 * Real.sqrt t := by
              calc
                Real.sqrt (4 * t) = Real.sqrt 4 * Real.sqrt t :=
                  Real.sqrt_mul (by norm_num) _
                _ = 2 * Real.sqrt t := by
                  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
                  norm_num
            rw [hsqrt4]
            field_simp [Real.sqrt_pos.2 ht]
          rw [hsqrtinv]
          congr 1
          · field_simp [Real.sqrt_pos.2 ht]
            norm_num
          · congr 1
            field_simp
            ring_nf
    have hderiv : |heatKernelSpaceDerivative x t i| ≤
        (1 / (2 * t)) * p *
          (8 * Real.sqrt t * Real.exp (-s / (8 * t))) := by
      rw [heatKernelSpaceDerivative, ite_eq_left ht, abs_mul, abs_div,
        abs_neg, abs_of_pos (by positivity : 0 < (2 * t : ℝ)),
        heatKernel_eq_formula_sum ht]
      rw [abs_of_nonneg (mul_nonneg hp (Real.exp_nonneg _))]
      have hbound := hexp_split
      change |x i| / (2 * t) * (p * Real.exp (-s / (4 * t))) ≤
        (1 / (2 * t)) * p * (8 * Real.sqrt t * Real.exp (-s / (8 * t)))
      calc
        |x i| / (2 * t) * (p * Real.exp (-s / (4 * t))) ≤
            |x i| / (2 * t) * (p *
              (Real.exp (-((x i) ^ 2) / (4 * t)) *
                Real.exp (-(s - (x i) ^ 2) / (8 * t)))) := by
          gcongr
        _ = (1 / (2 * t)) * p *
            (|x i| * Real.exp (-((x i) ^ 2) / (4 * t)) *
              Real.exp (-(s - (x i) ^ 2) / (8 * t))) := by ring_nf
        _ ≤ (1 / (2 * t)) * p *
            (8 * Real.sqrt t * Real.exp (-((x i) ^ 2) / (8 * t)) *
              Real.exp (-(s - (x i) ^ 2) / (8 * t))) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right hscalar' (Real.exp_nonneg _)
          · positivity
        _ = (1 / (2 * t)) * p *
            (8 * Real.sqrt t * Real.exp (-s / (8 * t))) := by
          have hexp : Real.exp (-((x i) ^ 2) / (8 * t)) *
              Real.exp (-(s - (x i) ^ 2) / (8 * t)) =
              Real.exp (-s / (8 * t)) := by
            rw [← Real.exp_add]
            congr 1
            field_simp
            ring_nf
          calc
            (1 / (2 * t)) * p *
                (8 * Real.sqrt t * Real.exp (-((x i) ^ 2) / (8 * t)) *
                  Real.exp (-(s - (x i) ^ 2) / (8 * t))) =
                (1 / (2 * t)) * p *
                  (8 * Real.sqrt t *
                    (Real.exp (-((x i) ^ 2) / (8 * t)) *
                      Real.exp (-(s - (x i) ^ 2) / (8 * t)))) := by ring_nf
            _ = (1 / (2 * t)) * p *
                (8 * Real.sqrt t * Real.exp (-s / (8 * t))) := by rw [hexp]
    calc
      |heatKernelSpaceDerivative x t i| ≤
          (1 / (2 * t)) * p *
            (8 * Real.sqrt t * Real.exp (-s / (8 * t))) := hderiv
      _ = 4 / Real.sqrt t * p * Real.exp (-s / (8 * t)) := by
        have hsqrt_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
        field_simp [Real.sqrt_pos.2 ht]
        rw [hsqrt_sq]
        ring_nf
  unfold heatKernelGradientNorm heatKernelGradientMajorant
  simp only [ite_eq_left ht]
  have hsum : (∑ i, |heatKernelSpaceDerivative x t i|) ≤
      ∑ i : Fin 3, 4 / Real.sqrt t * p * Real.exp (-s / (8 * t)) := by
    exact Finset.sum_le_sum (fun i _hi => hcomponent i)
  have hfinal : (∑ i, |heatKernelSpaceDerivative x t i|) ≤
      100 * (Real.sqrt t)⁻¹ * p * Real.exp (-s / (8 * t)) := by
    calc
      ∑ i, |heatKernelSpaceDerivative x t i| ≤
          ∑ i, 4 / Real.sqrt t * p * Real.exp (-s / (8 * t)) := hsum
      _ = 12 / Real.sqrt t * p * Real.exp (-s / (8 * t)) := by
        simp only [Finset.sum_const, Finset.card_fin]
        ring_nf
      _ ≤ 100 * (Real.sqrt t)⁻¹ * p * Real.exp (-s / (8 * t)) := by
        gcongr
        field_simp [Real.sqrt_pos.2 ht]
        norm_num
  convert hfinal using 1
  dsimp [s, p]
  ring_nf

private lemma heatKernelGradientMajorant_measurable :
    Measurable (fun p : ParabolicPoint => heatKernelGradientMajorant p.1 p.2) := by
  unfold heatKernelGradientMajorant
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
  · fun_prop
  · exact measurable_const

lemma heatKernelGradientMajorant_nonneg (x : Vec3) (t : ℝ) :
    0 ≤ heatKernelGradientMajorant x t := by
  unfold heatKernelGradientMajorant
  by_cases ht : 0 < t
  · simp only [ite_eq_left ht]
    positivity
  · simp only [ite_eq_right ht]
    norm_num

private lemma gaussian_eight_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Vec3 => Real.exp (-(∑ i, x i ^ 2) / (8 * t))) volume := by
  have hG := heatKernel_integrable (show 0 < 2 * t by positivity)
  have hc : 0 < (8 * Real.pi * t) ^ (-(3 : ℝ) / 2) := by positivity
  have heq : (fun x : Vec3 => Real.exp (-(∑ i, x i ^ 2) / (8 * t))) =
      (fun x : Vec3 => ((8 * Real.pi * t) ^ (-(3 : ℝ) / 2))⁻¹ *
        heatKernel x (2 * t)) := by
    funext x
    rw [heatKernel_eq_formula_sum (show 0 < 2 * t by positivity)]
    field_simp
    ring_nf
  rw [heq]
  exact hG.const_mul _

private lemma heat_prefactor_double_le {t : ℝ} (ht : 0 < t) :
    (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        (Real.sqrt (8 * Real.pi * t)) ^ (3 : ℕ) ≤ 4 := by
  have hbase : 0 < 4 * Real.pi * t := by positivity
  have hbase8 : 0 < 8 * Real.pi * t := by positivity
  have hsqrt : (Real.sqrt (8 * Real.pi * t)) ^ (3 : ℕ) =
      (8 * Real.pi * t) ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hbase8.le]
    norm_num
  rw [hsqrt]
  have hinv : (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) =
      ((4 * Real.pi * t) ^ ((3 : ℝ) / 2))⁻¹ := by
    rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring_nf, Real.rpow_neg hbase.le]
  rw [hinv]
  have hsplit : (8 * Real.pi * t) = 2 * (4 * Real.pi * t) := by ring_nf
  have htwo : (2 : ℝ) ^ ((3 : ℝ) / 2) ≤ 4 := by
    have htwo' : (2 : ℝ) ^ ((3 : ℝ) / 2) ≤ (2 : ℝ) ^ (2 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
        (y := (3 : ℝ) / 2) (z := 2) (by norm_num) (by norm_num)
    convert htwo' using 1
    norm_num
  have hratio : (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        (8 * Real.pi * t) ^ ((3 : ℝ) / 2) =
      (2 : ℝ) ^ ((3 : ℝ) / 2) := by
    have hp : (4 * Real.pi * t) ^ ((3 : ℝ) / 2) ≠ 0 :=
      (Real.rpow_pos_of_pos hbase _).ne'
    calc
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          (8 * Real.pi * t) ^ ((3 : ℝ) / 2) =
          ((4 * Real.pi * t) ^ ((3 : ℝ) / 2))⁻¹ *
            (2 * (4 * Real.pi * t)) ^ ((3 : ℝ) / 2) := by rw [hinv, hsplit]
      _ = ((4 * Real.pi * t) ^ ((3 : ℝ) / 2))⁻¹ *
            ((2 : ℝ) ^ ((3 : ℝ) / 2) *
              (4 * Real.pi * t) ^ ((3 : ℝ) / 2)) := by
        rw [Real.mul_rpow (by norm_num) hbase.le]
      _ = (2 : ℝ) ^ ((3 : ℝ) / 2) := by field_simp [hp]
  have hratio_inv : ((4 * Real.pi * t) ^ ((3 : ℝ) / 2))⁻¹ *
        (8 * Real.pi * t) ^ ((3 : ℝ) / 2) =
      (2 : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [← hinv]
    exact hratio
  rw [hratio_inv]
  exact htwo

lemma heatKernelGradientMajorant_slice_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Vec3 => heatKernelGradientMajorant x t) volume := by
  rw [show (fun x : Vec3 => heatKernelGradientMajorant x t) =
      (fun x : Vec3 => (Real.sqrt t)⁻¹ *
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ i, x i ^ 2) / (8 * t))) by
    funext x
    simp [heatKernelGradientMajorant, ht]]
  exact (gaussian_eight_integrable ht).const_mul _

lemma heatKernelGradientMajorant_slice_le {t : ℝ} (ht : 0 < t) :
    ∫ x : Vec3, ‖heatKernelGradientMajorant x t‖ ≤
      4 * (Real.sqrt t)⁻¹ := by
  have hnonneg : ∀ x : Vec3, 0 ≤ heatKernelGradientMajorant x t :=
    fun x => heatKernelGradientMajorant_nonneg x t
  have hform : (fun x : Vec3 => heatKernelGradientMajorant x t) =
      (fun x : Vec3 => (Real.sqrt t)⁻¹ *
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ i, x i ^ 2) / (8 * t))) := by
    funext x
    simp [heatKernelGradientMajorant, ht]
  rw [show (fun x : Vec3 => ‖heatKernelGradientMajorant x t‖) =
      (fun x : Vec3 => heatKernelGradientMajorant x t) by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]]
  rw [hform, integral_const_mul]
  have hg := gaussian_integral (2 * t) (by positivity)
  have heq : (fun x : Vec3 => Real.exp (-(∑ i, x i ^ 2) / (8 * t))) =
      (fun x : Vec3 => Real.exp (-(∑ i, x i ^ 2) / (4 * (2 * t)))) := by
    funext x
    congr 1
    ring_nf
  rw [heq, hg]
  have hsqrt2 : Real.sqrt (4 * Real.pi * (2 * t)) =
      Real.sqrt (8 * Real.pi * t) := by
    congr 1
    ring_nf
  rw [hsqrt2]
  have hpref := heat_prefactor_double_le ht
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  calc
    (Real.sqrt t)⁻¹ * (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        (Real.sqrt (8 * Real.pi * t)) ^ (3 : ℕ) ≤
        (Real.sqrt t)⁻¹ * 4 := by
      calc
        (Real.sqrt t)⁻¹ * (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
            (Real.sqrt (8 * Real.pi * t)) ^ (3 : ℕ) =
            (Real.sqrt t)⁻¹ *
              ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
                (Real.sqrt (8 * Real.pi * t)) ^ (3 : ℕ)) := by ring_nf
        _ ≤ (Real.sqrt t)⁻¹ * 4 :=
          mul_le_mul_of_nonneg_left hpref (by positivity)
    _ = 4 * (Real.sqrt t)⁻¹ := by ring_nf

private lemma heatKernelPlus_measurable :
    Measurable (fun p : ParabolicPoint => heatKernelPlus p) := by
  unfold heatKernelPlus
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
  · exact (by
      unfold heatKernel
      apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
      · fun_prop
      · exact measurable_const)
  · exact measurable_const

private lemma heatKernel_measurable :
    Measurable (fun p : ParabolicPoint => heatKernel p.1 p.2) := by
  unfold heatKernel
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
  · fun_prop
  · exact measurable_const

lemma heatKernelGradientNorm_measurable :
    Measurable (fun p : ParabolicPoint => heatKernelGradientNorm p.1 p.2) := by
  unfold heatKernelGradientNorm
  apply Finset.measurable_sum Finset.univ
  intro i hi
  have hderiv : Measurable
      (fun p : ParabolicPoint => heatKernelSpaceDerivative p.1 p.2 i) := by
    unfold heatKernelSpaceDerivative
    apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
    · have hcoord : Measurable (fun p : ParabolicPoint => p.1 i) :=
        measurable_pi_apply i |>.comp measurable_fst
      have htime : Measurable (fun p : ParabolicPoint => p.2) := measurable_snd
      exact (hcoord.neg.div (measurable_const.mul htime)).mul heatKernel_measurable
    · exact measurable_const
  exact (continuous_abs.measurable.comp hderiv)

lemma heatKernelPlus_integrable_prod {T : ℝ} :
    Integrable (fun p : Vec3 × ℝ => heatKernelPlus (show ParabolicPoint from p))
      ((volume : Measure Vec3).prod (volume.restrict (Ioc 0 T))) := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 T)
  change Integrable (fun p : Vec3 × ℝ => heatKernelPlus (show ParabolicPoint from p))
      ((volume : Measure Vec3).prod ν)
  have hmeas₀ := heatKernelPlus_measurable
  change Measurable (fun p : Vec3 × ℝ => heatKernelPlus (show ParabolicPoint from p)) at hmeas₀
  have hmeas : AEStronglyMeasurable
      (fun p : Vec3 × ℝ => heatKernelPlus (show ParabolicPoint from p)) (volume.prod ν) :=
    hmeas₀.aestronglyMeasurable
  apply (integrable_prod_iff' hmeas).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have heq : (fun x : Vec3 => heatKernelPlus (show ParabolicPoint from (x, t))) =
        (fun x : Vec3 => heatKernel x t) := by
      funext x
      exact heatKernelPlus_eq_heatKernel (show ParabolicPoint from (x, t))
    rw [heq]
    exact heatKernel_integrable ht.1
  · have houter : (fun t : ℝ => ∫ x : Vec3, ‖heatKernelPlus (x, t)‖) =ᵐ[ν]
        (fun _ => (1 : ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hnorm : (fun x : Vec3 =>
          ‖heatKernelPlus (show ParabolicPoint from (x, t))‖) =
          (fun x : Vec3 => heatKernel x t) := by
        funext x
        rw [heatKernelPlus_eq_heatKernel, Real.norm_eq_abs,
          abs_of_nonneg (heatKernel_nonneg _ _)]
      rw [hnorm, heatKernel_integral t ht.1]
    have hone : Integrable (fun _ : ℝ => (1 : ℝ)) ν :=
      integrableOn_const (s := Ioc 0 T) (μ := volume)
        (measure_Ioc_lt_top (μ := volume)).ne
    exact hone.congr houter.symm

lemma heatKernelPlus_integrableOn_time {T : ℝ} :
    IntegrableOn (fun p : ParabolicPoint => heatKernelPlus p)
      (Set.univ ×ˢ Ioc 0 T) volume := by
  change Integrable (fun p : Vec3 × ℝ =>
      heatKernelPlus (show ParabolicPoint from p))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        ((Set.univ : Set Vec3) ×ˢ Ioc 0 T))
  rw [← Measure.prod_restrict]
  simpa only [Measure.restrict_univ] using heatKernelPlus_integrable_prod

lemma time_sqrt_inv_integrable {T : ℝ} (hT : 0 < T) :
    Integrable (fun t : ℝ => 4 * (Real.sqrt t)⁻¹)
      (volume.restrict (Ioc 0 T)) := by
  have hpowIoo : IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (Ioo 0 T) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hT).2 (by norm_num)
  have hpowIoc : IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (Ioc 0 T) volume := by
    apply hpowIoo.congr_set_ae
    exact (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := T)).symm
  have hpow : Integrable (fun t : ℝ => t ^ (-(1 : ℝ) / 2))
      (volume.restrict (Ioc 0 T)) := hpowIoc
  have hmul := hpow.const_mul (4 : ℝ)
  apply hmul.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  rw [Real.sqrt_eq_rpow, show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring_nf,
    Real.rpow_neg ht0.le]

private lemma heatKernelGradientMajorant_integrable_prod {T : ℝ} (hT : 0 < T) :
    Integrable (fun p : Vec3 × ℝ =>
      heatKernelGradientMajorant p.1 p.2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioc 0 T))) := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 T)
  have hmeas₀ := heatKernelGradientMajorant_measurable
  change Measurable (fun p : Vec3 × ℝ =>
    heatKernelGradientMajorant p.1 p.2) at hmeas₀
  have hmeas : AEStronglyMeasurable (fun p : Vec3 × ℝ =>
      heatKernelGradientMajorant p.1 p.2) (volume.prod ν) :=
    hmeas₀.aestronglyMeasurable
  apply (integrable_prod_iff' hmeas).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact heatKernelGradientMajorant_slice_integrable ht.1
  · have houter_meas : AEStronglyMeasurable
        (fun t : ℝ => ∫ x : Vec3,
          ‖heatKernelGradientMajorant x t‖) ν := by
      exact hmeas.norm.prod_swap.integral_prod_right'
    have hdom := time_sqrt_inv_integrable hT
    apply hdom.mono' houter_meas
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hnonneg : 0 ≤ ∫ x : Vec3, ‖heatKernelGradientMajorant x t‖ :=
      integral_nonneg (fun x => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact heatKernelGradientMajorant_slice_le ht.1

lemma heatKernelGradientNorm_eq_zero_of_nonpos {x : Vec3} {t : ℝ}
    (ht : t ≤ 0) : heatKernelGradientNorm x t = 0 := by
  unfold heatKernelGradientNorm heatKernelSpaceDerivative
  simp [not_lt.mpr ht]

lemma heatKernelGradientNorm_integrable_prod {T : ℝ} (hT : 0 < T) :
    Integrable (fun p : Vec3 × ℝ =>
      heatKernelGradientNorm p.1 p.2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioc 0 T))) := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 T)
  have hM := (heatKernelGradientMajorant_integrable_prod hT).const_mul (100 : ℝ)
  have hgrad₀ := heatKernelGradientNorm_measurable
  change Measurable (fun p : Vec3 × ℝ =>
    heatKernelGradientNorm p.1 p.2) at hgrad₀
  have hgrad : AEStronglyMeasurable (fun p : Vec3 × ℝ =>
      heatKernelGradientNorm p.1 p.2) (volume.prod ν) :=
    hgrad₀.aestronglyMeasurable
  apply hM.mono' hgrad
  exact ae_of_all _ fun p => by
    by_cases ht : 0 < p.2
    · have hnonneg : 0 ≤ heatKernelGradientNorm p.1 p.2 := by
        unfold heatKernelGradientNorm
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact heatKernelGradientNorm_le_majorant ht
    · rw [heatKernelGradientNorm_eq_zero_of_nonpos (le_of_not_gt ht)]
      simp [heatKernelGradientMajorant, ht]

lemma heatKernelGradientNorm_integrableOn_time {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun p : ParabolicPoint => heatKernelGradientNorm p.1 p.2)
      (Set.univ ×ˢ Ioc 0 T) volume := by
  change Integrable (fun p : Vec3 × ℝ =>
      heatKernelGradientNorm p.1 p.2)
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        ((Set.univ : Set Vec3) ×ˢ Ioc 0 T))
  rw [← Measure.prod_restrict]
  simpa only [Measure.restrict_univ] using heatKernelGradientNorm_integrable_prod hT

lemma heatKernelPlus_locallyIntegrable :
    LocallyIntegrable (fun p : ParabolicPoint => heatKernelPlus p) volume := by
  intro p
  let top : ℝ := p.2 + 1 / 2
  let T : ℝ := max 1 top + 1
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hU := heatKernelPlus_integrableOn_time (T := T)
  have hN : IntegrableOn (fun q : ParabolicPoint => heatKernelPlus q)
      {q | q.2 ≤ 0} volume := by
    apply (integrableOn_zero (s := {q : ParabolicPoint | q.2 ≤ 0})).congr_fun
    · intro q hq
      exact (heatKernelPlus_eq_zero_of_nonpos hq).symm
    · exact measurableSet_Iic.preimage measurable_snd
  have hCyl : IntegrableOn (fun q : ParabolicPoint => heatKernelPlus q)
      (parabolicCylinder p.1 top 1) := by
    apply hU.union hN |>.mono_set
    intro q hq
    rcases hq with ⟨_, _, hupp⟩
    by_cases hqpos : 0 < q.2
    · left
      change q.1 ∈ (Set.univ : Set Vec3) ∧ q.2 ∈ Ioc 0 T
      refine ⟨Set.mem_univ _, hqpos, ?_⟩
      dsimp [T, top]
      exact (lt_of_le_of_lt (hupp.trans (le_max_right (1 : ℝ) top))
        (lt_add_one (max 1 top))).le
    · right
      exact le_of_not_gt hqpos
  have hball := metricBall_subset_parabolicCylinder (x := p.1)
    (t := top) (r := 1) (by norm_num)
  have hcenter : (p.1, top - (1 : ℝ) ^ 2 / 2) = p := by
    apply Prod.ext
    · rfl
    · dsimp [top]
      ring_nf
  rw [hcenter] at hball
  exact ⟨@Metric.ball ParabolicPoint parabolicPseudoMetricSpace p (1 / 2 : ℝ),
    @Metric.ball_mem_nhds ParabolicPoint parabolicPseudoMetricSpace p
      (1 / 2 : ℝ) (by norm_num), hCyl.mono_set hball⟩

lemma heatKernelGradientNorm_locallyIntegrable :
    LocallyIntegrable
      (fun p : ParabolicPoint => heatKernelGradientNorm p.1 p.2) volume := by
  intro p
  let top : ℝ := p.2 + 1 / 2
  let T : ℝ := max 1 top + 1
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hU := heatKernelGradientNorm_integrableOn_time (T := T) hT
  have hN : IntegrableOn
      (fun q : ParabolicPoint => heatKernelGradientNorm q.1 q.2)
      {q | q.2 ≤ 0} volume := by
    apply (integrableOn_zero (s := {q : ParabolicPoint | q.2 ≤ 0})).congr_fun
    · intro q hq
      exact (heatKernelGradientNorm_eq_zero_of_nonpos hq).symm
    · exact measurableSet_Iic.preimage measurable_snd
  have hCyl : IntegrableOn
      (fun q : ParabolicPoint => heatKernelGradientNorm q.1 q.2)
      (parabolicCylinder p.1 top 1) := by
    apply hU.union hN |>.mono_set
    intro q hq
    rcases hq with ⟨_, _, hupp⟩
    by_cases hqpos : 0 < q.2
    · left
      change q.1 ∈ (Set.univ : Set Vec3) ∧ q.2 ∈ Ioc 0 T
      refine ⟨Set.mem_univ _, hqpos, ?_⟩
      dsimp [T, top]
      exact (lt_of_le_of_lt (hupp.trans (le_max_right (1 : ℝ) top))
        (lt_add_one (max 1 top))).le
    · right
      exact le_of_not_gt hqpos
  have hball := metricBall_subset_parabolicCylinder (x := p.1)
    (t := top) (r := 1) (by norm_num)
  have hcenter : (p.1, top - (1 : ℝ) ^ 2 / 2) = p := by
    apply Prod.ext
    · rfl
    · dsimp [top]
      ring_nf
  rw [hcenter] at hball
  exact ⟨@Metric.ball ParabolicPoint parabolicPseudoMetricSpace p (1 / 2 : ℝ),
    @Metric.ball_mem_nhds ParabolicPoint parabolicPseudoMetricSpace p
      (1 / 2 : ℝ) (by norm_num), hCyl.mono_set hball⟩


end CKN.Foundation.Heat
