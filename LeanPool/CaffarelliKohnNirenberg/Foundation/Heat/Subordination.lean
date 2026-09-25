/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.HigherBounds
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Subordination

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Filter


noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

/-! The third spatial derivative is integrated in the heat-time variable.  This
is the explicit kernel corresponding to a degree-one pressure multiplier. -/

/-- Subordinated third-derivative heat kernel, integrated over times above the current time. -/
def subordinatedKernel (j l m : Fin 3) (x : Vec3) (t : ℝ) : ℝ :=
  if 0 < t then
    -∫ s in Ioi t, heatKernelSpaceThirdDerivative x s m j l
  else 0

/-- Spatial derivative of the subordinated kernel via the fourth heat-kernel derivative. -/
def subordinatedKernelSpatialDerivative (j l m i : Fin 3) (x : Vec3) (t : ℝ) : ℝ :=
  if 0 < t then
    -∫ s in Ioi t, heatKernelSpaceFourthDerivative x s m j l i
  else 0

private lemma third_derivative_integrableOn_Ioi {x : Vec3} {t : ℝ}
    (ht : 0 < t) (i j k : Fin 3) :
    IntegrableOn (fun s : ℝ => heatKernelSpaceThirdDerivative x s i j k) (Ioi t) volume := by
  let C : ℝ := 1000000000000
  have hdom : IntegrableOn (fun s : ℝ => C * s ^ (-(3 : ℝ))) (Ioi t) volume := by
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num) ht).const_mul C
  have hheat : Measurable (fun s : ℝ => heatKernel x s) := by
    unfold heatKernel
    apply Measurable.ite measurableSet_Ioi
    · measurability
    · measurability
  have hcoef : Measurable (fun s : ℝ =>
      (-(x i) * (x j) * (x k) / (8 * s ^ 3) +
        ((if i = j then x k else 0) + (if i = k then x j else 0) +
          (if j = k then x i else 0)) / (4 * s ^ 2))) := by
    measurability
  have hthird : Measurable
      (fun s : ℝ => heatKernelSpaceThirdDerivative x s i j k) := by
    unfold heatKernelSpaceThirdDerivative
    apply Measurable.ite measurableSet_Ioi
    · exact hcoef.mul hheat
    · measurability
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => heatKernelSpaceThirdDerivative x s i j k)
      (volume.restrict (Ioi t)) := hthird.aestronglyMeasurable.restrict
  refine hdom.mono' hmeas ?_
  exact (ae_restrict_mem measurableSet_Ioi).mono (fun s hs => by
    have hs' : 0 < s := lt_trans ht (mem_Ioi.mp hs)
    have hρ : Real.sqrt s ≤ rhoTwo x s := by
      unfold rhoTwo
      exact le_add_of_nonneg_left (vec3EuclideanNorm_nonneg x)
    have hbound := heatKernelSpaceThirdDerivative_abs_le_rho_inv_six
      (x := x) (t := s) hs' i j k
    have hden : 0 < rhoTwo x s := by
      unfold rhoTwo
      exact add_pos_of_nonneg_of_pos (vec3EuclideanNorm_nonneg x)
        (Real.sqrt_pos.2 hs')
    have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs'
    have hpow : (Real.sqrt s) ^ (6 : ℕ) = s ^ (3 : ℕ) := by
      rw [show (Real.sqrt s) ^ (6 : ℕ) = ((Real.sqrt s) ^ 2) ^ 3 by ring,
        Real.sq_sqrt hs'.le]
    have hcomp : C / rhoTwo x s ^ 6 ≤ C / (Real.sqrt s) ^ 6 := by
      gcongr
    have hrpow : s ^ (-(3 : ℝ)) = (s ^ (3 : ℕ))⁻¹ := by
      rw [Real.rpow_neg hs'.le]
      exact congrArg Inv.inv (Real.rpow_natCast s 3)
    rw [Real.norm_eq_abs]
    calc
      |heatKernelSpaceThirdDerivative x s i j k| ≤ C / rhoTwo x s ^ 6 := by
        simpa [C] using hbound
      _ ≤ C / (Real.sqrt s) ^ 6 := hcomp
      _ = C * s ^ (-(3 : ℝ)) := by
        rw [hpow, hrpow]
        ring)

private lemma rho_inv_six_integral_le {x : Vec3} {t : ℝ} (ht : 0 < t) :
    ∫ s in Ioi t, (rhoTwo x s) ^ (-(6 : ℝ)) ≤
      (1 / 2 : ℝ) * (rhoTwo x t) ^ (-(4 : ℝ)) := by
  let a : ℝ := vec3EuclideanNorm x
  let b : ℝ := Real.sqrt t
  have ha : 0 ≤ a := by
    dsimp [a]
    exact vec3EuclideanNorm_nonneg x
  have hb : 0 < b := by
    dsimp [b]
    exact Real.sqrt_pos.2 ht
  have hρt : rhoTwo x t = a + b := by
    dsimp [rhoTwo, a, b]
  have hchange := integral_comp_rpow_Ioi_of_pos'
    (g := fun s : ℝ => (rhoTwo x s) ^ (-(6 : ℝ)))
    (p := (2 : ℝ)) (by norm_num) (c := t) ht.le
  have hleft :
      ∫ y in Ioi b, 2 * y * (a + y) ^ (-(6 : ℝ)) =
        ∫ s in Ioi t, (rhoTwo x s) ^ (-(6 : ℝ)) := by
    have hcb : t ^ (2 : ℝ)⁻¹ = b := by
      dsimp [b]
      rw [Real.sqrt_eq_rpow]
      norm_num
    rw [← hchange, hcb]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : 0 < y := lt_trans hb (mem_Ioi.mp hy)
    have hsqrt : Real.sqrt (y ^ (2 : ℝ)) = y := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy'.le]
      norm_num
    simp only [smul_eq_mul]
    rw [rhoTwo, hsqrt]
    dsimp [a]
    norm_num [Real.rpow_one]
  have hshift :
      ∫ y in Ioi b, (a + y) ^ (-(5 : ℝ)) =
        (1 / 4 : ℝ) * (a + b) ^ (-(4 : ℝ)) := by
    have hderiv : ∀ y ∈ Ici b,
        HasDerivAt (fun q : ℝ => (-1 / 4 : ℝ) * (a + q) ^ (-(4 : ℝ)))
          ((a + y) ^ (-(5 : ℝ))) y := by
      intro y hy
      have hy' : 0 < a + y := by
        exact add_pos_of_nonneg_of_pos ha (lt_of_lt_of_le hb hy)
      have hbase : 0 < y + a := by linarith only [hy']
      have hderiv := (((hasDerivAt_id y).add_const a).rpow_const
        (p := (-4 : ℝ)) (Or.inl (by simpa [id_eq, add_comm] using hbase.ne'))
        ).const_mul (-1 / 4 : ℝ)
      convert hderiv using 1
      · funext q
        simp [id_eq, add_comm]
      · simp only [add_comm, Real.rpow_neg_ofNat, Int.reduceNeg, zpow_neg, zpow_ofNat, mul_neg,
        one_mul, id_eq,
    neg_mul]
        rw [show -4 - 1 = (-5 : ℝ) by norm_num,
          Real.rpow_neg hbase.le]
        norm_num
        ring_nf
    have hint : IntegrableOn (fun y : ℝ => (a + y) ^ (-(5 : ℝ))) (Ioi b) := by
      change Integrable (fun y : ℝ => (a + y) ^ (-(5 : ℝ)))
        (volume.restrict (Ioi b))
      have hI := integrableOn_add_rpow_Ioi_of_lt (a := (-5 : ℝ)) (c := b)
        (m := a) (by norm_num) (by linarith only [ha, hb])
      exact hI.congr (Filter.Eventually.of_forall (fun y => by simp [add_comm]))
    have hlim : Tendsto
        (fun y : ℝ => (-1 / 4 : ℝ) * (a + y) ^ (-(4 : ℝ)))
        atTop (𝓝 0) := by
      have hpow := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4)).comp
        (tendsto_atTop_add_const_right _ a tendsto_id)
      convert hpow.const_mul (-1 / 4 : ℝ) using 1 <;>
        simp [id_eq, add_comm]
    have hi := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
    have hi' : ∫ y in Ioi b, (y + a) ^ (-(5 : ℝ)) =
        -((-1 / 4 : ℝ) * (b + a) ^ (-(4 : ℝ))) := by
      simpa [id_eq, add_comm] using hi
    convert hi' using 1 <;> ring_nf
  have hpoint : ∀ᵐ y ∂(volume.restrict (Ioi b)),
      2 * y * (a + y) ^ (-(6 : ℝ)) ≤
        2 * (a + y) ^ (-(5 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : 0 < y := lt_trans hb (mem_Ioi.mp hy)
    have hbase : 0 ≤ a + y := (add_pos_of_nonneg_of_pos ha hy').le
    have hle : y ≤ a + y := by linarith only [ha]
    have hpow : 0 ≤ (a + y) ^ (-(6 : ℝ)) := Real.rpow_nonneg hbase _
    have hstep := mul_le_mul_of_nonneg_right hle hpow
    have hident : (a + y) ^ (-(5 : ℝ)) =
        (a + y) * (a + y) ^ (-(6 : ℝ)) := by
      calc
        (a + y) ^ (-(5 : ℝ)) = (a + y) ^ ((1 : ℝ) + (-(6 : ℝ))) := by
          congr 1
          ring_nf
        _ = (a + y) ^ (1 : ℝ) * (a + y) ^ (-(6 : ℝ)) := by
          rw [Real.rpow_add (by positivity : 0 < a + y)]
        _ = (a + y) * (a + y) ^ (-(6 : ℝ)) := by rw [Real.rpow_one]
    rw [hident]
    nlinarith only [hstep]
  calc
    ∫ s in Ioi t, (rhoTwo x s) ^ (-(6 : ℝ)) =
        ∫ y in Ioi b, 2 * y * (a + y) ^ (-(6 : ℝ)) := hleft.symm
    _ ≤ ∫ y in Ioi b, 2 * (a + y) ^ (-(5 : ℝ)) := by
      have hright : Integrable (fun y : ℝ =>
          2 * (a + y) ^ (-(5 : ℝ))) (volume.restrict (Ioi b)) := by
        have hI := (integrableOn_add_rpow_Ioi_of_lt (a := (-5 : ℝ))
          (c := b) (m := a) (by norm_num) (by linarith only [ha, hb])).const_mul 2
        simpa [add_comm] using hI
      have hleftbound : ∀ᵐ y ∂(volume.restrict (Ioi b)),
          ‖2 * y * (a + y) ^ (-(6 : ℝ))‖ ≤
            2 * (a + y) ^ (-(5 : ℝ)) := by
        filter_upwards [hpoint, ae_restrict_mem measurableSet_Ioi] with y hy hyS
        have hy' : 0 < y := lt_trans hb (mem_Ioi.mp hyS)
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact hy
        · positivity
      have hleft : Integrable (fun y : ℝ =>
          2 * y * (a + y) ^ (-(6 : ℝ))) (volume.restrict (Ioi b)) := by
        apply hright.mono'
        · measurability
        · exact hleftbound
      exact MeasureTheory.integral_mono_ae hleft hright hpoint
    _ = 2 * ∫ y in Ioi b, (a + y) ^ (-(5 : ℝ)) := by
      rw [integral_const_mul]
    _ = (1 / 2 : ℝ) * (a + b) ^ (-(4 : ℝ)) := by
      rw [hshift]
      ring_nf
    _ = (1 / 2 : ℝ) * (rhoTwo x t) ^ (-(4 : ℝ)) := by rw [hρt]

private lemma rho_inv_six_integrableOn_Ioi {x : Vec3} {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => (rhoTwo x s) ^ (-(6 : ℝ))) (Ioi t) volume := by
  let C : ℝ := 1000000000000
  have hdom : IntegrableOn (fun s : ℝ => C * s ^ (-(3 : ℝ)))
      (Ioi t) volume := by
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num) ht).const_mul C
  have hρmeas : Measurable (fun s : ℝ => (rhoTwo x s) ^ (-(6 : ℝ))) := by
    unfold rhoTwo
    measurability
  have hρameas : AEStronglyMeasurable
      (fun s : ℝ => (rhoTwo x s) ^ (-(6 : ℝ)))
      (volume.restrict (Ioi t)) := hρmeas.aestronglyMeasurable.restrict
  refine hdom.mono' hρameas ?_
  exact (ae_restrict_mem measurableSet_Ioi).mono (fun s hs => by
    have hs' : 0 < s := lt_trans ht (mem_Ioi.mp hs)
    have hρ : Real.sqrt s ≤ rhoTwo x s := by
      unfold rhoTwo
      exact le_add_of_nonneg_left (vec3EuclideanNorm_nonneg x)
    have hρpos : 0 < rhoTwo x s := by
      unfold rhoTwo
      exact add_pos_of_nonneg_of_pos (vec3EuclideanNorm_nonneg x)
        (Real.sqrt_pos.2 hs')
    have hcomp : (rhoTwo x s) ^ (-(6 : ℝ)) ≤
        (Real.sqrt s) ^ (-(6 : ℝ)) := by
      exact Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.2 hs') hρ
        (by norm_num)
    have hpow : (Real.sqrt s) ^ (6 : ℕ) = s ^ (3 : ℕ) := by
      rw [show (Real.sqrt s) ^ (6 : ℕ) = ((Real.sqrt s) ^ 2) ^ 3 by ring,
        Real.sq_sqrt hs'.le]
    have hpowr : (Real.sqrt s) ^ (6 : ℝ) = s ^ (3 : ℝ) := by
      calc
        (Real.sqrt s) ^ (6 : ℝ) = (Real.sqrt s) ^ (6 : ℕ) :=
          Real.rpow_natCast _ _
        _ = s ^ (3 : ℕ) := hpow
        _ = s ^ (3 : ℝ) := (Real.rpow_natCast _ _).symm
    have hrpow : s ^ (-(3 : ℝ)) = (s ^ (3 : ℕ))⁻¹ := by
      rw [Real.rpow_neg hs'.le]
      exact congrArg Inv.inv (Real.rpow_natCast s 3)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hρpos.le _)]
    calc
      (rhoTwo x s) ^ (-(6 : ℝ)) ≤ (Real.sqrt s) ^ (-(6 : ℝ)) := hcomp
      _ = s ^ (-(3 : ℝ)) := by
        rw [Real.rpow_neg (Real.sqrt_pos.2 hs').le 6, hpowr, hrpow]
        norm_num [Real.rpow_natCast]
      _ ≤ C * s ^ (-(3 : ℝ)) := by
        have hC : (1 : ℝ) ≤ C := by norm_num [C]
        have hnon : 0 ≤ s ^ (-(3 : ℝ)) := Real.rpow_nonneg hs'.le _
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hnon)

private lemma rho_inv_seven_integrableOn_Ioi {x : Vec3} {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => (rhoTwo x s) ^ (-(7 : ℝ))) (Ioi t) volume := by
  let R : ℝ := rhoTwo x t
  have hRpos : 0 < R := by
    dsimp [R, rhoTwo]
    exact add_pos_of_nonneg_of_pos (vec3EuclideanNorm_nonneg x)
      (Real.sqrt_pos.2 ht)
  have h6 := rho_inv_six_integrableOn_Ioi (x := x) (t := t) ht
  have hdom : IntegrableOn
      (fun s : ℝ => R ^ (-(1 : ℝ)) * (rhoTwo x s) ^ (-(6 : ℝ)))
      (Ioi t) volume := h6.const_mul _
  have hmeas : Measurable (fun s : ℝ => (rhoTwo x s) ^ (-(7 : ℝ))) := by
    unfold rhoTwo
    measurability
  have hameas : AEStronglyMeasurable
      (fun s : ℝ => (rhoTwo x s) ^ (-(7 : ℝ)))
      (volume.restrict (Ioi t)) := hmeas.aestronglyMeasurable.restrict
  refine hdom.mono' hameas ?_
  exact (ae_restrict_mem measurableSet_Ioi).mono (fun s hs => by
    have hs' : 0 < s := lt_trans ht (mem_Ioi.mp hs)
    have hρpos : 0 < rhoTwo x s := by
      unfold rhoTwo
      exact add_pos_of_nonneg_of_pos (vec3EuclideanNorm_nonneg x)
        (Real.sqrt_pos.2 hs')
    have hmon : R ≤ rhoTwo x s := by
      dsimp [R]
      unfold rhoTwo
      exact add_le_add le_rfl (Real.sqrt_le_sqrt (mem_Ioi.mp hs).le)
    have hinv : (rhoTwo x s) ^ (-(1 : ℝ)) ≤ R ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg hρpos.le, Real.rpow_one,
        Real.rpow_neg hRpos.le, Real.rpow_one]
      exact (inv_le_inv₀ hρpos hRpos).2 hmon
    have hsplit : (rhoTwo x s) ^ (-(7 : ℝ)) =
        (rhoTwo x s) ^ (-(1 : ℝ)) * (rhoTwo x s) ^ (-(6 : ℝ)) := by
      rw [show (-(7 : ℝ)) = (-(1 : ℝ)) + (-(6 : ℝ)) by ring,
        Real.rpow_add hρpos]
    rw [hsplit]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact mul_le_mul_of_nonneg_right hinv
        (Real.rpow_nonneg hρpos.le _)
    · exact mul_nonneg (Real.rpow_nonneg hρpos.le _)
        (Real.rpow_nonneg hρpos.le _))

private lemma rho_inv_seven_integral_le {x : Vec3} {t : ℝ} (ht : 0 < t) :
    ∫ s in Ioi t, (rhoTwo x s) ^ (-(7 : ℝ)) ≤
      (1 / 2 : ℝ) * (rhoTwo x t) ^ (-(5 : ℝ)) := by
  let R : ℝ := rhoTwo x t
  have hRpos : 0 < R := by
    dsimp [R, rhoTwo]
    exact add_pos_of_nonneg_of_pos (vec3EuclideanNorm_nonneg x)
      (Real.sqrt_pos.2 ht)
  have h7 := rho_inv_seven_integrableOn_Ioi (x := x) (t := t) ht
  have h6 := rho_inv_six_integrableOn_Ioi (x := x) (t := t) ht
  have hdom : IntegrableOn
      (fun s : ℝ => R ^ (-(1 : ℝ)) * (rhoTwo x s) ^ (-(6 : ℝ)))
      (Ioi t) volume := h6.const_mul _
  have hpoint : ∀ᵐ s ∂(volume.restrict (Ioi t)),
      (rhoTwo x s) ^ (-(7 : ℝ)) ≤
        R ^ (-(1 : ℝ)) * (rhoTwo x s) ^ (-(6 : ℝ)) := by
    exact (ae_restrict_mem measurableSet_Ioi).mono (fun s hs => by
      have hs' : 0 < s := lt_trans ht (mem_Ioi.mp hs)
      have hρpos : 0 < rhoTwo x s := by
        unfold rhoTwo
        exact add_pos_of_nonneg_of_pos (vec3EuclideanNorm_nonneg x)
          (Real.sqrt_pos.2 hs')
      have hmon : R ≤ rhoTwo x s := by
        dsimp [R]
        unfold rhoTwo
        exact add_le_add le_rfl (Real.sqrt_le_sqrt (mem_Ioi.mp hs).le)
      have hinv : (rhoTwo x s) ^ (-(1 : ℝ)) ≤ R ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg hρpos.le, Real.rpow_one,
          Real.rpow_neg hRpos.le, Real.rpow_one]
        exact (inv_le_inv₀ hρpos hRpos).2 hmon
      have hsplit : (rhoTwo x s) ^ (-(7 : ℝ)) =
          (rhoTwo x s) ^ (-(1 : ℝ)) * (rhoTwo x s) ^ (-(6 : ℝ)) := by
        rw [show (-(7 : ℝ)) = (-(1 : ℝ)) + (-(6 : ℝ)) by ring,
          Real.rpow_add hρpos]
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right hinv
        (Real.rpow_nonneg hρpos.le _))
  calc
    ∫ s in Ioi t, (rhoTwo x s) ^ (-(7 : ℝ)) ≤
        ∫ s in Ioi t, R ^ (-(1 : ℝ)) * (rhoTwo x s) ^ (-(6 : ℝ)) :=
      integral_mono_ae h7 hdom hpoint
    _ = R ^ (-(1 : ℝ)) * ∫ s in Ioi t, (rhoTwo x s) ^ (-(6 : ℝ)) := by
      rw [integral_const_mul]
    _ ≤ R ^ (-(1 : ℝ)) * ((1 / 2 : ℝ) * R ^ (-(4 : ℝ))) := by
      gcongr
      exact rho_inv_six_integral_le ht
    _ = (1 / 2 : ℝ) * R ^ (-(5 : ℝ)) := by
      have hsplit : R ^ (-(5 : ℝ)) =
          R ^ (-(1 : ℝ)) * R ^ (-(4 : ℝ)) := by
        rw [show (-(5 : ℝ)) = (-(1 : ℝ)) + (-(4 : ℝ)) by ring,
          Real.rpow_add hRpos]
      rw [hsplit]
      ring_nf

lemma subordinatedKernel_causal {j l m : Fin 3} {x : Vec3} {t : ℝ} (ht : t ≤ 0) :
    subordinatedKernel j l m x t = 0 := by
  simp [subordinatedKernel, not_lt.mpr ht]

lemma subordinatedKernel_integrable {j l m : Fin 3} {x : Vec3} {t : ℝ}
    (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => heatKernelSpaceThirdDerivative x s m j l) (Ioi t) volume := by
  exact third_derivative_integrableOn_Ioi ht m j l

lemma subordinatedKernel_abs_le_rho_inv_four {j l m : Fin 3} {x : Vec3} {t : ℝ}
    (ht : 0 < t) :
    |subordinatedKernel j l m x t| ≤ 1000000000000 / rhoTwo x t ^ 4 := by
  rw [subordinatedKernel, ite_eq_left ht, abs_neg]
  have hInt := subordinatedKernel_integrable (x := x) (j := j) (l := l) (m := m) ht
  have hnorm := MeasureTheory.norm_integral_le_integral_norm
    (μ := volume.restrict (Ioi t))
    (fun s : ℝ => heatKernelSpaceThirdDerivative x s m j l)
  let C : ℝ := 1000000000000
  have hρint : IntegrableOn (fun s : ℝ => (rhoTwo x s) ^ (-(6 : ℝ)))
      (Ioi t) volume := by
    have hdom : IntegrableOn (fun s : ℝ => C * s ^ (-(3 : ℝ)))
        (Ioi t) volume := by
      exact (integrableOn_Ioi_rpow_of_lt (by norm_num) ht).const_mul C
    have hρmeas : Measurable (fun s : ℝ => (rhoTwo x s) ^ (-(6 : ℝ))) := by
      unfold rhoTwo
      measurability
    have hρameas : AEStronglyMeasurable
        (fun s : ℝ => (rhoTwo x s) ^ (-(6 : ℝ)))
        (volume.restrict (Ioi t)) := hρmeas.aestronglyMeasurable.restrict
    refine hdom.mono' hρameas ?_
    exact (ae_restrict_mem measurableSet_Ioi).mono (fun s hs => by
      have hs' : 0 < s := lt_trans ht (mem_Ioi.mp hs)
      have hρ : Real.sqrt s ≤ rhoTwo x s := by
        unfold rhoTwo
        exact le_add_of_nonneg_left (vec3EuclideanNorm_nonneg x)
      have hρpos : 0 < rhoTwo x s := by
        unfold rhoTwo
        exact add_pos_of_nonneg_of_pos (vec3EuclideanNorm_nonneg x)
          (Real.sqrt_pos.2 hs')
      have hcomp : (rhoTwo x s) ^ (-(6 : ℝ)) ≤
          (Real.sqrt s) ^ (-(6 : ℝ)) := by
        exact Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.2 hs') hρ
          (by norm_num)
      have hpow : (Real.sqrt s) ^ (6 : ℕ) = s ^ (3 : ℕ) := by
        rw [show (Real.sqrt s) ^ (6 : ℕ) = ((Real.sqrt s) ^ 2) ^ 3 by ring,
          Real.sq_sqrt hs'.le]
      have hpowr : (Real.sqrt s) ^ (6 : ℝ) = s ^ (3 : ℝ) := by
        calc
          (Real.sqrt s) ^ (6 : ℝ) = (Real.sqrt s) ^ (6 : ℕ) :=
            Real.rpow_natCast _ _
          _ = s ^ (3 : ℕ) := hpow
          _ = s ^ (3 : ℝ) := (Real.rpow_natCast _ _).symm
      have hrpow : s ^ (-(3 : ℝ)) = (s ^ (3 : ℕ))⁻¹ := by
        rw [Real.rpow_neg hs'.le]
        exact congrArg Inv.inv (Real.rpow_natCast s 3)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hρpos.le _)]
      calc
        (rhoTwo x s) ^ (-(6 : ℝ)) ≤ (Real.sqrt s) ^ (-(6 : ℝ)) := hcomp
        _ = s ^ (-(3 : ℝ)) := by
          rw [Real.rpow_neg (Real.sqrt_pos.2 hs').le 6, hpowr, hrpow]
          norm_num [Real.rpow_natCast]
        _ ≤ C * s ^ (-(3 : ℝ)) := by
          have hC : (1 : ℝ) ≤ C := by norm_num [C]
          have hnon : 0 ≤ s ^ (-(3 : ℝ)) := Real.rpow_nonneg hs'.le _
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hnon)
  have hbound :
      ∫ s in Ioi t, |heatKernelSpaceThirdDerivative x s m j l| ≤
        ∫ s in Ioi t, C * (rhoTwo x s) ^ (-(6 : ℝ)) := by
    apply MeasureTheory.integral_mono_ae hInt.norm (hρint.const_mul C)
    exact (ae_restrict_mem measurableSet_Ioi).mono (fun s hs => by
      have hs' : 0 < s := lt_trans ht (mem_Ioi.mp hs)
      have h := heatKernelSpaceThirdDerivative_abs_le_rho_inv_six
        (x := x) (t := s) hs' m j l
      have hρ : 0 < rhoTwo x s := by
        unfold rhoTwo
        exact add_pos_of_nonneg_of_pos (vec3EuclideanNorm_nonneg x)
          (Real.sqrt_pos.2 hs')
      change ‖heatKernelSpaceThirdDerivative x s m j l‖ ≤
        C * (rhoTwo x s) ^ (-(6 : ℝ))
      rw [Real.norm_eq_abs]
      calc
        |heatKernelSpaceThirdDerivative x s m j l| ≤
            1000000000000 / rhoTwo x s ^ 6 := h
        _ = C * (rhoTwo x s) ^ (-(6 : ℝ)) := by
          dsimp [C]
          rw [Real.rpow_neg hρ.le 6, div_eq_mul_inv]
          have hr6 : (rhoTwo x s) ^ (6 : ℝ) = (rhoTwo x s) ^ (6 : ℕ) :=
            Real.rpow_natCast _ _
          rw [hr6]
          )
  calc
    |∫ s in Ioi t, heatKernelSpaceThirdDerivative x s m j l| ≤
        ∫ s in Ioi t, |heatKernelSpaceThirdDerivative x s m j l| := by
      simpa only [Real.norm_eq_abs] using hnorm
    _ ≤ ∫ s in Ioi t, C * (rhoTwo x s) ^ (-(6 : ℝ)) := hbound
    _ = C * ∫ s in Ioi t, (rhoTwo x s) ^ (-(6 : ℝ)) := by
      rw [integral_const_mul]
    _ ≤ C * ((1 / 2 : ℝ) * (rhoTwo x t) ^ (-(4 : ℝ))) := by
      gcongr
      exact rho_inv_six_integral_le ht
    _ ≤ C * (rhoTwo x t) ^ (-(4 : ℝ)) := by
      have hpow : 0 ≤ (rhoTwo x t) ^ (-(4 : ℝ)) :=
        Real.rpow_nonneg (add_nonneg (vec3EuclideanNorm_nonneg _)
          (Real.sqrt_nonneg _)) _
      have hhalf : (1 / 2 : ℝ) * (rhoTwo x t) ^ (-(4 : ℝ)) ≤
          (rhoTwo x t) ^ (-(4 : ℝ)) := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right (by norm_num : (1 / 2 : ℝ) ≤ 1) hpow)
      exact mul_le_mul_of_nonneg_left hhalf (by norm_num [C])
    _ = 1000000000000 / rhoTwo x t ^ 4 := by
      have hρ : 0 < rhoTwo x t := by
        unfold rhoTwo
        exact add_pos_of_nonneg_of_pos (vec3EuclideanNorm_nonneg x)
          (Real.sqrt_pos.2 ht)
      dsimp [C]
      rw [Real.rpow_neg hρ.le 4, div_eq_mul_inv]
      have hr4 : (rhoTwo x t) ^ (4 : ℝ) = (rhoTwo x t) ^ (4 : ℕ) :=
        Real.rpow_natCast _ _
      rw [hr4]

private lemma fourth_derivative_integrableOn_Ioi {x : Vec3} {t : ℝ}
    (ht : 0 < t) (i j k l : Fin 3) :
    IntegrableOn (fun s : ℝ => heatKernelSpaceFourthDerivative x s i j k l)
      (Ioi t) volume := by
  let C : ℝ := 1000000000000000000000000000000
  have hdom : IntegrableOn (fun s : ℝ => C * (rhoTwo x s) ^ (-(7 : ℝ)))
      (Ioi t) volume := by
    exact (rho_inv_seven_integrableOn_Ioi (x := x) (t := t) ht).const_mul C
  have hheat : Measurable (fun s : ℝ => heatKernel x s) := by
    unfold heatKernel
    apply Measurable.ite measurableSet_Ioi
    · measurability
    · measurability
  have hcoef : Measurable (fun s : ℝ =>
      ((x i) * (x j) * (x k) * (x l) / (16 * s ^ 4) -
        ((if i = j then (x k) * (x l) else 0) +
          (if i = k then (x j) * (x l) else 0) +
          (if i = l then (x j) * (x k) else 0) +
          (if j = k then (x i) * (x l) else 0) +
          (if j = l then (x i) * (x k) else 0) +
          (if k = l then (x i) * (x j) else 0)) / (8 * s ^ 3) +
        ((if i = j then (if k = l then (1 : ℝ) else 0) else 0) +
          (if i = k then (if j = l then (1 : ℝ) else 0) else 0) +
          (if i = l then (if j = k then (1 : ℝ) else 0) else 0)) /
          (4 * s ^ 2))) := by
    measurability
  have hfourth : Measurable
      (fun s : ℝ => heatKernelSpaceFourthDerivative x s i j k l) := by
    unfold heatKernelSpaceFourthDerivative
    apply Measurable.ite measurableSet_Ioi
    · exact hcoef.mul hheat
    · measurability
  have hameas : AEStronglyMeasurable
      (fun s : ℝ => heatKernelSpaceFourthDerivative x s i j k l)
      (volume.restrict (Ioi t)) := hfourth.aestronglyMeasurable.restrict
  refine hdom.mono' hameas ?_
  exact (ae_restrict_mem measurableSet_Ioi).mono (fun s hs => by
    have hs' : 0 < s := lt_trans ht (mem_Ioi.mp hs)
    have hρpos : 0 < rhoTwo x s := by
      unfold rhoTwo
      exact add_pos_of_nonneg_of_pos (vec3EuclideanNorm_nonneg x)
        (Real.sqrt_pos.2 hs')
    have h := heatKernelSpaceFourthDerivative_abs_le_rho_inv_seven
      (x := x) (t := s) hs' i j k l
    change ‖heatKernelSpaceFourthDerivative x s i j k l‖ ≤
      C * (rhoTwo x s) ^ (-(7 : ℝ))
    rw [Real.norm_eq_abs]
    calc
      |heatKernelSpaceFourthDerivative x s i j k l| ≤
          1000000000000000000000000000000 / rhoTwo x s ^ 7 := h
      _ = C * (rhoTwo x s) ^ (-(7 : ℝ)) := by
        dsimp [C]
        rw [Real.rpow_neg hρpos.le 7, div_eq_mul_inv]
        have hr7 : (rhoTwo x s) ^ (7 : ℝ) = (rhoTwo x s) ^ (7 : ℕ) :=
          Real.rpow_natCast _ _
        rw [hr7])

lemma subordinatedKernelSpatialDerivative_abs_le_rho_inv_five
    {j l m i : Fin 3} {x : Vec3} {t : ℝ} (ht : 0 < t) :
    |subordinatedKernelSpatialDerivative j l m i x t| ≤
      1000000000000000000000000000000 / rhoTwo x t ^ 5 := by
  rw [subordinatedKernelSpatialDerivative, ite_eq_left ht, abs_neg]
  have hInt := fourth_derivative_integrableOn_Ioi (x := x) (t := t) ht m j l i
  have hnorm := MeasureTheory.norm_integral_le_integral_norm
    (μ := volume.restrict (Ioi t))
    (fun s : ℝ => heatKernelSpaceFourthDerivative x s m j l i)
  let C : ℝ := 1000000000000000000000000000000
  have hbound :
      ∫ s in Ioi t, |heatKernelSpaceFourthDerivative x s m j l i| ≤
        ∫ s in Ioi t, C * (rhoTwo x s) ^ (-(7 : ℝ)) := by
    apply MeasureTheory.integral_mono_ae hInt.norm
      ((rho_inv_seven_integrableOn_Ioi (x := x) (t := t) ht).const_mul C)
    exact (ae_restrict_mem measurableSet_Ioi).mono (fun s hs => by
      have hs' : 0 < s := lt_trans ht (mem_Ioi.mp hs)
      have hρpos : 0 < rhoTwo x s := by
        unfold rhoTwo
        exact add_pos_of_nonneg_of_pos (vec3EuclideanNorm_nonneg x)
          (Real.sqrt_pos.2 hs')
      have h := heatKernelSpaceFourthDerivative_abs_le_rho_inv_seven
        (x := x) (t := s) hs' m j l i
      change ‖heatKernelSpaceFourthDerivative x s m j l i‖ ≤
        C * (rhoTwo x s) ^ (-(7 : ℝ))
      rw [Real.norm_eq_abs]
      calc
        |heatKernelSpaceFourthDerivative x s m j l i| ≤
            1000000000000000000000000000000 / rhoTwo x s ^ 7 := h
        _ = C * (rhoTwo x s) ^ (-(7 : ℝ)) := by
          dsimp [C]
          rw [Real.rpow_neg hρpos.le 7, div_eq_mul_inv]
          have hr7 : (rhoTwo x s) ^ (7 : ℝ) = (rhoTwo x s) ^ (7 : ℕ) :=
            Real.rpow_natCast _ _
          rw [hr7])
  calc
    |∫ s in Ioi t, heatKernelSpaceFourthDerivative x s m j l i| ≤
        ∫ s in Ioi t, |heatKernelSpaceFourthDerivative x s m j l i| := by
      simpa only [Real.norm_eq_abs] using hnorm
    _ ≤ ∫ s in Ioi t, C * (rhoTwo x s) ^ (-(7 : ℝ)) := hbound
    _ = C * ∫ s in Ioi t, (rhoTwo x s) ^ (-(7 : ℝ)) := by
      rw [integral_const_mul]
    _ ≤ C * ((1 / 2 : ℝ) * (rhoTwo x t) ^ (-(5 : ℝ))) := by
      gcongr
      exact rho_inv_seven_integral_le ht
    _ ≤ C * (rhoTwo x t) ^ (-(5 : ℝ)) := by
      have hpow : 0 ≤ (rhoTwo x t) ^ (-(5 : ℝ)) :=
        Real.rpow_nonneg
          (add_nonneg (vec3EuclideanNorm_nonneg x) (Real.sqrt_nonneg _)) _
      have hhalf : (1 / 2 : ℝ) * (rhoTwo x t) ^ (-(5 : ℝ)) ≤
          (rhoTwo x t) ^ (-(5 : ℝ)) := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right (by norm_num : (1 / 2 : ℝ) ≤ 1) hpow)
      exact mul_le_mul_of_nonneg_left hhalf (by norm_num [C])
    _ = 1000000000000000000000000000000 / rhoTwo x t ^ 5 := by
      have hρ : 0 < rhoTwo x t := by
        unfold rhoTwo
        exact add_pos_of_nonneg_of_pos (vec3EuclideanNorm_nonneg x)
          (Real.sqrt_pos.2 ht)
      dsimp [C]
      rw [Real.rpow_neg hρ.le 5, div_eq_mul_inv]
      have hr5 : (rhoTwo x t) ^ (5 : ℝ) = (rhoTwo x t) ^ (5 : ℕ) :=
        Real.rpow_natCast _ _
      rw [hr5]

lemma subordinatedKernel_timeDerivative_abs_le_rho_inv_six
    {j l m : Fin 3} {x : Vec3} {t : ℝ} (ht : 0 < t) :
    |heatKernelSpaceThirdDerivative x t m j l| ≤
      1000000000000 / rhoTwo x t ^ 6 :=
  heatKernelSpaceThirdDerivative_abs_le_rho_inv_six ht m j l

lemma subordinatedKernelSpatialDerivative_causal
    {j l m i : Fin 3} {x : Vec3} {t : ℝ} (ht : t ≤ 0) :
    subordinatedKernelSpatialDerivative j l m i x t = 0 := by
  simp [subordinatedKernelSpatialDerivative, not_lt.mpr ht]

lemma subordinatedKernel_two_point_abs_le
    {j l m : Fin 3} {x y : Vec3} {t R : ℝ} (ht : 0 < t) (hR : 0 < R)
    (hx : R ≤ rhoTwo x t) (hy : R ≤ rhoTwo y t) :
    |subordinatedKernel j l m x t - subordinatedKernel j l m y t| ≤
      2000000000000 / R ^ 4 := by
  have hxr := subordinatedKernel_abs_le_rho_inv_four
    (x := x) (j := j) (l := l) (m := m) (t := t) ht
  have hyr := subordinatedKernel_abs_le_rho_inv_four
    (x := y) (j := j) (l := l) (m := m) (t := t) ht
  have hxd : |subordinatedKernel j l m x t| ≤
      1000000000000 / R ^ 4 := by
    calc
      |subordinatedKernel j l m x t| ≤
          1000000000000 / rhoTwo x t ^ 4 := hxr
      _ ≤ 1000000000000 / R ^ 4 := by gcongr
  have hyd : |subordinatedKernel j l m y t| ≤
      1000000000000 / R ^ 4 := by
    calc
      |subordinatedKernel j l m y t| ≤
          1000000000000 / rhoTwo y t ^ 4 := hyr
      _ ≤ 1000000000000 / R ^ 4 := by gcongr
  calc
    |subordinatedKernel j l m x t - subordinatedKernel j l m y t| ≤
        |subordinatedKernel j l m x t| +
          |subordinatedKernel j l m y t| := by
      simpa [abs_neg] using
        (abs_sub_le (subordinatedKernel j l m x t) 0
          (subordinatedKernel j l m y t))
    _ ≤ 1000000000000 / R ^ 4 + 1000000000000 / R ^ 4 :=
      add_le_add hxd hyd
    _ = 2000000000000 / R ^ 4 := by ring_nf

end CKN.Foundation.Heat
