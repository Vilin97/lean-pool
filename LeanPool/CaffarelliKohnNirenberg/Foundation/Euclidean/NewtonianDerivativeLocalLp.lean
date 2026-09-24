/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Interior
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Newtonian Derivative Local Lp

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

/-- The scalar convolution convention used for the Newtonian derivative. -/
def scalarConvolution (f g : Vec3 → ℝ) (x : Vec3) : ℝ :=
  ∫ y : Vec3, f y * g (x - y)

def convolutionMajorant (f g : Vec3 → ℝ≥0∞) (x : Vec3) : ℝ≥0∞ :=
  ∫⁻ y : Vec3, f y * g (x - y)

private theorem convolutionMajorant_aemeasurable {f g : Vec3 → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (convolutionMajorant f g) := by
  apply Measurable.lintegral_prod_right
  exact ((hf.comp measurable_snd).mul (hg.comp (measurable_fst.sub measurable_snd)))

private theorem convolutionMajorant_integral {f g : Vec3 → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x : Vec3, convolutionMajorant f g x) =
      (∫⁻ y : Vec3, f y) * (∫⁻ z : Vec3, g z) := by
  unfold convolutionMajorant
  rw [lintegral_lintegral_swap
    ((hf.comp measurable_snd).mul
      (hg.comp (measurable_fst.sub measurable_snd))).aemeasurable]
  have hy (y : Vec3) : (∫⁻ x : Vec3, f y * g (x - y)) =
      f y * (∫⁻ x : Vec3, g x) := by
    rw [lintegral_const_mul (μ := volume) (f := fun x : Vec3 => g (x - y))
      (f y) (by fun_prop)]
    rw [lintegral_sub_right_eq_self g]
  simp_rw [hy]
  exact lintegral_mul_const _ hf

private theorem convolutionMajorant_three_halves_le {f g : Vec3 → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (x : Vec3) :
    convolutionMajorant f g x ^ (3 / 2 : ℝ) ≤
      convolutionMajorant (fun y => f y ^ (6 / 5 : ℝ))
          (fun y => g y ^ (6 / 5 : ℝ)) x *
        ((∫⁻ y : Vec3, f y ^ (6 / 5 : ℝ)) ^ (1 / 4 : ℝ) *
          (∫⁻ y : Vec3, g y ^ (6 / 5 : ℝ)) ^ (1 / 4 : ℝ)) := by
  have hconj : Real.HolderConjugate (3 / 2 : ℝ) 3 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hsplit (a b : ℝ≥0∞) :
      (a ^ (4 / 5 : ℝ) * b ^ (4 / 5 : ℝ)) *
          (a ^ (1 / 5 : ℝ) * b ^ (1 / 5 : ℝ)) = a * b := by
    calc
      _ = (a ^ (4 / 5 : ℝ) * a ^ (1 / 5 : ℝ)) *
          (b ^ (4 / 5 : ℝ) * b ^ (1 / 5 : ℝ)) := by ac_rfl
      _ = _ := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num),
          ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
        norm_num
  have hpow1 (a b : ℝ≥0∞) :
      (a ^ (4 / 5 : ℝ) * b ^ (4 / 5 : ℝ)) ^ (3 / 2 : ℝ) =
        a ^ (6 / 5 : ℝ) * b ^ (6 / 5 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul]
    congr 1 <;> norm_num
  have hpow2 (a b : ℝ≥0∞) :
      (a ^ (1 / 5 : ℝ) * b ^ (1 / 5 : ℝ)) ^ (3 : ℝ) =
        a ^ (3 / 5 : ℝ) * b ^ (3 / 5 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul]
    congr 1 <;> norm_num
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure Vec3)
    (p := (3 / 2 : ℝ)) (q := (3 : ℝ)) hconj
    (f := fun y => f y ^ (4 / 5 : ℝ) * g (x - y) ^ (4 / 5 : ℝ))
    (g := fun y => f y ^ (1 / 5 : ℝ) * g (x - y) ^ (1 / 5 : ℝ))
    (by fun_prop) (by fun_prop)
  have hholder' : convolutionMajorant f g x ≤
      convolutionMajorant (fun y => f y ^ (6 / 5 : ℝ))
          (fun y => g y ^ (6 / 5 : ℝ)) x ^ (2 / 3 : ℝ) *
        (∫⁻ y : Vec3, f y ^ (3 / 5 : ℝ) * g (x - y) ^ (3 / 5 : ℝ)) ^
          (1 / 3 : ℝ) := by
    have hleft :
        (∫⁻ a : Vec3,
          ((fun y => f y ^ (4 / 5 : ℝ) * g (x - y) ^ (4 / 5 : ℝ)) *
            (fun y => f y ^ (1 / 5 : ℝ) * g (x - y) ^ (1 / 5 : ℝ))) a) =
          convolutionMajorant f g x := by
      apply lintegral_congr
      intro a
      exact hsplit (f a) (g (x - a))
    have hfirst :
        (∫⁻ a : Vec3, (f a ^ (4 / 5 : ℝ) * g (x - a) ^ (4 / 5 : ℝ)) ^
          (3 / 2 : ℝ)) =
          ∫⁻ a : Vec3, f a ^ (6 / 5 : ℝ) * g (x - a) ^ (6 / 5 : ℝ) := by
      apply lintegral_congr
      intro a
      exact hpow1 (f a) (g (x - a))
    have hthird :
        (∫⁻ a : Vec3, (f a ^ (1 / 5 : ℝ) * g (x - a) ^ (1 / 5 : ℝ)) ^
          (3 : ℝ)) =
          ∫⁻ a : Vec3, f a ^ (3 / 5 : ℝ) * g (x - a) ^ (3 / 5 : ℝ) := by
      apply lintegral_congr
      intro a
      exact hpow2 (f a) (g (x - a))
    calc
      convolutionMajorant f g x =
          ∫⁻ a : Vec3,
            ((fun y => f y ^ (4 / 5 : ℝ) * g (x - y) ^ (4 / 5 : ℝ)) *
              (fun y => f y ^ (1 / 5 : ℝ) * g (x - y) ^ (1 / 5 : ℝ))) a := hleft.symm
      _ ≤ (∫⁻ a : Vec3,
          (f a ^ (4 / 5 : ℝ) * g (x - a) ^ (4 / 5 : ℝ)) ^ (3 / 2 : ℝ)) ^
            (1 / (3 / 2 : ℝ)) *
          (∫⁻ a : Vec3,
            (f a ^ (1 / 5 : ℝ) * g (x - a) ^ (1 / 5 : ℝ)) ^ (3 : ℝ)) ^
            (1 / 3 : ℝ) := hholder
      _ = convolutionMajorant (fun y => f y ^ (6 / 5 : ℝ))
          (fun y => g y ^ (6 / 5 : ℝ)) x ^ (2 / 3 : ℝ) *
          (∫⁻ y : Vec3, f y ^ (3 / 5 : ℝ) * g (x - y) ^ (3 / 5 : ℝ)) ^
            (1 / 3 : ℝ) := by
        rw [hfirst, hthird]
        norm_num [convolutionMajorant]
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure Vec3)
    Real.HolderConjugate.two_two
    (f := fun y => f y ^ (3 / 5 : ℝ))
    (g := fun y => g (x - y) ^ (3 / 5 : ℝ)) (by fun_prop) (by fun_prop)
  have hcs' : (∫⁻ y : Vec3, f y ^ (3 / 5 : ℝ) * g (x - y) ^ (3 / 5 : ℝ)) ≤
      (∫⁻ y : Vec3, f y ^ (6 / 5 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫⁻ y : Vec3, g y ^ (6 / 5 : ℝ)) ^ (1 / 2 : ℝ) := by
    have hcs0 := hcs
    simp only [Pi.mul_apply, ← ENNReal.rpow_mul] at hcs0
    norm_num at hcs0
    rw [lintegral_sub_left_eq_self (fun y => g y ^ (6 / 5 : ℝ)) x] at hcs0
    exact hcs0
  calc
    convolutionMajorant f g x ^ (3 / 2 : ℝ) ≤
        (convolutionMajorant (fun y => f y ^ (6 / 5 : ℝ))
          (fun y => g y ^ (6 / 5 : ℝ)) x ^ (2 / 3 : ℝ) *
          (∫⁻ y : Vec3, f y ^ (3 / 5 : ℝ) * g (x - y) ^ (3 / 5 : ℝ)) ^
            (1 / 3 : ℝ)) ^ (3 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hholder' (by norm_num)
    _ = convolutionMajorant (fun y => f y ^ (6 / 5 : ℝ))
          (fun y => g y ^ (6 / 5 : ℝ)) x *
          (∫⁻ y : Vec3, f y ^ (3 / 5 : ℝ) * g (x - y) ^ (3 / 5 : ℝ)) ^
            (1 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      congr 1 <;> norm_num
    _ ≤ convolutionMajorant (fun y => f y ^ (6 / 5 : ℝ))
          (fun y => g y ^ (6 / 5 : ℝ)) x *
          ((∫⁻ y : Vec3, f y ^ (6 / 5 : ℝ)) ^ (1 / 4 : ℝ) *
            (∫⁻ y : Vec3, g y ^ (6 / 5 : ℝ)) ^ (1 / 4 : ℝ)) := by
      have hnonneg : 0 ≤ convolutionMajorant
          (fun y => f y ^ (6 / 5 : ℝ)) (fun y => g y ^ (6 / 5 : ℝ)) x := bot_le
      have hpow := ENNReal.rpow_le_rpow hcs'
        (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      have hpow' :
          (∫⁻ y : Vec3, f y ^ (3 / 5 : ℝ) * g (x - y) ^ (3 / 5 : ℝ)) ^
              (1 / 2 : ℝ) ≤
            (∫⁻ y : Vec3, f y ^ (6 / 5 : ℝ)) ^ (1 / 4 : ℝ) *
              (∫⁻ y : Vec3, g y ^ (6 / 5 : ℝ)) ^ (1 / 4 : ℝ) := by
        calc
          _ ≤ ((∫⁻ y : Vec3, f y ^ (6 / 5 : ℝ)) ^ (1 / 2 : ℝ) *
              (∫⁻ y : Vec3, g y ^ (6 / 5 : ℝ)) ^ (1 / 2 : ℝ)) ^
                (1 / 2 : ℝ) := hpow
          _ = _ := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
              ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
            congr 1 <;> norm_num
      exact mul_le_mul_of_nonneg_left hpow' hnonneg

private theorem convolutionMajorant_young_three_halves {f g : Vec3 → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x : Vec3, convolutionMajorant f g x ^ (3 / 2 : ℝ)) ≤
      (∫⁻ y : Vec3, f y ^ (6 / 5 : ℝ)) ^ (5 / 4 : ℝ) *
        (∫⁻ z : Vec3, g z ^ (6 / 5 : ℝ)) ^ (5 / 4 : ℝ) := by
  let F := ∫⁻ y : Vec3, f y ^ (6 / 5 : ℝ)
  let G := ∫⁻ y : Vec3, g y ^ (6 / 5 : ℝ)
  calc
    _ ≤ ∫⁻ x : Vec3,
        convolutionMajorant (fun y => f y ^ (6 / 5 : ℝ))
          (fun y => g y ^ (6 / 5 : ℝ)) x * (F ^ (1 / 4 : ℝ) * G ^ (1 / 4 : ℝ)) :=
      lintegral_mono (convolutionMajorant_three_halves_le hf hg)
    _ = (F * G) * (F ^ (1 / 4 : ℝ) * G ^ (1 / 4 : ℝ)) := by
      rw [lintegral_mul_const _
        (convolutionMajorant_aemeasurable (hf.pow_const _) (hg.pow_const _)),
        convolutionMajorant_integral (hf.pow_const _) (hg.pow_const _)]
    _ = F ^ (5 / 4 : ℝ) * G ^ (5 / 4 : ℝ) := by
      calc
        _ = (F * F ^ (1 / 4 : ℝ)) * (G * G ^ (1 / 4 : ℝ)) := by ac_rfl
        _ = (F ^ (1 : ℝ) * F ^ (1 / 4 : ℝ)) *
            (G ^ (1 : ℝ) * G ^ (1 / 4 : ℝ)) := by simp
        _ = F ^ (1 + (1 / 4 : ℝ)) * G ^ (1 + (1 / 4 : ℝ)) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num),
            ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
        _ = F ^ (5 / 4 : ℝ) * G ^ (5 / 4 : ℝ) := by norm_num

private theorem scalarConvolution_aemeasurable {f g : Vec3 → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    AEStronglyMeasurable (scalarConvolution f g) (volume : Measure Vec3) := by
  exact ((hf.comp measurable_snd).mul
      (hg.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable.integral_prod_right'

private theorem enorm_scalarConvolution_le (f g : Vec3 → ℝ) (x : Vec3) :
    ‖scalarConvolution f g x‖ₑ ≤
      convolutionMajorant (fun y => ‖f y‖ₑ) (fun y => ‖g y‖ₑ) x := by
  simpa only [scalarConvolution, convolutionMajorant, enorm_mul] using
    (enorm_integral_le_lintegral_enorm
      (fun y : Vec3 => f y * g (x - y)))

/-- Young's estimate for the exponents used by the truncated Newtonian derivative.
The proof uses Hölder twice and Tonelli on the nonnegative majorant. -/
theorem eLpNorm_scalarConvolution_six_fifths_three_halves
    {f g : Vec3 → ℝ} (hf : Measurable f) (hg : Measurable g) :
    eLpNorm (scalarConvolution f g) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      eLpNorm f (ENNReal.ofReal (6 / 5 : ℝ)) volume *
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  have hmajor := convolutionMajorant_young_three_halves hf.enorm hg.enorm
  have hb : (∫⁻ x : Vec3, ‖scalarConvolution f g x‖ₑ ^ (3 / 2 : ℝ)) ≤
      (∫⁻ y : Vec3, ‖f y‖ₑ ^ (6 / 5 : ℝ)) ^ (5 / 4 : ℝ) *
        (∫⁻ z : Vec3, ‖g z‖ₑ ^ (6 / 5 : ℝ)) ^ (5 / 4 : ℝ) := by
    refine (lintegral_mono fun x => ?_).trans hmajor
    exact ENNReal.rpow_le_rpow (enorm_scalarConvolution_le f g x) (by norm_num)
  have hp := ENNReal.rpow_le_rpow hb (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (p := ENNReal.ofReal (3 / 2 : ℝ)) (by positivity) ENNReal.ofReal_ne_top
      (scalarConvolution_aemeasurable hf hg),
    eLpNorm_eq_lintegral_rpow_enorm_toReal
      (p := ENNReal.ofReal (6 / 5 : ℝ)) (by positivity) ENNReal.ofReal_ne_top
        hf.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal
      (p := ENNReal.ofReal (6 / 5 : ℝ)) (by positivity) ENNReal.ofReal_ne_top hg.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2),
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6 / 5)]
  norm_num only [ENNReal.toReal_ofReal, ENNReal.rpow_two]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at hp
  norm_num at hp
  exact hp

private theorem ae_integrable_scalarConvolution_six_fifths_three_halves
    {f g : Vec3 → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf₆ : MemLp f (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hg₆ : MemLp g (ENNReal.ofReal (6 / 5 : ℝ)) volume) :
    ∀ᵐ x ∂volume, Integrable (fun y : Vec3 => f y * g (x - y)) := by
  have hfm : (∫⁻ y : Vec3, ‖f y‖ₑ ^ (6 / 5 : ℝ)) < ∞ := by
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6 / 5)] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (p := ENNReal.ofReal (6 / 5 : ℝ)) (by positivity) ENNReal.ofReal_ne_top
        hf₆.eLpNorm_lt_top)
  have hgm : (∫⁻ y : Vec3, ‖g y‖ₑ ^ (6 / 5 : ℝ)) < ∞ := by
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6 / 5)] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (p := ENNReal.ofReal (6 / 5 : ℝ)) (by positivity) ENNReal.ofReal_ne_top
        hg₆.eLpNorm_lt_top)
  have hmajor := convolutionMajorant_young_three_halves hf.enorm hg.enorm
  have hfin : (∫⁻ x : Vec3,
      convolutionMajorant (fun y => ‖f y‖ₑ) (fun y => ‖g y‖ₑ) x ^ (3 / 2 : ℝ)) < ∞ := by
    exact hmajor.trans_lt (by finiteness)
  have htop : ∀ᵐ x ∂volume,
      convolutionMajorant (fun y => ‖f y‖ₑ) (fun y => ‖g y‖ₑ) x < ∞ := by
    have hpow : ∀ᵐ x ∂volume,
        convolutionMajorant (fun y => ‖f y‖ₑ) (fun y => ‖g y‖ₑ) x ^ (3 / 2 : ℝ) < ∞ :=
      ae_lt_top ((convolutionMajorant_aemeasurable hf.enorm hg.enorm).pow_const _)
        (by exact hfin.ne)
    filter_upwards [hpow] with x hx
    by_contra hx'
    have htop' : convolutionMajorant (fun y => ‖f y‖ₑ) (fun y => ‖g y‖ₑ) x = ∞ :=
      top_unique (le_of_not_gt hx')
    simp [htop'] at hx
  filter_upwards [htop] with x hx
  refine ⟨(hf.mul (hg.comp (measurable_const.sub measurable_id))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [convolutionMajorant, enorm_mul] using hx

/-! The next declarations specialize the preceding Young estimate to the
three-dimensional Newtonian derivative. -/

/-- The Newtonian derivative kernel truncated to a ball about the origin. -/
def truncatedNewtonianDerivative (R : ℝ) (i : Fin 3) : Vec3 → ℝ := fun z =>
  if ‖z‖ < R then spatialDeriv newtonianKernel i z else 0

/-- The truncated Newtonian derivative kernel is measurable. -/
theorem measurable_truncatedNewtonianDerivative (R : ℝ) (i : Fin 3) :
    Measurable (truncatedNewtonianDerivative R i) := by
  exact (measurable_fderiv_apply_const ℝ newtonianKernel (CKN.basisVec i)).piecewise
    (measurableSet_lt measurable_norm measurable_const) measurable_const

/-! The complementary kernel is kept separate so that the local estimate can
be assembled from a Young bound and a pointwise tail bound. -/

/-- The Newtonian derivative kernel restricted to the complement of a ball. -/
def farNewtonianDerivative (R : ℝ) (i : Fin 3) : Vec3 → ℝ := fun z =>
  if R ≤ ‖z‖ then spatialDeriv newtonianKernel i z else 0

/-- The complementary Newtonian derivative kernel is measurable. -/
theorem measurable_farNewtonianDerivative (R : ℝ) (i : Fin 3) :
    Measurable (farNewtonianDerivative R i) := by
  exact (measurable_fderiv_apply_const ℝ newtonianKernel (CKN.basisVec i)).piecewise
    (measurableSet_le measurable_const measurable_norm) measurable_const

/-- The truncated Newtonian derivative belongs to `L^(6/5)`. -/
theorem truncatedNewtonianDerivative_memLp
    {R : ℝ} (_ : 0 < R) (i : Fin 3) :
    MemLp (truncatedNewtonianDerivative R i)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  let k := truncatedNewtonianDerivative R i
  have hkmeas : AEStronglyMeasurable k volume :=
    (measurable_truncatedNewtonianDerivative R i).aestronglyMeasurable
  let kp : Vec3 → ℝ := fun z => ‖k z‖ ^ (6 / 5 : ℝ)
  have hkpmeas : AEStronglyMeasurable kp volume := by
    exact ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 6 / 5)).measurable.comp_aemeasurable
      hkmeas.norm.aemeasurable).aestronglyMeasurable
  have hz0 : ∀ᵐ z ∂volume.restrict (ball (0 : Vec3) R), z ≠ 0 :=
    ae_restrict_of_ae (Measure.ae_ne volume (0 : Vec3))
  have hdecay : ∀ᵐ z ∂volume.restrict (ball (0 : Vec3) R),
      ‖kp z‖ ≤ ((4 * Real.pi)⁻¹) ^ (6 / 5 : ℝ) *
        ‖z‖ ^ (-(12 / 5 : ℝ)) := by
    filter_upwards [ae_restrict_mem (isOpen_ball.measurableSet), hz0]
      with z hz hzero
    have hbound := newtonianKernel_spatialDeriv_size_bound hzero i
    have hkval : k z = spatialDeriv newtonianKernel i z := by
      dsimp [k, truncatedNewtonianDerivative]
      simp only [mem_ball_zero_iff] at hz
      simp only [hz, ite_true]
    dsimp [kp]
    rw [hkval, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have hpow := Real.rpow_le_rpow (abs_nonneg _) hbound
      (by positivity : 0 ≤ (6 / 5 : ℝ))
    have hright : ((4 * Real.pi)⁻¹) ^ (6 / 5 : ℝ) *
        ‖z‖ ^ (-(12 / 5 : ℝ)) =
        ((4 * Real.pi)⁻¹ * (‖z‖ ^ (-2 : ℝ))) ^ (6 / 5 : ℝ) := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
      congr 1
      norm_num
    calc
      |spatialDeriv newtonianKernel i z| ^ (6 / 5 : ℝ) ≤
          ((4 * Real.pi)⁻¹ * (‖z‖ ^ (-2 : ℝ))) ^ (6 / 5 : ℝ) := by
        simpa only [Real.norm_eq_abs, Real.rpow_neg (norm_nonneg _), Real.rpow_two] using hpow
      _ = _ := hright.symm
  have hintOn : IntegrableOn kp (ball (0 : Vec3) R) volume := by
    apply integrableOn_ball_of_norm_le_rpow (E := Vec3) (F := ℝ)
      (by change 1 ≤ Module.finrank ℝ (Fin 3 → ℝ); rw [Module.finrank_fin_fun]; norm_num)
      (by change (12 / 5 : ℝ) < (Module.finrank ℝ Vec3 : ℝ)
          ; rw [Module.finrank_fin_fun]
          ; norm_num)
      hdecay hkpmeas
  have hint : Integrable kp volume := by
    exact hintOn.integrable_of_forall_notMem_eq_zero (by
      intro z hz
      have hz' : ¬ ‖z‖ < R := by simpa [mem_ball_zero_iff] using hz
      simp [kp, k, truncatedNewtonianDerivative, hz'])
  rw [← (integrable_norm_rpow_iff hkmeas (by norm_num) (by norm_num))]
  convert hint using 1
  norm_num [kp]

/-- The first Newtonian derivative potential, with the derivative in the kernel slot. -/
def newtonianDerivativePotential (i : Fin 3) (G : Vec3 → ℝ) (x : Vec3) : ℝ :=
  ∫ y, spatialDeriv newtonianKernel i (x - y) * G y

/-- The derivative kernel has the expected inverse-square bound away from the origin. -/
theorem newtonianDerivative_far_kernel_bound {R' : ℝ} {z : Vec3}
    (hR' : 0 < R') (hz : R' ≤ ‖z‖) (i : Fin 3) :
    |spatialDeriv newtonianKernel i z| ≤
      (4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹ := by
  have hzero : z ≠ 0 := by
    intro hz0
    subst z
    simp only [norm_zero] at hz
    linarith only [hR', hz]
  have hsq : R' ^ 2 ≤ ‖z‖ ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hz
  have hinv : (‖z‖ ^ 2)⁻¹ ≤ (R' ^ 2)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hsq
  have hbound := newtonianKernel_spatialDeriv_size_bound hzero i
  exact hbound.trans (mul_le_mul_of_nonneg_left hinv (by positivity))

/-- The far kernel is bounded by its inverse-square value at the cutoff. -/
theorem norm_farNewtonianDerivative_le {R : ℝ} (hR : 0 < R) (i : Fin 3) (z : Vec3) :
    ‖farNewtonianDerivative R i z‖ ≤
      (4 * Real.pi)⁻¹ * (R ^ 2)⁻¹ := by
  by_cases hz : R ≤ ‖z‖
  · simp only [farNewtonianDerivative, hz, ite_true]
    simpa only [Real.norm_eq_abs] using newtonianDerivative_far_kernel_bound hR hz i
  · simp only [farNewtonianDerivative, hz, ite_false, norm_zero]
    positivity

/-- At points whose support is outside the near ball, the far potential is bounded
by the inverse-square kernel constant times the `L¹` size of the data. -/
theorem newtonianDerivative_far_integral_enorm_le
    {G : Vec3 → ℝ} (i : Fin 3) {R' : ℝ} (hR' : 0 < R') (x : Vec3)
    (hfar : ∀ y, G y ≠ 0 → R' ≤ ‖x - y‖) :
    ‖newtonianDerivativePotential i G x‖ₑ ≤
      ENNReal.ofReal ((4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹) *
        (∫⁻ y, ‖G y‖ₑ) := by
  calc
    ‖newtonianDerivativePotential i G x‖ₑ ≤
        ∫⁻ y, ‖spatialDeriv newtonianKernel i (x - y) * G y‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, ENNReal.ofReal ((4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹) * ‖G y‖ₑ := by
      apply lintegral_mono
      intro y
      by_cases hGy : G y = 0
      · simp [hGy]
      · have hbound := newtonianDerivative_far_kernel_bound hR' (hfar y hGy) i
        have hbound' : ‖spatialDeriv newtonianKernel i (x - y)‖ₑ ≤
          ENNReal.ofReal ((4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹) := by
          simpa only [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal hbound
        calc
          ‖spatialDeriv newtonianKernel i (x - y) * G y‖ₑ =
              ‖spatialDeriv newtonianKernel i (x - y)‖ₑ * ‖G y‖ₑ := by
            rw [← enorm_mul]
          _ ≤ ENNReal.ofReal ((4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹) * ‖G y‖ₑ :=
            mul_le_mul_of_nonneg_right hbound' (by positivity)
    _ = ENNReal.ofReal ((4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹) *
        (∫⁻ y, ‖G y‖ₑ) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The convolution with the far kernel has the same pointwise tail bound. -/
theorem scalarConvolution_far_enorm_le
    {G : Vec3 → ℝ} (i : Fin 3) {R : ℝ} (hR : 0 < R) (x : Vec3) :
    ‖scalarConvolution G (farNewtonianDerivative R i) x‖ₑ ≤
      ENNReal.ofReal ((4 * Real.pi)⁻¹ * (R ^ 2)⁻¹) *
        (∫⁻ y, ‖G y‖ₑ) := by
  calc
    ‖scalarConvolution G (farNewtonianDerivative R i) x‖ₑ ≤
        ∫⁻ y, ‖G y * farNewtonianDerivative R i (x - y)‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, ENNReal.ofReal ((4 * Real.pi)⁻¹ * (R ^ 2)⁻¹) * ‖G y‖ₑ := by
      apply lintegral_mono
      intro y
      calc
        ‖G y * farNewtonianDerivative R i (x - y)‖ₑ =
            ‖farNewtonianDerivative R i (x - y)‖ₑ * ‖G y‖ₑ := by
          rw [enorm_mul]
          ac_rfl
        _ ≤ ENNReal.ofReal ((4 * Real.pi)⁻¹ * (R ^ 2)⁻¹) * ‖G y‖ₑ := by
          have hbound := norm_farNewtonianDerivative_le hR i (x - y)
          have hbound' : ‖farNewtonianDerivative R i (x - y)‖ₑ ≤
              ENNReal.ofReal ((4 * Real.pi)⁻¹ * (R ^ 2)⁻¹) := by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal hbound
          exact mul_le_mul_of_nonneg_right hbound' (by positivity)
    _ = ENNReal.ofReal ((4 * Real.pi)⁻¹ * (R ^ 2)⁻¹) *
        (∫⁻ y, ‖G y‖ₑ) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Compact support converts the `L^(6/5)` size into the `L¹` size needed by
the far part. -/
theorem eLpNorm_one_le_of_memLp_six_fifths_of_support
    {G : Vec3 → ℝ} {R : ℝ} (_ : 0 < R) (hGmeas : Measurable G)
    (_ : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    eLpNorm G 1 volume ≤
      volume (closedBall (0 : Vec3) R) ^ (1 / 6 : ℝ) *
        eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  let K : Set Vec3 := closedBall (0 : Vec3) R
  have hKmeas : MeasurableSet K := isClosed_closedBall.measurableSet
  have hKtop : volume K ≠ ∞ := measure_closedBall_lt_top.ne
  have hconj : Real.HolderConjugate (6 / 5 : ℝ) 6 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  let oneK : Vec3 → ENNReal := K.indicator (fun _ => 1)
  have honeK : AEMeasurable oneK := by
    exact (measurable_const.indicator hKmeas).aemeasurable
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure Vec3)
    hconj hGmeas.enorm.aemeasurable honeK
  have hleft : (∫⁻ y, ‖G y‖ₑ * oneK y) = ∫⁻ y, ‖G y‖ₑ := by
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ K
    · simp [oneK, Set.indicator_of_mem hy]
    · have hGy : G y = 0 := hGzero y hy
      simp [oneK, Set.indicator_of_notMem hy, hGy]
  have hKpow : (∫⁻ y, oneK y ^ (6 : ℝ)) = volume K := by
    rw [show (fun y => oneK y ^ (6 : ℝ)) = K.indicator (fun _ => (1 : ENNReal)) by
      funext y
      by_cases hy : y ∈ K <;> simp [oneK, Set.indicator_of_mem, Set.indicator_of_notMem, hy]]
    rw [lintegral_indicator hKmeas]
    simp
  have hGnorm : eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume =
      (∫⁻ y, ‖G y‖ₑ ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (p := ENNReal.ofReal (6 / 5 : ℝ)) (by positivity) ENNReal.ofReal_ne_top
      hGmeas.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6 / 5)]
    congr 1
    norm_num
  calc
    eLpNorm G 1 volume = ∫⁻ y, ‖G y‖ₑ :=
      eLpNorm_one_eq_lintegral_enorm hGmeas.aestronglyMeasurable
    _ = ∫⁻ y, ‖G y‖ₑ * oneK y := hleft.symm
    _ ≤ (∫⁻ y, ‖G y‖ₑ ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) *
        (∫⁻ y, oneK y ^ (6 : ℝ)) ^ (1 / 6 : ℝ) := by
      convert hholder using 1; norm_num
    _ = volume K ^ (1 / 6 : ℝ) *
        eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
      rw [hKpow, hGnorm]
      ac_rfl

/-- The local Newtonian derivative estimate obtained by adding the near Young
estimate to the bounded far tail. -/
theorem newtonianDerivativePotential_eLpNorm_three_halves_restrict_ball_le_split
    {G : Vec3 → ℝ} (i : Fin 3) {R ρ R' : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (hR' : 0 < R') (hGmeas : Measurable G)
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    eLpNorm (newtonianDerivativePotential i G)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (ball (0 : Vec3) ρ)) ≤
      eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume *
          eLpNorm (truncatedNewtonianDerivative R' i)
            (ENNReal.ofReal (6 / 5 : ℝ)) volume +
        ENNReal.ofReal ((4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹) *
          volume (ball (0 : Vec3) ρ) ^ (2 / 3 : ℝ) *
          volume (closedBall (0 : Vec3) R) ^ (1 / 6 : ℝ) *
          eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  let μ : Measure Vec3 := volume.restrict (ball (0 : Vec3) ρ)
  let kNear := truncatedNewtonianDerivative R' i
  let kFar := farNewtonianDerivative R' i
  have hkNear : MemLp kNear (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    exact truncatedNewtonianDerivative_memLp (R := R') hR' i
  have hkNearMeas : Measurable kNear := by
    exact measurable_truncatedNewtonianDerivative R' i
  have hkFarMeas : Measurable kFar := by
    exact measurable_farNewtonianDerivative R' i
  have hnearAE := ae_integrable_scalarConvolution_six_fifths_three_halves
    hGmeas hkNearMeas hG hkNear
  have hG1norm : eLpNorm G 1 volume < ∞ := by
    have hbound := eLpNorm_one_le_of_memLp_six_fifths_of_support
      hR hGmeas hG hGzero
    exact hbound.trans_lt
      (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
          measure_closedBall_lt_top.ne)
        hG.eLpNorm_lt_top)
  have hGint : Integrable G volume := by
    rw [← memLp_one_iff_integrable]
    exact hG1norm
  have hfarInt (x : Vec3) :
      Integrable (fun y : Vec3 => G y * kFar (x - y)) volume := by
    apply hGint.mul_bdd
    · exact (hkFarMeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · filter_upwards [] with y
      exact norm_farNewtonianDerivative_le hR' i (x - y)
  have hkernel (z : Vec3) :
      spatialDeriv newtonianKernel i z = kNear z + kFar z := by
    by_cases hz : ‖z‖ < R'
    · simp [kNear, kFar, truncatedNewtonianDerivative, farNewtonianDerivative, hz,
        not_le.mpr hz]
    · have hz' : R' ≤ ‖z‖ := le_of_not_gt hz
      simp [kNear, kFar, truncatedNewtonianDerivative, farNewtonianDerivative, hz, hz']
  have hdecomp (x : Vec3)
      (hx : Integrable (fun y : Vec3 => G y * kNear (x - y)) volume) :
      newtonianDerivativePotential i G x =
        scalarConvolution G kNear x + scalarConvolution G kFar x := by
    rw [newtonianDerivativePotential, scalarConvolution, scalarConvolution]
    have hfun : (fun y : Vec3 => spatialDeriv newtonianKernel i (x - y) * G y) =
        (fun y : Vec3 => G y * kNear (x - y)) +
          (fun y : Vec3 => G y * kFar (x - y)) := by
      funext y
      rw [hkernel]
      simp only [Pi.add_apply]
      ring
    rw [hfun]
    change (∫ y : Vec3, G y * kNear (x - y) + G y * kFar (x - y)) = _
    exact integral_add hx (hfarInt x)
  have hdecompAE : newtonianDerivativePotential i G =ᵐ[μ]
      scalarConvolution G kNear + scalarConvolution G kFar := by
    filter_upwards [ae_restrict_of_ae hnearAE] with x hx
    exact hdecomp x hx
  have hfarBound (x : Vec3) :
      ‖scalarConvolution G kFar x‖ₑ ≤
        ‖(4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹ * (∫ y : Vec3, ‖G y‖)‖ₑ := by
    have h := scalarConvolution_far_enorm_le (G := G) i hR' x
    have hnormG : ENNReal.ofReal (∫ y : Vec3, ‖G y‖) = ∫⁻ y, ‖G y‖ₑ :=
      ofReal_integral_norm_eq_lintegral_enorm hGint
    have hC : 0 ≤ (4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹ := by positivity
    rw [Real.enorm_eq_ofReal (mul_nonneg hC (integral_nonneg (fun _ => norm_nonneg _))),
      ENNReal.ofReal_mul hC, hnormG]
    exact h
  have hfarMeas : AEStronglyMeasurable (scalarConvolution G kFar) volume :=
    scalarConvolution_aemeasurable hGmeas hkFarMeas
  have hfarLp : eLpNorm (scalarConvolution G kFar) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
      eLpNorm (fun _ : Vec3 =>
        (4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹ * (∫ y : Vec3, ‖G y‖))
        (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    apply eLpNorm_mono_enorm_ae (μ := μ) hfarMeas.restrict
    exact Eventually.of_forall hfarBound
  have hμne : μ ≠ 0 := by
    intro hzero
    have hzvol : volume (ball (0 : Vec3) ρ) = 0 :=
      Measure.restrict_eq_zero.mp (show volume.restrict (ball (0 : Vec3) ρ) = 0 by
        exact hzero)
    exact (ne_of_gt (Metric.isOpen_ball.measure_pos volume
      (Metric.nonempty_ball.mpr hρ))) hzvol
  have hconst := eLpNorm_const
    ((4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹ * (∫ y : Vec3, ‖G y‖))
    (by positivity : ENNReal.ofReal (3 / 2 : ℝ) ≠ 0) hμne
  have hC : 0 ≤ (4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹ := by positivity
  have hGintnorm : ENNReal.ofReal (∫ y : Vec3, ‖G y‖) =
      eLpNorm G 1 volume := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hGint,
      (eLpNorm_one_eq_lintegral_enorm hGmeas.aestronglyMeasurable).symm]
  have hfarLp' : eLpNorm (scalarConvolution G kFar) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
      ENNReal.ofReal ((4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹) *
        volume (ball (0 : Vec3) ρ) ^ (2 / 3 : ℝ) *
        volume (closedBall (0 : Vec3) R) ^ (1 / 6 : ℝ) *
        eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    calc
      _ ≤ eLpNorm (fun _ : Vec3 =>
          (4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹ * (∫ y : Vec3, ‖G y‖))
          (ENNReal.ofReal (3 / 2 : ℝ)) μ := hfarLp
      _ = ‖(4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹ * (∫ y : Vec3, ‖G y‖)‖ₑ *
          μ univ ^ (1 / (ENNReal.ofReal (3 / 2 : ℝ)).toReal) := hconst
      _ ≤ ENNReal.ofReal ((4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹) *
          volume (ball (0 : Vec3) ρ) ^ (2 / 3 : ℝ) *
          volume (closedBall (0 : Vec3) R) ^ (1 / 6 : ℝ) *
          eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
        rw [Measure.restrict_apply_univ,
          Real.enorm_eq_ofReal (mul_nonneg hC (integral_nonneg (fun _ => norm_nonneg _))),
          ENNReal.ofReal_mul hC, hGintnorm,
          ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)]
        have hL1 := eLpNorm_one_le_of_memLp_six_fifths_of_support
          hR hGmeas hG hGzero
        have hexp : 1 / (3 / 2 : ℝ) = (2 / 3 : ℝ) := by
          norm_num
        rw [hexp]
        calc
          ENNReal.ofReal ((4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹) *
              eLpNorm G 1 volume * volume (ball (0 : Vec3) ρ) ^ (2 / 3 : ℝ) =
              (ENNReal.ofReal ((4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹) *
                volume (ball (0 : Vec3) ρ) ^ (2 / 3 : ℝ)) * eLpNorm G 1 volume := by
            ac_rfl
          _ ≤ (ENNReal.ofReal ((4 * Real.pi)⁻¹ * (R' ^ 2)⁻¹) *
                volume (ball (0 : Vec3) ρ) ^ (2 / 3 : ℝ)) *
              (volume (closedBall (0 : Vec3) R) ^ (1 / 6 : ℝ) *
                eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume) :=
            mul_le_mul_of_nonneg_left hL1 (by positivity)
          _ = _ := by ac_rfl
  calc
    eLpNorm (newtonianDerivativePotential i G)
        (ENNReal.ofReal (3 / 2 : ℝ)) μ =
        eLpNorm (scalarConvolution G kNear + scalarConvolution G kFar)
          (ENNReal.ofReal (3 / 2 : ℝ)) μ := eLpNorm_congr_ae hdecompAE
    _ ≤ eLpNorm (scalarConvolution G kNear) (ENNReal.ofReal (3 / 2 : ℝ)) μ +
        eLpNorm (scalarConvolution G kFar) (ENNReal.ofReal (3 / 2 : ℝ)) μ :=
      eLpNorm_add_le (by norm_num)
    _ ≤ eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume *
          eLpNorm kNear (ENNReal.ofReal (6 / 5 : ℝ)) volume +
        eLpNorm (scalarConvolution G kFar) (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
      have hnearGlobal :=
        eLpNorm_scalarConvolution_six_fifths_three_halves hGmeas hkNearMeas
      have hnearRestr :
          eLpNorm (scalarConvolution G kNear) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
            eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume *
              eLpNorm kNear (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
        exact
          (eLpNorm_mono_measure (scalarConvolution G kNear) Measure.restrict_le_self).trans
            hnearGlobal
      exact add_le_add_left hnearRestr _
    _ ≤ _ := by
      exact add_le_add_right hfarLp' _

/-- On a ball, compact support lets the potential use the truncated kernel. -/
theorem newtonianDerivativePotential_eLpNorm_three_halves_restrict_ball_le
    {G : Vec3 → ℝ} (i : Fin 3) {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (hGmeas : Measurable G)
    (_ : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    eLpNorm (newtonianDerivativePotential i G)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (ball (0 : Vec3) ρ)) ≤
      eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume *
        eLpNorm (truncatedNewtonianDerivative (R + ρ) i)
          (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  have hRρ : 0 < R + ρ := by linarith only [hR, hρ]
  have hk : MemLp (truncatedNewtonianDerivative (R + ρ) i)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
    truncatedNewtonianDerivative_memLp hRρ i
  have hkm : Measurable (truncatedNewtonianDerivative (R + ρ) i) :=
    measurable_truncatedNewtonianDerivative (R + ρ) i
  have heq : newtonianDerivativePotential i G =ᵐ[
      volume.restrict (ball (0 : Vec3) ρ)]
      scalarConvolution G (truncatedNewtonianDerivative (R + ρ) i) := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
    have hxnorm : ‖x‖ < ρ := mem_ball_zero_iff.mp hx
    rw [newtonianDerivativePotential, scalarConvolution]
    apply integral_congr_ae
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
      simp only [truncatedNewtonianDerivative, hxy, ite_true]
      ring
  calc
    eLpNorm (newtonianDerivativePotential i G)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (ball (0 : Vec3) ρ)) =
        eLpNorm (scalarConvolution G (truncatedNewtonianDerivative (R + ρ) i))
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (ball (0 : Vec3) ρ)) := eLpNorm_congr_ae heq
    _ ≤ eLpNorm (scalarConvolution G (truncatedNewtonianDerivative (R + ρ) i))
          (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume *
        eLpNorm (truncatedNewtonianDerivative (R + ρ) i)
          (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
      eLpNorm_scalarConvolution_six_fifths_three_halves hGmeas hkm

end CKN.Foundation.Euclidean
