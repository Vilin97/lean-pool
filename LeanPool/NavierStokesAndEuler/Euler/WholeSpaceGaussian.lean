/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LeanPool.NavierStokesAndEuler.Euler.LpParameterIntegral
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Function.L2Space

/-!
The normalized Gaussian on ordinary three-dimensional space.  The estimates
below concern the literal Bochner integral, including its L²-to-uniform bound.
The parameterization exp(-|x|²/t) has heat generator one quarter of the Laplacian.
-/

@[expose] public section


noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation Filter
open scoped ContDiff ENNReal RealInnerProductSpace

/-- Normalization, given by `(Real.pi*t)^(-(3:ℝ)/2)`. -/
def normalization (t : ℝ) : ℝ := (Real.pi*t)^(-(3:ℝ)/2)

/-- Kernel, given by `normalization t * Real.exp (-t⁻¹*‖x‖^2)`. -/
def kernel (t : ℝ) (x : Space) : ℝ :=
  normalization t * Real.exp (-t⁻¹*‖x‖^2)

theorem normalization_pos {t : ℝ} (ht : 0 < t) : 0 < normalization t :=
  Real.rpow_pos_of_pos (mul_pos Real.pi_pos ht) _

theorem kernel_pos {t : ℝ} (ht : 0 < t) (x : Space) : 0 < kernel t x :=
  mul_pos (normalization_pos ht) (Real.exp_pos _)

theorem kernel_nonneg {t : ℝ} (ht : 0 < t) (x : Space) : 0 ≤ kernel t x :=
  (kernel_pos ht x).le

theorem kernel_le_normalization {t : ℝ} (ht : 0 < t) (x : Space) :
    kernel t x ≤ normalization t := by
  unfold kernel
  apply mul_le_of_le_one_right (normalization_pos ht).le
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (inv_pos.mpr ht).le) (sq_nonneg ‖x‖))

theorem kernel_smooth (t : ℝ) : ContDiff ℝ ∞ (kernel t) := by
  unfold kernel
  have hn : ContDiff ℝ ∞ (fun x : Space => ‖x‖^2) := contDiff_id.norm_sq ℝ
  exact contDiff_const.mul ((contDiff_const.mul hn).exp)

theorem exp_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Space => Real.exp (-b*‖x‖^2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Space) (b := (b : ℂ)) (by simpa using hb) 0 0).re
  change Integrable (fun x : Space => (Complex.exp
    (-(b : ℂ)*‖x‖^2 + 0*inner ℝ (0 : Space) x)).re) at h
  simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_re] using h

theorem kernel_integrable {t : ℝ} (ht : 0 < t) : Integrable (kernel t) :=
  (exp_integrable (inv_pos.mpr ht)).const_mul _

theorem integral_kernel {t : ℝ} (ht : 0 < t) :
    (∫ x : Space, kernel t x) = 1 := by
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  simp only [kernel]
  rw [integral_const_mul,
    GaussianFourier.integral_rexp_neg_mul_sq_norm (inv_pos.mpr ht), hdim]
  simp only [Nat.cast_ofNat, div_inv_eq_mul]
  unfold normalization
  rw [← Real.rpow_add (mul_pos Real.pi_pos ht)]
  norm_num

theorem kernel_sq_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Space => kernel t x ^ 2) := by
  apply ((kernel_integrable ht).const_mul (normalization t)).mono'
    ((kernel_smooth t).continuous.pow 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  change ‖kernel t x ^ 2‖ ≤ normalization t * kernel t x
  rw [Real.norm_of_nonneg (sq_nonneg _), pow_two]
  exact mul_le_mul_of_nonneg_right (kernel_le_normalization ht x) (kernel_nonneg ht x)

theorem kernel_memLp {t : ℝ} (ht : 0 < t) : MemLp (kernel t) 2 volume :=
  (memLp_two_iff_integrable_sq (kernel_smooth t).continuous.aestronglyMeasurable).2
    (kernel_sq_integrable ht)

theorem integral_kernel_sq_le {t : ℝ} (ht : 0 < t) :
    (∫ x : Space, kernel t x ^ 2) ≤ normalization t := by
  calc
    _ ≤ ∫ x : Space, normalization t * kernel t x :=
      integral_mono (kernel_sq_integrable ht) ((kernel_integrable ht).const_mul _)
        (fun x => by
          rw [pow_two]
          exact mul_le_mul_of_nonneg_right (kernel_le_normalization ht x) (kernel_nonneg ht x))
    _ = normalization t := by rw [integral_const_mul, integral_kernel ht, mul_one]

theorem sqrt_normalization {t : ℝ} (ht : 0 < t) :
    Real.sqrt (normalization t) = (Real.pi*t)^(-(3:ℝ)/4) := by
  rw [Real.sqrt_eq_rpow, normalization, ← Real.rpow_mul (mul_pos Real.pi_pos ht).le]
  norm_num

theorem sqrt_normalization_le {t : ℝ} (ht : 0 < t) :
    Real.sqrt (normalization t) ≤ t^(-(3:ℝ)/4) := by
  rw [sqrt_normalization ht]
  apply Real.rpow_le_rpow_of_nonpos ht
  · nlinarith [Real.pi_pos, Real.two_le_pi]
  · norm_num

section Averaging

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual whole-space Gaussian average, with no periodic identification. -/
def average (t : ℝ) (f : Space → V) (x : Space) : V :=
  ∫ y : Space, kernel t y • f (x+y)

theorem average_integrable_of_bound {t : ℝ} (ht : 0 < t)
    (f : Space → V) (hf : Continuous f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) (x : Space) :
    Integrable (fun y : Space => kernel t y • f (x+y)) := by
  apply ((kernel_integrable ht).mul_const C).mono'
    (((kernel_smooth t).continuous.smul (hf.comp (continuous_const.add
        continuous_id))).aestronglyMeasurable)
  apply Eventually.of_forall
  intro y
  change ‖kernel t y • f (x+y)‖ ≤ kernel t y * C
  rw [norm_smul, Real.norm_of_nonneg (kernel_nonneg ht y)]
  exact mul_le_mul_of_nonneg_left (hb _) (kernel_nonneg ht y)

theorem average_norm_le {t : ℝ} (ht : 0 < t) (f : Space → V)
    (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) (x : Space) : ‖average t f x‖ ≤ C := by
  have h := norm_integral_le_of_norm_le ((kernel_integrable ht).mul_const C)
    (f := fun y : Space => kernel t y • f (x+y)) (Eventually.of_forall (fun y => by
      rw [norm_smul, Real.norm_of_nonneg (kernel_nonneg ht y)]
      exact mul_le_mul_of_nonneg_left (hb _) (kernel_nonneg ht y)))
  simpa only [integral_mul_const, integral_kernel ht, one_mul, average] using h

/-- Cauchy--Schwarz for scalar multiplication, in a form that retains the
ordinary L² norm of a Banach-valued field. -/
theorem norm_integral_smul_le (k : Space → ℝ) (f : Space → V)
    (hk : MemLp k 2 volume) (hf : MemLp f 2 volume) :
    ‖∫ x : Space, k x • f x‖ ≤
      Real.sqrt (∫ x : Space, ‖k x‖^2) * (eLpNorm f 2 volume).toReal := by
  have hp : (2:ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hk' : MemLp (fun x => ‖k x‖) (ENNReal.ofReal (2:ℝ)) volume := by simpa using hk.norm
  have hf' : MemLp (fun x => ‖f x‖) (ENNReal.ofReal (2:ℝ)) volume := by simpa using hf.norm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hp
    (Eventually.of_forall (fun x => norm_nonneg (k x)))
    (Eventually.of_forall (fun x => norm_nonneg (f x))) hk' hf'
  have hnorm : (∫ x : Space, ‖k x‖*‖f x‖) ≤
      Real.sqrt (∫ x : Space, ‖k x‖^2) * Real.sqrt (∫ x : Space, ‖f x‖^2) := by
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using h
  have he : Real.sqrt (∫ x : Space, ‖f x‖^2) = (eLpNorm f 2 volume).toReal := by
    rw [EulerLpParameterIntegral.integral_norm_sq_eq volume f hf,
      Real.sqrt_sq ENNReal.toReal_nonneg]
  rw [he] at hnorm
  exact (norm_integral_le_integral_norm _).trans (by simpa only [norm_smul] using hnorm)

/-- The three-dimensional smoothing power t^(-3/4) is proved from the
normalized Gaussian density and the ordinary whole-space L² norm. -/
theorem average_norm_le_L2 {t : ℝ} (ht : 0 < t) (f : Space → V)
    (hf : MemLp f 2 volume) (x : Space) :
    ‖average t f x‖ ≤ t^(-(3:ℝ)/4) * (eLpNorm f 2 volume).toReal := by
  have hmp := measurePreserving_add_left (volume : Measure Space) x
  have hs : MemLp (fun y : Space => f (x+y)) 2 volume := hf.comp_measurePreserving hmp
  have he : eLpNorm (fun y : Space => f (x+y)) 2 volume = eLpNorm f 2 volume :=
    eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hmp
  have h := norm_integral_smul_le (kernel t) (fun y : Space => f (x+y)) (kernel_memLp ht) hs
  rw [he] at h
  have hk : (∫ y : Space, ‖kernel t y‖^2) ≤ normalization t := by
    simpa only [Real.norm_eq_abs, sq_abs] using integral_kernel_sq_le ht
  exact h.trans (mul_le_mul_of_nonneg_right
    ((Real.sqrt_le_sqrt hk).trans (sqrt_normalization_le ht)) ENNReal.toReal_nonneg)

theorem average_smoothField_norm {t : ℝ} (ht : 0 < t) (A : SmoothL2Field V) (x : Space) :
    ‖average t A.field x‖ ≤ t^(-(3:ℝ)/4) * ‖A.toLp‖ := by
  simpa only [SmoothL2Field.toLp, Lp.norm_toLp] using average_norm_le_L2 ht A.field A.memLp x

end Averaging
end EulerWholeSpaceGaussian
