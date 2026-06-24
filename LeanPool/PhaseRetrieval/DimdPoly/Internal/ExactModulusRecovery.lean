/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Topology.Algebra.Module.Cardinality
import LeanPool.PhaseRetrieval.DimdPoly.Internal.TensorBasis

/-! # ExactModulusRecovery -/


noncomputable section

namespace DimdPolyLEAN

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology

/-!
# ExactModulusRecovery

WIP scaffold for the STFT/ambiguity bridge, exposing the finite-facing
corollary needed by downstream modules.
-/

/-!
## WIP phase-space API stubs

These declarations freeze the proof-facing objects from the exact-modulus
  The definitions are only placeholders; the theorem statements below
are the real work items needed to replace
`coeff_kernel_of_exact_modulus_recovery_skappa_ae_wip`.
-/

private lemma sqrtTwoC_sq : ((Real.sqrt 2 : ℂ) ^ 2) = 2 := by
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt]

private lemma sqrtTwoC_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))

private lemma sqrtTwoC_inv : (Real.sqrt 2 : ℂ)⁻¹ = (Real.sqrt 2 : ℂ) / 2 := by
  field_simp [sqrtTwoC_ne]
  rw [sqrtTwoC_sq]

private lemma piPow_quarter_sq_mul_half :
    ((↑(Real.pi ^ (-1 / 4 : ℝ)) : ℂ) ^ 2 * ((↑Real.pi : ℂ) ^ (1 / 2 : ℂ))) = 1 := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (le_of_lt Real.pi_pos) (1 / 2 : ℝ)]
  have hpi_real :
      (Real.pi ^ (-1 / 4 : ℝ)) ^ 2 * Real.pi ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt Real.pi_pos),
      ← Real.rpow_add Real.pi_pos]
    norm_num
  exact_mod_cast hpi_real

private lemma piPowQuarterC_sq :
    (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) ^ 2) =
      ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [sq, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.rpow_add Real.pi_pos]
  norm_num

private lemma cexp_neg_half_sq_sq (t : ℝ) :
    Complex.exp (-((t : ℂ) ^ 2 / 2)) * Complex.exp (-((t : ℂ) ^ 2 / 2)) =
      ((Real.exp (-(t ^ (2 : ℕ))) : ℝ) : ℂ) := by
  rw [← Complex.exp_add, show -((t : ℂ) ^ 2 / 2) + -((t : ℂ) ^ 2 / 2) =
    ((-(t ^ (2 : ℕ)) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_exp]

private lemma star_sub_div_sqrtTwo (x ω : ℝ) :
    star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
        (Real.sqrt 2 : ℂ)) =
      ((x : ℂ) + (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
        (Real.sqrt 2 : ℂ) := by
  change conj
      (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
        (Real.sqrt 2 : ℂ)) = _
  simp only [map_div₀, map_sub, map_mul, map_ofNat, Complex.conj_ofReal]
  rw [Complex.conj_I]
  ring_nf

/-- `realHermiteGenerating`: real Hermite Generating. -/
noncomputable def realHermiteGenerating (t : ℝ) (u : ℂ) : ℂ :=
  ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
    Complex.exp
      (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) * (t : ℂ) * u - u ^ 2 / 2)

theorem realHermiteGenerating_conj (t : ℝ) (u : ℂ) :
    star (realHermiteGenerating t u) = realHermiteGenerating t (star u) := by
  unfold realHermiteGenerating
  rw [star_mul]
  have hpi : star (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) =
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) := by
    change conj (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) = _
    rw [Complex.conj_ofReal]
  rw [hpi, mul_comm]
  congr 1
  change (starRingEnd ℂ)
      (Complex.exp (-(↑t ^ 2 / 2) + ↑√2 * ↑t * u - u ^ 2 / 2)) =
    Complex.exp (-(↑t ^ 2 / 2) + ↑√2 * ↑t * star u - star u ^ 2 / 2)
  rw [← Complex.exp_conj]
  congr 1
  have htwo : (starRingEnd ℂ) 2 = (2 : ℂ) := Complex.conj_ofReal 2
  simp only [map_sub, map_add, map_neg, map_div₀, map_pow, Complex.conj_ofReal,
    map_mul, RCLike.star_def]
  rw [htwo]

theorem realHermiteGenerating_hasDerivAt (t : ℝ) (u : ℂ) :
    HasDerivAt (realHermiteGenerating t)
      (((Real.sqrt 2 : ℂ) * (t : ℂ) - u) * realHermiteGenerating t u) u := by
  have hpoly :
      HasDerivAt
        (fun v : ℂ =>
          -(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) * (t : ℂ) * v - v ^ 2 / 2)
        ((Real.sqrt 2 : ℂ) * (t : ℂ) - u) u := by
    have hlin :
        HasDerivAt (fun v : ℂ => (Real.sqrt 2 : ℂ) * (t : ℂ) * v)
          ((Real.sqrt 2 : ℂ) * (t : ℂ)) u := by
      simpa using HasDerivAt.const_mul
        ((Real.sqrt 2 : ℂ) * (t : ℂ)) (hasDerivAt_id u)
    have hquad : HasDerivAt (fun v : ℂ => v ^ 2 / 2) u u := by
      simpa [id, two_mul] using
        HasDerivAt.div_const ((hasDerivAt_id u).fun_pow 2) 2
    convert ((hlin.add_const (-(((t : ℂ) ^ 2) / 2))).sub hquad) using 1 <;>
      first
      | rfl
      | (funext v; simp only [Pi.sub_apply]; ring_nf)
  unfold realHermiteGenerating
  convert HasDerivAt.const_mul
    (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) hpoly.cexp using 1 <;>
      first
      | rfl
      | ring

theorem realHermiteGenerating_integral_mul (u w : ℂ) :
    (∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) =
      Complex.exp (u * w) := by
  unfold realHermiteGenerating
  let a : ℂ := ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)
  let b : ℂ := (Real.sqrt 2 : ℂ) * (u + w)
  let c : ℂ := -(u ^ 2 + w ^ 2) / 2
  change (∫ t : ℝ,
      a * Complex.exp (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) *
          (t : ℂ) * u - u ^ 2 / 2) *
        (a * Complex.exp (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) *
          (t : ℂ) * w - w ^ 2 / 2))) =
      Complex.exp (u * w)
  have hquad : ∀ t : ℝ,
      a * Complex.exp (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) *
          (t : ℂ) * u - u ^ 2 / 2) *
        (a * Complex.exp (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) *
          (t : ℂ) * w - w ^ 2 / 2)) =
      (a * a) * Complex.exp (-(1 : ℂ) * (t : ℂ) ^ 2 + b * (t : ℂ) + c) := by
    intro t
    have hsum :
        (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) * (t : ℂ) * u - u ^ 2 / 2) +
            (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) * (t : ℂ) * w -
              w ^ 2 / 2) =
          -(1 : ℂ) * (t : ℂ) ^ 2 + b * (t : ℂ) + c := by
      simp only [b, c]
      ring_nf
    rw [← hsum, Complex.exp_add]
    ring
  simp_rw [hquad]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_cexp_quadratic]
  · simp only [a, b, c]
    ring_nf
    rw [sqrtTwoC_sq]
    ring_nf
    rw [piPow_quarter_sq_mul_half]
    ring_nf
  · simp

theorem realHermiteGenerating_integral_mul_conj (u w : ℂ) :
    (∫ t : ℝ, realHermiteGenerating t u * star (realHermiteGenerating t w)) =
      Complex.exp (u * star w) := by
  simp_rw [realHermiteGenerating_conj]
  exact realHermiteGenerating_integral_mul u (star w)

theorem realHermiteGenerating_stft_integral_raw
    (x ω : ℝ) (u v : ℂ) :
    (∫ t : ℝ,
      realHermiteGenerating t u * realHermiteGenerating (t - x) v *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        (-((x : ℂ) ^ 2) / 2 - (Real.sqrt 2 : ℂ) * (x : ℂ) * v -
          (u ^ 2 + v ^ 2) / 2 +
          (((x : ℂ) + (Real.sqrt 2 : ℂ) * (u + v) -
              (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) ^ 2) / 4) := by
  unfold realHermiteGenerating
  let a : ℂ := ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)
  let b : ℂ :=
    (x : ℂ) + (Real.sqrt 2 : ℂ) * (u + v) -
      (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)
  let c : ℂ :=
    -((x : ℂ) ^ 2) / 2 - (Real.sqrt 2 : ℂ) * (x : ℂ) * v -
      (u ^ 2 + v ^ 2) / 2
  change (∫ t : ℝ,
      a * Complex.exp
          (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) * (t : ℂ) * u -
            u ^ 2 / 2) *
        (a * Complex.exp
          (-((((t - x : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t - x : ℝ) : ℂ) * v - v ^ 2 / 2)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        (-((x : ℂ) ^ 2) / 2 - (Real.sqrt 2 : ℂ) * (x : ℂ) * v -
          (u ^ 2 + v ^ 2) / 2 +
          (((x : ℂ) + (Real.sqrt 2 : ℂ) * (u + v) -
              (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) ^ 2) / 4)
  have hquad : ∀ t : ℝ,
      a * Complex.exp
          (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) * (t : ℂ) * u -
            u ^ 2 / 2) *
        (a * Complex.exp
          (-((((t - x : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t - x : ℝ) : ℂ) * v - v ^ 2 / 2)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) =
      (a * a) * Complex.exp (-(1 : ℂ) * (t : ℂ) ^ 2 + b * (t : ℂ) + c) := by
    intro t
    have htx : (((t - x : ℝ) : ℂ)) = (t : ℂ) - (x : ℂ) := by norm_num
    have hsum :
        (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) * (t : ℂ) * u -
            u ^ 2 / 2) +
          (-((((t - x : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t - x : ℝ) : ℂ) * v - v ^ 2 / 2) +
          (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) =
        -(1 : ℂ) * (t : ℂ) ^ 2 + b * (t : ℂ) + c := by
      simp only [b, c]
      rw [htx]
      ring_nf
    rw [← hsum, Complex.exp_add, Complex.exp_add]
    ring
  simp_rw [hquad]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_cexp_quadratic]
  · simp only [a, b, c]
    ring_nf
    rw [piPow_quarter_sq_mul_half]
    ring_nf
  · simp

theorem realHermiteGenerating_integral_shift_mul_modulated_completed
    (u v : ℂ) (x ω : ℝ) :
    (∫ t : ℝ,
      realHermiteGenerating t u * realHermiteGenerating (t - x) v *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        ((-((x : ℂ) ^ 2) / 2 - (Real.sqrt 2 : ℂ) * (x : ℂ) * v -
            (u ^ 2 + v ^ 2) / 2) +
          (((x : ℂ) + (Real.sqrt 2 : ℂ) * (u + v) -
              (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) ^ 2) / 4) :=
  realHermiteGenerating_stft_integral_raw x ω u v

theorem realHermiteGenerating_integral_shift_mul_modulated
    (u v : ℂ) (x ω : ℝ) :
    (∫ t : ℝ,
      realHermiteGenerating t u * realHermiteGenerating (t - x) v *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        ((-((x : ℂ) ^ 2) / 2 - (Real.sqrt 2 : ℂ) * (x : ℂ) * v -
            (u ^ 2 + v ^ 2) / 2) -
          (((x : ℂ) + (Real.sqrt 2 : ℂ) * (u + v) -
              (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) ^ 2) /
            (4 * (-(1 : ℂ)))) := by
  rw [realHermiteGenerating_integral_shift_mul_modulated_completed]
  congr 1
  ring

theorem realHermiteGenerating_stft_integral_kernel
    (x ω : ℝ) (u v : ℂ) :
    (∫ t : ℝ,
      realHermiteGenerating t u * realHermiteGenerating (t - x) v *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp (-(Real.pi : ℂ) * Complex.I * ((x : ℂ) * (ω : ℂ))) *
        Complex.exp
          (u * v +
            (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                (Real.sqrt 2 : ℂ)) * u -
              star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                (Real.sqrt 2 : ℂ)) * v) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  rw [realHermiteGenerating_stft_integral_raw, Complex.ofReal_exp,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [star_sub_div_sqrtTwo]
  ring_nf
  rw [sqrtTwoC_inv, Complex.I_sq]
  norm_num [← Complex.ofReal_pow]
  ring

theorem realHermiteGenerating_ambiguity_integral_raw
    (x ω : ℝ) (u v : ℂ) :
    (∫ t : ℝ,
      realHermiteGenerating (t + x / 2) u *
        realHermiteGenerating (t - x / 2) v *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        (-((x : ℂ) ^ 2) / 4 +
          (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
          (Real.sqrt 2 : ℂ) * (x : ℂ) * v / 2 -
          (u ^ 2 + v ^ 2) / 2 +
          (((Real.sqrt 2 : ℂ) * (u + v) -
              (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) ^ 2) / 4) := by
  unfold realHermiteGenerating
  let a : ℂ := ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)
  let b : ℂ :=
    (Real.sqrt 2 : ℂ) * (u + v) -
      (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)
  let c : ℂ :=
    -((x : ℂ) ^ 2) / 4 +
      (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
      (Real.sqrt 2 : ℂ) * (x : ℂ) * v / 2 -
      (u ^ 2 + v ^ 2) / 2
  change (∫ t : ℝ,
      a * Complex.exp
          (-((((t + x / 2 : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t + x / 2 : ℝ) : ℂ) * u -
            u ^ 2 / 2) *
        (a * Complex.exp
          (-((((t - x / 2 : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t - x / 2 : ℝ) : ℂ) * v -
            v ^ 2 / 2)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        (-((x : ℂ) ^ 2) / 4 +
          (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
          (Real.sqrt 2 : ℂ) * (x : ℂ) * v / 2 -
          (u ^ 2 + v ^ 2) / 2 +
          (((Real.sqrt 2 : ℂ) * (u + v) -
              (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) ^ 2) / 4)
  have hquad : ∀ t : ℝ,
      a * Complex.exp
          (-((((t + x / 2 : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t + x / 2 : ℝ) : ℂ) * u -
            u ^ 2 / 2) *
        (a * Complex.exp
          (-((((t - x / 2 : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t - x / 2 : ℝ) : ℂ) * v -
            v ^ 2 / 2)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) =
      (a * a) * Complex.exp (-(1 : ℂ) * (t : ℂ) ^ 2 + b * (t : ℂ) + c) := by
    intro t
    have hplus : (((t + x / 2 : ℝ) : ℂ)) = (t : ℂ) + (x : ℂ) / 2 := by norm_num
    have hminus : (((t - x / 2 : ℝ) : ℂ)) = (t : ℂ) - (x : ℂ) / 2 := by norm_num
    have hsum :
        (-((((t + x / 2 : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t + x / 2 : ℝ) : ℂ) * u -
            u ^ 2 / 2) +
          (-((((t - x / 2 : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t - x / 2 : ℝ) : ℂ) * v -
            v ^ 2 / 2) +
          (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) =
        -(1 : ℂ) * (t : ℂ) ^ 2 + b * (t : ℂ) + c := by
      simp only [b, c]
      rw [hplus, hminus]
      ring_nf
    rw [← hsum]
    calc
      a * Complex.exp
          (-((((t + x / 2 : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t + x / 2 : ℝ) : ℂ) * u -
            u ^ 2 / 2) *
        (a * Complex.exp
          (-((((t - x / 2 : ℝ) : ℂ) ^ 2) / 2) +
            (Real.sqrt 2 : ℂ) * ((t - x / 2 : ℝ) : ℂ) * v -
            v ^ 2 / 2)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) =
          (a * a) *
            (Complex.exp
              (-((((t + x / 2 : ℝ) : ℂ) ^ 2) / 2) +
                (Real.sqrt 2 : ℂ) * ((t + x / 2 : ℝ) : ℂ) * u -
                u ^ 2 / 2) *
              Complex.exp
                (-((((t - x / 2 : ℝ) : ℂ) ^ 2) / 2) +
                  (Real.sqrt 2 : ℂ) * ((t - x / 2 : ℝ) : ℂ) * v -
                  v ^ 2 / 2) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) := by ring
      _ = (a * a) *
            Complex.exp
              ((-((((t + x / 2 : ℝ) : ℂ) ^ 2) / 2) +
                  (Real.sqrt 2 : ℂ) * ((t + x / 2 : ℝ) : ℂ) * u -
                  u ^ 2 / 2) +
                (-((((t - x / 2 : ℝ) : ℂ) ^ 2) / 2) +
                  (Real.sqrt 2 : ℂ) * ((t - x / 2 : ℝ) : ℂ) * v -
                  v ^ 2 / 2) +
                (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) := by
            rw [← Complex.exp_add, ← Complex.exp_add]
  simp_rw [hquad]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_cexp_quadratic]
  · simp only [a, b, c]
    ring_nf
    rw [piPow_quarter_sq_mul_half]
    ring_nf
  · simp

theorem realHermiteGenerating_ambiguity_integral_linear_form
    (x ω : ℝ) (u v : ℂ) :
    (∫ t : ℝ,
      realHermiteGenerating (t + x / 2) u *
        realHermiteGenerating (t - x / 2) v *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        (-(((x : ℂ) ^ 2 + (2 * Real.pi : ℂ) ^ 2 * (ω : ℂ) ^ 2) / 4)) *
        Complex.exp
          (((Real.sqrt 2 : ℂ) * (x : ℂ) / 2 -
              (Real.sqrt 2 : ℂ) * (Real.pi : ℂ) * Complex.I * (ω : ℂ)) * u -
            ((Real.sqrt 2 : ℂ) * (x : ℂ) / 2 +
              (Real.sqrt 2 : ℂ) * (Real.pi : ℂ) * Complex.I * (ω : ℂ)) * v +
            u * v) := by
  rw [realHermiteGenerating_ambiguity_integral_raw, ← Complex.exp_add]
  congr 1
  ring_nf
  rw [sqrtTwoC_sq, Complex.I_sq]
  ring

theorem realHermiteGenerating_ambiguity_integral_kernel
    (x ω : ℝ) (u w : ℂ) :
    (∫ t : ℝ,
      realHermiteGenerating (t + x / 2) u *
        realHermiteGenerating (t - x / 2) w *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        (u * w +
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) * u -
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) * w) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  rw [realHermiteGenerating_ambiguity_integral_linear_form, Complex.ofReal_exp,
    ← Complex.exp_add, star_sub_div_sqrtTwo]
  ring_nf
  rw [sqrtTwoC_inv]
  ring_nf
  rw [← Complex.exp_add]
  congr 1
  rw [show
      (((x ^ 2 * (-1 / 4) - Real.pi ^ 2 * ω ^ 2) : ℝ) : ℂ) =
        (x : ℂ) ^ 2 * (-1 / 4) - (Real.pi : ℂ) ^ 2 * (ω : ℂ) ^ 2 by
    norm_num [← Complex.ofReal_pow]]
  ring_nf

theorem realHermiteGenerating_ambiguity_integral_conj_raw
    (x ω : ℝ) (u v : ℂ) :
    (∫ t : ℝ,
      realHermiteGenerating (t + x / 2) u *
        star (realHermiteGenerating (t - x / 2) v) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        (-((x : ℂ) ^ 2) / 4 +
          (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
          (Real.sqrt 2 : ℂ) * (x : ℂ) * star v / 2 -
          (u ^ 2 + (star v) ^ 2) / 2 +
          (((Real.sqrt 2 : ℂ) * (u + star v) -
              (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) ^ 2) / 4) := by
  simp_rw [realHermiteGenerating_conj]
  simpa using realHermiteGenerating_ambiguity_integral_raw x ω u (star v)

theorem realHermiteGenerating_ambiguity_integral_conj_kernel
    (x ω : ℝ) (u v : ℂ) :
    (∫ t : ℝ,
      realHermiteGenerating (t + x / 2) u *
        star (realHermiteGenerating (t - x / 2) v) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        (u * star v +
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) * u -
          (((x : ℂ) + (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) * star v) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  rw [realHermiteGenerating_ambiguity_integral_conj_raw, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  ring_nf
  rw [sqrtTwoC_inv]
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) by rw [pow_two, Complex.I_mul_I]]
  rw [sqrtTwoC_sq]
  rw [show
      (((x ^ 2 * (-1 / 4) - Real.pi ^ 2 * ω ^ 2) : ℝ) : ℂ) =
        (x : ℂ) ^ 2 * (-1 / 4) - (Real.pi : ℂ) ^ 2 * (ω : ℂ) ^ 2 by
    norm_num [← Complex.ofReal_pow]]
  ring_nf

theorem realHermiteGenerating_ambiguity_integral_independent_kernel
    (x ω : ℝ) (u w : ℂ) :
    (∫ t : ℝ,
      realHermiteGenerating (t + x / 2) u *
        realHermiteGenerating (t - x / 2) w *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (ω * t : ℂ))) =
      Complex.exp
        (u * w +
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) * u -
            star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) * w) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  simpa using realHermiteGenerating_ambiguity_integral_kernel x ω u w

private lemma realHermiteGenerating_norm_le_of_norm_le
    (t : ℝ) (u : ℂ) {K : ℝ} (huK : ‖u‖ ≤ K) :
    ‖realHermiteGenerating t u‖ ≤
      Real.pi ^ (-(1 / 4 : ℝ)) *
        Real.exp (-(t ^ 2) / 2 + Real.sqrt 2 * |t| * K + K ^ 2 / 2) := by
  have hK_nonneg : 0 ≤ K := (norm_nonneg u).trans huK
  have hlin :
      (((Real.sqrt 2 : ℂ) * (t : ℂ) * u).re) ≤ Real.sqrt 2 * |t| * K := by
    have hcoef_nonneg : 0 ≤ Real.sqrt 2 * |t| :=
      mul_nonneg (Real.sqrt_nonneg 2) (abs_nonneg t)
    calc
      (((Real.sqrt 2 : ℂ) * (t : ℂ) * u).re) ≤
          |(((Real.sqrt 2 : ℂ) * (t : ℂ) * u).re)| := le_abs_self _
      _ ≤ ‖(Real.sqrt 2 : ℂ) * (t : ℂ) * u‖ := Complex.abs_re_le_norm _
      _ = Real.sqrt 2 * |t| * ‖u‖ := by simp [abs_of_nonneg (Real.sqrt_nonneg 2)]
      _ ≤ Real.sqrt 2 * |t| * K := mul_le_mul_of_nonneg_left huK hcoef_nonneg
  have hquad : (-(u ^ 2 / 2)).re ≤ K ^ 2 / 2 := by
    have hsq : ‖u‖ ^ 2 ≤ K ^ 2 := by nlinarith [norm_nonneg u, hK_nonneg, huK]
    calc
      (-(u ^ 2 / 2)).re ≤ |(-(u ^ 2 / 2)).re| := le_abs_self _
      _ ≤ ‖-(u ^ 2 / 2)‖ := Complex.abs_re_le_norm _
      _ = ‖u‖ ^ 2 / 2 := by simp [norm_pow]
      _ ≤ K ^ 2 / 2 := by nlinarith
  have hre :
      (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) * (t : ℂ) * u - u ^ 2 / 2).re
        ≤ -(t ^ 2) / 2 + Real.sqrt 2 * |t| * K + K ^ 2 / 2 := by
    have ht : (-( ((t : ℂ) ^ 2) / 2)).re = -(t ^ 2) / 2 := by
      norm_num [Complex.div_re]
      rw [pow_two]
      simp [Complex.mul_re]
      ring
    have hquad_re : -(u ^ 2 / 2).re ≤ K ^ 2 / 2 := by simpa using hquad
    simp only [Complex.add_re, Complex.sub_re]
    rw [ht]
    nlinarith [hlin, hquad_re]
  unfold realHermiteGenerating
  rw [norm_mul, Complex.norm_exp]
  have hpi_nonneg : 0 ≤ Real.pi ^ (-(1 / 4 : ℝ)) :=
    (Real.rpow_pos_of_pos Real.pi_pos _).le
  rw [show ‖((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)‖ =
      Real.pi ^ (-(1 / 4 : ℝ)) by
    simpa using abs_of_nonneg hpi_nonneg]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hre) hpi_nonneg

/-- `shiftedGeneratingRightDerivBoundConstant`: shifted Generating Right Deriv Bound Constant. -/
noncomputable def shiftedGeneratingRightDerivBoundConstant
    (u w0 : ℂ) (x R : ℝ) : ℝ :=
  Real.pi ^ (-(1 / 2 : ℝ)) *
    Real.exp
      (((Real.sqrt 2 * (‖u‖ + (‖w0‖ + R))) ^ 2) / 2 +
        (Real.sqrt 2 * (|x| / 2) * (‖u‖ + (‖w0‖ + R)) +
          ((‖u‖ ^ 2 + (‖w0‖ + R) ^ 2) / 2)))

/-- `shiftedGeneratingRightDerivBound`: shifted Generating Right Deriv Bound. -/
noncomputable def shiftedGeneratingRightDerivBound
    (u w0 : ℂ) (x R : ℝ) (t : ℝ) : ℝ :=
  shiftedGeneratingRightDerivBoundConstant u w0 x R *
    (1 + (Real.sqrt 2 * |t| +
      (Real.sqrt 2 * (|x| / 2) + (‖w0‖ + R)))) *
    Real.exp (-(t ^ 2) / 2)

private lemma integrable_abs_mul_exp_neg_half_sq_wip25 :
    Integrable (fun t : ℝ => |t| * Real.exp (-(t ^ 2) / 2)) volume := by
  have hlin :
      Integrable (fun t : ℝ => t ^ (1 : ℝ) *
        Real.exp (-(1 / 2 : ℝ) * t ^ 2)) volume := by
    simpa using integrable_rpow_mul_exp_neg_mul_sq
      (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num : (-1 : ℝ) < 1)
  refine hlin.abs.congr ?_
  filter_upwards with t
  rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _),
    show t ^ (1 : ℝ) = t by simp,
    show (-(1 / 2 : ℝ) * t ^ 2) = -(t ^ 2) / 2 by ring]

private lemma integrable_abs_sq_mul_exp_neg_half_sq_wip25 :
    Integrable (fun t : ℝ => |t| ^ (2 : ℕ) * Real.exp (-(t ^ 2) / 2)) volume := by
  have hsq :
      Integrable (fun t : ℝ => t ^ (2 : ℝ) *
        Real.exp (-(1 / 2 : ℝ) * t ^ 2)) volume := by
    simpa using integrable_rpow_mul_exp_neg_mul_sq
      (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num : (-1 : ℝ) < 2)
  refine hsq.congr ?_
  filter_upwards with t
  have hpow : t ^ (2 : ℝ) = |t| ^ (2 : ℕ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact (sq_abs t).symm
  rw [hpow]
  congr 1
  ring_nf

private theorem shiftedGeneratingRightDerivBound_integrable
    (u w0 : ℂ) (x R : ℝ) :
    Integrable (shiftedGeneratingRightDerivBound u w0 x R) (volume : Measure ℝ) := by
  let K : ℝ := ‖w0‖ + R
  let B : ℝ := Real.sqrt 2 * (|x| / 2) + K
  let C : ℝ := shiftedGeneratingRightDerivBoundConstant u w0 x R
  have hgauss0 := integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
  have hgauss : Integrable (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) volume := by
    refine hgauss0.congr ?_
    filter_upwards with t
    congr 1
    ring
  have hsum : Integrable (fun t : ℝ =>
      Real.sqrt 2 * (|t| * Real.exp (-(t ^ 2) / 2)) +
        (1 + B) * Real.exp (-(t ^ 2) / 2)) volume :=
    (integrable_abs_mul_exp_neg_half_sq_wip25.const_mul (Real.sqrt 2)).add
      (hgauss.const_mul (1 + B))
  exact (hsum.const_mul C).congr (by
    filter_upwards with t
    simp only [shiftedGeneratingRightDerivBound, C, B, K]
    ring)

private noncomputable def shiftedGeneratingLeftRightDerivBound
    (x : ℝ) (t : ℝ) : ℝ :=
  (Real.sqrt 2 * |t| + Real.sqrt 2 * (|x| / 2)) *
    shiftedGeneratingRightDerivBound 0 0 (-x) 1 t

private theorem shiftedGeneratingLeftRightDerivBound_integrable
    (x : ℝ) :
    Integrable (shiftedGeneratingLeftRightDerivBound x) (volume : Measure ℝ) := by
  let A : ℝ := Real.sqrt 2
  let B : ℝ := Real.sqrt 2 * (|x| / 2)
  let D : ℝ := Real.sqrt 2 * (|x| / 2) + 1
  let C : ℝ := shiftedGeneratingRightDerivBoundConstant 0 0 (-x) 1
  have hgauss0 := integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
  have hgauss : Integrable (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) volume := by
    refine hgauss0.congr ?_
    filter_upwards with t
    congr 1
    ring
  have hsum : Integrable (fun t : ℝ =>
      (A * A) * (|t| ^ (2 : ℕ) * Real.exp (-(t ^ 2) / 2)) +
        (A * (1 + D) + B * A) * (|t| * Real.exp (-(t ^ 2) / 2)) +
          (B * (1 + D)) * Real.exp (-(t ^ 2) / 2)) :=
    ((integrable_abs_sq_mul_exp_neg_half_sq_wip25.const_mul (A * A)).add
      (integrable_abs_mul_exp_neg_half_sq_wip25.const_mul (A * (1 + D) + B * A))).add
        (hgauss.const_mul (B * (1 + D)))
  exact (hsum.const_mul C).congr (by
    filter_upwards with t
    simp only [shiftedGeneratingLeftRightDerivBound, shiftedGeneratingRightDerivBound,
      C, A, B, D, norm_zero, zero_add, abs_neg]
    ring)

private lemma norm_le_of_mem_ball_complex
    {u0 z : ℂ} {R : ℝ} (hz : z ∈ Metric.ball u0 R) :
    ‖z‖ ≤ ‖u0‖ + R := by
  have hdist : ‖z - u0‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  calc
    ‖z‖ = ‖u0 + (z - u0)‖ := by ring_nf
    _ ≤ ‖u0‖ + ‖z - u0‖ := norm_add_le _ _
    _ ≤ ‖u0‖ + R := by linarith

private lemma abs_add_half_mul_le (t x : ℝ) :
    |t + (1 / 2 : ℝ) * x| ≤ |t| + |x| / 2 := by
  calc
    |t + (1 / 2 : ℝ) * x| ≤ |t| + |(1 / 2 : ℝ) * x| := abs_add_le _ _
    _ = |t| + |x| / 2 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring

private lemma abs_sub_half_mul_le (t x : ℝ) :
    |t - (1 / 2 : ℝ) * x| ≤ |t| + |x| / 2 := by
  calc
    |t - (1 / 2 : ℝ) * x| = |t + -((1 / 2 : ℝ) * x)| := by ring_nf
    _ ≤ |t| + |-((1 / 2 : ℝ) * x)| := abs_add_le _ _
    _ = |t| + |x| / 2 := by
      rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring

private lemma shifted_deriv_factor_norm_le
    (t x : ℝ) {z : ℂ} {K : ℝ} (hzK : ‖z‖ ≤ K) :
    ‖(Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - z‖ ≤
      Real.sqrt 2 * |t| + (Real.sqrt 2 * (|x| / 2) + K) := by
  have hshift := abs_sub_half_mul_le t x
  calc
    ‖(Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - z‖ ≤
        ‖(Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ)‖ + ‖z‖ :=
      norm_sub_le _ _
    _ = ‖((Real.sqrt 2 * (t - (1 / 2 : ℝ) * x) : ℝ) : ℂ)‖ + ‖z‖ := by
      congr 1
      rw [Complex.ofReal_mul]
    _ = |Real.sqrt 2 * (t - (1 / 2 : ℝ) * x)| + ‖z‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    _ = Real.sqrt 2 * |t - (1 / 2 : ℝ) * x| + ‖z‖ := by
      simp [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
    _ ≤ Real.sqrt 2 * (|t| + |x| / 2) + K := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      nlinarith [mul_le_mul_of_nonneg_left hshift hsqrt_nonneg, hzK]
    _ = Real.sqrt 2 * |t| + (Real.sqrt 2 * (|x| / 2) + K) := by ring

private lemma norm_modulation_phase (ω t : ℝ) :
    ‖Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
        ((inner ℝ ω t : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre :
      (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ)).re = 0 := by simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

private lemma shifted_generating_exponent_bound
    {uK zK : ℝ} (huK : 0 ≤ uK) (hzK : 0 ≤ zK) (x t : ℝ) :
    -((t + (1 / 2 : ℝ) * x) ^ 2) / 2 +
          Real.sqrt 2 * |t + (1 / 2 : ℝ) * x| * uK + uK ^ 2 / 2 +
        (-((t - (1 / 2 : ℝ) * x) ^ 2) / 2 +
          Real.sqrt 2 * |t - (1 / 2 : ℝ) * x| * zK + zK ^ 2 / 2) ≤
      -(t ^ 2) +
        Real.sqrt 2 * |t| * (uK + zK) +
        (Real.sqrt 2 * (|x| / 2) * (uK + zK) + (uK ^ 2 + zK ^ 2) / 2) := by
  have hplus := abs_add_half_mul_le t x
  have hminus := abs_sub_half_mul_le t x
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hquad :
      -((t + (1 / 2 : ℝ) * x) ^ 2) / 2 -
          ((t - (1 / 2 : ℝ) * x) ^ 2) / 2 ≤ -(t ^ 2) := by
    have hsumsq :
        (t + (1 / 2 : ℝ) * x) ^ 2 + (t - (1 / 2 : ℝ) * x) ^ 2 =
          2 * t ^ 2 + x ^ 2 / 2 := by ring
    nlinarith [sq_nonneg x]
  have hlin_plus :
      Real.sqrt 2 * |t + (1 / 2 : ℝ) * x| * uK ≤
        Real.sqrt 2 * (|t| + |x| / 2) * uK := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hplus hsqrt_nonneg) huK
  have hlin_minus :
      Real.sqrt 2 * |t - (1 / 2 : ℝ) * x| * zK ≤
        Real.sqrt 2 * (|t| + |x| / 2) * zK := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hminus hsqrt_nonneg) hzK
  nlinarith [hquad, hlin_plus, hlin_minus]

private theorem shifted_generating_mul_modulated_bound_of_mem_ball
    (u w0 : ℂ) (x ω : ℝ) {R : ℝ} (hR : 0 < R) (t : ℝ) {z : ℂ}
    (hz : z ∈ Metric.ball w0 R) :
    ‖(realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
          realHermiteGenerating (t - (1 / 2 : ℝ) * x) z) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ ω t : ℝ) : ℂ))‖ ≤
      shiftedGeneratingRightDerivBound u w0 x R t := by
  let U : ℝ := ‖u‖
  let K : ℝ := ‖w0‖ + R
  let A : ℝ := Real.sqrt 2 * (U + K)
  let B : ℝ := Real.sqrt 2 * (|x| / 2) * (U + K) + (U ^ 2 + K ^ 2) / 2
  let L : ℝ := Real.sqrt 2 * |t| + (Real.sqrt 2 * (|x| / 2) + K)
  let C : ℝ := shiftedGeneratingRightDerivBoundConstant u w0 x R
  have hU_nonneg : 0 ≤ U := by simp [U]
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C, shiftedGeneratingRightDerivBoundConstant]
    positivity
  have hzK : ‖z‖ ≤ K := by
    simpa [K] using norm_le_of_mem_ball_complex (u0 := w0) (z := z) (R := R) hz
  have hpi_quarter_nonneg : 0 ≤ Real.pi ^ (-(1 / 4 : ℝ)) :=
    (Real.rpow_pos_of_pos Real.pi_pos _).le
  have hpi_half_nonneg : 0 ≤ Real.pi ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_pos_of_pos Real.pi_pos _).le
  have hleft := realHermiteGenerating_norm_le_of_norm_le
    (t + (1 / 2 : ℝ) * x) u (le_rfl : ‖u‖ ≤ U)
  have hright := realHermiteGenerating_norm_le_of_norm_le
    (t - (1 / 2 : ℝ) * x) z hzK
  have hphase := norm_modulation_phase ω t
  have hnorm₁ :
      ‖(realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
            realHermiteGenerating (t - (1 / 2 : ℝ) * x) z) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))‖ ≤
        (Real.pi ^ (-(1 / 4 : ℝ)) *
            Real.exp
              (-((t + (1 / 2 : ℝ) * x) ^ 2) / 2 +
                Real.sqrt 2 * |t + (1 / 2 : ℝ) * x| * U + U ^ 2 / 2)) *
          (Real.pi ^ (-(1 / 4 : ℝ)) *
            Real.exp
              (-((t - (1 / 2 : ℝ) * x) ^ 2) / 2 +
                Real.sqrt 2 * |t - (1 / 2 : ℝ) * x| * K + K ^ 2 / 2)) := by
    rw [norm_mul, hphase, mul_one, norm_mul]
    exact mul_le_mul hleft hright (norm_nonneg _)
      (mul_nonneg hpi_quarter_nonneg (Real.exp_nonneg _))
  have hcombine :
      (Real.pi ^ (-(1 / 4 : ℝ)) *
            Real.exp
              (-((t + (1 / 2 : ℝ) * x) ^ 2) / 2 +
                Real.sqrt 2 * |t + (1 / 2 : ℝ) * x| * U + U ^ 2 / 2)) *
          (Real.pi ^ (-(1 / 4 : ℝ)) *
            Real.exp
              (-((t - (1 / 2 : ℝ) * x) ^ 2) / 2 +
                Real.sqrt 2 * |t - (1 / 2 : ℝ) * x| * K + K ^ 2 / 2)) ≤
        Real.pi ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(t ^ 2) + A * |t| + B) := by
    have hpi :
        Real.pi ^ (-(1 / 4 : ℝ)) * Real.pi ^ (-(1 / 4 : ℝ)) =
          Real.pi ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add Real.pi_pos]
      norm_num
    have hexponent := shifted_generating_exponent_bound hU_nonneg hK_nonneg x t
    have hexp :
        Real.exp
          ((-((t + (1 / 2 : ℝ) * x) ^ 2) / 2 +
              Real.sqrt 2 * |t + (1 / 2 : ℝ) * x| * U + U ^ 2 / 2) +
            (-((t - (1 / 2 : ℝ) * x) ^ 2) / 2 +
              Real.sqrt 2 * |t - (1 / 2 : ℝ) * x| * K + K ^ 2 / 2)) ≤
          Real.exp (-(t ^ 2) + A * |t| + B) := Real.exp_le_exp.2 (by
        simpa [A, B, mul_assoc, mul_left_comm, mul_comm] using hexponent)
    calc
      (Real.pi ^ (-(1 / 4 : ℝ)) *
            Real.exp
              (-((t + (1 / 2 : ℝ) * x) ^ 2) / 2 +
                Real.sqrt 2 * |t + (1 / 2 : ℝ) * x| * U + U ^ 2 / 2)) *
          (Real.pi ^ (-(1 / 4 : ℝ)) *
            Real.exp
              (-((t - (1 / 2 : ℝ) * x) ^ 2) / 2 +
                Real.sqrt 2 * |t - (1 / 2 : ℝ) * x| * K + K ^ 2 / 2)) =
        (Real.pi ^ (-(1 / 4 : ℝ)) * Real.pi ^ (-(1 / 4 : ℝ))) *
          Real.exp
            ((-((t + (1 / 2 : ℝ) * x) ^ 2) / 2 +
                Real.sqrt 2 * |t + (1 / 2 : ℝ) * x| * U + U ^ 2 / 2) +
              (-((t - (1 / 2 : ℝ) * x) ^ 2) / 2 +
                Real.sqrt 2 * |t - (1 / 2 : ℝ) * x| * K + K ^ 2 / 2)) := by
          rw [Real.exp_add
            (-((t + (1 / 2 : ℝ) * x) ^ 2) / 2 +
              Real.sqrt 2 * |t + (1 / 2 : ℝ) * x| * U + U ^ 2 / 2)
            (-((t - (1 / 2 : ℝ) * x) ^ 2) / 2 +
              Real.sqrt 2 * |t - (1 / 2 : ℝ) * x| * K + K ^ 2 / 2)]
          ring
      _ ≤ Real.pi ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(t ^ 2) + A * |t| + B) := by
          rw [hpi]
          exact mul_le_mul_of_nonneg_left hexp hpi_half_nonneg
  have hcomplete : -(t ^ 2) + A * |t| + B ≤ -(t ^ 2) / 2 + A ^ 2 / 2 + B := by
    have hsquare : 0 ≤ (|t| - A) ^ 2 := sq_nonneg _
    have habs_sq : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith
  have hexp :
      Real.exp (-(t ^ 2) + A * |t| + B) ≤
        Real.exp (A ^ 2 / 2 + B) * Real.exp (-(t ^ 2) / 2) := by
    calc
      Real.exp (-(t ^ 2) + A * |t| + B) ≤
          Real.exp (-(t ^ 2) / 2 + A ^ 2 / 2 + B) := Real.exp_le_exp.2 hcomplete
      _ = Real.exp (A ^ 2 / 2 + B) * Real.exp (-(t ^ 2) / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hcore :
      Real.pi ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2) + A * |t| + B) ≤
        C * Real.exp (-(t ^ 2) / 2) := by
    calc
      Real.pi ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2) + A * |t| + B) ≤
          Real.pi ^ (-(1 / 2 : ℝ)) *
            (Real.exp (A ^ 2 / 2 + B) * Real.exp (-(t ^ 2) / 2)) :=
        mul_le_mul_of_nonneg_left hexp hpi_half_nonneg
      _ = C * Real.exp (-(t ^ 2) / 2) := by
        simp only [C, shiftedGeneratingRightDerivBoundConstant, A, B, U, K]
        ring
  calc
    ‖(realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
          realHermiteGenerating (t - (1 / 2 : ℝ) * x) z) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ ω t : ℝ) : ℂ))‖
        ≤ Real.pi ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(t ^ 2) + A * |t| + B) := hnorm₁.trans hcombine
    _ ≤ C * Real.exp (-(t ^ 2) / 2) := hcore
    _ ≤ shiftedGeneratingRightDerivBound u w0 x R t := by
      have hone_le : (1 : ℝ) ≤ 1 + L := by linarith
      have hCe_nonneg : 0 ≤ C * Real.exp (-(t ^ 2) / 2) :=
        mul_nonneg hC_nonneg (Real.exp_nonneg _)
      calc
        C * Real.exp (-(t ^ 2) / 2) = (C * Real.exp (-(t ^ 2) / 2)) * 1 := by ring
        _ ≤ (C * Real.exp (-(t ^ 2) / 2)) * (1 + L) :=
          mul_le_mul_of_nonneg_left hone_le hCe_nonneg
        _ = shiftedGeneratingRightDerivBound u w0 x R t := by
          simp only [shiftedGeneratingRightDerivBound, C, L, K]
          ring

private theorem shifted_generating_right_deriv_bound_of_mem_ball
    (u w0 : ℂ) (x ω : ℝ) {R : ℝ} (hR : 0 < R) (t : ℝ) {z : ℂ}
    (hz : z ∈ Metric.ball w0 R) :
    ‖(realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
          (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - z) *
            realHermiteGenerating (t - (1 / 2 : ℝ) * x) z)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ ω t : ℝ) : ℂ))‖ ≤
      shiftedGeneratingRightDerivBound u w0 x R t := by
  let U : ℝ := ‖u‖
  let K : ℝ := ‖w0‖ + R
  let A : ℝ := Real.sqrt 2 * (U + K)
  let B : ℝ := Real.sqrt 2 * (|x| / 2) * (U + K) + (U ^ 2 + K ^ 2) / 2
  let L : ℝ := Real.sqrt 2 * |t| + (Real.sqrt 2 * (|x| / 2) + K)
  let C : ℝ := shiftedGeneratingRightDerivBoundConstant u w0 x R
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hU_nonneg : 0 ≤ U := by simp [U]
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C, shiftedGeneratingRightDerivBoundConstant]
    positivity
  have hzK : ‖z‖ ≤ K := by
    simpa [K] using norm_le_of_mem_ball_complex (u0 := w0) (z := z) (R := R) hz
  have hpi_quarter_nonneg : 0 ≤ Real.pi ^ (-(1 / 4 : ℝ)) :=
    (Real.rpow_pos_of_pos Real.pi_pos _).le
  have hpi_half_nonneg : 0 ≤ Real.pi ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_pos_of_pos Real.pi_pos _).le
  have hleft := realHermiteGenerating_norm_le_of_norm_le
    (t + (1 / 2 : ℝ) * x) u (le_rfl : ‖u‖ ≤ U)
  have hright := realHermiteGenerating_norm_le_of_norm_le
    (t - (1 / 2 : ℝ) * x) z hzK
  have hfac := shifted_deriv_factor_norm_le t x hzK
  have hphase := norm_modulation_phase ω t
  have hnorm₁ :
      ‖(realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - z) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) z)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))‖ ≤
        L *
          ((Real.pi ^ (-(1 / 4 : ℝ)) *
              Real.exp
                (-((t + (1 / 2 : ℝ) * x) ^ 2) / 2 +
                  Real.sqrt 2 * |t + (1 / 2 : ℝ) * x| * U + U ^ 2 / 2)) *
            (Real.pi ^ (-(1 / 4 : ℝ)) *
              Real.exp
                (-((t - (1 / 2 : ℝ) * x) ^ 2) / 2 +
                  Real.sqrt 2 * |t - (1 / 2 : ℝ) * x| * K + K ^ 2 / 2))) := by
    let bleft : ℝ :=
      Real.pi ^ (-(1 / 4 : ℝ)) *
        Real.exp
          (-((t + (1 / 2 : ℝ) * x) ^ 2) / 2 +
            Real.sqrt 2 * |t + (1 / 2 : ℝ) * x| * U + U ^ 2 / 2)
    let bright : ℝ :=
      Real.pi ^ (-(1 / 4 : ℝ)) *
        Real.exp
          (-((t - (1 / 2 : ℝ) * x) ^ 2) / 2 +
            Real.sqrt 2 * |t - (1 / 2 : ℝ) * x| * K + K ^ 2 / 2)
    have hbright_nonneg : 0 ≤ bright := by
      simp only [bright]
      positivity
    rw [norm_mul, hphase, mul_one, norm_mul, norm_mul]
    have hfac_right :
        ‖(Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - z‖ *
            ‖realHermiteGenerating (t - (1 / 2 : ℝ) * x) z‖ ≤ L * bright :=
      mul_le_mul hfac (by simpa [bright] using hright) (norm_nonneg _) hL_nonneg
    calc
      ‖realHermiteGenerating (t + (1 / 2 : ℝ) * x) u‖ *
          (‖(Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - z‖ *
            ‖realHermiteGenerating (t - (1 / 2 : ℝ) * x) z‖) ≤
        bleft * (L * bright) :=
          mul_le_mul (by simpa [bleft] using hleft) hfac_right
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (mul_nonneg hpi_quarter_nonneg (Real.exp_nonneg _))
      _ = L * (bleft * bright) := by ring
  have hcombine :
      (Real.pi ^ (-(1 / 4 : ℝ)) *
            Real.exp
              (-((t + (1 / 2 : ℝ) * x) ^ 2) / 2 +
                Real.sqrt 2 * |t + (1 / 2 : ℝ) * x| * U + U ^ 2 / 2)) *
          (Real.pi ^ (-(1 / 4 : ℝ)) *
            Real.exp
              (-((t - (1 / 2 : ℝ) * x) ^ 2) / 2 +
                Real.sqrt 2 * |t - (1 / 2 : ℝ) * x| * K + K ^ 2 / 2)) ≤
        Real.pi ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(t ^ 2) + A * |t| + B) := by
    have hpi :
        Real.pi ^ (-(1 / 4 : ℝ)) * Real.pi ^ (-(1 / 4 : ℝ)) =
          Real.pi ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add Real.pi_pos]
      norm_num
    have hexponent := shifted_generating_exponent_bound hU_nonneg hK_nonneg x t
    have hexp :
        Real.exp
          ((-((t + (1 / 2 : ℝ) * x) ^ 2) / 2 +
              Real.sqrt 2 * |t + (1 / 2 : ℝ) * x| * U + U ^ 2 / 2) +
            (-((t - (1 / 2 : ℝ) * x) ^ 2) / 2 +
              Real.sqrt 2 * |t - (1 / 2 : ℝ) * x| * K + K ^ 2 / 2)) ≤
          Real.exp (-(t ^ 2) + A * |t| + B) := Real.exp_le_exp.2 (by
        simpa [A, B, mul_assoc, mul_left_comm, mul_comm] using hexponent)
    calc
      (Real.pi ^ (-(1 / 4 : ℝ)) *
            Real.exp
              (-((t + (1 / 2 : ℝ) * x) ^ 2) / 2 +
                Real.sqrt 2 * |t + (1 / 2 : ℝ) * x| * U + U ^ 2 / 2)) *
          (Real.pi ^ (-(1 / 4 : ℝ)) *
            Real.exp
              (-((t - (1 / 2 : ℝ) * x) ^ 2) / 2 +
                Real.sqrt 2 * |t - (1 / 2 : ℝ) * x| * K + K ^ 2 / 2)) =
        (Real.pi ^ (-(1 / 4 : ℝ)) * Real.pi ^ (-(1 / 4 : ℝ))) *
          Real.exp
            ((-((t + (1 / 2 : ℝ) * x) ^ 2) / 2 +
                Real.sqrt 2 * |t + (1 / 2 : ℝ) * x| * U + U ^ 2 / 2) +
              (-((t - (1 / 2 : ℝ) * x) ^ 2) / 2 +
                Real.sqrt 2 * |t - (1 / 2 : ℝ) * x| * K + K ^ 2 / 2)) := by
          rw [Real.exp_add
            (-((t + (1 / 2 : ℝ) * x) ^ 2) / 2 +
              Real.sqrt 2 * |t + (1 / 2 : ℝ) * x| * U + U ^ 2 / 2)
            (-((t - (1 / 2 : ℝ) * x) ^ 2) / 2 +
              Real.sqrt 2 * |t - (1 / 2 : ℝ) * x| * K + K ^ 2 / 2)]
          ring
      _ ≤ Real.pi ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(t ^ 2) + A * |t| + B) := by
          rw [hpi]
          exact mul_le_mul_of_nonneg_left hexp hpi_half_nonneg
  have hcomplete : -(t ^ 2) + A * |t| + B ≤ -(t ^ 2) / 2 + A ^ 2 / 2 + B := by
    have hsquare : 0 ≤ (|t| - A) ^ 2 := sq_nonneg _
    have habs_sq : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith
  have hexp :
      Real.exp (-(t ^ 2) + A * |t| + B) ≤
        Real.exp (A ^ 2 / 2 + B) * Real.exp (-(t ^ 2) / 2) := by
    calc
      Real.exp (-(t ^ 2) + A * |t| + B) ≤
          Real.exp (-(t ^ 2) / 2 + A ^ 2 / 2 + B) := Real.exp_le_exp.2 hcomplete
      _ = Real.exp (A ^ 2 / 2 + B) * Real.exp (-(t ^ 2) / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hcore :
      L * (Real.pi ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2) + A * |t| + B)) ≤
        C * L * Real.exp (-(t ^ 2) / 2) := by
    calc
      L * (Real.pi ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2) + A * |t| + B)) ≤
          L * (Real.pi ^ (-(1 / 2 : ℝ)) *
            (Real.exp (A ^ 2 / 2 + B) * Real.exp (-(t ^ 2) / 2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp hpi_half_nonneg) hL_nonneg
      _ = C * L * Real.exp (-(t ^ 2) / 2) := by
        simp only [C, shiftedGeneratingRightDerivBoundConstant, A, B, U, K]
        ring
  calc
    ‖(realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
          (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - z) *
            realHermiteGenerating (t - (1 / 2 : ℝ) * x) z)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ ω t : ℝ) : ℂ))‖
        ≤ L * (Real.pi ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(t ^ 2) + A * |t| + B)) :=
      hnorm₁.trans (mul_le_mul_of_nonneg_left hcombine hL_nonneg)
    _ ≤ C * L * Real.exp (-(t ^ 2) / 2) := hcore
    _ ≤ shiftedGeneratingRightDerivBound u w0 x R t := by
      have hL_le : L ≤ 1 + L := by linarith
      have hCe_nonneg : 0 ≤ C * Real.exp (-(t ^ 2) / 2) :=
        mul_nonneg hC_nonneg (Real.exp_nonneg _)
      calc
        C * L * Real.exp (-(t ^ 2) / 2) = (C * Real.exp (-(t ^ 2) / 2)) * L := by ring
        _ ≤ (C * Real.exp (-(t ^ 2) / 2)) * (1 + L) :=
          mul_le_mul_of_nonneg_left hL_le hCe_nonneg
        _ = shiftedGeneratingRightDerivBound u w0 x R t := by
          simp only [shiftedGeneratingRightDerivBound, C, L, K]
          ring

private theorem shifted_generating_left_right_deriv_bound_of_mem_ball
    (x ω : ℝ) (t : ℝ) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    ‖((((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ)) *
          realHermiteGenerating (t - (1 / 2 : ℝ) * x) 0) *
        (((Real.sqrt 2 : ℂ) * ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) - z) *
          realHermiteGenerating (t + (1 / 2 : ℝ) * x) z) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ ω t : ℝ) : ℂ)))‖ ≤
      shiftedGeneratingLeftRightDerivBound x t := by
  have hfac :
      ‖(Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ)‖ ≤
        Real.sqrt 2 * |t| + Real.sqrt 2 * (|x| / 2) := by
    simpa using shifted_deriv_factor_norm_le t x
      (z := (0 : ℂ)) (K := 0) (by simp)
  have hbase :
      ‖(realHermiteGenerating (t - (1 / 2 : ℝ) * x) 0 *
          (((Real.sqrt 2 : ℂ) * ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) - z) *
            realHermiteGenerating (t + (1 / 2 : ℝ) * x) z)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))‖ ≤
        shiftedGeneratingRightDerivBound 0 0 (-x) 1 t := by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc,
      mul_comm, mul_left_comm] using
      shifted_generating_right_deriv_bound_of_mem_ball
        (u := 0) (w0 := 0) (-x) ω (R := 1) zero_lt_one t (z := z) hz
  calc
    ‖((((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ)) *
          realHermiteGenerating (t - (1 / 2 : ℝ) * x) 0) *
        (((Real.sqrt 2 : ℂ) * ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) - z) *
          realHermiteGenerating (t + (1 / 2 : ℝ) * x) z) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ ω t : ℝ) : ℂ)))‖ =
        ‖((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ)) *
          ((realHermiteGenerating (t - (1 / 2 : ℝ) * x) 0 *
            (((Real.sqrt 2 : ℂ) * ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) - z) *
              realHermiteGenerating (t + (1 / 2 : ℝ) * x) z)) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ)))‖ := by
        congr 1
        ring
    _ = ‖(Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ)‖ *
        ‖(realHermiteGenerating (t - (1 / 2 : ℝ) * x) 0 *
          (((Real.sqrt 2 : ℂ) * ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) - z) *
            realHermiteGenerating (t + (1 / 2 : ℝ) * x) z)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))‖ := by rw [norm_mul]
    _ ≤ (Real.sqrt 2 * |t| + Real.sqrt 2 * (|x| / 2)) *
        shiftedGeneratingRightDerivBound 0 0 (-x) 1 t :=
        mul_le_mul hfac hbase (norm_nonneg _)
          (by positivity)
    _ = shiftedGeneratingLeftRightDerivBound x t := by rw [shiftedGeneratingLeftRightDerivBound]

theorem hasDerivAt_integral_fixed_mul_shifted_modulated_realHermiteGenerating_right_of_bound
    (phi : ℝ → ℂ) (x ω : ℝ) (w0 : ℂ) {s : Set ℂ} {bound : ℝ → ℝ}
    (hs : s ∈ 𝓝 w0)
    (hF_meas : ∀ᶠ z in 𝓝 w0,
      AEStronglyMeasurable
        (fun t : ℝ =>
          (phi t * realHermiteGenerating (t - (1 / 2 : ℝ) * x) z) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ)))
        (volume : Measure ℝ))
    (hF_int : Integrable
      (fun t : ℝ =>
        (phi t * realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      (volume : Measure ℝ))
    (hF'_meas : AEStronglyMeasurable
      (fun t : ℝ =>
        (phi t *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - w0) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      (volume : Measure ℝ))
    (h_bound : ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ), ∀ z : ℂ, z ∈ s →
      ‖(phi t *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - z) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) z)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))‖ ≤
        bound t)
    (bound_integrable : Integrable bound (volume : Measure ℝ)) :
    HasDerivAt
      (fun z : ℂ => ∫ t : ℝ,
        (phi t * realHermiteGenerating (t - (1 / 2 : ℝ) * x) z) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      (∫ t : ℝ,
        (phi t *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - w0) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      w0 := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t =>
      (phi t * realHermiteGenerating (t - (1 / 2 : ℝ) * x) z) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ ω t : ℝ) : ℂ)))
    (F' := fun z t =>
      (phi t *
          (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - z) *
            realHermiteGenerating (t - (1 / 2 : ℝ) * x) z)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ ω t : ℝ) : ℂ)))
    (bound := bound) hs hF_meas hF_int hF'_meas h_bound bound_integrable ?_).2
  exact ae_of_all _ fun t z _ => by
    simpa [mul_assoc] using
      ((realHermiteGenerating_hasDerivAt (t - (1 / 2 : ℝ) * x) z).const_mul
        (phi t)).mul_const
          (Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))

theorem hasDerivAt_integral_shifted_generating_mul_modulated_right_of_bound
    (u w0 : ℂ) (x ω : ℝ) {s : Set ℂ} {bound : ℝ → ℝ}
    (hs : s ∈ 𝓝 w0)
    (hF_meas : ∀ᶠ z in 𝓝 w0,
      AEStronglyMeasurable
        (fun t : ℝ =>
          (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
            realHermiteGenerating (t - (1 / 2 : ℝ) * x) z) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                ((inner ℝ ω t : ℝ) : ℂ)))
        (volume : Measure ℝ))
    (hF_int : Integrable
      (fun t : ℝ =>
        (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
          realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ)))
      (volume : Measure ℝ))
    (hF'_meas : AEStronglyMeasurable
      (fun t : ℝ =>
        (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - w0) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      (volume : Measure ℝ))
    (h_bound : ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ), ∀ z : ℂ, z ∈ s →
      ‖(realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - z) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) z)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))‖ ≤
        bound t)
    (bound_integrable : Integrable bound (volume : Measure ℝ)) :
    HasDerivAt
      (fun z : ℂ => ∫ t : ℝ,
        (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
          realHermiteGenerating (t - (1 / 2 : ℝ) * x) z) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ)))
      (∫ t : ℝ,
        (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - w0) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      w0 := by
  exact
    hasDerivAt_integral_fixed_mul_shifted_modulated_realHermiteGenerating_right_of_bound
      (phi := fun t : ℝ => realHermiteGenerating (t + (1 / 2 : ℝ) * x) u)
      (x := x) (ω := ω) (w0 := w0) (s := s) (bound := bound)
      hs hF_meas hF_int hF'_meas h_bound bound_integrable

private theorem hasDerivAt_integral_shifted_generating_mul_modulated_right_ball
    (u w0 : ℂ) (x omega : ℝ) {R : ℝ} (hR : 0 < R) :
    HasDerivAt
      (fun w : ℂ => ∫ t : ℝ,
        (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
          realHermiteGenerating (t - (1 / 2 : ℝ) * x) w) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ omega t : ℝ) : ℂ)))
      (∫ t : ℝ,
        (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - w0) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ omega t : ℝ) : ℂ)))
      w0 := by
  let bound : ℝ → ℝ := shiftedGeneratingRightDerivBound u w0 x R
  have hbound_integrable : Integrable bound (volume : Measure ℝ) := by
    simpa [bound] using shiftedGeneratingRightDerivBound_integrable u w0 x R
  have hw0_mem : w0 ∈ Metric.ball w0 R := by simpa [Metric.mem_ball, dist_self] using hR
  have hF_meas : ∀ᶠ z in 𝓝 w0,
      AEStronglyMeasurable
        (fun t : ℝ =>
          (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
            realHermiteGenerating (t - (1 / 2 : ℝ) * x) z) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                ((inner ℝ omega t : ℝ) : ℂ)))
        (volume : Measure ℝ) := by
    refine Filter.Eventually.of_forall fun z => ?_
    exact Continuous.aestronglyMeasurable (by
      unfold realHermiteGenerating
      fun_prop)
  have hF_int_meas : AEStronglyMeasurable
      (fun t : ℝ =>
        (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
          realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ omega t : ℝ) : ℂ)))
      (volume : Measure ℝ) := Continuous.aestronglyMeasurable (by
      unfold realHermiteGenerating
      fun_prop)
  have hF_int_bound : ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ),
      ‖(realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
          realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ omega t : ℝ) : ℂ))‖ ≤ bound t :=
    ae_of_all _ fun t => by
      simpa [bound] using
        shifted_generating_mul_modulated_bound_of_mem_ball
          u w0 x omega hR t (z := w0) hw0_mem
  have hF_int : Integrable
      (fun t : ℝ =>
        (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
          realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ omega t : ℝ) : ℂ)))
      (volume : Measure ℝ) :=
    hbound_integrable.mono' hF_int_meas hF_int_bound
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ =>
        (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - w0) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ omega t : ℝ) : ℂ)))
      (volume : Measure ℝ) := Continuous.aestronglyMeasurable (by
      unfold realHermiteGenerating
      fun_prop)
  have h_bound : ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ), ∀ z : ℂ,
      z ∈ Metric.ball w0 R →
      ‖(realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - z) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) z)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ omega t : ℝ) : ℂ))‖ ≤
        bound t :=
    ae_of_all _ fun t z hz => by
      simpa [bound] using
        shifted_generating_right_deriv_bound_of_mem_ball
          u w0 x omega hR t (z := z) hz
  exact
    hasDerivAt_integral_shifted_generating_mul_modulated_right_of_bound
      (u := u) (w0 := w0) (x := x) (ω := omega)
      (s := Metric.ball w0 R) (bound := bound)
      (Metric.ball_mem_nhds w0 hR) hF_meas hF_int hF'_meas h_bound
      hbound_integrable

theorem hasDerivAt_integral_shifted_generating_mul_modulated_right_closed
    (u w0 : ℂ) (x ω : ℝ) :
    HasDerivAt
      (fun w : ℂ => ∫ t : ℝ,
        realHermiteGenerating (t + x / 2) u *
          realHermiteGenerating (t - x / 2) w *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (ω * t : ℂ)))
      (((u -
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) *
          Complex.exp
            (u * w0 +
              (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * u -
                star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * w0)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))))
      w0 := by
  let z : ℂ :=
    ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
      (Real.sqrt 2 : ℂ)
  let E : ℂ :=
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))
  have hfun :
      (fun w : ℂ => ∫ t : ℝ,
        realHermiteGenerating (t + x / 2) u *
          realHermiteGenerating (t - x / 2) w *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (ω * t : ℂ))) =
      fun w : ℂ => Complex.exp (u * w + z * u - star z * w) * E := by
    funext w
    simpa [z, E] using
      realHermiteGenerating_ambiguity_integral_independent_kernel x ω u w
  rw [hfun]
  have hu : HasDerivAt (fun w : ℂ => u * w) u w0 := by
    simpa using HasDerivAt.const_mul u (hasDerivAt_id w0)
  have hz : HasDerivAt (fun w : ℂ => star z * w) (star z) w0 := by
    simpa using HasDerivAt.const_mul (star z) (hasDerivAt_id w0)
  have hlin :
      HasDerivAt (fun w : ℂ => u * w + z * u - star z * w) (u - star z) w0 := by
    have h := (hu.add_const (z * u)).sub hz
    have heq : (fun w : ℂ => u * w + z * u - star z * w) =
        (fun x => u * x + z * u) - fun w => star z * w := by
      funext w; simp [Pi.sub_apply]
    rw [heq]; exact h
  simpa [z, E, mul_assoc, mul_left_comm, mul_comm] using hlin.cexp.mul_const E

private theorem integral_shifted_generating_right_deriv_eq_closed
    (u w0 : ℂ) (x ω : ℝ) :
    (∫ t : ℝ,
        (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - w0) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))) =
      ((u -
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) *
          Complex.exp
            (u * w0 +
              (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * u -
                star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * w0)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  have hball :=
    hasDerivAt_integral_shifted_generating_mul_modulated_right_ball
      u w0 x ω (R := 1) zero_lt_one
  have hclosed :=
    hasDerivAt_integral_shifted_generating_mul_modulated_right_closed u w0 x ω
  have hball' :
      HasDerivAt
        (fun w : ℂ => ∫ t : ℝ,
          realHermiteGenerating (t + x / 2) u *
            realHermiteGenerating (t - x / 2) w *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (ω * t : ℂ)))
        (∫ t : ℝ,
          (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
              (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - w0) *
                realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0)) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ)))
        w0 := by simpa [inner, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hball
  exact hball'.unique hclosed

theorem hasDerivAt_integral_shifted_generating_mul_modulated_left_closed
    (u0 w : ℂ) (x ω : ℝ) :
    HasDerivAt
      (fun u : ℂ => ∫ t : ℝ,
        realHermiteGenerating (t + x / 2) u *
          realHermiteGenerating (t - x / 2) w *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (ω * t : ℂ)))
      (((w +
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) *
          Complex.exp
            (u0 * w +
              (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * u0 -
                star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * w)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))))
      u0 := by
  let z : ℂ :=
    ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
      (Real.sqrt 2 : ℂ)
  let E : ℂ :=
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))
  have hfun :
      (fun u : ℂ => ∫ t : ℝ,
        realHermiteGenerating (t + x / 2) u *
          realHermiteGenerating (t - x / 2) w *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (ω * t : ℂ))) =
      fun u : ℂ => Complex.exp (u * w + z * u - star z * w) * E := by
    funext u
    simpa [z, E] using
      realHermiteGenerating_ambiguity_integral_independent_kernel x ω u w
  rw [hfun]
  have hw : HasDerivAt (fun u : ℂ => u * w) w u0 := by
    simpa using HasDerivAt.mul_const (hasDerivAt_id u0) w
  have hz : HasDerivAt (fun u : ℂ => z * u) z u0 := by
    simpa using HasDerivAt.const_mul z (hasDerivAt_id u0)
  have hlin :
      HasDerivAt (fun u : ℂ => u * w + z * u - star z * w) (w + z) u0 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (hw.add hz).sub_const (star z * w)
  simpa [z, E, mul_assoc, mul_left_comm, mul_comm] using hlin.cexp.mul_const E

theorem iteratedDeriv_cexp_mul_right_at_zero (n : ℕ) (w : ℂ) :
    iteratedDeriv n (fun u : ℂ => Complex.exp (u * w)) 0 = w ^ n := by
  rw [show (fun u : ℂ => Complex.exp (u * w)) =
      (fun u : ℂ => Complex.exp (w * u)) by
    funext u
    rw [mul_comm]]
  simp [iteratedDeriv_cexp_const_mul]

theorem iteratedDeriv_pow_at_zero (m n : ℕ) :
    iteratedDeriv m (fun w : ℂ => w ^ n) 0 =
      if m = n then (Nat.factorial n : ℂ) else 0 := by
  simpa using (iteratedDeriv_fun_pow_zero (𝕜 := ℂ) (n := m) (m := n))

theorem iteratedDeriv_iteratedDeriv_cexp_mul_at_zero (m n : ℕ) :
    iteratedDeriv m
      (fun w : ℂ => iteratedDeriv n (fun u : ℂ => Complex.exp (u * w)) 0) 0 =
      if m = n then (Nat.factorial n : ℂ) else 0 := by
  have hfun :
      (fun w : ℂ => iteratedDeriv n (fun u : ℂ => Complex.exp (u * w)) 0) =
        fun w : ℂ => w ^ n := by
    funext w
    exact iteratedDeriv_cexp_mul_right_at_zero n w
  rw [hfun]
  exact iteratedDeriv_pow_at_zero m n

private theorem iteratedDeriv_cexp_affine_at_zero (n : ℕ) (a b : ℂ) :
    iteratedDeriv n (fun u : ℂ => Complex.exp (a * u + b)) 0 =
      a ^ n * Complex.exp b := by
  rw [show (fun u : ℂ => Complex.exp (a * u + b)) =
      fun u : ℂ => Complex.exp b * Complex.exp (a * u) by
    funext u
    rw [Complex.exp_add]
    ring]
  rw [iteratedDeriv_const_mul_field]
  simp [iteratedDeriv_cexp_const_mul, mul_comm]

private theorem iteratedDeriv_shifted_pow_at_zero (n k : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w : ℂ => (w + z) ^ k) 0 =
      (k.descFactorial n : ℂ) * z ^ (k - n) := by
  rw [show (fun w : ℂ => (w + z) ^ k) = fun w : ℂ => (fun y : ℂ => y ^ k) (w + z) by rfl]
  have h := congrFun (iteratedDeriv_comp_add_const n (fun y : ℂ => y ^ k) z) 0
  simpa [Nat.cast_mul] using h

private theorem iteratedDeriv_cexp_ambiguity_kernel_u_at_zero
    (k : ℕ) (z w : ℂ) :
    iteratedDeriv k
      (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) 0 =
      (w + z) ^ k * Complex.exp (-(star z) * w) := by
  rw [show (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) =
      fun u : ℂ => Complex.exp ((w + z) * u + (-(star z) * w)) by
    funext u
    congr 1
    ring]
  rw [iteratedDeriv_cexp_affine_at_zero]

private theorem iteratedDeriv_cexp_ambiguity_kernel_diag_at_zero_sum
    (k : ℕ) (z : ℂ) :
    iteratedDeriv k
      (fun w : ℂ =>
        iteratedDeriv k
          (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) 0) 0 =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) *
          (((k.descFactorial i : ℕ) : ℂ) * z ^ (k - i)) *
            (-(star z)) ^ (k - i) := by
  rw [show
      (fun w : ℂ =>
        iteratedDeriv k
          (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) 0) =
      fun w : ℂ => (w + z) ^ k * Complex.exp (-(star z) * w) by
    funext w
    exact iteratedDeriv_cexp_ambiguity_kernel_u_at_zero k z w]
  rw [iteratedDeriv_fun_mul]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [iteratedDeriv_shifted_pow_at_zero, iteratedDeriv_cexp_const_mul]
    simp [mul_assoc]
  · fun_prop
  · fun_prop

private theorem iteratedDeriv_cexp_ambiguity_kernel_at_zero_sum
    (n k : ℕ) (z : ℂ) :
    iteratedDeriv k
      (fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) 0) 0 =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) *
          (((n.descFactorial i : ℕ) : ℂ) * z ^ (n - i)) *
            (-(star z)) ^ (k - i) := by
  rw [show
      (fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) 0) =
      fun w : ℂ => (w + z) ^ n * Complex.exp (-(star z) * w) by
    funext w
    exact iteratedDeriv_cexp_ambiguity_kernel_u_at_zero n z w]
  rw [iteratedDeriv_fun_mul]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [iteratedDeriv_shifted_pow_at_zero, iteratedDeriv_cexp_const_mul]
    simp [mul_assoc]
  · fun_prop
  · fun_prop

private theorem neg_one_pow_mul_of_le (k i : ℕ) (hi : i ≤ k) :
    ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ i) = (-1 : ℂ) ^ (k - i) := by
  calc
    ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ i) =
        (-1 : ℂ) ^ (k + i) := by rw [← pow_add]
    _ = (-1 : ℂ) ^ ((k - i) + 2 * i) := by
        congr 1
        omega
    _ = (-1 : ℂ) ^ (k - i) * ((-1 : ℂ) ^ 2) ^ i := by rw [pow_add, pow_mul]
    _ = (-1 : ℂ) ^ (k - i) := by norm_num

private theorem cexp_ambiguity_kernel_diag_sum_eq_complexHermite
    (k : ℕ) (z : ℂ) :
    (∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) *
          (((k.descFactorial i : ℕ) : ℂ) * z ^ (k - i)) *
            (-(star z)) ^ (k - i)) =
      (-1 : ℂ) ^ k * complexHermite k k z := by
  rw [complexHermite, Nat.min_self, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  rw [show (-(star z)) ^ (k - i) =
      (-1 : ℂ) ^ (k - i) * (star z) ^ (k - i) by
    rw [neg_eq_neg_one_mul, mul_pow]]
  rw [← neg_one_pow_mul_of_le k i hi_le]
  norm_num [Nat.cast_mul]
  ring

private theorem cexp_ambiguity_kernel_sum_eq_complexHermite
    (n k : ℕ) (z : ℂ) :
    (∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) *
          (((n.descFactorial i : ℕ) : ℂ) * z ^ (n - i)) *
            (-(star z)) ^ (k - i)) =
      (-1 : ℂ) ^ k * complexHermite n k z := by
  rw [complexHermite, Finset.mul_sum]
  have hsubset : Finset.range (min n k + 1) ⊆ Finset.range (k + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi ⊢
    exact Nat.lt_succ_of_le ((Nat.lt_succ_iff.mp hi).trans (Nat.min_le_right n k))
  rw [← Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro i hi
    have hi_le_min : i ≤ min n k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hi_le_n : i ≤ n := hi_le_min.trans (Nat.min_le_left n k)
    have hi_le_k : i ≤ k := hi_le_min.trans (Nat.min_le_right n k)
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    rw [show (-(star z)) ^ (k - i) =
        (-1 : ℂ) ^ (k - i) * (star z) ^ (k - i) by
      rw [neg_eq_neg_one_mul, mul_pow]]
    rw [← neg_one_pow_mul_of_le k i hi_le_k]
    norm_num [Nat.cast_mul]
    ring
  · intro i hi hnot
    have hi_le_k : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hn_lt_i : n < i := by
      by_contra hni
      have hi_le_n : i ≤ n := Nat.le_of_not_gt hni
      have hi_min : i ∈ Finset.range (min n k + 1) := by
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (le_min hi_le_n hi_le_k)
      exact hnot hi_min
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.choose_eq_zero_of_lt hn_lt_i]
    simp

private theorem iteratedDeriv_cexp_ambiguity_kernel_diag_at_zero
    (k : ℕ) (z : ℂ) :
    iteratedDeriv k
      (fun w : ℂ =>
        iteratedDeriv k
          (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) 0) 0 =
      (-1 : ℂ) ^ k * complexHermite k k z := by
  rw [iteratedDeriv_cexp_ambiguity_kernel_diag_at_zero_sum]
  exact cexp_ambiguity_kernel_diag_sum_eq_complexHermite k z

private theorem iteratedDeriv_cexp_ambiguity_kernel_at_zero
    (n k : ℕ) (z : ℂ) :
    iteratedDeriv k
      (fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) 0) 0 =
      (-1 : ℂ) ^ k * complexHermite n k z := by
  rw [iteratedDeriv_cexp_ambiguity_kernel_at_zero_sum]
  exact cexp_ambiguity_kernel_sum_eq_complexHermite n k z

private theorem inv_factorial_mul_complexHermite_self_eq_phi1D
    (k : ℕ) (z : ℂ) :
    ((Nat.factorial k : ℂ)⁻¹) * complexHermite k k z = phi1D k k z := by
  have hsqrt :
      Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial k : ℝ)) =
        (Nat.factorial k : ℝ) := by
    rw [← pow_two, Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg (by positivity)
  rw [phi1D, hsqrt]
  norm_num

theorem realHermiteGenerating_deriv_zero (t : ℝ) :
    deriv (realHermiteGenerating t) 0 =
      (Real.sqrt 2 : ℂ) * (t : ℂ) * ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(((t : ℂ) ^ 2) / 2)) := by
  unfold realHermiteGenerating
  rw [deriv_const_mul]
  · rw [deriv_cexp]
    · rw [show deriv
          (fun u : ℂ => -(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) * (t : ℂ) * u -
            u ^ 2 / 2) 0 = (Real.sqrt 2 : ℂ) * (t : ℂ) by
        rw [show (fun u : ℂ => -(((t : ℂ) ^ 2) / 2) +
              (Real.sqrt 2 : ℂ) * (t : ℂ) * u - u ^ 2 / 2) =
            (fun u : ℂ => (Real.sqrt 2 : ℂ) * (t : ℂ) * u +
              (-(((t : ℂ) ^ 2) / 2) + u ^ 2 * (-1 / 2))) by
          funext u
          ring]
        rw [deriv_fun_add]
        · rw [deriv_const_mul]
          · simp [deriv_fun_mul]
          · fun_prop
        · fun_prop
        · fun_prop]
      ring_nf
    · fun_prop
  · fun_prop

/-- `realHermite1D`: real Hermite1 D. -/
noncomputable def realHermite1D (n : ℕ) (t : ℝ) : ℂ :=
  ((Real.sqrt (Nat.factorial n : ℝ) : ℂ) / (Nat.factorial n : ℂ)) *
    iteratedDeriv n (realHermiteGenerating t) 0

theorem realHermite1D_zero (t : ℝ) :
    realHermite1D 0 t = realHermiteGenerating t 0 := by simp [realHermite1D]

theorem realHermite1D_one (t : ℝ) :
    realHermite1D 1 t = (Real.sqrt 2 : ℂ) * (t : ℂ) * realHermiteGenerating t 0 := by
  simp [realHermite1D, realHermiteGenerating_deriv_zero, realHermiteGenerating]
  ring_nf

theorem realHermite1D_inner_zero_zero :
    (∫ t : ℝ, realHermite1D 0 t * star (realHermite1D 0 t)) = 1 := by
  simpa [realHermite1D] using realHermiteGenerating_integral_mul_conj 0 0

theorem integral_real_sq_exp_neg_sq :
    (∫ x : ℝ, x ^ (2 : ℕ) * Real.exp (-(x ^ (2 : ℕ)))) = Real.sqrt Real.pi / 2 := by
  have h_abs : (fun x : ℝ => x ^ (2 : ℕ) * Real.exp (-(x ^ (2 : ℕ)))) =
      fun x : ℝ => (fun y : ℝ => y ^ (2 : ℕ) * Real.exp (-(y ^ (2 : ℕ)))) |x| := by
    funext x
    simp [sq_abs]
  rw [h_abs]
  rw [show (∫ x : ℝ, (fun y : ℝ => y ^ (2 : ℕ) * Real.exp (-(y ^ (2 : ℕ)))) |x|) =
      2 * ∫ x in Set.Ioi (0 : ℝ),
        (fun y : ℝ => y ^ (2 : ℕ) * Real.exp (-(y ^ (2 : ℕ)))) x by
    simpa using
      (integral_comp_abs
        (f := fun y : ℝ => y ^ (2 : ℕ) * Real.exp (-(y ^ (2 : ℕ)))))]
  rw [show (∫ x in Set.Ioi (0 : ℝ),
      (fun y : ℝ => y ^ (2 : ℕ) * Real.exp (-(y ^ (2 : ℕ)))) x) =
      ∫ x in Set.Ioi (0 : ℝ), x ^ (2 : ℝ) * Real.exp (-1 * x ^ (2 : ℝ)) by
    congr 1
    funext x
    norm_num]
  rw [integral_rpow_mul_exp_neg_mul_rpow]
  · rw [show ((2 : ℝ) + 1) / 2 = ((1 : ℕ) : ℝ) + 1 / 2 by norm_num]
    rw [Real.Gamma_nat_add_half]
    norm_num
    ring_nf
  · norm_num
  · norm_num
  · norm_num

theorem integral_real_mul_exp_neg_sq :
    (∫ x : ℝ, x * Real.exp (-(x ^ (2 : ℕ)))) = 0 := by
  have h := MeasureTheory.integral_neg_eq_self
    (f := fun x : ℝ => x * Real.exp (-(x ^ (2 : ℕ))))
    (μ := (volume : MeasureTheory.Measure ℝ))
  rw [show (fun x : ℝ => (-x) * Real.exp (-((-x) ^ (2 : ℕ)))) =
      fun x : ℝ => -(x * Real.exp (-(x ^ (2 : ℕ)))) by
    funext x
    rw [show (-x) ^ (2 : ℕ) = x ^ (2 : ℕ) by ring]
    ring]
    at h
  rw [MeasureTheory.integral_neg] at h
  linarith

theorem realHermite1D_inner_one_one :
    (∫ t : ℝ, realHermite1D 1 t * star (realHermite1D 1 t)) = 1 := by
  simp_rw [realHermite1D_one]
  rw [show (fun t : ℝ =>
      ((Real.sqrt 2 : ℂ) * (t : ℂ) * realHermiteGenerating t 0) *
        star ((Real.sqrt 2 : ℂ) * (t : ℂ) * realHermiteGenerating t 0)) =
      fun t : ℝ => (((2 : ℝ) * (Real.pi ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) *
        ((t ^ (2 : ℕ) * Real.exp (-(t ^ (2 : ℕ)))) : ℂ) by
    funext t
    unfold realHermiteGenerating
    rw [show Complex.exp (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) *
          (t : ℂ) * 0 - 0 ^ 2 / 2) =
        Complex.exp (-(((t : ℂ) ^ 2) / 2)) by
      ring_nf]
    simp only [star_mul, RCLike.star_def, Complex.conj_ofReal]
    rw [← Complex.exp_conj]
    simp only [map_neg, map_div₀, map_pow, Complex.conj_ofReal, map_ofNat]
    rw [show Complex.exp (-(↑t ^ 2 / 2)) *
        ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * ((t : ℂ) * (Real.sqrt 2 : ℂ)) =
        (Real.sqrt 2 : ℂ) * ↑t *
          (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * Complex.exp (-(↑t ^ 2 / 2))) by
      ring]
    rw [show (Real.sqrt 2 : ℂ) * ↑t *
        (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * Complex.exp (-(↑t ^ 2 / 2))) *
        ((Real.sqrt 2 : ℂ) * ↑t *
          (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
            Complex.exp (-(↑t ^ 2 / 2)))) =
        ((Real.sqrt 2 : ℂ) ^ 2) * ((t : ℂ) ^ 2) *
          (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) ^ 2) *
            (Complex.exp (-(↑t ^ 2 / 2)) * Complex.exp (-(↑t ^ 2 / 2))) by
      ring]
    rw [cexp_neg_half_sq_sq, sqrtTwoC_sq, piPowQuarterC_sq]
    ring_nf
    norm_num]
  rw [MeasureTheory.integral_const_mul]
  rw [show (∫ t : ℝ, (t : ℂ) ^ (2 : ℕ) *
      ((Real.exp (-(t ^ (2 : ℕ))) : ℝ) : ℂ)) =
      ∫ t : ℝ, ((t ^ (2 : ℕ) * Real.exp (-(t ^ (2 : ℕ))) : ℝ) : ℂ) by
    congr 1
    funext t
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]]
  rw [integral_complex_ofReal, integral_real_sq_exp_neg_sq]
  rw [show (((2 : ℝ) : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
      ((Real.sqrt Real.pi / 2 : ℝ) : ℂ) = 1 by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    change ((2 * Real.pi ^ (-(1 / 2 : ℝ)) * (Real.sqrt Real.pi / 2) : ℝ) : ℂ) =
      ((1 : ℝ) : ℂ)
    congr 1
    rw [Real.sqrt_eq_rpow]
    ring_nf
    rw [← Real.rpow_add Real.pi_pos]
    norm_num]

theorem realHermite1D_inner_zero_one :
    (∫ t : ℝ, realHermite1D 0 t * star (realHermite1D 1 t)) = 0 := by
  simp_rw [realHermite1D_zero, realHermite1D_one]
  rw [show (fun t : ℝ => realHermiteGenerating t 0 *
      star ((Real.sqrt 2 : ℂ) * (t : ℂ) * realHermiteGenerating t 0)) =
      fun t : ℝ => ((Real.sqrt 2 * (Real.pi ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) *
        ((t * Real.exp (-(t ^ (2 : ℕ))) : ℝ) : ℂ) by
    funext t
    unfold realHermiteGenerating
    rw [show Complex.exp (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) *
          (t : ℂ) * 0 - 0 ^ 2 / 2) =
        Complex.exp (-(((t : ℂ) ^ 2) / 2)) by
      ring_nf]
    simp only [star_mul, RCLike.star_def, Complex.conj_ofReal]
    rw [← Complex.exp_conj]
    simp only [map_neg, map_div₀, map_pow, Complex.conj_ofReal, map_ofNat]
    rw [show Complex.exp (-(↑t ^ 2 / 2)) *
        ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * ((t : ℂ) * (Real.sqrt 2 : ℂ)) =
        (Real.sqrt 2 : ℂ) * ↑t *
          (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * Complex.exp (-(↑t ^ 2 / 2))) by
      ring]
    rw [show (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (-(↑t ^ 2 / 2))) *
        ((Real.sqrt 2 : ℂ) * ↑t *
          (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
            Complex.exp (-(↑t ^ 2 / 2)))) =
        (Real.sqrt 2 : ℂ) * (t : ℂ) *
          (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) ^ 2) *
            (Complex.exp (-(↑t ^ 2 / 2)) * Complex.exp (-(↑t ^ 2 / 2))) by
      ring]
    rw [cexp_neg_half_sq_sq, piPowQuarterC_sq]
    rw [show ((Real.sqrt 2 * (Real.pi ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) =
        (Real.sqrt 2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) by
      rw [← Complex.ofReal_mul]]
    rw [Complex.ofReal_mul]
    ring_nf]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_complex_ofReal, integral_real_mul_exp_neg_sq]
  simp

theorem realHermite1D_inner_one_zero :
    (∫ t : ℝ, realHermite1D 1 t * star (realHermite1D 0 t)) = 0 := by
  calc
    (∫ t : ℝ, realHermite1D 1 t * star (realHermite1D 0 t))
        = ∫ t : ℝ, conj (realHermite1D 0 t * star (realHermite1D 1 t)) := by
          congr 1
          funext t
          simp [RCLike.star_def, mul_comm]
    _ = conj (∫ t : ℝ, realHermite1D 0 t * star (realHermite1D 1 t)) := by
      simpa [RCLike.star_def] using
        (integral_conj (μ := (volume : MeasureTheory.Measure ℝ))
          (f := fun t : ℝ => realHermite1D 0 t * star (realHermite1D 1 t)))
    _ = 0 := by
      rw [realHermite1D_inner_zero_one]
      simp

private lemma neg_ofReal_sq_div_two_re (t : ℝ) :
    (-(↑t ^ 2 / 2) : ℂ).re = -(t ^ (2 : ℕ)) / 2 := by
  norm_num [Complex.div_re]
  rw [pow_two]
  simp [Complex.mul_re]
  ring

private lemma real_exp_neg_sq_eq_sq (t : ℝ) :
    Real.exp (-(t ^ (2 : ℕ))) = Real.exp (-(t ^ (2 : ℕ)) / 2) ^ (2 : ℕ) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem realHermite1D_zero_memLp :
    MemLp (realHermite1D 0) 2 (volume : Measure ℝ) := by
  have hfun : realHermite1D 0 = (fun t : ℝ =>
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(((t : ℂ) ^ 2) / 2)))) := by
    funext t
    simp [realHermite1D_zero, realHermiteGenerating]
  rw [hfun]
  refine (MeasureTheory.memLp_two_iff_integrable_sq_norm ?_).2 ?_
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · have hbase : Integrable (fun t : ℝ => Real.exp (-1 * t ^ (2 : ℝ))) := by
      simpa using integrable_exp_neg_mul_sq (b := (1 : ℝ)) zero_lt_one
    have hbase_nat : Integrable (fun t : ℝ => Real.exp (-(t ^ (2 : ℕ)))) := by
      convert hbase using 1
      funext t
      norm_num
    refine (hbase_nat.const_mul
      (‖((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)‖ ^ (2 : ℕ))).congr ?_
    filter_upwards with t
    rw [norm_mul, Complex.norm_exp]
    rw [neg_ofReal_sq_div_two_re t]
    rw [real_exp_neg_sq_eq_sq t]
    ring

theorem realHermite1D_one_memLp :
    MemLp (realHermite1D 1) 2 (volume : Measure ℝ) := by
  have hfun : realHermite1D 1 = (fun t : ℝ =>
      (Real.sqrt 2 : ℂ) * (t : ℂ) *
        ((((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (-(((t : ℂ) ^ 2) / 2))))) := by
    funext t
    rw [realHermite1D_one]
    unfold realHermiteGenerating
    rw [show Complex.exp (-(((t : ℂ) ^ 2) / 2) +
          (Real.sqrt 2 : ℂ) * (t : ℂ) * 0 - 0 ^ 2 / 2) =
        Complex.exp (-(((t : ℂ) ^ 2) / 2)) by
      ring_nf]
  rw [hfun]
  refine (MeasureTheory.memLp_two_iff_integrable_sq_norm ?_).2 ?_
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · have hbase :
        Integrable (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-(t ^ (2 : ℕ)))) := by
      have hbase' :
          Integrable (fun t : ℝ => t ^ (2 : ℝ) * Real.exp (-1 * t ^ (2 : ℝ))) := by
        simpa using integrable_rpow_mul_exp_neg_mul_sq
          (b := (1 : ℝ)) zero_lt_one (by norm_num : (-1 : ℝ) < 2)
      convert hbase' using 1
      funext t
      norm_num
    refine (hbase.const_mul
      (‖(Real.sqrt 2 : ℂ) *
          ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)‖ ^ (2 : ℕ))).congr ?_
    filter_upwards with t
    simp only [norm_mul, Complex.norm_exp]
    rw [neg_ofReal_sq_div_two_re t]
    rw [real_exp_neg_sq_eq_sq t]
    rw [show t ^ (2 : ℕ) = ‖(t : ℂ)‖ ^ (2 : ℕ) by
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq]
      ring]
    ring

private lemma integrable_pow_mul_exp_neg_sq
    (n : ℕ) :
    Integrable (fun r : ℝ => r ^ n * Real.exp (-r ^ 2)) volume := by
  have hs : (-1 : ℝ) < (n : ℝ) := by exact_mod_cast (show -1 < (n : ℤ) by omega)
  have h := integrable_rpow_mul_exp_neg_mul_sq one_pos hs
  refine h.congr ?_
  filter_upwards with r
  rw [Real.rpow_natCast]
  ring_nf

theorem complex_monomial_gaussian_memLp
    (k : ℕ) :
    MemLp (fun t : ℝ => (t : ℂ) ^ k *
      Complex.exp (-(((t : ℂ) ^ 2) / 2))) 2 (volume : Measure ℝ) := by
  refine (MeasureTheory.memLp_two_iff_integrable_sq_norm ?_).2 ?_
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · have hbase :
        Integrable (fun t : ℝ => t ^ (2 * k) * Real.exp (-(t ^ (2 : ℕ)))) := by
      simpa [pow_two] using integrable_pow_mul_exp_neg_sq (2 * k)
    refine hbase.congr ?_
    filter_upwards with t
    simp only [norm_mul, norm_pow, Complex.norm_exp]
    rw [neg_ofReal_sq_div_two_re t]
    rw [real_exp_neg_sq_eq_sq t]
    rw [show t ^ (2 * k) = ‖(t : ℂ)‖ ^ (k * 2) by
      rw [show ‖(t : ℂ)‖ ^ (k * 2) = t ^ (k * 2) by
        rw [pow_mul, ← norm_pow, ← Complex.normSq_eq_norm_sq]
        simp [Complex.normSq_ofReal, ← Complex.ofReal_pow, pow_mul]
        ring_nf]
      ring_nf]
    rw [pow_mul]
    ring_nf

/-- `complexMonomialGaussian`: complex monomial gaussian. -/
noncomputable def complexMonomialGaussian (k : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ k * Complex.exp (-(((t : ℂ) ^ 2) / 2))

theorem complex_monomial_gaussian_product_integrable
    (k l : ℕ) :
    Integrable
      (fun t : ℝ =>
        complexMonomialGaussian k t * complexMonomialGaussian l t)
      (volume : Measure ℝ) := by
  have hk : MemLp (complexMonomialGaussian k) 2 (volume : Measure ℝ) :=
    complex_monomial_gaussian_memLp k
  have hl : MemLp (complexMonomialGaussian l) 2 (volume : Measure ℝ) :=
    complex_monomial_gaussian_memLp l
  have hmul := hk.integrable_mul hl
  refine hmul.congr ?_
  filter_upwards with t
  rfl

theorem complex_monomial_gaussian_product_integral_of_odd
    {k l : ℕ} (hodd : Odd (k + l)) :
    (∫ t : ℝ,
      complexMonomialGaussian k t * complexMonomialGaussian l t) = 0 := by
  let f : ℝ → ℂ :=
    fun t => complexMonomialGaussian k t * complexMonomialGaussian l t
  have hneg := MeasureTheory.integral_neg_eq_self
    (f := f) (μ := (volume : Measure ℝ))
  have hpoint : (fun t : ℝ => f (-t)) = fun t : ℝ => -f t := by
    funext t
    let z : ℂ := (t : ℂ)
    let e : ℂ := Complex.exp (-(z ^ (2 : ℕ) / 2))
    have hcast : ((-t : ℝ) : ℂ) = -z := by simp [z]
    simp only [f, complexMonomialGaussian, hcast]
    rw [show -((-z) ^ (2 : ℕ) / 2) = -(z ^ (2 : ℕ) / 2) by ring]
    change ((-z) ^ k * e) * ((-z) ^ l * e) =
      -((z ^ k * e) * (z ^ l * e))
    calc
      ((-z) ^ k * e) * ((-z) ^ l * e) =
          (-z) ^ (k + l) * (e * e) := by
            rw [show ((-z) ^ k * e) * ((-z) ^ l * e) =
              ((-z) ^ k * (-z) ^ l) * (e * e) by ring]
            rw [← pow_add]
      _ = -(z ^ (k + l) * (e * e)) := by
            rw [hodd.neg_pow]
            ring
      _ = -((z ^ k * e) * (z ^ l * e)) := by
            rw [show ((z ^ k * e) * (z ^ l * e)) =
              (z ^ k * z ^ l) * (e * e) by ring]
            rw [← pow_add]
  rw [hpoint, MeasureTheory.integral_neg] at hneg
  exact CharZero.neg_eq_self_iff.mp hneg

theorem integral_real_pow_exp_neg_sq_of_even
    {n : ℕ} (heven : Even n) :
    (∫ x : ℝ, x ^ n * Real.exp (-(x ^ (2 : ℕ)))) =
      Real.Gamma (((n : ℝ) + 1) / 2) := by
  have h_abs : (fun x : ℝ => x ^ n * Real.exp (-(x ^ (2 : ℕ)))) =
      fun x : ℝ => (fun y : ℝ => y ^ n * Real.exp (-(y ^ (2 : ℕ)))) |x| := by
    funext x
    simp [sq_abs, heven.pow_abs x]
  rw [h_abs]
  rw [show (∫ x : ℝ,
        (fun y : ℝ => y ^ n * Real.exp (-(y ^ (2 : ℕ)))) |x|) =
      2 * ∫ x in Set.Ioi (0 : ℝ),
        (fun y : ℝ => y ^ n * Real.exp (-(y ^ (2 : ℕ)))) x by
    simpa using
      (integral_comp_abs
        (f := fun y : ℝ => y ^ n * Real.exp (-(y ^ (2 : ℕ)))))]
  rw [show (∫ x in Set.Ioi (0 : ℝ),
      (fun y : ℝ => y ^ n * Real.exp (-(y ^ (2 : ℕ)))) x) =
      ∫ x in Set.Ioi (0 : ℝ), x ^ (n : ℝ) * Real.exp (-1 * x ^ (2 : ℝ)) by
    congr 1
    funext x
    norm_num]
  rw [integral_rpow_mul_exp_neg_mul_rpow]
  · rw [Real.one_rpow]
    ring
  · norm_num
  · exact_mod_cast (show -1 < (n : ℤ) by omega)
  · norm_num

theorem complex_monomial_gaussian_product_integral_of_even
    {k l : ℕ} (heven : Even (k + l)) :
    (∫ t : ℝ,
      complexMonomialGaussian k t * complexMonomialGaussian l t) =
      (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ) := by
  rw [show (fun t : ℝ =>
      complexMonomialGaussian k t * complexMonomialGaussian l t) =
      fun t : ℝ =>
        ((t ^ (k + l) * Real.exp (-(t ^ (2 : ℕ))) : ℝ) : ℂ) by
    funext t
    unfold complexMonomialGaussian
    let z : ℂ := (t : ℂ)
    let e : ℂ := Complex.exp (-(z ^ (2 : ℕ) / 2))
    change (z ^ k * e) * (z ^ l * e) =
      ((t ^ (k + l) * Real.exp (-(t ^ (2 : ℕ))) : ℝ) : ℂ)
    calc
      (z ^ k * e) * (z ^ l * e) =
          z ^ (k + l) * (e * e) := by
            rw [show (z ^ k * e) * (z ^ l * e) =
              (z ^ k * z ^ l) * (e * e) by ring]
            rw [← pow_add]
      _ = z ^ (k + l) * Complex.exp (-(z ^ (2 : ℕ))) := by
            rw [show e * e = Complex.exp (-(z ^ (2 : ℕ))) by
              simp only [e]
              rw [← Complex.exp_add]
              congr 1
              ring]
      _ = ((t ^ (k + l) * Real.exp (-(t ^ (2 : ℕ))) : ℝ) : ℂ) := by
            rw [show z ^ (k + l) = ((t ^ (k + l) : ℝ) : ℂ) by simp [z, ← Complex.ofReal_pow]]
            rw [show Complex.exp (-(z ^ (2 : ℕ))) =
                ((Real.exp (-(t ^ (2 : ℕ))) : ℝ) : ℂ) by
              rw [show -(z ^ (2 : ℕ)) = ((-(t ^ (2 : ℕ)) : ℝ) : ℂ) by
                simp [z, ← Complex.ofReal_pow]]
              rw [← Complex.ofReal_exp]]
            rw [← Complex.ofReal_mul]]
  rw [integral_complex_ofReal, integral_real_pow_exp_neg_sq_of_even heven]

open scoped Nat in
theorem complex_monomial_gaussian_product_integral_of_eq_two_mul
    {k l r : ℕ} (hkl : k + l = 2 * r) :
    (∫ t : ℝ,
      complexMonomialGaussian k t * complexMonomialGaussian l t) =
      (((((2 * r - 1 : ℕ)‼ : ℕ) : ℝ) * Real.sqrt Real.pi /
        (2 ^ r : ℝ)) : ℂ) := by
  have heven : Even (k + l) := by
    rw [hkl]
    exact ⟨r, by ring⟩
  rw [complex_monomial_gaussian_product_integral_of_even heven]
  rw [show ((((k + l : ℕ) : ℝ) + 1) / 2) = (r : ℝ) + 1 / 2 by
    rw [hkl]
    norm_num
    ring]
  rw [Real.Gamma_nat_add_half, Complex.ofReal_div, Complex.ofReal_mul]

theorem complex_monomial_gaussian_product_integral_eq_ite
    (k l : ℕ) :
    (∫ t : ℝ,
      complexMonomialGaussian k t * complexMonomialGaussian l t) =
      if Even (k + l) then
        (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ)
      else 0 := by
  by_cases heven : Even (k + l)
  · simp [heven, complex_monomial_gaussian_product_integral_of_even heven]
  · have hodd : Odd (k + l) := Nat.not_even_iff_odd.mp heven
    simp [heven, complex_monomial_gaussian_product_integral_of_odd hodd]

private theorem monomial_gaussian_bilinear_row_integrable
    (t : Finset ℕ) (a b : ℕ → ℂ) (k : ℕ) :
    Integrable
      (fun x : ℝ =>
        ∑ l ∈ t,
          (a k * b l) *
            (complexMonomialGaussian k x * complexMonomialGaussian l x))
      (volume : Measure ℝ) := by
  refine MeasureTheory.integrable_finsetSum t ?_
  intro l hl
  exact (complex_monomial_gaussian_product_integrable k l).const_mul (a k * b l)

theorem complex_monomial_gaussian_finite_bilinear_integrable
    (s t : Finset ℕ) (a b : ℕ → ℂ) :
    Integrable
      (fun x : ℝ =>
        ∑ k ∈ s, ∑ l ∈ t,
          (a k * b l) *
            (complexMonomialGaussian k x *
              complexMonomialGaussian l x))
      (volume : Measure ℝ) := by
  refine MeasureTheory.integrable_finsetSum s ?_
  intro k hk
  exact monomial_gaussian_bilinear_row_integrable t a b k

theorem complex_monomial_gaussian_finite_bilinear_integral_eq_ite
    (s t : Finset ℕ) (a b : ℕ → ℂ) :
    (∫ x : ℝ,
      ∑ k ∈ s, ∑ l ∈ t,
        (a k * b l) *
          (complexMonomialGaussian k x *
            complexMonomialGaussian l x)) =
      ∑ k ∈ s, ∑ l ∈ t,
        (a k * b l) *
          (if Even (k + l) then
            (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ)
          else 0) := by
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro l hl
      rw [MeasureTheory.integral_const_mul]
      rw [complex_monomial_gaussian_product_integral_eq_ite]
    · intro l hl
      exact (complex_monomial_gaussian_product_integrable k l).const_mul
        (a k * b l)
  · intro k hk
    exact monomial_gaussian_bilinear_row_integrable t a b k

theorem complex_monomial_gaussian_finite_bilinear_integral_eq_zero_of_odd
    (s t : Finset ℕ) (a b : ℕ → ℂ)
    (hodd : ∀ k ∈ s, ∀ l ∈ t, Odd (k + l)) :
    (∫ x : ℝ,
      ∑ k ∈ s, ∑ l ∈ t,
        (a k * b l) *
          (complexMonomialGaussian k x *
            complexMonomialGaussian l x)) = 0 := by
  rw [complex_monomial_gaussian_finite_bilinear_integral_eq_ite]
  refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l hl => ?_
  rw [if_neg (Nat.not_even_iff_odd.mpr (hodd k hk l hl)), mul_zero]

theorem complex_monomial_gaussian_finite_bilinear_integral_eq_even_moments
    (s t : Finset ℕ) (a b : ℕ → ℂ)
    (heven : ∀ k ∈ s, ∀ l ∈ t, Even (k + l)) :
    (∫ x : ℝ,
      ∑ k ∈ s, ∑ l ∈ t,
        (a k * b l) *
          (complexMonomialGaussian k x *
            complexMonomialGaussian l x)) =
      ∑ k ∈ s, ∑ l ∈ t,
        (a k * b l) *
          (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ) := by
  rw [complex_monomial_gaussian_finite_bilinear_integral_eq_ite]
  refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
  rw [if_pos (heven k hk l hl)]

private theorem iteratedDeriv_cexp_neg_sq_div_two_zero_of_odd
    {n : ℕ} (hodd : Odd n) :
    iteratedDeriv n (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) 0 = 0 := by
  let q : ℂ → ℂ := fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)
  have hfun : (fun u : ℂ => q (-u)) = q := by
    funext u
    simp [q]
  have hder := iteratedDeriv_comp_neg n q (0 : ℂ)
  rw [hfun] at hder
  simp only [neg_zero] at hder
  have hneg : ((-1 : ℂ) ^ n) = -1 := by simpa using hodd.neg_one_pow
  rw [hneg, neg_smul, one_smul] at hder
  exact CharZero.neg_eq_self_iff.mp hder.symm

private theorem deriv_cexp_neg_sq_div_two :
    deriv (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) =
      fun u : ℂ => -u * Complex.exp (-(u ^ (2 : ℕ)) / 2) := by
  funext u
  rw [deriv_cexp]
  · have hpoly : deriv (fun y : ℂ => -y ^ (2 : ℕ) / 2) u = -u := by
      rw [show (fun y : ℂ => -y ^ (2 : ℕ) / 2) =
          fun y : ℂ => (-1 / 2 : ℂ) * y ^ (2 : ℕ) by
        funext y
        ring]
      rw [deriv_const_mul]
      · rw [deriv_pow_field]
        ring
      · fun_prop
    rw [hpoly]
    ring
  · fun_prop

private theorem iteratedDeriv_cexp_neg_sq_div_two_zero_of_two_mul
    (r : ℕ) :
    iteratedDeriv (2 * r)
      (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) 0 =
      (-1 : ℂ) ^ r * ((2 * r - 1)‼ : ℂ) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [show 2 * (r + 1) = 2 * r + 1 + 1 by omega,
        iteratedDeriv_succ',
        deriv_cexp_neg_sq_div_two,
        iteratedDeriv_fun_mul]
      · rw [Finset.sum_eq_single (1 : ℕ)]
        · simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
            Nat.cast_one, iteratedDeriv_one, deriv_neg'', mul_neg, mul_one, neg_add_rev,
            add_tsub_cancel_right, ih]
          rw [Nat.doubleFactorial_add_one (2 * r)]
          norm_num
          ring
        · intro b hb hbne
          have hb_ne_one : b ≠ 1 := by omega
          have hder : iteratedDeriv b (fun u : ℂ => -u) 0 = 0 := by
            rw [show (fun u : ℂ => -u) = fun u : ℂ => (-1 : ℂ) * u by
              funext u
              ring]
            rw [iteratedDeriv_const_mul_field]
            simp [iteratedDeriv_fun_id_zero, hb_ne_one]
          rw [hder]
          ring
        · intro hnot
          simp at hnot
      · fun_prop
      · fun_prop

private theorem iteratedDeriv_cexp_neg_sq_div_two_zero_of_even
    {n : ℕ} (heven : Even n) :
    iteratedDeriv n (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) 0 =
      (-1 : ℂ) ^ (n / 2) * ((n - 1)‼ : ℂ) := by
  rcases heven with ⟨r, hr⟩
  rw [hr, show r + r = 2 * r by ring]
  simpa [Nat.mul_div_right _ (by norm_num : 0 < 2)]
    using iteratedDeriv_cexp_neg_sq_div_two_zero_of_two_mul r

theorem realHermiteGenerating_iteratedDeriv_zero_expansion
    (n : ℕ) (t : ℝ) :
    iteratedDeriv n (realHermiteGenerating t) 0 =
      ∑ k ∈ Finset.range (n + 1),
        ((((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
            ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
              iteratedDeriv (n - k)
                (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) 0)) *
          ((t : ℂ) ^ k * Complex.exp (-(((t : ℂ) ^ 2) / 2)))) := by
  let a : ℂ :=
    (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
      Complex.exp (-(((t : ℂ) ^ 2) / 2)))
  let b : ℂ := (Real.sqrt 2 : ℂ) * (t : ℂ)
  let q : ℂ → ℂ := fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)
  have hfun : realHermiteGenerating t =
      fun u : ℂ => a * (Complex.exp (b * u) * q u) := by
    funext u
    unfold realHermiteGenerating
    simp only [a, b, q]
    calc
      ((↑(Real.pi ^ (-(1 / 4 : ℝ))) : ℂ) *
          Complex.exp (-(↑t ^ 2 / 2) + ↑√2 * ↑t * u - u ^ 2 / 2)) =
          ((↑(Real.pi ^ (-(1 / 4 : ℝ))) : ℂ) *
            (Complex.exp (-(↑t ^ 2 / 2)) *
              (Complex.exp (b * u) * Complex.exp (-(u ^ (2 : ℕ)) / 2)))) := by
        congr 1
        rw [← Complex.exp_add (b * u) (-(u ^ (2 : ℕ)) / 2),
          ← Complex.exp_add (-(↑t ^ 2 / 2)) (b * u + -(u ^ (2 : ℕ)) / 2)]
        congr 1
        ring
      _ = (↑(Real.pi ^ (-(1 / 4 : ℝ))) *
            Complex.exp (-(↑t ^ 2 / 2))) *
          (Complex.exp (b * u) * Complex.exp (-(u ^ (2 : ℕ)) / 2)) := by ring
  calc
    iteratedDeriv n (realHermiteGenerating t) 0 =
        a * ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℂ) *
            b ^ k *
              iteratedDeriv (n - k) q 0 := by
      rw [hfun, iteratedDeriv_const_mul_field, iteratedDeriv_fun_mul]
      · congr 1
        apply Finset.sum_congr rfl
        intro k hk
        simp [iteratedDeriv_cexp_const_mul]
      · fun_prop
      · fun_prop
    _ = ∑ k ∈ Finset.range (n + 1),
        ((((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
            ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
              iteratedDeriv (n - k)
                (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) 0)) *
          ((t : ℂ) ^ k * Complex.exp (-(((t : ℂ) ^ 2) / 2)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [a, b, q]
      ring_nf

/-- `realHermiteGeneratingExpansionCoeff`: real Hermite Generating Expansion Coeff. -/
noncomputable def realHermiteGeneratingExpansionCoeff (n k : ℕ) : ℂ :=
  (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
    ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
      iteratedDeriv (n - k)
        (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) 0))

theorem realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_sub
    {n k : ℕ} (hodd : Odd (n - k)) :
    realHermiteGeneratingExpansionCoeff n k = 0 := by
  simp [realHermiteGeneratingExpansionCoeff,
    iteratedDeriv_cexp_neg_sq_div_two_zero_of_odd hodd]

theorem realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_add
    {n k : ℕ} (hk : k ≤ n) (hodd : Odd (n + k)) :
    realHermiteGeneratingExpansionCoeff n k = 0 := by
  apply realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_sub
  rw [Nat.odd_sub hk]
  exact Nat.odd_add.mp hodd

theorem realHermiteGeneratingExpansionCoeff_eq_of_even_sub
    {n k : ℕ} (heven : Even (n - k)) :
    realHermiteGeneratingExpansionCoeff n k =
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
          ((-1 : ℂ) ^ ((n - k) / 2) *
            (((n - k) - 1)‼ : ℂ)))) := by
  unfold realHermiteGeneratingExpansionCoeff
  rw [iteratedDeriv_cexp_neg_sq_div_two_zero_of_even heven]

theorem realHermiteGeneratingExpansionCoeff_eq_even_add_closed
    {n k : ℕ} (hk : k ≤ n) (heven : Even (n + k)) :
    realHermiteGeneratingExpansionCoeff n k =
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
          ((-1 : ℂ) ^ ((n - k) / 2) *
            (((n - k) - 1)‼ : ℂ)))) := by
  apply realHermiteGeneratingExpansionCoeff_eq_of_even_sub
  rw [Nat.even_sub hk]
  exact Nat.even_add.mp heven

theorem realHermiteGeneratingExpansionCoeff_eq_scaled_hermite_coeff_of_even_add
    {n k : ℕ} (hk : k ≤ n) (heven : Even (n + k)) :
    realHermiteGeneratingExpansionCoeff n k =
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        ((Real.sqrt 2 : ℂ) ^ k * ((Polynomial.hermite n).coeff k : ℂ))) := by
  rw [realHermiteGeneratingExpansionCoeff_eq_even_add_closed hk heven]
  have hcoeff := Polynomial.coeff_hermite_of_even_add (n := n) (k := k) heven
  rw [hcoeff]
  norm_num
  ring_nf
  simp

theorem realHermiteGeneratingExpansionCoeff_eq_scaled_hermite_coeff
    (n k : ℕ) :
    realHermiteGeneratingExpansionCoeff n k =
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        ((Real.sqrt 2 : ℂ) ^ k * ((Polynomial.hermite n).coeff k : ℂ))) := by
  by_cases hk : k ≤ n
  · by_cases heven : Even (n + k)
    · exact realHermiteGeneratingExpansionCoeff_eq_scaled_hermite_coeff_of_even_add hk heven
    · have hodd : Odd (n + k) := Nat.not_even_iff_odd.mp heven
      rw [realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_add hk hodd,
        Polynomial.coeff_hermite_of_odd_add hodd]
      ring
  · have hlt : n < k := Nat.lt_of_not_ge hk
    rw [Polynomial.coeff_hermite_of_lt hlt]
    simp [realHermiteGeneratingExpansionCoeff, Nat.choose_eq_zero_of_lt hlt]

/-- `standardGaussianMoment`: standard Gaussian Moment. -/
noncomputable def standardGaussianMoment (r : ℕ) : ℂ :=
  if Even r then ((r - 1)‼ : ℂ) else 0

private noncomputable def realHermiteCoeffScale : ℂ :=
  (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ))

private lemma standardGaussianMoment_add_two (r : ℕ) :
    standardGaussianMoment (r + 2) =
      (r + 1 : ℂ) * standardGaussianMoment r := by
  unfold standardGaussianMoment
  by_cases hr : Even r
  · rcases hr with ⟨s, hs⟩
    have h2 : Even (r + 2) := by
      refine ⟨s + 1, ?_⟩
      rw [hs]
      ring
    rw [if_pos h2, if_pos ⟨s, hs⟩, show r + 2 - 1 = r + 1 by omega, Nat.doubleFactorial_add_one]
    norm_num
  · have hodd : Odd r := Nat.not_even_iff_odd.mp hr
    rcases hodd with ⟨s, hs⟩
    have h2odd : Odd (r + 2) := by
      refine ⟨s + 1, ?_⟩
      rw [hs]
      ring
    have h2 : ¬ Even (r + 2) := Nat.not_even_iff_odd.mpr h2odd
    rw [if_neg h2, if_neg hr]
    simp

private lemma standardGaussianMoment_succ_eq_mul_pred (k : ℕ) :
    standardGaussianMoment (k + 1) =
      (k : ℂ) * standardGaussianMoment (k - 1) := by
  cases k with
  | zero => simp [standardGaussianMoment]
  | succ n =>
      simpa [Nat.succ_eq_add_one, add_assoc]
        using standardGaussianMoment_add_two n

private lemma realHermiteCoeffScale_sq_mul_sqrt_pi :
    (realHermiteCoeffScale * realHermiteCoeffScale) *
        (Real.sqrt Real.pi : ℂ) = 1 := by
  unfold realHermiteCoeffScale
  have hA2 :
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
          ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) =
        ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← Real.rpow_add Real.pi_pos]
    norm_num
  rw [hA2, ← Complex.ofReal_mul]
  change ((Real.pi ^ (-(1 / 2 : ℝ)) * Real.sqrt Real.pi : ℝ) : ℂ) =
    (1 : ℂ)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos]
  norm_num

private lemma scaled_gamma_moment_eq_standard (r : ℕ) :
    (realHermiteCoeffScale * realHermiteCoeffScale) *
        (Real.sqrt 2 : ℂ) ^ r *
      (if Even r then (Real.Gamma ((((r : ℕ) : ℝ) + 1) / 2) : ℂ) else 0) =
      standardGaussianMoment r := by
  unfold standardGaussianMoment
  by_cases hr : Even r
  · rcases hr with ⟨s, hs⟩
    rw [if_pos ⟨s, hs⟩, if_pos ⟨s, hs⟩, hs, show s + s = 2 * s by ring]
    rw [show ((((2 * s : ℕ) : ℝ) + 1) / 2) = (s : ℝ) + 1 / 2 by
      norm_num
      ring]
    rw [Real.Gamma_nat_add_half]
    have hsqrt2pow : (Real.sqrt 2 : ℂ) ^ (2 * s) = (2 : ℂ) ^ s := by
      rw [show (Real.sqrt 2 : ℂ) ^ (2 * s) =
          ((Real.sqrt 2 : ℂ) ^ 2) ^ s by rw [pow_mul]]
      rw [sqrtTwoC_sq]
    rw [hsqrt2pow]
    have hcancel :
        (2 : ℂ) ^ s *
          ((((((2 * s - 1 : ℕ)‼ : ℕ) : ℝ) * Real.sqrt Real.pi /
                  2 ^ s : ℝ) : ℂ)) =
        (((2 * s - 1 : ℕ)‼ : ℕ) : ℂ) *
          (Real.sqrt Real.pi : ℂ) := by
      rw [Complex.ofReal_div, Complex.ofReal_mul]
      norm_num
      field_simp
    rw [mul_assoc, hcancel]
    calc
      realHermiteCoeffScale * realHermiteCoeffScale *
          ((((2 * s - 1 : ℕ)‼ : ℕ) : ℂ) *
            (Real.sqrt Real.pi : ℂ)) =
          (((2 * s - 1 : ℕ)‼ : ℕ) : ℂ) *
            ((realHermiteCoeffScale * realHermiteCoeffScale) *
              (Real.sqrt Real.pi : ℂ)) := by ring
      _ = (((2 * s - 1 : ℕ)‼ : ℕ) : ℂ) := by
            rw [realHermiteCoeffScale_sq_mul_sqrt_pi]
            ring
  · rw [if_neg hr, if_neg hr]
    ring

private noncomputable def gaussianMomentFunctional (p : Polynomial ℤ) : ℂ :=
  p.sum fun k a => (a : ℂ) * standardGaussianMoment k

private lemma gaussianMomentFunctional_add (p q : Polynomial ℤ) :
    gaussianMomentFunctional (p + q) =
      gaussianMomentFunctional p + gaussianMomentFunctional q := by
  unfold gaussianMomentFunctional
  rw [Polynomial.sum_add_index]
  · intro i
    simp
  · intro i a b
    norm_num
    ring

private lemma gaussianMomentFunctional_monomial (k : ℕ) (a : ℤ) :
    gaussianMomentFunctional (Polynomial.monomial k a) =
      (a : ℂ) * standardGaussianMoment k := by
  unfold gaussianMomentFunctional
  rw [Polynomial.sum_monomial_index]
  simp

private lemma gaussianMomentFunctional_neg (p : Polynomial ℤ) :
    gaussianMomentFunctional (-p) = -gaussianMomentFunctional p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [neg_add, gaussianMomentFunctional_add, gaussianMomentFunctional_add, hp, hq,
        neg_add]
  | monomial k a =>
      rw [← Polynomial.monomial_neg, gaussianMomentFunctional_monomial,
        gaussianMomentFunctional_monomial]
      push_cast
      ring

private lemma gaussianMomentFunctional_sub (p q : Polynomial ℤ) :
    gaussianMomentFunctional (p - q) =
      gaussianMomentFunctional p - gaussianMomentFunctional q := by
  rw [sub_eq_add_neg, gaussianMomentFunctional_add, gaussianMomentFunctional_neg]
  ring

private lemma gaussianMomentFunctional_smul_int (c : ℤ) (p : Polynomial ℤ) :
    gaussianMomentFunctional (c • p) =
      (c : ℂ) * gaussianMomentFunctional p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show c • (p + q) = c • p + c • q from smul_add c p q,
        gaussianMomentFunctional_add, gaussianMomentFunctional_add, hp, hq, mul_add]
  | monomial k a =>
      rw [show c • Polynomial.monomial k a = Polynomial.monomial k (c • a) from
          Polynomial.smul_monomial c k a]
      rw [gaussianMomentFunctional_monomial, gaussianMomentFunctional_monomial, smul_eq_mul]
      push_cast
      ring

private lemma gaussianMomentFunctional_finset_sum
    {α : Type*} (s : Finset α) (f : α → Polynomial ℤ) :
    gaussianMomentFunctional (∑ x ∈ s, f x) =
      ∑ x ∈ s, gaussianMomentFunctional (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gaussianMomentFunctional]
  | insert a s ha ih =>
      simp [ha, gaussianMomentFunctional_add, ih]

private lemma gaussianMomentFunctional_polynomial_sum
    (p : Polynomial ℤ) (f : ℕ → ℤ → Polynomial ℤ) :
    gaussianMomentFunctional (p.sum f) =
      p.sum fun k a => gaussianMomentFunctional (f k a) := by
  rw [Polynomial.sum_def, gaussianMomentFunctional_finset_sum]
  rfl

private noncomputable def gaussianMomentBilinear
    (p q : Polynomial ℤ) : ℂ :=
  p.sum fun k a =>
    q.sum fun l b => (a : ℂ) * (b : ℂ) * standardGaussianMoment (k + l)

private lemma gaussianMomentFunctional_mul (p q : Polynomial ℤ) :
    gaussianMomentFunctional (p * q) = gaussianMomentBilinear p q := by
  rw [Polynomial.mul_eq_sum_sum, gaussianMomentFunctional_finset_sum]
  unfold gaussianMomentBilinear
  apply Finset.sum_congr rfl
  intro i hi
  rw [gaussianMomentFunctional_polynomial_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [gaussianMomentFunctional_monomial]

private lemma gaussianMomentFunctional_X_mul_eq_derivative
    (p : Polynomial ℤ) :
    gaussianMomentFunctional (Polynomial.X * p) =
      gaussianMomentFunctional (Polynomial.derivative p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [mul_add, Polynomial.derivative_add, gaussianMomentFunctional_add,
        gaussianMomentFunctional_add, hp, hq]
  | monomial n a =>
      rw [Polynomial.X_mul_monomial, Polynomial.derivative_monomial,
        gaussianMomentFunctional_monomial, gaussianMomentFunctional_monomial,
        standardGaussianMoment_succ_eq_mul_pred]
      norm_num
      ring

private lemma derivative_hermite_int (n : ℕ) :
    Polynomial.derivative (Polynomial.hermite n) =
      (n : ℤ) • Polynomial.hermite (n - 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          cases n with
          | zero => simp
          | succ n =>
              have ih_succ :
                  Polynomial.derivative (Polynomial.hermite (n + 1)) =
                    ((n + 1 : ℕ) : ℤ) •
                      Polynomial.hermite ((n + 1) - 1) :=
                ih (n + 1) (by omega)
              have ih_n :
                  Polynomial.derivative (Polynomial.hermite n) =
                    (n : ℤ) • Polynomial.hermite (n - 1) :=
                ih n (by omega)
              rw [Polynomial.hermite_succ, Polynomial.derivative_sub,
                Polynomial.derivative_mul, Polynomial.derivative_X, ih_succ]
              rw [show (n + 1 - 1 : ℕ) = n by omega,
                map_zsmul Polynomial.derivative, ih_n,
                show (n + 1 + 1 - 1 : ℕ) = n + 1 by omega,
                Polynomial.hermite_succ,
                ih_n]
              norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
              ring

private lemma derivative_hermite_succ_int (n : ℕ) :
    Polynomial.derivative (Polynomial.hermite (n + 1)) =
      ((n + 1 : ℕ) : ℤ) • Polynomial.hermite n := by simpa using derivative_hermite_int (n + 1)

private noncomputable def hermiteStandardInner (n m : ℕ) : ℂ :=
  gaussianMomentFunctional (Polynomial.hermite n * Polynomial.hermite m)

private lemma hermiteStandardInner_comm (n m : ℕ) :
    hermiteStandardInner n m = hermiteStandardInner m n := by
  unfold hermiteStandardInner
  rw [mul_comm]

private lemma hermiteStandardInner_zero_zero : hermiteStandardInner 0 0 = 1 := by
  unfold hermiteStandardInner
  simp only [Polynomial.hermite_zero]
  rw [show Polynomial.C (1 : ℤ) * Polynomial.C (1 : ℤ) =
      Polynomial.C (1 : ℤ) by norm_num]
  unfold gaussianMomentFunctional standardGaussianMoment
  rw [Polynomial.sum_C_index]
  · norm_num
  · simp

private lemma hermiteStandardInner_succ_zero (n : ℕ) :
    hermiteStandardInner (n + 1) 0 = 0 := by
  unfold hermiteStandardInner
  simp only [Polynomial.hermite_zero]
  rw [show Polynomial.hermite (n + 1) * Polynomial.C (1 : ℤ) =
      Polynomial.hermite (n + 1) by norm_num]
  rw [Polynomial.hermite_succ,
    gaussianMomentFunctional_sub,
    gaussianMomentFunctional_X_mul_eq_derivative]
  simp

private lemma hermiteStandardInner_zero_succ (m : ℕ) :
    hermiteStandardInner 0 (m + 1) = 0 := by
  rw [hermiteStandardInner_comm]
  exact hermiteStandardInner_succ_zero m

private lemma hermiteStandardInner_succ_succ (n m : ℕ) :
    hermiteStandardInner (n + 1) (m + 1) =
      ((m + 1 : ℕ) : ℂ) * hermiteStandardInner n m := by
  unfold hermiteStandardInner
  rw [Polynomial.hermite_succ n, sub_mul, gaussianMomentFunctional_sub]
  have hX :
      gaussianMomentFunctional
          ((Polynomial.X * Polynomial.hermite n) *
            Polynomial.hermite (m + 1)) =
        gaussianMomentFunctional
          (Polynomial.derivative
            (Polynomial.hermite n * Polynomial.hermite (m + 1))) := by
    rw [mul_assoc]
    exact gaussianMomentFunctional_X_mul_eq_derivative _
  rw [hX,
    Polynomial.derivative_mul,
    gaussianMomentFunctional_add,
    sub_eq_iff_eq_add,
    derivative_hermite_succ_int,
    mul_smul_comm,
    gaussianMomentFunctional_smul_int]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

private theorem hermiteStandardInner_eq_factorial (n m : ℕ) :
    hermiteStandardInner n m =
      if n = m then (Nat.factorial n : ℂ) else 0 := by
  induction n generalizing m with
  | zero =>
      cases m with
      | zero => simp [hermiteStandardInner_zero_zero]
      | succ m => simp [hermiteStandardInner_zero_succ]
  | succ n ih =>
      cases m with
      | zero => simp [hermiteStandardInner_succ_zero]
      | succ m =>
          rw [hermiteStandardInner_succ_succ, ih m]
          by_cases h : n = m
          · subst m
            simp [Nat.factorial_succ]
          · have hs : n + 1 ≠ m + 1 := by omega
            simp [h]

private lemma hermite_support_subset_range_succ (n : ℕ) :
    (Polynomial.hermite n).support ⊆ Finset.range (n + 1) := by
  intro k hk
  rw [Finset.mem_range]
  by_contra h
  have hlt : n < k := by omega
  exact (Polynomial.mem_support_iff.mp hk)
    (Polynomial.coeff_hermite_of_lt hlt)

private lemma gaussianMomentBilinear_hermite_eq_finite_sum
    (n m : ℕ) :
    gaussianMomentBilinear (Polynomial.hermite n) (Polynomial.hermite m) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        ((Polynomial.hermite n).coeff k : ℂ) *
          ((Polynomial.hermite m).coeff l : ℂ) *
            standardGaussianMoment (k + l) := by
  unfold gaussianMomentBilinear
  rw [Polynomial.sum_eq_of_subset
    (p := Polynomial.hermite n)
    (f := fun k a =>
      (Polynomial.hermite m).sum fun l b =>
        (a : ℂ) * (b : ℂ) * standardGaussianMoment (k + l))
    (hf := by intro i; simp [Polynomial.sum_def])
    (s := Finset.range (n + 1))
    (hs := hermite_support_subset_range_succ n)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.sum_eq_of_subset
    (p := Polynomial.hermite m)
    (f := fun l b =>
      ((Polynomial.hermite n).coeff k : ℂ) * (b : ℂ) *
        standardGaussianMoment (k + l))
    (hf := by intro i; simp)
    (s := Finset.range (m + 1))
    (hs := hermite_support_subset_range_succ m)]

private lemma hermiteStandardInner_eq_finite_sum (n m : ℕ) :
    hermiteStandardInner n m =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        ((Polynomial.hermite n).coeff k : ℂ) *
          ((Polynomial.hermite m).coeff l : ℂ) *
            standardGaussianMoment (k + l) := by
  unfold hermiteStandardInner
  rw [gaussianMomentFunctional_mul]
  exact gaussianMomentBilinear_hermite_eq_finite_sum n m

private lemma realHermiteGeneratingExpansionCoeff_eq_scale_coeff
    (n k : ℕ) :
    realHermiteGeneratingExpansionCoeff n k =
      realHermiteCoeffScale *
        ((Real.sqrt 2 : ℂ) ^ k * ((Polynomial.hermite n).coeff k : ℂ)) := by
  simpa [realHermiteCoeffScale]
    using realHermiteGeneratingExpansionCoeff_eq_scaled_hermite_coeff n k

theorem realHermiteGenerating_iteratedDeriv_zero_expansion_monomial
    (n : ℕ) (t : ℝ) :
    iteratedDeriv n (realHermiteGenerating t) 0 =
      ∑ k ∈ Finset.range (n + 1),
        realHermiteGeneratingExpansionCoeff n k *
          complexMonomialGaussian k t := by
  rw [realHermiteGenerating_iteratedDeriv_zero_expansion]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [realHermiteGeneratingExpansionCoeff, complexMonomialGaussian]

theorem realHermiteGenerating_iteratedDeriv_zero_product_expansion
    (n m : ℕ) (t : ℝ) :
    iteratedDeriv n (realHermiteGenerating t) 0 *
        iteratedDeriv m (realHermiteGenerating t) 0 =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          (complexMonomialGaussian k t *
            complexMonomialGaussian l t) := by
  rw [realHermiteGenerating_iteratedDeriv_zero_expansion_monomial n t,
    realHermiteGenerating_iteratedDeriv_zero_expansion_monomial m t]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem realHermiteGenerating_iteratedDeriv_inner_finite_sum
    (n m : ℕ) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        iteratedDeriv m (realHermiteGenerating t) 0) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          (if Even (k + l) then
            (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ)
          else 0) := by
  calc
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        iteratedDeriv m (realHermiteGenerating t) 0) =
        ∫ t : ℝ,
          ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
            (realHermiteGeneratingExpansionCoeff n k *
                realHermiteGeneratingExpansionCoeff m l) *
              (complexMonomialGaussian k t *
                complexMonomialGaussian l t) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          rw [realHermiteGenerating_iteratedDeriv_zero_product_expansion]
    _ = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          (if Even (k + l) then
            (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ)
          else 0) := by
          exact complex_monomial_gaussian_finite_bilinear_integral_eq_ite
            (Finset.range (n + 1)) (Finset.range (m + 1))
            (realHermiteGeneratingExpansionCoeff n)
            (realHermiteGeneratingExpansionCoeff m)

theorem realHermiteGenerating_iteratedDeriv_inner_eq_zero_of_odd_add
    {n m : ℕ} (hodd : Odd (n + m)) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        iteratedDeriv m (realHermiteGenerating t) 0) = 0 := by
  rw [realHermiteGenerating_iteratedDeriv_inner_finite_sum]
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro l hl
  have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hl_le : l ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  by_cases hnk : Odd (n + k)
  · rw [realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_add hk_le hnk]
    ring
  · by_cases hml : Odd (m + l)
    · rw [realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_add hl_le hml]
      ring
    · have hnk_even : Even (n + k) := Nat.not_odd_iff_even.mp hnk
      have hml_even : Even (m + l) := Nat.not_odd_iff_even.mp hml
      have hkl_odd : Odd (k + l) := by grind [Nat.odd_add]
      have hkl_not_even : ¬ Even (k + l) := Nat.not_even_iff_odd.mpr hkl_odd
      simp [hkl_not_even]

theorem realHermiteGenerating_inner_finite_sum_eq_factorial
    (n m : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          (if Even (k + l) then
            (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ)
          else 0)) =
      if n = m then (Nat.factorial n : ℂ) else 0 := by
  rw [← hermiteStandardInner_eq_factorial n m, hermiteStandardInner_eq_finite_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [realHermiteGeneratingExpansionCoeff_eq_scale_coeff,
    realHermiteGeneratingExpansionCoeff_eq_scale_coeff]
  rw [← scaled_gamma_moment_eq_standard (k + l), pow_add]
  ring

theorem realHermiteGenerating_iteratedDeriv_inner_eq_factorial
    (n m : ℕ) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        iteratedDeriv m (realHermiteGenerating t) 0) =
      if n = m then (Nat.factorial n : ℂ) else 0 := by
  rw [realHermiteGenerating_iteratedDeriv_inner_finite_sum]
  exact realHermiteGenerating_inner_finite_sum_eq_factorial n m

theorem realHermiteGenerating_no_conj_interchange_of_finite_sum
    (n m : ℕ) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        iteratedDeriv m (realHermiteGenerating t) 0) =
      iteratedDeriv m
        (fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) 0) 0 := by
  have hleft := realHermiteGenerating_iteratedDeriv_inner_eq_factorial n m
  have hright :
      iteratedDeriv m
        (fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) 0) 0 =
        if n = m then (Nat.factorial n : ℂ) else 0 := by
    calc
      iteratedDeriv m
        (fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) 0) 0 =
          iteratedDeriv m
            (fun w : ℂ =>
              iteratedDeriv n (fun u : ℂ => Complex.exp (u * w)) 0) 0 := by
            congr 1
            funext w
            congr 1
            funext u
            rw [realHermiteGenerating_integral_mul]
      _ = if n = m then (Nat.factorial n : ℂ) else 0 := by
            simpa [eq_comm] using iteratedDeriv_iteratedDeriv_cexp_mul_at_zero m n
  exact hleft.trans hright.symm

theorem realHermiteGenerating_iteratedDeriv_zero_memLp
    (n : ℕ) :
    MemLp (fun t : ℝ => iteratedDeriv n (realHermiteGenerating t) 0)
      2 (volume : Measure ℝ) := by
  have hsum :
      MemLp
        (fun t : ℝ =>
          ∑ k ∈ Finset.range (n + 1),
            ((((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
                ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
                  iteratedDeriv (n - k)
                    (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) 0)) *
              ((t : ℂ) ^ k * Complex.exp (-(((t : ℂ) ^ 2) / 2)))))
        2 (volume : Measure ℝ) := by
    refine MeasureTheory.memLp_finsetSum (Finset.range (n + 1)) ?_
    intro k hk
    exact (complex_monomial_gaussian_memLp k).const_mul
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
          iteratedDeriv (n - k)
            (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) 0))
  simpa [realHermiteGenerating_iteratedDeriv_zero_expansion] using hsum

theorem realHermite1D_memLp (n : ℕ) :
    MemLp (realHermite1D n) 2 (volume : Measure ℝ) := by
  refine MeasureTheory.MemLp.ae_eq ?_
    ((realHermiteGenerating_iteratedDeriv_zero_memLp n).const_mul
      ((Real.sqrt (Nat.factorial n : ℝ) : ℂ) / (Nat.factorial n : ℂ)))
  filter_upwards with t
  rfl

theorem realHermite1D_inner_of_iteratedDeriv_inner (n m : ℕ)
    (hderiv :
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating t) 0 *
          star (iteratedDeriv m (realHermiteGenerating t) 0)) =
        if n = m then (Nat.factorial n : ℂ) else 0) :
    (∫ t : ℝ, realHermite1D n t * star (realHermite1D m t)) =
      if n = m then 1 else 0 := by
  unfold realHermite1D
  let cn : ℂ := (Real.sqrt (Nat.factorial n : ℝ) : ℂ) / (Nat.factorial n : ℂ)
  let cm : ℂ := (Real.sqrt (Nat.factorial m : ℝ) : ℂ) / (Nat.factorial m : ℂ)
  change (∫ t : ℝ,
      (cn * iteratedDeriv n (realHermiteGenerating t) 0) *
        star (cm * iteratedDeriv m (realHermiteGenerating t) 0)) =
      if n = m then 1 else 0
  have hcm : star cm = cm := by simp [cm, Complex.conj_ofReal]
  have hcombine :
      (∫ t : ℝ,
          (cn * iteratedDeriv n (realHermiteGenerating t) 0) *
            star (cm * iteratedDeriv m (realHermiteGenerating t) 0)) =
        (cn * cm) * ∫ t : ℝ,
          iteratedDeriv n (realHermiteGenerating t) 0 *
            star (iteratedDeriv m (realHermiteGenerating t) 0) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [star_mul, hcm]
    ring
  rw [hcombine, hderiv]
  by_cases hnm : n = m
  · subst m
    have hnorm : (cn * cm) * (Nat.factorial n : ℂ) = 1 := by
      have hfac_pos : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
      have hfac_ne : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have hsqrt_ne : (Real.sqrt (Nat.factorial n : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.2 hfac_pos).ne'
      have hsqrt_sq :
          (Real.sqrt (Nat.factorial n : ℝ) : ℂ) ^ 2 = (Nat.factorial n : ℂ) := by
        norm_num [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt hfac_pos)]
      simp only [cn, cm]
      rw [← hsqrt_sq]
      field_simp [hfac_ne, hsqrt_ne]
    simpa using hnorm
  · simp [hnm]

private lemma star_deriv_of_conj_symm {g : ℂ → ℂ}
    (hgdiff : Differentiable ℂ g)
    (hgstar : ∀ z : ℂ, star (g z) = g (star z)) (z : ℂ) :
    star (deriv g z) = deriv g (star z) := by
  have hderiv := (hgdiff z).hasDerivAt.conj_conj
  have hfun : (conj ∘ g ∘ conj) = g := by
    funext x
    change star (g (star x)) = g x
    simpa using hgstar (star x)
  have hderiv' : HasDerivAt g (star (deriv g z)) (star z) := by simpa [hfun] using hderiv
  exact hderiv'.deriv.symm

private lemma star_iteratedDeriv_of_conj_symm {f : ℂ → ℂ}
    (hf : ContDiff ℂ (⊤ : WithTop ℕ∞) f)
    (hfstar : ∀ z : ℂ, star (f z) = f (star z)) :
    ∀ n : ℕ, ∀ z : ℂ,
      star (iteratedDeriv n f z) = iteratedDeriv n f (star z) := by
  intro n
  induction n with
  | zero =>
      intro z
      simpa using hfstar z
  | succ n ih =>
      intro z
      simp only [iteratedDeriv_succ]
      exact star_deriv_of_conj_symm
        (g := iteratedDeriv n f)
        (hf.differentiable_iteratedDeriv n (by simp))
        ih
        z

theorem realHermiteGenerating_iteratedDeriv_zero_star (n : ℕ) (t : ℝ) :
    star (iteratedDeriv n (realHermiteGenerating t) 0) =
      iteratedDeriv n (realHermiteGenerating t) 0 := by
  have hcont : ContDiff ℂ (⊤ : WithTop ℕ∞) (realHermiteGenerating t) := by
    unfold realHermiteGenerating
    fun_prop
  have h := star_iteratedDeriv_of_conj_symm
    (f := realHermiteGenerating t) hcont
    (fun z => realHermiteGenerating_conj t z) n 0
  simpa using h

private theorem realHermiteGenerating_stft_integral_eq_phase_mul_halfCentered
    (n k : ℕ) (x ω : ℝ) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        iteratedDeriv k (realHermiteGenerating (t - x)) 0 *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))) =
      Complex.exp (-(Real.pi : ℂ) * Complex.I * ((x : ℂ) * (ω : ℂ))) *
        (∫ t : ℝ,
          iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
            iteratedDeriv k (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                ((inner ℝ ω t : ℝ) : ℂ))) := by
  let F : ℝ → ℂ := fun t =>
    iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
      iteratedDeriv k (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ ω t : ℝ) : ℂ))
  let G : ℝ → ℂ := fun t =>
    iteratedDeriv n (realHermiteGenerating t) 0 *
      iteratedDeriv k (realHermiteGenerating (t - x)) 0 *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ ω t : ℝ) : ℂ))
  let phase : ℂ := Complex.exp (-(Real.pi : ℂ) * Complex.I * ((x : ℂ) * (ω : ℂ)))
  let phaseInv : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * ((x : ℂ) * (ω : ℂ)))
  have hshift :
      (∫ t : ℝ, F t) =
        ∫ t : ℝ, F (t + (-(1 / 2 : ℝ) * x)) := by
    simpa [F] using
      (MeasureTheory.integral_add_right_eq_self
        (μ := volume) F (-(1 / 2 : ℝ) * x)).symm
  have hshift_eval :
      (∫ t : ℝ, F (t + (-(1 / 2 : ℝ) * x))) =
        phaseInv * ∫ t : ℝ, G t := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    dsimp [F, G, phaseInv]
    have htplus : t + -(1 / 2 : ℝ) * x + (1 / 2 : ℝ) * x = t := by ring
    have htminus : t + -(1 / 2 : ℝ) * x - (1 / 2 : ℝ) * x = t - x := by ring
    rw [htplus, htminus]
    rw [show
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            (((t + -(1 / 2 : ℝ) * x) * (starRingEnd ℝ) ω : ℝ) : ℂ)) =
          Complex.exp ((Real.pi : ℂ) * Complex.I * ((x : ℂ) * (ω : ℂ))) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((t * (starRingEnd ℝ) ω : ℝ) : ℂ)) by
      rw [← Complex.exp_add]
      congr 1
      simp
      ring_nf]
    ring
  have hF : (∫ t : ℝ, F t) = phaseInv * ∫ t : ℝ, G t := by rw [hshift, hshift_eval]
  have hphase : phase * phaseInv = 1 := by
    dsimp [phase, phaseInv]
    rw [← Complex.exp_add]
    ring_nf
    simp
  change (∫ t : ℝ, G t) = phase * (∫ t : ℝ, F t)
  rw [hF, ← mul_assoc, hphase, one_mul]

private lemma ambiguity_kernel_iteratedDeriv_factor (n : ℕ) (x ω : ℝ) :
    (fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ =>
            ∫ t : ℝ,
              realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
                realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
                  Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                    ((inner ℝ ω t : ℝ) : ℂ))) 0) =
      fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ =>
            Complex.exp
              (u * w +
                  ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                      (Real.sqrt 2 : ℂ) * u -
                star
                    (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                      (Real.sqrt 2 : ℂ)) * w)) 0 *
          Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  funext w
  rw [show
      (fun u : ℂ =>
        ∫ t : ℝ,
          realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
            realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                ((inner ℝ ω t : ℝ) : ℂ))) =
        fun u : ℂ =>
          Complex.exp
            (u * w +
                ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                    (Real.sqrt 2 : ℂ) * u -
              star
                  (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                    (Real.sqrt 2 : ℂ)) * w) *
            Complex.ofReal
              (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) by
      funext u
      simpa [inner, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using realHermiteGenerating_ambiguity_integral_independent_kernel x ω u w]
  rw [iteratedDeriv_mul_const_field]

private theorem realHermiteGenerating_stft_interchange_of_halfCentered_interchange
    (n k : ℕ) (x ω : ℝ)
    (hhalf :
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
          iteratedDeriv k (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ))) =
        iteratedDeriv k
          (fun w : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ,
                  realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
                    realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
                      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                        ((inner ℝ ω t : ℝ) : ℂ))) 0) 0) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        iteratedDeriv k (realHermiteGenerating (t - x)) 0 *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))) =
      iteratedDeriv k
        (fun v : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ,
                realHermiteGenerating t u *
                  realHermiteGenerating (t - x) v *
                    Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ ω t : ℝ) : ℂ))) 0) 0 := by
  let z : ℂ :=
    ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
      (Real.sqrt 2 : ℂ)
  let E : ℂ :=
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))
  let phase : ℂ := Complex.exp (-(Real.pi : ℂ) * Complex.I * ((x : ℂ) * (ω : ℂ)))
  have hleft :=
    realHermiteGenerating_stft_integral_eq_phase_mul_halfCentered n k x ω
  have hhalfKernel :
      iteratedDeriv k
        (fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ,
                realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
                  realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
                    Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ ω t : ℝ) : ℂ))) 0) 0 =
        ((-1 : ℂ) ^ k * complexHermite n k z) * E := by
    show iteratedDeriv k
        (fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ,
                realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
                  realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
                    Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ ω t : ℝ) : ℂ))) 0) 0 = _
    rw [ambiguity_kernel_iteratedDeriv_factor n x ω, iteratedDeriv_mul_const_field,
      iteratedDeriv_cexp_ambiguity_kernel_at_zero]
  have hstftKernel :
      iteratedDeriv k
        (fun v : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ,
                realHermiteGenerating t u *
                  realHermiteGenerating (t - x) v *
                    Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ ω t : ℝ) : ℂ))) 0) 0 =
        phase * (((-1 : ℂ) ^ k * complexHermite n k z) * E) := by
    have hfun :
        (fun v : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ,
                  realHermiteGenerating t u *
                    realHermiteGenerating (t - x) v *
                      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                        ((inner ℝ ω t : ℝ) : ℂ))) 0) =
          fun v : ℂ =>
            phase *
              (iteratedDeriv n
                (fun u : ℂ => Complex.exp (u * v + z * u - star z * v)) 0 * E) := by
      funext v
      rw [show
          (fun u : ℂ =>
            ∫ t : ℝ,
              realHermiteGenerating t u *
                realHermiteGenerating (t - x) v *
                  Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                    ((inner ℝ ω t : ℝ) : ℂ))) =
          fun u : ℂ =>
            phase * (Complex.exp (u * v + z * u - star z * v) * E) by
        funext u
        simpa [phase, z, E, inner, mul_assoc, mul_left_comm, mul_comm]
          using realHermiteGenerating_stft_integral_kernel x ω u v]
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_mul_const_field]
    rw [hfun,
      iteratedDeriv_const_mul_field,
      iteratedDeriv_mul_const_field,
      iteratedDeriv_cexp_ambiguity_kernel_at_zero]
  rw [hleft, hhalf, hhalfKernel, hstftKernel]

private theorem realHermite1D_stft_integral_formula_of_interchange
    (n k : ℕ) (x ω : ℝ)
    (hinterchange :
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating t) 0 *
          iteratedDeriv k (realHermiteGenerating (t - x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ))) =
        iteratedDeriv k
          (fun v : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ,
                  realHermiteGenerating t u *
                    realHermiteGenerating (t - x) v *
                      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                        ((inner ℝ ω t : ℝ) : ℂ))) 0) 0) :
    (∫ t : ℝ,
      realHermite1D n t *
        star (realHermite1D k (t - x)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))) =
      (-1 : ℂ) ^ k *
        Complex.exp (-(Real.pi : ℂ) * Complex.I * ((x : ℂ) * (ω : ℂ))) *
          (Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) *
            phi1D k n (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ))) := by
  let cn : ℂ := (Real.sqrt (Nat.factorial n : ℝ) : ℂ) / (Nat.factorial n : ℂ)
  let ck : ℂ := (Real.sqrt (Nat.factorial k : ℝ) : ℂ) / (Nat.factorial k : ℂ)
  let z : ℂ :=
    ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
      (Real.sqrt 2 : ℂ)
  let E : ℂ :=
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))
  let phase : ℂ :=
    Complex.exp (-(Real.pi : ℂ) * Complex.I * ((x : ℂ) * (ω : ℂ)))
  have hck_star : star ck = ck := by simp [ck, Complex.conj_ofReal]
  have hscale :
      cn * ck * complexHermite n k z = phi1D k n z := by
    let sn : ℂ := (Real.sqrt (Nat.factorial n : ℝ) : ℂ)
    let sk : ℂ := (Real.sqrt (Nat.factorial k : ℝ) : ℂ)
    let fn : ℂ := (Nat.factorial n : ℂ)
    let fk : ℂ := (Nat.factorial k : ℂ)
    have hfn_ne0 : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hfk_ne0 : (Nat.factorial k : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hfn_ne : fn ≠ 0 := by simpa [fn] using hfn_ne0
    have hfk_ne : fk ≠ 0 := by simpa [fk] using hfk_ne0
    have hfn_pos : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hfk_pos : 0 < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hsn_ne0 : ((Real.sqrt (Nat.factorial n : ℝ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hfn_pos).ne'
    have hsk_ne0 : ((Real.sqrt (Nat.factorial k : ℝ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hfk_pos).ne'
    have hsn_ne : sn ≠ 0 := by simpa [sn] using hsn_ne0
    have hsk_ne : sk ≠ 0 := by simpa [sk] using hsk_ne0
    have hsn_sq : sn ^ 2 = fn := by
      norm_num [sn, fn, ← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt hfn_pos)]
    have hsk_sq : sk ^ 2 = fk := by
      norm_num [sk, fk, ← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt hfk_pos)]
    have hsqrt_mul :
        ((Real.sqrt ((Nat.factorial n : ℝ) * (Nat.factorial k : ℝ))) : ℂ) =
          sn * sk := by
      rw [← Complex.ofReal_mul]
      congr 1
      rw [Real.sqrt_mul (le_of_lt hfn_pos)]
    have hscale_scalar : cn * ck = (sn * sk)⁻¹ := by
      change (sn / fn) * (sk / fk) = (sn * sk)⁻¹
      field_simp [hfn_ne, hfk_ne, hsn_ne, hsk_ne]
      rw [← hsn_sq, ← hsk_sq]
    unfold phi1D
    rw [hsqrt_mul, hscale_scalar]
  have hscaled_integral :
      (∫ t : ℝ,
        realHermite1D n t *
          star (realHermite1D k (t - x)) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ))) =
        (cn * ck) *
          ∫ t : ℝ,
            iteratedDeriv n (realHermiteGenerating t) 0 *
              iteratedDeriv k (realHermiteGenerating (t - x)) 0 *
                Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                  ((inner ℝ ω t : ℝ) : ℂ)) := by
    unfold realHermite1D
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [star_mul, hck_star, realHermiteGenerating_iteratedDeriv_zero_star]
    ring
  have hkernel :
      iteratedDeriv k
          (fun v : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ,
                  realHermiteGenerating t u *
                    realHermiteGenerating (t - x) v *
                      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                        ((inner ℝ ω t : ℝ) : ℂ))) 0) 0 =
        phase * (((-1 : ℂ) ^ k * complexHermite n k z) * E) := by
    have hfun :
        (fun v : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ,
                  realHermiteGenerating t u *
                    realHermiteGenerating (t - x) v *
                      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                        ((inner ℝ ω t : ℝ) : ℂ))) 0) =
          fun v : ℂ =>
            phase *
              (iteratedDeriv n
                (fun u : ℂ => Complex.exp (u * v + z * u - star z * v)) 0 * E) := by
      funext v
      rw [show
          (fun u : ℂ =>
            ∫ t : ℝ,
              realHermiteGenerating t u *
                realHermiteGenerating (t - x) v *
                  Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                    ((inner ℝ ω t : ℝ) : ℂ))) =
          fun u : ℂ =>
            phase * (Complex.exp (u * v + z * u - star z * v) * E) by
        funext u
        simpa [phase, z, E, inner, mul_assoc, mul_left_comm, mul_comm]
          using realHermiteGenerating_stft_integral_kernel x ω u v]
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_mul_const_field]
    rw [hfun,
      iteratedDeriv_const_mul_field,
      iteratedDeriv_mul_const_field,
      iteratedDeriv_cexp_ambiguity_kernel_at_zero]
  rw [hscaled_integral, hinterchange, hkernel]
  change (cn * ck) * (phase * (((-1 : ℂ) ^ k * complexHermite n k z) * E)) =
    (-1 : ℂ) ^ k * phase * (E * phi1D k n z)
  rw [← hscale]
  ring_nf

private theorem realHermite1D_stft_integral_formula_of_halfCentered_interchange
    (n k : ℕ) (x ω : ℝ)
    (hhalf :
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
          iteratedDeriv k (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ))) =
        iteratedDeriv k
          (fun w : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ,
                  realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
                    realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
                      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                        ((inner ℝ ω t : ℝ) : ℂ))) 0) 0) :
    (∫ t : ℝ,
      realHermite1D n t *
        star (realHermite1D k (t - x)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))) =
      (-1 : ℂ) ^ k *
        Complex.exp (-(Real.pi : ℂ) * Complex.I * ((x : ℂ) * (ω : ℂ))) *
          (Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) *
            phi1D k n (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ))) :=
  realHermite1D_stft_integral_formula_of_interchange n k x ω
    (realHermiteGenerating_stft_interchange_of_halfCentered_interchange n k x ω hhalf)

theorem realHermiteGenerating_iteratedDeriv_inner_of_no_conj_interchange
    (n m : ℕ)
    (hinterchange :
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating t) 0 *
          iteratedDeriv m (realHermiteGenerating t) 0) =
        iteratedDeriv m
          (fun w : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) 0) 0) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        star (iteratedDeriv m (realHermiteGenerating t) 0)) =
      if n = m then (Nat.factorial n : ℂ) else 0 := by
  calc
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        star (iteratedDeriv m (realHermiteGenerating t) 0)) =
        ∫ t : ℝ,
          iteratedDeriv n (realHermiteGenerating t) 0 *
            iteratedDeriv m (realHermiteGenerating t) 0 := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          rw [realHermiteGenerating_iteratedDeriv_zero_star]
    _ = iteratedDeriv m
          (fun w : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) 0) 0 := hinterchange
    _ = iteratedDeriv m
          (fun w : ℂ => iteratedDeriv n (fun u : ℂ => Complex.exp (u * w)) 0) 0 := by
          congr 1
          funext w
          congr 1
          funext u
          rw [realHermiteGenerating_integral_mul]
    _ = if n = m then (Nat.factorial n : ℂ) else 0 := by
          simpa [eq_comm] using iteratedDeriv_iteratedDeriv_cexp_mul_at_zero m n

theorem realHermite1D_inner_orthonormal_of_no_conj_interchange
    (hinterchange : ∀ n m : ℕ,
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating t) 0 *
          iteratedDeriv m (realHermiteGenerating t) 0) =
        iteratedDeriv m
          (fun w : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) 0) 0) :
    ∀ n m : Nat,
      (∫ t : ℝ, realHermite1D m t * star (realHermite1D n t)) =
        if n = m then (1 : ℂ) else 0 := by
  intro n m
  have hderiv :
      (∫ t : ℝ,
        iteratedDeriv m (realHermiteGenerating t) 0 *
          star (iteratedDeriv n (realHermiteGenerating t) 0)) =
        if m = n then (Nat.factorial m : ℂ) else 0 :=
    realHermiteGenerating_iteratedDeriv_inner_of_no_conj_interchange
      m n (hinterchange m n)
  simpa [eq_comm] using realHermite1D_inner_of_iteratedDeriv_inner m n hderiv

theorem realHermite1D_memLp_inner_orthonormal_of_no_conj_interchange
    (hmem : ∀ n : Nat, MemLp (realHermite1D n) 2 (volume : Measure ℝ))
    (hinterchange : ∀ n m : ℕ,
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating t) 0 *
          iteratedDeriv m (realHermiteGenerating t) 0) =
        iteratedDeriv m
          (fun w : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) 0) 0) :
    (∀ n : Nat, MemLp (realHermite1D n) 2 (volume : Measure ℝ)) ∧
      ∀ n m : Nat,
        (∫ t : ℝ, realHermite1D m t * star (realHermite1D n t)) =
          if n = m then (1 : ℂ) else 0 :=
  ⟨hmem, realHermite1D_inner_orthonormal_of_no_conj_interchange hinterchange⟩

/-- `realHermiteTensorRep`: real Hermite Tensor Rep. -/
noncomputable def realHermiteTensorRep {d : Nat} (alpha : Idx d) :
    RealVec d -> ℂ :=
  fun x => Finset.prod Finset.univ fun q : Fin d => realHermite1D (alpha q) (x q)

/-- `varphiKappa`: varphi Kappa. -/
noncomputable def varphiKappa {d : Nat} (kappa : MultiIndex d) : L2Real d := by
  classical
  exact
    if h : MemLp (realHermiteTensorRep kappa) 2
        (volume : Measure (RealVec d)) then
      h.toLp (realHermiteTensorRep kappa)
    else 0

/-- `realHermiteTensorL2`: real Hermite Tensor L2. -/
noncomputable def realHermiteTensorL2 {d : Nat} (alpha : Idx d) : L2Real d :=
  varphiKappa alpha

/-- `bKappaSeriesRep`: b Kappa Series Rep. -/
noncomputable def bKappaSeriesRep {d : Nat} (kappa : MultiIndex d)
    (U : Skappa d kappa) : RealVec d -> ℂ :=
  fun x => ∑' alpha : Idx d, coeffSkappa U alpha * realHermiteTensorRep alpha x

/-- `bKappa`: b Kappa. -/
noncomputable def bKappa {d : Nat} (kappa : MultiIndex d)
    (U : Skappa d kappa) : L2Real d :=
  ∑' alpha : Idx d, coeffSkappa U alpha • realHermiteTensorL2 alpha

/-- `bKappaRep`: b Kappa Rep. -/
noncomputable def bKappaRep {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) :
    RealVec d -> ℂ :=
  (bKappa kappa U : L2Real d)

theorem bKappa_smul
    {d : Nat} (kappa : MultiIndex d) (w : ℂ) (U : Skappa d kappa) :
    bKappa kappa (w • U) = w • bKappa kappa U := by
  classical
  unfold bKappa
  calc
    (∑' alpha : Idx d, coeffSkappa (w • U) alpha • realHermiteTensorL2 alpha) =
        ∑' alpha : Idx d, w • (coeffSkappa U alpha • realHermiteTensorL2 alpha) := by
          apply tsum_congr
          intro alpha
          change (w * U.coeff alpha) • realHermiteTensorL2 alpha =
            w • (U.coeff alpha • realHermiteTensorL2 alpha)
          rw [smul_smul]
    _ = w • ∑' alpha : Idx d, coeffSkappa U alpha • realHermiteTensorL2 alpha := by
          rw [tsum_const_smul'']

theorem realHermiteTensorL2_eq_toLp_of_memLp
    {d : Nat} (alpha : Idx d)
    (h : MemLp (realHermiteTensorRep alpha) 2
      (volume : Measure (RealVec d))) :
    realHermiteTensorL2 alpha = h.toLp (realHermiteTensorRep alpha) := by
  unfold realHermiteTensorL2 varphiKappa
  simp [h]

theorem realHermiteTensorL2_inner_eq_integral_of_memLp
    {d : Nat} (alpha beta : Idx d)
    (hα : MemLp (realHermiteTensorRep alpha) 2
      (volume : Measure (RealVec d)))
    (hβ : MemLp (realHermiteTensorRep beta) 2
      (volume : Measure (RealVec d))) :
    inner ℂ (realHermiteTensorL2 alpha) (realHermiteTensorL2 beta) =
      ∫ x : RealVec d,
        realHermiteTensorRep beta x * star (realHermiteTensorRep alpha x) := by
  rw [realHermiteTensorL2_eq_toLp_of_memLp alpha hα,
    realHermiteTensorL2_eq_toLp_of_memLp beta hβ, MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hα.coeFn_toLp, hβ.coeFn_toLp] with x hαx hβx
  rw [hαx, hβx]
  simp

theorem realHermiteTensorL2_orthonormal_of_memLp_integral
    {d : Nat}
    (hmem : ∀ alpha : Idx d,
      MemLp (realHermiteTensorRep alpha) 2
        (volume : Measure (RealVec d)))
    (hinner : ∀ alpha beta : Idx d,
      (∫ x : RealVec d,
        realHermiteTensorRep beta x * star (realHermiteTensorRep alpha x)) =
        if alpha = beta then (1 : ℂ) else 0) :
    Orthonormal ℂ (fun alpha : Idx d => realHermiteTensorL2 alpha) := by
  classical
  rw [orthonormal_iff_ite]
  intro alpha beta
  rw [realHermiteTensorL2_inner_eq_integral_of_memLp alpha beta
    (hmem alpha) (hmem beta)]
  exact hinner alpha beta

theorem realHermite1D_memLp_inner_orthonormal :
    (∀ n : Nat, MemLp (realHermite1D n) 2 (volume : Measure ℝ)) ∧
      ∀ n m : Nat,
        (∫ t : ℝ, realHermite1D m t * star (realHermite1D n t)) =
          if n = m then (1 : ℂ) else 0 := by
  /-
  Remaining one-dimensional analytic core.  The generating-function identity
  `realHermiteGenerating_integral_mul_conj` and the derivative coefficient
  lemma above reduce the Gram identity to differentiating under the integral.
  `MemLp` follows from the corresponding polynomial-times-Gaussian expression.
  -/
  refine realHermite1D_memLp_inner_orthonormal_of_no_conj_interchange ?_ ?_
  · intro n
    exact realHermite1D_memLp n
  · intro n m
    exact realHermiteGenerating_no_conj_interchange_of_finite_sum n m

theorem realHermiteTensorRep_memLp_of_realHermite1D_memLp
    {d : Nat} (alpha : Idx d)
    (hmem1 : ∀ n : Nat, MemLp (realHermite1D n) 2 (volume : Measure ℝ)) :
    MemLp (realHermiteTensorRep alpha) 2 (volume : Measure (RealVec d)) := by
  classical
  let g : (Fin d -> ℝ) -> ℂ :=
    fun y => ∏ q : Fin d, realHermite1D (alpha q) (y q)
  let μpi : Measure (Fin d -> ℝ) :=
    Measure.pi (fun _ : Fin d => (volume : Measure ℝ))
  have hg_integrable_norm_sq_pi :
      Integrable (fun y : Fin d -> ℝ => ‖g y‖ ^ (2 : ℝ)) μpi := by
    have hcoord :
        ∀ q : Fin d, Integrable
          (fun t : ℝ => ‖realHermite1D (alpha q) t‖ ^ (2 : ℝ)) := by
      intro q
      simpa using
        (hmem1 (alpha q)).integrable_norm_rpow
          (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    have hprod :
        Integrable
          (fun y : Fin d -> ℝ =>
            ∏ q : Fin d, ‖realHermite1D (alpha q) (y q)‖ ^ (2 : ℝ))
          μpi :=
      MeasureTheory.Integrable.fintype_prod
        (μ := fun _ : Fin d => (volume : Measure ℝ)) hcoord
    exact hprod.congr (Filter.Eventually.of_forall fun y => by
      simpa [g, norm_prod] using
        (Real.finsetProd_rpow
          (s := Finset.univ)
          (f := fun q : Fin d => ‖realHermite1D (alpha q) (y q)‖)
          (by
            intro q _hq
            exact norm_nonneg _)
          (2 : ℝ)))
  have hg_aesm_pi : AEStronglyMeasurable g μpi := by
    have hcoord_aesm :
        ∀ q : Fin d,
          AEStronglyMeasurable
            (fun y : Fin d -> ℝ => realHermite1D (alpha q) (y q)) μpi := by
      intro q
      have hqmp :
          MeasureTheory.Measure.QuasiMeasurePreserving (Function.eval q) μpi
            (volume : Measure ℝ) := by
        simpa [μpi] using
          (MeasureTheory.Measure.quasiMeasurePreserving_eval
            (μ := fun _ : Fin d => (volume : Measure ℝ)) q)
      exact
        (hmem1 (alpha q)).aestronglyMeasurable.comp_quasiMeasurePreserving
          hqmp
    change
      AEStronglyMeasurable
        (fun y : Fin d -> ℝ =>
          ∏ q : Fin d, realHermite1D (alpha q) (y q)) μpi
    exact
      Finset.univ.aestronglyMeasurable_fun_prod
        (μ := μpi)
        (f := fun q (y : Fin d -> ℝ) =>
          realHermite1D (alpha q) (y q))
        (by
          intro q _hq
          exact hcoord_aesm q)
  have hg_pi : MemLp g 2 μpi := by
    rw [← integrable_norm_rpow_iff hg_aesm_pi
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    simpa using hg_integrable_norm_sq_pi
  have hg : MemLp g 2 (volume : Measure (Fin d -> ℝ)) := hg_pi
  have hcomp :
      MemLp (g ∘ (WithLp.ofLp : RealVec d -> (Fin d -> ℝ))) 2
        (volume : Measure (RealVec d)) :=
    hg.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin d))
  refine MeasureTheory.MemLp.ae_eq ?_ hcomp
  filter_upwards with x
  simp only [Function.comp_apply, g, realHermiteTensorRep]

theorem realHermiteTensorRep_inner_of_realHermite1D_inner
    {d : Nat} (alpha beta : Idx d)
    (hinner1 : ∀ n m : Nat,
      (∫ t : ℝ, realHermite1D m t * star (realHermite1D n t)) =
        if n = m then (1 : ℂ) else 0) :
    (∫ x : RealVec d,
      realHermiteTensorRep beta x * star (realHermiteTensorRep alpha x)) =
      if alpha = beta then (1 : ℂ) else 0 := by
  calc
    (∫ x : RealVec d,
      realHermiteTensorRep beta x * star (realHermiteTensorRep alpha x))
        =
          ∫ x : RealVec d,
            (fun y : Fin d -> ℝ =>
              ∏ q : Fin d, realHermite1D (beta q) (y q) *
                star (realHermite1D (alpha q) (y q))) (WithLp.ofLp x) := by
          congr with x
          simp [realHermiteTensorRep, Finset.prod_mul_distrib]
    _ =
        ∫ y : Fin d -> ℝ,
          ∏ q : Fin d, realHermite1D (beta q) (y q) *
            star (realHermite1D (alpha q) (y q)) := by
          simpa [MeasurableEquiv.coe_toLp_symm] using
            (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp'
              (g := fun y : Fin d -> ℝ =>
                ∏ q : Fin d, realHermite1D (beta q) (y q) *
                  star (realHermite1D (alpha q) (y q)))
    _ = if alpha = beta then (1 : ℂ) else 0 := by
      have hprod :
          (∫ y : Fin d -> ℝ,
            ∏ q : Fin d, realHermite1D (beta q) (y q) *
              star (realHermite1D (alpha q) (y q))) =
            ∏ q : Fin d,
              ∫ t : ℝ, realHermite1D (beta q) t *
                star (realHermite1D (alpha q) t) := by
        exact
          MeasureTheory.integral_fintype_prod_volume_eq_prod
            (f := fun q (t : ℝ) =>
              realHermite1D (beta q) t * star (realHermite1D (alpha q) t))
      rw [hprod]
      simp_rw [hinner1]
      by_cases h : alpha = beta
      · subst beta
        simp
      · rw [if_neg h]
        have hq : ∃ q, alpha q ≠ beta q := by
          by_contra hnone
          apply h
          funext q
          by_contra hq
          exact hnone ⟨q, hq⟩
        rcases hq with ⟨q, hq⟩
        have hfactor : (if alpha q = beta q then (1 : ℂ) else 0) = 0 := by simp [hq]
        rw [show (∏ q : Fin d, if alpha q = beta q then (1 : ℂ) else 0) = 0 from by
          rw [Finset.prod_eq_zero_iff]
          exact ⟨q, Finset.mem_univ q, hfactor⟩]

theorem realHermiteTensorL2_orthonormal {d : Nat} :
    Orthonormal ℂ (fun alpha : Idx d => realHermiteTensorL2 alpha) := by
  /-
  This is the real-side analogue of `TensorBasis.PhiL2_orthonormal_family`.
  The remaining work is the real Hermite orthonormality package:
  one-dimensional real Hermite orthonormality in Lebesgue `L²(ℝ)`, tensorized
  over `RealVec d`, with `varphiKappa` unfolded through its `MemLp` branch.
  -/
  have hpackage :
      (∀ alpha : Idx d,
        MemLp (realHermiteTensorRep alpha) 2
          (volume : Measure (RealVec d))) ∧
        ∀ alpha beta : Idx d,
          (∫ x : RealVec d,
            realHermiteTensorRep beta x * star (realHermiteTensorRep alpha x)) =
            if alpha = beta then (1 : ℂ) else 0 := by
    exact
      ⟨fun alpha =>
          realHermiteTensorRep_memLp_of_realHermite1D_memLp alpha
            realHermite1D_memLp_inner_orthonormal.1,
        fun alpha beta =>
          realHermiteTensorRep_inner_of_realHermite1D_inner alpha beta
            realHermite1D_memLp_inner_orthonormal.2⟩
  exact realHermiteTensorL2_orthonormal_of_memLp_integral hpackage.1 hpackage.2

theorem varphiKappa_isL2Rep
    {d : Nat} (kappa : MultiIndex d) :
    IsL2Rep (varphiKappa kappa) (realHermiteTensorRep kappa) := by
  have hmem :
      MemLp (realHermiteTensorRep kappa) 2
        (volume : Measure (RealVec d)) :=
    realHermiteTensorRep_memLp_of_realHermite1D_memLp kappa
      realHermite1D_memLp_inner_orthonormal.1
  refine ⟨hmem, ?_⟩
  unfold varphiKappa
  simp [hmem]

theorem varphiKappa_coe_ae_eq_realHermiteTensorRep
    {d : Nat} (kappa : MultiIndex d) :
    ((varphiKappa kappa : L2Real d) : RealVec d -> ℂ)
      =ᵐ[(volume : Measure (RealVec d))] realHermiteTensorRep kappa := by
  rcases varphiKappa_isL2Rep kappa with ⟨hmem, h_eq⟩
  rw [← h_eq]
  exact hmem.coeFn_toLp

theorem summable_realHermiteTensorL2_coeff_smul_of_orthonormal
    {d : Nat} (kappa : MultiIndex d)
    (horth : Orthonormal ℂ (fun alpha : Idx d => realHermiteTensorL2 alpha))
    (U : Skappa d kappa) :
    Summable (fun alpha : Idx d => coeffSkappa U alpha • realHermiteTensorL2 alpha) := by
  classical
  have hOrthogonalFamily := horth.orthogonalFamily
  have hcoeff : Summable (fun alpha : Idx d => ‖coeffSkappa U alpha‖ ^ 2) := by
    simpa [coeffSkappa] using U.summable_norm_sq
  simpa using
    (hOrthogonalFamily.summable_iff_norm_sq_summable
      (fun alpha : Idx d => coeffSkappa U alpha)).2 hcoeff

theorem bKappa_coeff_recovery_of_realHermite_orthonormal
    {d : Nat} (kappa : MultiIndex d)
    (horth : Orthonormal ℂ (fun alpha : Idx d => realHermiteTensorL2 alpha))
    (U : Skappa d kappa) (beta : Idx d) :
    coeffSkappa U beta =
      inner ℂ (realHermiteTensorL2 beta) (bKappa kappa U) := by
  classical
  have hsummable :=
    summable_realHermiteTensorL2_coeff_smul_of_orthonormal kappa horth U
  unfold bKappa
  change coeffSkappa U beta =
    (innerSL ℂ (realHermiteTensorL2 beta))
      (∑' alpha : Idx d, coeffSkappa U alpha • realHermiteTensorL2 alpha)
  rw [ContinuousLinearMap.map_tsum
    (innerSL ℂ (realHermiteTensorL2 beta)) hsummable]
  rw [tsum_eq_single beta]
  · have hbb :
        inner ℂ (realHermiteTensorL2 beta) (realHermiteTensorL2 beta) = 1 := by
      simpa using orthonormal_iff_ite.mp horth beta beta
    change coeffSkappa U beta =
      inner ℂ (realHermiteTensorL2 beta)
        (coeffSkappa U beta • realHermiteTensorL2 beta)
    rw [inner_smul_right, hbb, mul_one]
  · intro alpha halpha
    have hba :
        inner ℂ (realHermiteTensorL2 beta) (realHermiteTensorL2 alpha) = 0 := by
      simpa [Ne.symm halpha] using orthonormal_iff_ite.mp horth beta alpha
    change
      (innerSL ℂ (realHermiteTensorL2 beta))
        (coeffSkappa U alpha • realHermiteTensorL2 alpha) = 0
    rw [innerSL_apply_apply, inner_smul_right, hba, mul_zero]

private theorem skappa_ext_coeff_from_realHermite
    {d : Nat} {kappa : MultiIndex d} {U V : Skappa d kappa}
    (hcoeff : ∀ alpha, coeffSkappa U alpha = coeffSkappa V alpha) :
    U = V := by
  cases U
  cases V
  simp only [coeffSkappa] at hcoeff
  congr
  funext alpha
  exact hcoeff alpha

theorem bKappa_injective_of_realHermite_coeff_recovery
    {d : Nat} (kappa : MultiIndex d)
    (hcoeff : ∀ (U : Skappa d kappa) (alpha : Idx d),
      coeffSkappa U alpha =
        inner ℂ (realHermiteTensorL2 alpha) (bKappa kappa U)) :
    Function.Injective (bKappa kappa) := by
  intro U V hUV
  apply skappa_ext_coeff_from_realHermite
  intro alpha
  rw [hcoeff U alpha, hcoeff V alpha, hUV]

theorem bKappa_injective_of_realHermite_orthonormal
    {d : Nat} (kappa : MultiIndex d)
    (horth : Orthonormal ℂ (fun alpha : Idx d => realHermiteTensorL2 alpha)) :
    Function.Injective (bKappa kappa) :=
  bKappa_injective_of_realHermite_coeff_recovery kappa
    (fun U alpha =>
      bKappa_coeff_recovery_of_realHermite_orthonormal kappa horth U alpha)

theorem bKappa_injective {d : Nat} (kappa : MultiIndex d) :
    Function.Injective (bKappa kappa) := bKappa_injective_of_realHermite_orthonormal kappa
    (realHermiteTensorL2_orthonormal (d := d))

theorem bKappaRep_isL2Rep
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) :
    IsL2Rep (bKappa kappa U) (bKappaRep kappa U) := by
  refine ⟨MeasureTheory.Lp.memLp (bKappa kappa U), ?_⟩
  apply MeasureTheory.Lp.ext
  exact (MeasureTheory.Lp.memLp (bKappa kappa U)).coeFn_toLp

private theorem ambiguityRep_varphiKappa_eq_tensorRep_integral
    {d : Nat} (kappa : MultiIndex d) (ξ : PhaseSpace d) :
    ambiguityRep (varphiKappa kappa) (varphiKappa kappa) ξ =
      ∫ t : RealVec d,
        realHermiteTensorRep kappa (t + ((1 / 2 : ℝ) • ξ.1)) *
          star (realHermiteTensorRep kappa (t - ((1 / 2 : ℝ) • ξ.1))) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ξ.2 t : ℝ) : ℂ)) := by
  unfold ambiguityRep
  apply MeasureTheory.integral_congr_ae
  have hcoe := varphiKappa_coe_ae_eq_realHermiteTensorRep kappa
  have hplus :
      (fun t : RealVec d =>
        ((varphiKappa kappa : L2Real d) : RealVec d -> ℂ)
          (t + ((1 / 2 : ℝ) • ξ.1)))
        =ᵐ[(volume : Measure (RealVec d))]
          fun t : RealVec d =>
            realHermiteTensorRep kappa (t + ((1 / 2 : ℝ) • ξ.1)) := by
    simpa [Function.comp_def] using
      ((MeasureTheory.measurePreserving_add_right
        (volume : Measure (RealVec d))
        (((1 / 2 : ℝ) • ξ.1))).quasiMeasurePreserving).ae_eq_comp hcoe
  have hminus :
      (fun t : RealVec d =>
        ((varphiKappa kappa : L2Real d) : RealVec d -> ℂ)
          (t - ((1 / 2 : ℝ) • ξ.1)))
        =ᵐ[(volume : Measure (RealVec d))]
          fun t : RealVec d =>
            realHermiteTensorRep kappa (t - ((1 / 2 : ℝ) • ξ.1)) := by
    simpa [Function.comp_def, sub_eq_add_neg] using
      ((MeasureTheory.measurePreserving_add_right
        (volume : Measure (RealVec d))
        (-((1 / 2 : ℝ) • ξ.1))).quasiMeasurePreserving).ae_eq_comp hcoe
  filter_upwards [hplus, hminus] with t hplus_t hminus_t
  rw [hplus_t, hminus_t]

/-- `TKappa`: T Kappa. -/
noncomputable def TKappa {d : Nat} :
    PhaseSpace d -> Cd d :=
  fun ξ q =>
    ((ξ.1 q : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ξ.2 q : ℂ)) /
      (Real.sqrt 2 : ℂ)

/-- `QKappa`: Q Kappa. -/
noncomputable def QKappa {d : Nat} :
    PhaseSpace d -> ℝ :=
  fun ξ => (‖ξ.1‖ ^ 2 + (2 * Real.pi) ^ 2 * ‖ξ.2‖ ^ 2) / 4

/-- `WKappa`: W Kappa. -/
noncomputable def WKappa {d : Nat} :
    PhaseSpace d -> ℝ :=
  fun ξ => Real.exp (-(QKappa ξ))

theorem WKappa_pos {d : Nat} (ξ : PhaseSpace d) :
    0 < WKappa ξ := by
  dsimp [WKappa]
  positivity

/-- `phaseSpacePolyEval`: phase Space Poly Eval. -/
noncomputable def phaseSpacePolyEval {d : Nat}
    (ξ : PhaseSpace d) : (Fin d ⊕ Fin d) -> ℂ
  | Sum.inl q => (ξ.1 q : ℂ)
  | Sum.inr q => (ξ.2 q : ℂ)

/-- `IsPhaseSpacePolynomial`: Is Phase Space Polynomial. -/
def IsPhaseSpacePolynomial {d : Nat} (P : PhaseSpace d -> ℂ) : Prop :=
  ∃ p : MvPolynomial (Fin d ⊕ Fin d) ℂ,
    ∀ ξ : PhaseSpace d, P ξ = MvPolynomial.eval (phaseSpacePolyEval ξ) p

private noncomputable def tKappaCoordPoly {d : Nat} (q : Fin d) :
    MvPolynomial (Fin d ⊕ Fin d) ℂ :=
  MvPolynomial.C ((Real.sqrt 2 : ℂ)⁻¹) *
    (MvPolynomial.X (Sum.inl q) -
      MvPolynomial.C ((2 * Real.pi : ℂ) * Complex.I) * MvPolynomial.X (Sum.inr q))

private noncomputable def tKappaConjCoordPoly {d : Nat} (q : Fin d) :
    MvPolynomial (Fin d ⊕ Fin d) ℂ :=
  MvPolynomial.C ((Real.sqrt 2 : ℂ)⁻¹) *
    (MvPolynomial.X (Sum.inl q) +
      MvPolynomial.C ((2 * Real.pi : ℂ) * Complex.I) * MvPolynomial.X (Sum.inr q))

private theorem tKappaCoordPoly_eval
    {d : Nat} (_kappa : MultiIndex d) (ξ : PhaseSpace d) (q : Fin d) :
    MvPolynomial.eval (phaseSpacePolyEval ξ) (tKappaCoordPoly q) =
      TKappa ξ q := by
  simp [tKappaCoordPoly, TKappa, phaseSpacePolyEval, div_eq_mul_inv]
  ring

private theorem tKappaConjCoordPoly_eval
    {d : Nat} (_kappa : MultiIndex d) (ξ : PhaseSpace d) (q : Fin d) :
    MvPolynomial.eval (phaseSpacePolyEval ξ) (tKappaConjCoordPoly q) =
      star (TKappa ξ q) := by
  simp [tKappaConjCoordPoly, TKappa, phaseSpacePolyEval, div_eq_mul_inv]
  ring

private noncomputable def complexHermiteMvPolynomial {σ : Type*}
    (m n : Nat) (Z Zstar : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  Finset.sum (Finset.range (min m n + 1)) fun j =>
    MvPolynomial.C (((-1 : ℂ) ^ j) * (Nat.factorial j : ℂ) *
      (Nat.choose m j : ℂ) * (Nat.choose n j : ℂ)) *
      Z ^ (m - j) * Zstar ^ (n - j)

private theorem complexHermiteMvPolynomial_eval
    {σ : Type*} (ev : σ -> ℂ)
    (m n : Nat) (Z Zstar : MvPolynomial σ ℂ) (z : ℂ)
    (hZ : MvPolynomial.eval ev Z = z)
    (hZstar : MvPolynomial.eval ev Zstar = star z) :
    MvPolynomial.eval ev (complexHermiteMvPolynomial m n Z Zstar) =
      complexHermite m n z := by
  simp [complexHermiteMvPolynomial, complexHermite, hZ, hZstar, mul_assoc]

private noncomputable def phi1DMvPolynomial {σ : Type*}
    (k n : Nat) (Z Zstar : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  MvPolynomial.C
      (((Real.sqrt ((Nat.factorial n : ℝ) * (Nat.factorial k : ℝ))) : ℂ)⁻¹) *
    complexHermiteMvPolynomial n k Z Zstar

private theorem phi1DMvPolynomial_eval
    {σ : Type*} (ev : σ -> ℂ)
    (k n : Nat) (Z Zstar : MvPolynomial σ ℂ) (z : ℂ)
    (hZ : MvPolynomial.eval ev Z = z)
    (hZstar : MvPolynomial.eval ev Zstar = star z) :
    MvPolynomial.eval ev (phi1DMvPolynomial k n Z Zstar) = phi1D k n z := by
  simp [phi1DMvPolynomial, phi1D,
    complexHermiteMvPolynomial_eval ev n k Z Zstar z hZ hZstar]

private noncomputable def PhiTKappaMvPolynomial {d : Nat}
    (kappa alpha : MultiIndex d) : MvPolynomial (Fin d ⊕ Fin d) ℂ :=
  Finset.prod Finset.univ fun q : Fin d =>
    phi1DMvPolynomial (kappa q) (alpha q)
      (tKappaCoordPoly q) (tKappaConjCoordPoly q)

private theorem PhiTKappaMvPolynomial_eval
    {d : Nat} (kappa alpha : MultiIndex d) (ξ : PhaseSpace d) :
    MvPolynomial.eval (phaseSpacePolyEval ξ) (PhiTKappaMvPolynomial kappa alpha) =
      Phi kappa alpha (TKappa ξ) := by
  simp only [PhiTKappaMvPolynomial, Phi, MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro q _hq
  exact phi1DMvPolynomial_eval (phaseSpacePolyEval ξ) (kappa q) (alpha q)
    (tKappaCoordPoly q) (tKappaConjCoordPoly q) (TKappa ξ q)
    (tKappaCoordPoly_eval kappa ξ q) (tKappaConjCoordPoly_eval kappa ξ q)

/-- `PKappa`: P Kappa. -/
noncomputable def PKappa {d : Nat} (kappa : MultiIndex d) :
    PhaseSpace d -> ℂ :=
  fun ξ =>
    (-1 : ℂ) ^ ((Finset.univ : Finset (Fin d)).sum fun q => kappa q) *
      Phi kappa kappa (TKappa ξ)

theorem PKappa_isPolynomial {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    IsPhaseSpacePolynomial (PKappa kappa) := by
  let _ := hd
  refine ⟨MvPolynomial.C
      ((-1 : ℂ) ^ ((Finset.univ : Finset (Fin d)).sum fun q => kappa q)) *
    PhiTKappaMvPolynomial kappa kappa, ?_⟩
  intro ξ
  simp [PKappa, PhiTKappaMvPolynomial_eval]

private lemma complexHermite_self_zero (k : Nat) :
    complexHermite k k 0 = (-1 : ℂ) ^ k * (Nat.factorial k : ℂ) := by
  unfold complexHermite
  simp only [Nat.min_self]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j hj hjne
    have hjlt : j < k := by
      have hjle : j < k + 1 := Finset.mem_range.mp hj
      omega
    have hpos : 0 < k - j := Nat.sub_pos_of_lt hjlt
    simp [hpos.ne']
  · intro hknot
    exact False.elim (hknot (by simp))

private lemma phi1D_self_zero_ne (k : Nat) : phi1D k k 0 ≠ 0 := by
  rw [phi1D, complexHermite_self_zero]
  apply mul_ne_zero
  · apply inv_ne_zero
    norm_num [Nat.factorial_ne_zero]
  · apply mul_ne_zero
    · simp
    · exact_mod_cast Nat.factorial_ne_zero k

private lemma Phi_self_zero_ne {d : Nat} (kappa : MultiIndex d) :
    Phi kappa kappa (0 : Cd d) ≠ 0 := by
  unfold Phi
  apply Finset.prod_ne_zero_iff.mpr
  intro q _hq
  simpa using phi1D_self_zero_ne (kappa q)

private lemma TKappa_zero {d : Nat} :
    TKappa ((0, 0) : PhaseSpace d) = 0 := by
  ext q
  simp [TKappa]

private noncomputable def stftModelPhase {d : Nat} (kappa : MultiIndex d) :
    PhaseSpace d -> ℂ :=
  fun ξ =>
    (-1 : ℂ) ^ ((Finset.univ : Finset (Fin d)).sum fun q => kappa q) *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ))

private theorem stftModelPhase_norm {d : Nat} (kappa : MultiIndex d)
    (ξ : PhaseSpace d) :
    ‖stftModelPhase kappa ξ‖ = 1 := by
  unfold stftModelPhase
  rw [norm_mul]
  have hpow :
      ‖((-1 : ℂ) ^
          ((Finset.univ : Finset (Fin d)).sum fun q => kappa q))‖ = 1 := by simp
  have hexp :
      ‖Complex.exp (-(Real.pi : ℂ) * Complex.I *
          ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre :
        (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  rw [hpow, hexp]
  norm_num

private theorem stftRep_varphiKappa_realHermiteTensorL2_eq_tensorRep_integral
    {d : Nat} (kappa alpha : MultiIndex d) (ξ : PhaseSpace d) :
    stftRep (varphiKappa kappa) (realHermiteTensorL2 alpha) ξ =
      ∫ t : RealVec d,
        realHermiteTensorRep alpha t *
          star (realHermiteTensorRep kappa (t - ξ.1)) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ξ.2 t : ℝ) : ℂ)) := by
  unfold stftRep
  apply MeasureTheory.integral_congr_ae
  have hsig :
      ((realHermiteTensorL2 alpha : L2Real d) : RealVec d -> ℂ)
        =ᵐ[(volume : Measure (RealVec d))] realHermiteTensorRep alpha := by
    simpa [realHermiteTensorL2] using varphiKappa_coe_ae_eq_realHermiteTensorRep alpha
  have hwin :
      (fun t : RealVec d =>
        ((varphiKappa kappa : L2Real d) : RealVec d -> ℂ) (t - ξ.1))
        =ᵐ[(volume : Measure (RealVec d))]
          fun t : RealVec d => realHermiteTensorRep kappa (t - ξ.1) := by
    simpa [Function.comp_def, sub_eq_add_neg] using
      ((MeasureTheory.measurePreserving_add_right
        (volume : Measure (RealVec d))
        (-ξ.1)).quasiMeasurePreserving).ae_eq_comp
          (varphiKappa_coe_ae_eq_realHermiteTensorRep kappa)
  filter_upwards [hsig, hwin] with t hsig_t hwin_t
  rw [hsig_t, hwin_t]

private theorem tensorRep_stft_integral_eq_prod_oneD
    {d : Nat} (kappa alpha : MultiIndex d) (ξ : PhaseSpace d) :
    (∫ t : RealVec d,
      realHermiteTensorRep alpha t *
        star (realHermiteTensorRep kappa (t - ξ.1)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ξ.2 t : ℝ) : ℂ))) =
      ∏ q : Fin d,
        ∫ s : ℝ,
          realHermite1D (alpha q) s *
            star (realHermite1D (kappa q) (s - ξ.1 q)) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                ((inner ℝ (ξ.2 q) s : ℝ) : ℂ)) := by
  classical
  let f : (q : Fin d) → ℝ → ℂ := fun q s =>
    realHermite1D (alpha q) s *
      star (realHermite1D (kappa q) (s - ξ.1 q)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ (ξ.2 q) s : ℝ) : ℂ))
  have h_real_to_pi :
      (∫ t : RealVec d,
        realHermiteTensorRep alpha t *
          star (realHermiteTensorRep kappa (t - ξ.1)) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ξ.2 t : ℝ) : ℂ))) =
        ∫ y : Fin d → ℝ, ∏ q : Fin d, f q (y q) := by
    calc
      (∫ t : RealVec d,
        realHermiteTensorRep alpha t *
          star (realHermiteTensorRep kappa (t - ξ.1)) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ξ.2 t : ℝ) : ℂ))) =
          ∫ t : RealVec d,
            (fun y : Fin d → ℝ => ∏ q : Fin d, f q (y q)) (WithLp.ofLp t) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with t
            simp only [f, realHermiteTensorRep, Finset.prod_mul_distrib]
            rw [star_prod]
            have hphase :
                Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                    ((inner ℝ ξ.2 t : ℝ) : ℂ)) =
                  ∏ q : Fin d,
                    Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ (ξ.2 q) (WithLp.ofLp t q) : ℝ) : ℂ)) := by
              rw [show
                  -(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ ξ.2 t : ℝ) : ℂ) =
                    ∑ q : Fin d,
                      -(2 * Real.pi : ℂ) * Complex.I *
                        ((inner ℝ (ξ.2 q) (WithLp.ofLp t q) : ℝ) : ℂ) by
                simp only [PiLp.inner_apply, Complex.ofReal_sum, Finset.mul_sum]]
              rw [Complex.exp_sum]
            rw [hphase]
            simp [mul_assoc, mul_comm, sub_eq_add_neg]
      _ = ∫ y : Fin d → ℝ, ∏ q : Fin d, f q (y q) := by
            simpa [MeasurableEquiv.coe_toLp_symm] using
              (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp'
                (g := fun y : Fin d → ℝ => ∏ q : Fin d, f q (y q))
  rw [h_real_to_pi]
  exact
    MeasureTheory.integral_fintype_prod_volume_eq_prod
      (f := fun q (t : ℝ) => f q t)

private theorem prod_oneDRealHermiteSTFT_closed_eq_model
    {d : Nat} (kappa alpha : MultiIndex d) (ξ : PhaseSpace d) :
    (∏ q : Fin d,
      (-1 : ℂ) ^ kappa q *
        Complex.exp (-(Real.pi : ℂ) * Complex.I * (((ξ.1 q : ℝ) : ℂ) * (ξ.2 q : ℂ))) *
          (Complex.ofReal
            (Real.exp (-(((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4))) *
            phi1D (kappa q) (alpha q) (TKappa ξ q))) =
      stftModelPhase kappa ξ *
        (((WKappa ξ : ℝ) : ℂ) *
          Phi kappa alpha (TKappa ξ)) := by
  classical
  let coordQ : Fin d → ℝ := fun q =>
    (((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4)
  have hQsum : QKappa ξ = ∑ q : Fin d, coordQ q := by
    simp only [QKappa, coordQ, EuclideanSpace.real_norm_sq_eq]
    ring_nf
    rw [Finset.sum_add_distrib]
    simp only [one_div, Finset.sum_mul]
    rw [add_comm, Finset.mul_sum]
  have hprod_pow :
      (∏ q : Fin d, (-1 : ℂ) ^ kappa q) =
        (-1 : ℂ) ^ ((Finset.univ : Finset (Fin d)).sum fun q => kappa q) := by
    simpa using
      (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin d))
        (fun q : Fin d => kappa q) (-1 : ℂ))
  have hprod_phase :
      (∏ q : Fin d,
        Complex.exp (-(Real.pi : ℂ) * Complex.I *
          (((ξ.1 q : ℝ) : ℂ) * (ξ.2 q : ℂ)))) =
        Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) := by
    calc
      (∏ q : Fin d,
        Complex.exp (-(Real.pi : ℂ) * Complex.I *
          (((ξ.1 q : ℝ) : ℂ) * (ξ.2 q : ℂ)))) =
          Complex.exp
            (∑ q : Fin d,
              -(Real.pi : ℂ) * Complex.I * (((ξ.1 q : ℝ) : ℂ) * (ξ.2 q : ℂ))) := by
            rw [Complex.exp_sum]
      _ = Complex.exp (-(Real.pi : ℂ) * Complex.I *
            ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) := by
            congr 1
            simp only [PiLp.inner_apply, Complex.ofReal_sum, Finset.mul_sum]
            simp [inner, mul_assoc, mul_comm]
  have hprod_exp :
      (∏ q : Fin d, Complex.ofReal (Real.exp (-(coordQ q)))) =
        Complex.ofReal (Real.exp (-(QKappa ξ))) := by
    calc
      (∏ q : Fin d, Complex.ofReal (Real.exp (-(coordQ q)))) =
          ∏ q : Fin d, Complex.exp (((-(coordQ q) : ℝ) : ℂ)) := by
            apply Finset.prod_congr rfl
            intro q _hq
            rw [Complex.ofReal_exp]
      _ = Complex.exp (∑ q : Fin d, (((-(coordQ q) : ℝ) : ℂ))) := by rw [Complex.exp_sum]
      _ = Complex.ofReal (Real.exp (-(QKappa ξ))) := by
            rw [Complex.ofReal_exp]
            congr 1
            rw [← Complex.ofReal_sum]
            congr 1
            rw [hQsum, Finset.sum_neg_distrib]
  calc
    (∏ q : Fin d,
      (-1 : ℂ) ^ kappa q *
        Complex.exp (-(Real.pi : ℂ) * Complex.I * (((ξ.1 q : ℝ) : ℂ) * (ξ.2 q : ℂ))) *
          (Complex.ofReal
            (Real.exp (-(((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4))) *
            phi1D (kappa q) (alpha q) (TKappa ξ q))) =
        (∏ q : Fin d, (-1 : ℂ) ^ kappa q) *
          (∏ q : Fin d,
            Complex.exp (-(Real.pi : ℂ) * Complex.I *
              (((ξ.1 q : ℝ) : ℂ) * (ξ.2 q : ℂ)))) *
            ((∏ q : Fin d, Complex.ofReal (Real.exp (-(coordQ q)))) *
              (∏ q : Fin d, phi1D (kappa q) (alpha q) (TKappa ξ q))) := by
          simp [coordQ, Finset.prod_mul_distrib, mul_assoc]
    _ = stftModelPhase kappa ξ *
        (((WKappa ξ : ℝ) : ℂ) * Phi kappa alpha (TKappa ξ)) := by
          rw [hprod_pow, hprod_phase, hprod_exp]
          simp [stftModelPhase, WKappa, Phi, mul_assoc]

private noncomputable def oneDWindowAmbiguityFactor
    (k : Nat) (x ω : ℝ) : ℂ :=
  ∫ t : ℝ,
    realHermite1D k (t + (1 / 2 : ℝ) * x) *
      star (realHermite1D k (t - (1 / 2 : ℝ) * x)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ))

private theorem oneDWindowAmbiguityFactor_eq_scaled_iteratedDeriv_integral
    (k : Nat) (x ω : ℝ) :
    oneDWindowAmbiguityFactor k x ω =
      ((Nat.factorial k : ℂ)⁻¹) *
        ∫ t : ℝ,
          iteratedDeriv k (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
            iteratedDeriv k (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                ((inner ℝ ω t : ℝ) : ℂ)) := by
  let c : ℂ := (Real.sqrt (Nat.factorial k : ℝ) : ℂ) / (Nat.factorial k : ℂ)
  have hc_star : star c = c := by simp [c]
  have hfac_ne : (Nat.factorial k : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hsqrt_sq :
      ((Real.sqrt (Nat.factorial k : ℝ) : ℂ) ^ (2 : ℕ)) =
        (Nat.factorial k : ℂ) := by
    rw [← Complex.ofReal_pow]
    congr 1
    rw [Real.sq_sqrt]
    positivity
  have hc_sq : c * c = (Nat.factorial k : ℂ)⁻¹ := by
    dsimp [c]
    field_simp [hfac_ne]
    rw [hsqrt_sq]
  unfold oneDWindowAmbiguityFactor realHermite1D
  change (∫ t : ℝ,
      (c * iteratedDeriv k (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0) *
        star (c * iteratedDeriv k (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ))) =
    ((Nat.factorial k : ℂ)⁻¹) *
      ∫ t : ℝ,
        iteratedDeriv k (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
          iteratedDeriv k (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ))
  rw [← hc_sq, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [star_mul, hc_star, realHermiteGenerating_iteratedDeriv_zero_star]
  ring

private theorem oneDWindowAmbiguityFactor_zero
    (x ω : ℝ) :
    oneDWindowAmbiguityFactor 0 x ω =
      Complex.ofReal
        (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  simpa [oneDWindowAmbiguityFactor, realHermite1D_zero, inner, div_eq_mul_inv, mul_assoc,
    mul_comm, mul_left_comm]
    using realHermiteGenerating_ambiguity_integral_conj_kernel x ω 0 0

private noncomputable def realHermite1DExpansionScale (n : ℕ) : ℂ :=
  (Real.sqrt (Nat.factorial n : ℝ) : ℂ) / (Nat.factorial n : ℂ)

private theorem realHermiteGenerating_pi_quarter_mul_self :
    (((Real.pi ^ (-(4 : ℝ)⁻¹) : ℝ) : ℂ) *
        ((Real.pi ^ (-(4 : ℝ)⁻¹) : ℝ) : ℂ)) =
      ((Real.pi ^ (-(2 : ℝ)⁻¹) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← Real.rpow_add Real.pi_pos]
  norm_num

private theorem realHermiteGeneratingExpansionCoeff_one_zero :
    realHermiteGeneratingExpansionCoeff 1 0 = 0 :=
  realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_sub (by norm_num)

private theorem realHermiteGeneratingExpansionCoeff_one_one :
    realHermiteGeneratingExpansionCoeff 1 1 =
      ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * (Real.sqrt 2 : ℂ) := by
  simp [realHermiteGeneratingExpansionCoeff]

private theorem realHermiteGeneratingExpansionCoeff_two_zero :
    realHermiteGeneratingExpansionCoeff 2 0 =
      -(((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) := by
  simp only [realHermiteGeneratingExpansionCoeff, one_div, Nat.choose_zero_right, Nat.cast_one,
    pow_zero, mul_one, tsub_zero, one_mul]
  rw [show iteratedDeriv 2
      (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) 0 = (-1 : ℂ) by
    simpa using iteratedDeriv_cexp_neg_sq_div_two_zero_of_two_mul 1]
  ring

private theorem realHermiteGeneratingExpansionCoeff_two_one :
    realHermiteGeneratingExpansionCoeff 2 1 = 0 :=
  realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_sub (by norm_num)

private theorem realHermiteGeneratingExpansionCoeff_two_two :
    realHermiteGeneratingExpansionCoeff 2 2 =
      ((2 : ℂ) * ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) := by
  simp only [realHermiteGeneratingExpansionCoeff, one_div, Nat.choose_self, Nat.cast_one, one_mul,
    tsub_self, iteratedDeriv_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    neg_zero, zero_div, Complex.exp_zero, mul_one]
  rw [sqrtTwoC_sq]
  ring

private theorem realHermiteGeneratingExpansionCoeff_three_zero :
    realHermiteGeneratingExpansionCoeff 3 0 = 0 :=
  realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_sub (by norm_num)

private theorem realHermiteGeneratingExpansionCoeff_three_one :
    realHermiteGeneratingExpansionCoeff 3 1 =
      -((3 : ℂ) * ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        (Real.sqrt 2 : ℂ)) := by
  simp only [realHermiteGeneratingExpansionCoeff, one_div, Nat.choose_one_right, Nat.cast_ofNat,
    pow_one, Nat.add_one_sub_one]
  rw [show iteratedDeriv 2
      (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) 0 = (-1 : ℂ) by
    simpa using iteratedDeriv_cexp_neg_sq_div_two_zero_of_two_mul 1]
  ring

private theorem realHermiteGeneratingExpansionCoeff_three_two :
    realHermiteGeneratingExpansionCoeff 3 2 = 0 :=
  realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_sub (by norm_num)

private theorem realHermiteGeneratingExpansionCoeff_three_three :
  realHermiteGeneratingExpansionCoeff 3 3 =
      (2 : ℂ) * ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        (Real.sqrt 2 : ℂ) := by
  simp only [realHermiteGeneratingExpansionCoeff, one_div, Nat.choose_self, Nat.cast_one, one_mul,
    tsub_self, iteratedDeriv_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    neg_zero, zero_div, Complex.exp_zero, mul_one]
  rw [show (Real.sqrt 2 : ℂ) ^ 3 = 2 * (Real.sqrt 2 : ℂ) by
    rw [show (Real.sqrt 2 : ℂ) ^ 3 =
        (Real.sqrt 2 : ℂ) ^ 2 * (Real.sqrt 2 : ℂ) by ring]
    rw [sqrtTwoC_sq]]
  ring

private theorem realHermite1D_finite_monomial_expansion
    (n : ℕ) (t : ℝ) :
    realHermite1D n t =
      ∑ k ∈ Finset.range (n + 1),
        realHermite1DExpansionScale n *
          realHermiteGeneratingExpansionCoeff n k *
            complexMonomialGaussian k t := by
  rw [realHermite1D, realHermiteGenerating_iteratedDeriv_zero_expansion_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [realHermite1DExpansionScale]
  ring

private noncomputable def oneDWindowAmbiguityMonomialKernel
    (k l : ℕ) (x ω t : ℝ) : ℂ :=
  complexMonomialGaussian k (t + (1 / 2 : ℝ) * x) *
    star (complexMonomialGaussian l (t - (1 / 2 : ℝ) * x)) *
      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ))

private theorem star_complex_monomial_gaussian (k : ℕ) (t : ℝ) :
    star (complexMonomialGaussian k t) = complexMonomialGaussian k t := by
  unfold complexMonomialGaussian
  rw [star_mul, star_pow]
  have ht : star ((t : ℂ)) = (t : ℂ) := Complex.conj_ofReal t
  rw [ht]
  have hexp : star (Complex.exp (-(((t : ℂ) ^ 2) / 2))) =
      Complex.exp (-(((t : ℂ) ^ 2) / 2)) := by
    change (starRingEnd ℂ) (Complex.exp (-(((t : ℂ) ^ 2) / 2))) =
      Complex.exp (-(((t : ℂ) ^ 2) / 2))
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_div₀, map_pow, Complex.conj_ofReal]
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
    rw [htwo]
  rw [hexp]
  ring

private theorem oneDWindowAmbiguityMonomialKernel_one_one_eq_shifted_moment_integrand
    (x ω t : ℝ) :
    oneDWindowAmbiguityMonomialKernel 1 1 x ω t =
      (((t : ℂ) ^ 2 - (x : ℂ) ^ 2 / 4) *
        Complex.exp (-((t : ℂ) ^ 2 + (x : ℂ) ^ 2 / 4)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) := by
  rw [oneDWindowAmbiguityMonomialKernel, star_complex_monomial_gaussian]
  unfold complexMonomialGaussian
  simp only [pow_one]
  have hpoly :
      ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) *
          ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) =
        (t : ℂ) ^ 2 - (x : ℂ) ^ 2 / 4 := by
    norm_num
    ring
  have hexp :
      Complex.exp (-((((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2)) *
          Complex.exp (-((((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2)) =
        Complex.exp (-((t : ℂ) ^ 2 + (x : ℂ) ^ 2 / 4)) := by
    rw [← Complex.exp_add]
    congr 1
    norm_num
    ring
  have hinner : ((inner ℝ ω t : ℝ) : ℂ) = (ω : ℂ) * (t : ℂ) := by
    simp [inner]
    ring
  rw [hinner]
  calc
    ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) *
          Complex.exp (-((((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2)) *
        (((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) *
          Complex.exp (-((((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2))) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) =
      (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) *
          ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ)) *
        (Complex.exp (-((((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2)) *
          Complex.exp (-((((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2))) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) := by ring
    _ = (((t : ℂ) ^ 2 - (x : ℂ) ^ 2 / 4) *
        Complex.exp (-((t : ℂ) ^ 2 + (x : ℂ) ^ 2 / 4)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) := by rw [hpoly, hexp]

private noncomputable def oneDWindowAmbiguityShiftedModulatedGaussian
    (x ω t : ℝ) : ℂ :=
  Complex.exp (-((t : ℂ) ^ 2 + (x : ℂ) ^ 2 / 4)) *
    Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))

private theorem gaussianPDFReal_zero_half_scalar :
    (Real.sqrt 2 : ℂ) *
        (((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) =
      ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hreal : Real.sqrt 2 * ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹) =
      Real.pi ^ (-(1 / 2 : ℝ)) := by
    have hsqrt2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp [hsqrt2]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos]
    norm_num
  exact_mod_cast hreal

private theorem gaussianPDFReal_zero_half_eq (t : ℝ) :
    ((ProbabilityTheory.gaussianPDFReal 0 (1 / 2 : NNReal) t : ℝ) : ℂ) =
      ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-((t : ℂ) ^ 2)) := by
  unfold ProbabilityTheory.gaussianPDFReal
  norm_num
  rw [gaussianPDFReal_zero_half_scalar]

private theorem integral_gaussian_zero_half_eq_density (f : ℝ → ℂ) :
    (∫ t : ℝ, f t ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))) =
      ∫ t : ℝ, ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-((t : ℂ) ^ 2)) * f t := by
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
    (μ := (0 : ℝ)) (v := (1 / 2 : NNReal)) (f := f) (by norm_num)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  change ((ProbabilityTheory.gaussianPDFReal 0 (1 / 2 : NNReal) t : ℝ) : ℂ) *
      f t = _
  rw [gaussianPDFReal_zero_half_eq]

private theorem gaussian_half_moment_eq_iteratedDeriv (n : ℕ) (z : ℂ) :
    (∫ x : ℝ, ((x : ℂ) ^ n * Complex.exp (z * (x : ℂ)))
        ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))) =
      iteratedDeriv n (fun z : ℂ => Complex.exp (z ^ 2 / 4)) z := by
  rw [← ProbabilityTheory.iteratedDeriv_complexMGF
    (X := fun x : ℝ => x)
    (μ := ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))
    (z := z) (n := n) (by simp)]
  congr 1
  funext y
  change ProbabilityTheory.complexMGF id
      (ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)) y =
    Complex.exp (y ^ 2 / 4)
  rw [ProbabilityTheory.complexMGF_id_gaussianReal
    (μ := (0 : ℝ)) (v := (1 / 2 : NNReal)) y]
  congr 1
  norm_num
  ring

private theorem gaussian_half_integrable_monomial_exp (n : ℕ) (z : ℂ) :
    Integrable (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (z * (t : ℂ)))
      (ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)) := by
  exact ProbabilityTheory.integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
    (X := fun t : ℝ => t)
    (μ := ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))
    (z := z) (by simp) n

private theorem deriv_div_two (z : ℂ) :
    deriv (fun c : ℂ => c / 2) z = (1 / 2 : ℂ) := by
  rw [show (fun c : ℂ => c / 2) = fun c : ℂ => (1 / 2 : ℂ) * c by
    funext c
    ring]
  rw [deriv_const_mul]
  · rw [deriv_id'']
    ring
  · fun_prop

private theorem deriv_sq_div_four (z : ℂ) :
    deriv (fun c : ℂ => c ^ 2 / 4) z = z / 2 := by
  rw [show (fun c : ℂ => c ^ 2 / 4) = fun c : ℂ => (1 / 4 : ℂ) * c ^ 2 by
    funext c
    ring]
  rw [deriv_const_mul]
  · rw [deriv_pow_field]
    ring
  · fun_prop

private theorem deriv_cexp_sq_div_four (z : ℂ) :
    deriv (fun c : ℂ => Complex.exp (c ^ 2 / 4)) z =
      (z / 2) * Complex.exp (z ^ 2 / 4) := by
  rw [deriv_cexp]
  · rw [deriv_sq_div_four]
    ring
  · fun_prop

private theorem deriv_mgf_two_formula (z : ℂ) :
    deriv (fun c : ℂ => (c / 2) * Complex.exp (c ^ 2 / 4)) z =
      ((1 / 2 : ℂ) + z ^ 2 / 4) * Complex.exp (z ^ 2 / 4) := by
  rw [show (fun c : ℂ => c / 2 * Complex.exp (c ^ 2 / 4)) =
      (fun c : ℂ => c / 2) * (fun c : ℂ => Complex.exp (c ^ 2 / 4)) by rfl]
  rw [deriv_mul]
  · rw [deriv_div_two, deriv_cexp_sq_div_four]
    ring
  · fun_prop
  · fun_prop

private theorem deriv_mgf_three_formula (z : ℂ) :
    deriv (fun c : ℂ =>
      ((1 / 2 : ℂ) + c ^ 2 / 4) * Complex.exp (c ^ 2 / 4)) z =
      ((3 / 4 : ℂ) * z + z ^ 3 / 8) * Complex.exp (z ^ 2 / 4) := by
  rw [show (fun c : ℂ =>
      ((1 / 2 : ℂ) + c ^ 2 / 4) * Complex.exp (c ^ 2 / 4)) =
      (fun c : ℂ => (1 / 2 : ℂ) + c ^ 2 / 4) *
        (fun c : ℂ => Complex.exp (c ^ 2 / 4)) by rfl]
  rw [deriv_mul]
  · rw [show deriv (fun c : ℂ => (1 / 2 : ℂ) + c ^ 2 / 4) z = z / 2 by
      rw [show (fun c : ℂ => (1 / 2 : ℂ) + c ^ 2 / 4) =
          (fun _ : ℂ => (1 / 2 : ℂ)) + (fun c : ℂ => c ^ 2 / 4) by rfl]
      rw [deriv_add (by fun_prop) (by fun_prop), deriv_const, deriv_sq_div_four]
      ring]
    rw [deriv_cexp_sq_div_four]
    ring
  · fun_prop
  · fun_prop

private theorem deriv_mgf_four_formula (z : ℂ) :
    deriv (fun c : ℂ =>
      ((3 / 4 : ℂ) * c + c ^ 3 / 8) * Complex.exp (c ^ 2 / 4)) z =
      ((3 / 4 : ℂ) + (3 / 4 : ℂ) * z ^ 2 + z ^ 4 / 16) *
        Complex.exp (z ^ 2 / 4) := by
  rw [show (fun c : ℂ =>
      ((3 / 4 : ℂ) * c + c ^ 3 / 8) * Complex.exp (c ^ 2 / 4)) =
      (fun c : ℂ => (3 / 4 : ℂ) * c + c ^ 3 / 8) *
        (fun c : ℂ => Complex.exp (c ^ 2 / 4)) by rfl]
  rw [deriv_mul]
  · rw [show deriv (fun c : ℂ => (3 / 4 : ℂ) * c + c ^ 3 / 8) z =
        (3 / 4 : ℂ) + (3 / 8 : ℂ) * z ^ 2 by
      have h := ((hasDerivAt_id z).const_mul (3 / 4 : ℂ)).add
          ((hasDerivAt_pow 3 z).div_const (8 : ℂ))
      convert h.deriv using 1
      · congr 1
      · push_cast
        ring]
    rw [deriv_cexp_sq_div_four]
    ring
  · fun_prop
  · fun_prop

private theorem deriv_mgf_five_formula (z : ℂ) :
    deriv (fun c : ℂ =>
      ((3 / 4 : ℂ) + (3 / 4 : ℂ) * c ^ 2 + c ^ 4 / 16) *
        Complex.exp (c ^ 2 / 4)) z =
      ((15 / 8 : ℂ) * z + (5 / 8 : ℂ) * z ^ 3 + z ^ 5 / 32) *
        Complex.exp (z ^ 2 / 4) := by
  rw [show (fun c : ℂ =>
      ((3 / 4 : ℂ) + (3 / 4 : ℂ) * c ^ 2 + c ^ 4 / 16) *
        Complex.exp (c ^ 2 / 4)) =
      (fun c : ℂ => (3 / 4 : ℂ) + (3 / 4 : ℂ) * c ^ 2 + c ^ 4 / 16) *
        (fun c : ℂ => Complex.exp (c ^ 2 / 4)) by rfl]
  rw [deriv_mul]
  · rw [show
        deriv (fun c : ℂ => (3 / 4 : ℂ) + (3 / 4 : ℂ) * c ^ 2 + c ^ 4 / 16) z =
          (3 / 2 : ℂ) * z + z ^ 3 / 4 by
        have h := ((hasDerivAt_const z (3 / 4 : ℂ)).add
            (((hasDerivAt_pow 2 z).const_mul (3 / 4 : ℂ)))).add
            (((hasDerivAt_pow 4 z).div_const (16 : ℂ)))
        convert h.deriv using 1
        · congr 1
        · push_cast
          ring]
    rw [deriv_cexp_sq_div_four]
    ring
  · fun_prop
  · fun_prop

private theorem deriv_mgf_six_formula (z : ℂ) :
    deriv (fun c : ℂ =>
      ((15 / 8 : ℂ) * c + (5 / 8 : ℂ) * c ^ 3 + c ^ 5 / 32) *
        Complex.exp (c ^ 2 / 4)) z =
      ((15 / 8 : ℂ) + (45 / 16 : ℂ) * z ^ 2 + (15 / 32 : ℂ) * z ^ 4 +
          z ^ 6 / 64) * Complex.exp (z ^ 2 / 4) := by
  rw [show (fun c : ℂ =>
      ((15 / 8 : ℂ) * c + (5 / 8 : ℂ) * c ^ 3 + c ^ 5 / 32) *
        Complex.exp (c ^ 2 / 4)) =
      (fun c : ℂ => (15 / 8 : ℂ) * c + (5 / 8 : ℂ) * c ^ 3 + c ^ 5 / 32) *
        (fun c : ℂ => Complex.exp (c ^ 2 / 4)) by rfl]
  rw [deriv_mul]
  · rw [show
        deriv (fun c : ℂ => (15 / 8 : ℂ) * c + (5 / 8 : ℂ) * c ^ 3 + c ^ 5 / 32) z =
          (15 / 8 : ℂ) + (15 / 8 : ℂ) * z ^ 2 + (5 / 32 : ℂ) * z ^ 4 by
        have h := (((hasDerivAt_id z).const_mul (15 / 8 : ℂ)).add
            (((hasDerivAt_pow 3 z).const_mul (5 / 8 : ℂ)))).add
            (((hasDerivAt_pow 5 z).div_const (32 : ℂ)))
        convert h.deriv using 1
        · congr 1
        · push_cast
          ring]
    rw [deriv_cexp_sq_div_four]
    ring
  · fun_prop
  · fun_prop

private theorem deriv_mgf_one_fun :
    deriv (fun c : ℂ => Complex.exp (c ^ 2 / 4)) =
      fun c : ℂ => (c / 2) * Complex.exp (c ^ 2 / 4) := by
  funext c
  rw [deriv_cexp_sq_div_four]

private theorem deriv_mgf_two_fun :
    deriv (fun c : ℂ => (c / 2) * Complex.exp (c ^ 2 / 4)) =
      fun c : ℂ => ((1 / 2 : ℂ) + c ^ 2 / 4) * Complex.exp (c ^ 2 / 4) := by
  funext c
  rw [deriv_mgf_two_formula]

private theorem deriv_mgf_three_fun :
    deriv (fun c : ℂ => ((1 / 2 : ℂ) + c ^ 2 / 4) * Complex.exp (c ^ 2 / 4)) =
      fun c : ℂ => ((3 / 4 : ℂ) * c + c ^ 3 / 8) * Complex.exp (c ^ 2 / 4) := by
  funext c
  rw [deriv_mgf_three_formula]

private theorem deriv_mgf_four_fun :
    deriv (fun c : ℂ => ((3 / 4 : ℂ) * c + c ^ 3 / 8) * Complex.exp (c ^ 2 / 4)) =
      fun c : ℂ =>
        ((3 / 4 : ℂ) + (3 / 4 : ℂ) * c ^ 2 + c ^ 4 / 16) * Complex.exp (c ^ 2 / 4) := by
  funext c
  rw [deriv_mgf_four_formula]

private theorem deriv_mgf_five_fun :
    deriv (fun c : ℂ =>
        ((3 / 4 : ℂ) + (3 / 4 : ℂ) * c ^ 2 + c ^ 4 / 16) * Complex.exp (c ^ 2 / 4)) =
      fun c : ℂ =>
        ((15 / 8 : ℂ) * c + (5 / 8 : ℂ) * c ^ 3 + c ^ 5 / 32) * Complex.exp (c ^ 2 / 4) := by
  funext c
  rw [deriv_mgf_five_formula]

private theorem iteratedDeriv_two_cexp_sq_div_four (z : ℂ) :
    iteratedDeriv 2 (fun c : ℂ => Complex.exp (c ^ 2 / 4)) z =
      ((1 / 2 : ℂ) + z ^ 2 / 4) * Complex.exp (z ^ 2 / 4) := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [deriv_mgf_one_fun, deriv_mgf_two_formula]

private theorem iteratedDeriv_four_cexp_sq_div_four (z : ℂ) :
    iteratedDeriv 4 (fun c : ℂ => Complex.exp (c ^ 2 / 4)) z =
      ((3 / 4 : ℂ) + (3 / 4 : ℂ) * z ^ 2 + z ^ 4 / 16) *
        Complex.exp (z ^ 2 / 4) := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [deriv_mgf_one_fun, deriv_mgf_two_fun, deriv_mgf_three_fun, deriv_mgf_four_formula]

private theorem iteratedDeriv_six_cexp_sq_div_four (z : ℂ) :
    iteratedDeriv 6 (fun c : ℂ => Complex.exp (c ^ 2 / 4)) z =
      ((15 / 8 : ℂ) + (45 / 16 : ℂ) * z ^ 2 + (15 / 32 : ℂ) * z ^ 4 +
          z ^ 6 / 64) *
        Complex.exp (z ^ 2 / 4) := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [deriv_mgf_one_fun, deriv_mgf_two_fun, deriv_mgf_three_fun, deriv_mgf_four_fun,
    deriv_mgf_five_fun, deriv_mgf_six_formula]

private theorem gaussian_half_moment_zero (z : ℂ) :
    (∫ t : ℝ, Complex.exp (z * (t : ℂ))
        ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))) =
      Complex.exp (z ^ 2 / 4) := by simpa using gaussian_half_moment_eq_iteratedDeriv 0 z

private theorem gaussian_half_moment_two (z : ℂ) :
    (∫ t : ℝ, (t : ℂ) ^ 2 * Complex.exp (z * (t : ℂ))
        ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))) =
      ((1 / 2 : ℂ) + z ^ 2 / 4) * Complex.exp (z ^ 2 / 4) := by
  rw [gaussian_half_moment_eq_iteratedDeriv, iteratedDeriv_two_cexp_sq_div_four]

private theorem gaussian_half_moment_four (z : ℂ) :
    (∫ t : ℝ, (t : ℂ) ^ 4 * Complex.exp (z * (t : ℂ))
        ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))) =
      ((3 / 4 : ℂ) + (3 / 4 : ℂ) * z ^ 2 + z ^ 4 / 16) *
        Complex.exp (z ^ 2 / 4) := by
  rw [gaussian_half_moment_eq_iteratedDeriv, iteratedDeriv_four_cexp_sq_div_four]

private theorem gaussian_half_moment_six (z : ℂ) :
    (∫ t : ℝ, (t : ℂ) ^ 6 * Complex.exp (z * (t : ℂ))
        ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))) =
      ((15 / 8 : ℂ) + (45 / 16 : ℂ) * z ^ 2 + (15 / 32 : ℂ) * z ^ 4 +
          z ^ 6 / 64) *
        Complex.exp (z ^ 2 / 4) := by
  rw [gaussian_half_moment_eq_iteratedDeriv, iteratedDeriv_six_cexp_sq_div_four]

private theorem gaussian_half_quartic_exp_integral (A C z : ℂ) :
    (∫ t : ℝ,
        ((2 : ℂ) * (t : ℂ) ^ 4 - A * (t : ℂ) ^ 2 + C) *
          Complex.exp (z * (t : ℂ))
        ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))) =
      ((2 : ℂ) * ((3 / 4 : ℂ) + (3 / 4 : ℂ) * z ^ 2 + z ^ 4 / 16) -
          A * ((1 / 2 : ℂ) + z ^ 2 / 4) + C) * Complex.exp (z ^ 2 / 4) := by
  let μ := ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)
  let f4 : ℝ → ℂ := fun t => (t : ℂ) ^ 4 * Complex.exp (z * (t : ℂ))
  let f2 : ℝ → ℂ := fun t => (t : ℂ) ^ 2 * Complex.exp (z * (t : ℂ))
  let f0 : ℝ → ℂ := fun t => Complex.exp (z * (t : ℂ))
  have hf4 : Integrable f4 μ := by simpa [f4, μ] using gaussian_half_integrable_monomial_exp 4 z
  have hf2 : Integrable f2 μ := by simpa [f2, μ] using gaussian_half_integrable_monomial_exp 2 z
  have hf0 : Integrable f0 μ := by simpa [f0, μ] using gaussian_half_integrable_monomial_exp 0 z
  have hsplit :
      (∫ t : ℝ,
        ((2 : ℂ) * (t : ℂ) ^ 4 - A * (t : ℂ) ^ 2 + C) *
          Complex.exp (z * (t : ℂ)) ∂μ) =
        (2 : ℂ) * ∫ t : ℝ, f4 t ∂μ -
          A * ∫ t : ℝ, f2 t ∂μ + C * ∫ t : ℝ, f0 t ∂μ := by
    calc
      (∫ t : ℝ,
        ((2 : ℂ) * (t : ℂ) ^ 4 - A * (t : ℂ) ^ 2 + C) *
          Complex.exp (z * (t : ℂ)) ∂μ) =
          ∫ t : ℝ, ((2 : ℂ) * f4 t - A * f2 t) + C * f0 t ∂μ := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with t
            simp [f4, f2, f0]
            ring
      _ = ∫ t : ℝ, ((2 : ℂ) * f4 t - A * f2 t) ∂μ +
            ∫ t : ℝ, C * f0 t ∂μ := by
            rw [MeasureTheory.integral_add]
            · exact (hf4.const_mul 2).sub (hf2.const_mul A)
            · exact hf0.const_mul C
      _ = ((2 : ℂ) * ∫ t : ℝ, f4 t ∂μ -
            A * ∫ t : ℝ, f2 t ∂μ) + C * ∫ t : ℝ, f0 t ∂μ := by
            rw [MeasureTheory.integral_sub]
            · simp only [MeasureTheory.integral_const_mul]
            · exact hf4.const_mul 2
            · exact hf2.const_mul A
      _ = (2 : ℂ) * ∫ t : ℝ, f4 t ∂μ -
          A * ∫ t : ℝ, f2 t ∂μ + C * ∫ t : ℝ, f0 t ∂μ := by ring
  rw [hsplit]
  simp only [f4, f2, f0, μ]
  rw [gaussian_half_moment_four, gaussian_half_moment_two, gaussian_half_moment_zero]
  ring

private theorem gaussian_half_sextic_exp_integral (A B C z : ℂ) :
    (∫ t : ℝ,
        ((4 / 3 : ℂ) * (t : ℂ) ^ 6 - A * (t : ℂ) ^ 4 +
            B * (t : ℂ) ^ 2 + C) *
          Complex.exp (z * (t : ℂ))
        ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))) =
      ((4 / 3 : ℂ) *
          ((15 / 8 : ℂ) + (45 / 16 : ℂ) * z ^ 2 + (15 / 32 : ℂ) * z ^ 4 +
            z ^ 6 / 64) -
        A * ((3 / 4 : ℂ) + (3 / 4 : ℂ) * z ^ 2 + z ^ 4 / 16) +
        B * ((1 / 2 : ℂ) + z ^ 2 / 4) + C) * Complex.exp (z ^ 2 / 4) := by
  let μ := ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)
  let f6 : ℝ → ℂ := fun t => (t : ℂ) ^ 6 * Complex.exp (z * (t : ℂ))
  let f4 : ℝ → ℂ := fun t => (t : ℂ) ^ 4 * Complex.exp (z * (t : ℂ))
  let f2 : ℝ → ℂ := fun t => (t : ℂ) ^ 2 * Complex.exp (z * (t : ℂ))
  let f0 : ℝ → ℂ := fun t => Complex.exp (z * (t : ℂ))
  have hf6 : Integrable f6 μ := by simpa [f6, μ] using gaussian_half_integrable_monomial_exp 6 z
  have hf4 : Integrable f4 μ := by simpa [f4, μ] using gaussian_half_integrable_monomial_exp 4 z
  have hf2 : Integrable f2 μ := by simpa [f2, μ] using gaussian_half_integrable_monomial_exp 2 z
  have hf0 : Integrable f0 μ := by simpa [f0, μ] using gaussian_half_integrable_monomial_exp 0 z
  have hsplit :
      (∫ t : ℝ,
        ((4 / 3 : ℂ) * (t : ℂ) ^ 6 - A * (t : ℂ) ^ 4 +
            B * (t : ℂ) ^ 2 + C) *
          Complex.exp (z * (t : ℂ)) ∂μ) =
        (4 / 3 : ℂ) * ∫ t : ℝ, f6 t ∂μ -
          A * ∫ t : ℝ, f4 t ∂μ +
          B * ∫ t : ℝ, f2 t ∂μ + C * ∫ t : ℝ, f0 t ∂μ := by
    calc
      (∫ t : ℝ,
        ((4 / 3 : ℂ) * (t : ℂ) ^ 6 - A * (t : ℂ) ^ 4 +
            B * (t : ℂ) ^ 2 + C) *
          Complex.exp (z * (t : ℂ)) ∂μ) =
          ∫ t : ℝ, (((4 / 3 : ℂ) * f6 t - A * f4 t) + B * f2 t) +
            C * f0 t ∂μ := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with t
            simp [f6, f4, f2, f0]
            ring
      _ = ∫ t : ℝ, (((4 / 3 : ℂ) * f6 t - A * f4 t) + B * f2 t) ∂μ +
            ∫ t : ℝ, C * f0 t ∂μ := by
            rw [MeasureTheory.integral_add]
            · exact ((hf6.const_mul (4 / 3 : ℂ)).sub (hf4.const_mul A)).add
                (hf2.const_mul B)
            · exact hf0.const_mul C
      _ = (∫ t : ℝ, ((4 / 3 : ℂ) * f6 t - A * f4 t) ∂μ +
              ∫ t : ℝ, B * f2 t ∂μ) +
            ∫ t : ℝ, C * f0 t ∂μ := by
            rw [MeasureTheory.integral_add]
            · exact (hf6.const_mul (4 / 3 : ℂ)).sub (hf4.const_mul A)
            · exact hf2.const_mul B
      _ = (((4 / 3 : ℂ) * ∫ t : ℝ, f6 t ∂μ -
              A * ∫ t : ℝ, f4 t ∂μ) +
            B * ∫ t : ℝ, f2 t ∂μ) +
            C * ∫ t : ℝ, f0 t ∂μ := by
            rw [MeasureTheory.integral_sub]
            · simp only [MeasureTheory.integral_const_mul]
            · exact hf6.const_mul (4 / 3 : ℂ)
            · exact hf4.const_mul A
      _ = (4 / 3 : ℂ) * ∫ t : ℝ, f6 t ∂μ -
          A * ∫ t : ℝ, f4 t ∂μ +
          B * ∫ t : ℝ, f2 t ∂μ + C * ∫ t : ℝ, f0 t ∂μ := by ring
  rw [hsplit]
  simp only [f6, f4, f2, f0, μ]
  rw [gaussian_half_moment_six, gaussian_half_moment_four, gaussian_half_moment_two,
    gaussian_half_moment_zero]
  ring

private theorem oneDWindowAmbiguityTwoShiftedPolynomial_eq (x t : ℝ) :
    ((1 / 2 : ℂ) -
        ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ (2 : Nat) -
        ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ (2 : Nat) +
        (2 : ℂ) *
          (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ (2 : Nat) *
            ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ (2 : Nat))) =
      (2 : ℂ) * (t : ℂ) ^ 4 - ((2 : ℂ) + (x : ℂ) ^ 2) * (t : ℂ) ^ 2 +
        ((1 / 2 : ℂ) - (x : ℂ) ^ 2 / 2 + (x : ℂ) ^ 4 / 8) := by
  norm_num
  ring

private theorem oneDWindowAmbiguityTwoClosedPolynomial_eq (x ω : ℝ) :
    (let lam : ℂ := -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)
     let A : ℂ := (2 : ℂ) + (x : ℂ) ^ 2
     let C : ℂ := (1 / 2 : ℂ) - (x : ℂ) ^ 2 / 2 + (x : ℂ) ^ 4 / 8
     (2 : ℂ) * ((3 / 4 : ℂ) + (3 / 4 : ℂ) * lam ^ 2 + lam ^ 4 / 16) -
          A * ((1 / 2 : ℂ) + lam ^ 2 / 4) + C) =
      (1 - (2 : ℂ) *
        (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ)) *
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ)) +
        (1 / 2 : ℂ) *
          ((((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ)) *
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) ^ (2 : Nat)) := by
  rw [star_sub_div_sqrtTwo]
  have hsqrt2_two : Real.sqrt 2 ^ 2 = (2 : ℝ) := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrt2_four : Real.sqrt 2 ^ 4 = (4 : ℝ) := by
    rw [show Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 by ring, hsqrt2_two]
    norm_num
  field_simp [sqrtTwoC_ne]
  ring_nf
  norm_num [← Complex.ofReal_pow, hsqrt2_two, hsqrt2_four]
  ring_nf

private theorem oneDWindowAmbiguityThreeClosedPolynomial_eq (x ω : ℝ) :
    (let lam : ℂ := -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)
     let A : ℂ := (4 : ℂ) + (x : ℂ) ^ 2
     let B : ℂ := (3 : ℂ) + (x : ℂ) ^ 4 / 4
     let C : ℂ :=
       -(3 / 4 : ℂ) * (x : ℂ) ^ 2 + (1 / 4 : ℂ) * (x : ℂ) ^ 4 -
         (1 / 48 : ℂ) * (x : ℂ) ^ 6
     (4 / 3 : ℂ) *
          ((15 / 8 : ℂ) + (45 / 16 : ℂ) * lam ^ 2 +
            (15 / 32 : ℂ) * lam ^ 4 + lam ^ 6 / 64) -
        A * ((3 / 4 : ℂ) + (3 / 4 : ℂ) * lam ^ 2 + lam ^ 4 / 16) +
        B * ((1 / 2 : ℂ) + lam ^ 2 / 4) + C) =
      (1 - (3 : ℂ) *
        (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ)) *
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ)) +
        (3 / 2 : ℂ) *
          ((((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ)) *
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) ^ (2 : Nat) -
        (1 / 6 : ℂ) *
          ((((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ)) *
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) ^ (3 : Nat)) := by
  rw [star_sub_div_sqrtTwo]
  have hsqrt2_two : Real.sqrt 2 ^ 2 = (2 : ℝ) := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrt2_four : Real.sqrt 2 ^ 4 = (4 : ℝ) := by
    rw [show Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 by ring, hsqrt2_two]
    norm_num
  have hsqrt2_six : Real.sqrt 2 ^ 6 = (8 : ℝ) := by
    rw [show Real.sqrt 2 ^ 6 = (Real.sqrt 2 ^ 2) ^ 3 by ring, hsqrt2_two]
    norm_num
  field_simp [sqrtTwoC_ne]
  ring_nf
  norm_num [← Complex.ofReal_pow, hsqrt2_two, hsqrt2_four, hsqrt2_six]
  ring_nf

private theorem gaussian_half_exp_factor_eq_closed_exp (x ω : ℝ) :
    Complex.exp (-((x : ℂ) ^ 2 / 4)) *
        Complex.exp ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) ^ 2 / 4) =
      Complex.ofReal (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  rw [← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  norm_num [← Complex.ofReal_pow]
  ring_nf
  rw [Complex.I_sq]
  norm_num [← Complex.ofReal_pow]
  ring_nf

private theorem shifted_mgf_generating_eq_kernel
    (x ω : ℝ) (u w : ℂ) :
    Complex.exp (-((x : ℂ) ^ 2 / 4)) *
      Complex.exp
        (-(u ^ 2) / 2 - (w ^ 2) / 2 +
          (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
          (Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2 +
          ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) +
              (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2) / 4) =
    Complex.exp
      (u * w +
        (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ)) * u -
        star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ)) * w) *
      Complex.ofReal
        (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  let lam : ℂ := -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)
  let z : ℂ := ((x : ℂ) + lam) / (Real.sqrt 2 : ℂ)
  have hz :
      z =
        (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ)) := by
    simp [z, lam]
    ring
  have hstar : star z = ((x : ℂ) - lam) / (Real.sqrt 2 : ℂ) := by simp [z, lam]
  have hbig :
      (-(u ^ 2) / 2 - (w ^ 2) / 2 +
          (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
          (Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2 +
          ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2) / 4) =
        lam ^ 2 / 4 + (u * w + z * u - star z * w) := by
    rw [hstar]
    simp only [z]
    have hsqrt2_cube : (Real.sqrt 2 : ℂ) ^ 3 = 2 * (Real.sqrt 2 : ℂ) := by
      rw [show (Real.sqrt 2 : ℂ) ^ 3 = (Real.sqrt 2 : ℂ) ^ 2 * (Real.sqrt 2 : ℂ)
        by ring]
      rw [sqrtTwoC_sq]
    field_simp [sqrtTwoC_ne]
    ring_nf
    rw [hsqrt2_cube, sqrtTwoC_sq]
    ring
  rw [show
      -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) +
            (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w =
        lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w by
    simp [lam]]
  rw [hbig, Complex.exp_add, hz]
  calc
    Complex.exp (-((x : ℂ) ^ 2 / 4)) *
        (Complex.exp (lam ^ 2 / 4) *
          Complex.exp
            (u * w +
              (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * u -
                star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * w)) =
      Complex.exp
          (u * w +
            (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                (Real.sqrt 2 : ℂ)) * u -
              star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                (Real.sqrt 2 : ℂ)) * w) *
        (Complex.exp (-((x : ℂ) ^ 2 / 4)) * Complex.exp (lam ^ 2 / 4)) := by ring
    _ = _ := by
        rw [show lam = -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) by simp [lam]]
        rw [gaussian_half_exp_factor_eq_closed_exp]

private theorem iteratedDeriv_iteratedDeriv_add
    (i j : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv j (iteratedDeriv i f) = iteratedDeriv (j + i) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    Function.iterate_add_apply]

private theorem contDiff_iteratedDeriv_cexp_sq_div_four
    (i n : ℕ) :
    ContDiff ℂ n (iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))) := by
  have hF : ContDiff ℂ (⊤ : WithTop ℕ∞) (fun z : ℂ => Complex.exp (z ^ 2 / 4)) := by fun_prop
  rw [contDiff_nat_iff_iteratedDeriv]
  constructor
  · intro m hm
    rw [iteratedDeriv_iteratedDeriv_add]
    exact hF.continuous_iteratedDeriv (m + i) (by simp)
  · intro m hm
    rw [iteratedDeriv_iteratedDeriv_add]
    exact hF.differentiable_iteratedDeriv (m + i) (by simp)

private theorem iteratedDeriv_cexp_sq_div_four_affine_at_zero
    (i : ℕ) (lam w : ℂ) :
    iteratedDeriv i
      (fun u : ℂ => Complex.exp
        ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2 / 4)) 0 =
      (Real.sqrt 2 : ℂ) ^ i *
        iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
          (lam + (Real.sqrt 2 : ℂ) * w) := by
  rw [show
      (fun u : ℂ => Complex.exp
        ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2 / 4)) =
        fun u : ℂ =>
          (fun y : ℂ => Complex.exp ((y + (lam + (Real.sqrt 2 : ℂ) * w)) ^ 2 / 4))
            ((Real.sqrt 2 : ℂ) * u) by
    funext u
    congr 1
    ring]
  have hscale := congrFun
    (iteratedDeriv_comp_const_mul
      (n := i)
      (f := fun y : ℂ => Complex.exp ((y + (lam + (Real.sqrt 2 : ℂ) * w)) ^ 2 / 4))
      (by fun_prop) (Real.sqrt 2 : ℂ)) 0
  rw [hscale]
  rw [show
      (fun y : ℂ => Complex.exp ((y + (lam + (Real.sqrt 2 : ℂ) * w)) ^ 2 / 4)) =
        fun y : ℂ => (fun z : ℂ => Complex.exp (z ^ 2 / 4))
          (y + (lam + (Real.sqrt 2 : ℂ) * w)) by
    rfl]
  have hcomp := congrFun
    (iteratedDeriv_comp_add_const i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
      (lam + (Real.sqrt 2 : ℂ) * w)) 0
  simpa using congrArg (fun y : ℂ => (Real.sqrt 2 : ℂ) ^ i * y) hcomp

private theorem iteratedDeriv_linear_exp_mul_shifted_square_at_zero
    (k : ℕ) (x : ℝ) (lam w : ℂ) :
    iteratedDeriv k
      (fun u : ℂ =>
        Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2) *
          Complex.exp
            ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2 / 4)) 0 =
      (Real.sqrt 2 : ℂ) ^ k *
        (∑ i ∈ Finset.range (k + 1),
          (Nat.choose k i : ℂ) * ((x : ℂ) / 2) ^ (k - i) *
            iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
              (lam + (Real.sqrt 2 : ℂ) * w)) := by
  rw [show
      (fun u : ℂ =>
        Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2) *
          Complex.exp
            ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2 / 4)) =
        fun u : ℂ =>
          Complex.exp
            ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2 / 4) *
            Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2) by
    funext u
    ring]
  rw [iteratedDeriv_fun_mul]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [iteratedDeriv_cexp_sq_div_four_affine_at_zero]
    rw [show
        iteratedDeriv (k - i)
          (fun u : ℂ => Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2)) 0 =
          ((Real.sqrt 2 : ℂ) * (x : ℂ) / 2) ^ (k - i) by
      rw [show
          (fun u : ℂ => Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2)) =
          fun u : ℂ => Complex.exp (((Real.sqrt 2 : ℂ) * (x : ℂ) / 2) * u) by
        funext u
        congr 1
        ring]
      simp [iteratedDeriv_cexp_const_mul]]
    have hi_le : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    rw [show ((Real.sqrt 2 : ℂ) * (x : ℂ) / 2) ^ (k - i) =
        (Real.sqrt 2 : ℂ) ^ (k - i) * ((x : ℂ) / 2) ^ (k - i) by
      rw [show (Real.sqrt 2 : ℂ) * (x : ℂ) / 2 =
          (Real.sqrt 2 : ℂ) * ((x : ℂ) / 2) by ring]
      rw [mul_pow]]
    have hpow : i + (k - i) = k := by omega
    let D : ℂ := iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
      (lam + (Real.sqrt 2 : ℂ) * w)
    let X : ℂ := ((x : ℂ) / 2) ^ (k - i)
    calc
      (Nat.choose k i : ℂ) *
          ((Real.sqrt 2 : ℂ) ^ i * D) *
          ((Real.sqrt 2 : ℂ) ^ (k - i) * X) =
        ((Real.sqrt 2 : ℂ) ^ i * (Real.sqrt 2 : ℂ) ^ (k - i)) *
          ((Nat.choose k i : ℂ) * X * D) := by ring
      _ = (Real.sqrt 2 : ℂ) ^ k * ((Nat.choose k i : ℂ) * X * D) := by rw [← pow_add, hpow]
      _ = (Real.sqrt 2 : ℂ) ^ k *
          ((Nat.choose k i : ℂ) * ((x : ℂ) / 2) ^ (k - i) *
            iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
              (lam + (Real.sqrt 2 : ℂ) * w)) := by simp [D, X]
  · fun_prop
  · fun_prop

private theorem iteratedDeriv_u_shifted_factor_expansion
    (n : ℕ) (x : ℝ) (lam w : ℂ) :
    iteratedDeriv n
      (fun u : ℂ =>
        Complex.exp (-(u ^ 2) / 2) *
          (Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2) *
            Complex.exp
              ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2 / 4))) 0 =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
          iteratedDeriv (n - k) (fun u : ℂ => Complex.exp (-(u ^ 2) / 2)) 0 *
            (∑ i ∈ Finset.range (k + 1),
              (Nat.choose k i : ℂ) * ((x : ℂ) / 2) ^ (k - i) *
                iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                  (lam + (Real.sqrt 2 : ℂ) * w)) := by
  rw [show
      (fun u : ℂ =>
        Complex.exp (-(u ^ 2) / 2) *
          (Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2) *
            Complex.exp
              ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2 / 4))) =
        fun u : ℂ =>
          (Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2) *
            Complex.exp
              ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2 / 4)) *
            Complex.exp (-(u ^ 2) / 2) by
    funext u
    ring]
  rw [iteratedDeriv_fun_mul]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDeriv_linear_exp_mul_shifted_square_at_zero]
    ring
  · fun_prop
  · fun_prop

private theorem iteratedDeriv_shifted_iterated_cexp_sq_div_four
    (i j : ℕ) (lam : ℂ) :
    iteratedDeriv j
      (fun w : ℂ => iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
        (lam + (Real.sqrt 2 : ℂ) * w)) 0 =
      (Real.sqrt 2 : ℂ) ^ j *
        iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4)) lam := by
  rw [show
      (fun w : ℂ => iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
        (lam + (Real.sqrt 2 : ℂ) * w)) =
      fun w : ℂ => (fun y : ℂ =>
        iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4)) (y + lam))
          ((Real.sqrt 2 : ℂ) * w) by
    funext w
    congr 1
    ring]
  have hscale := congrFun
    (iteratedDeriv_comp_const_mul
      (n := j)
      (f := fun y : ℂ =>
        iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4)) (y + lam))
      (by
        have hFi := contDiff_iteratedDeriv_cexp_sq_div_four i j
        fun_prop)
      (Real.sqrt 2 : ℂ)) 0
  rw [hscale]
  rw [show
      (fun y : ℂ =>
        iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4)) (y + lam)) =
      fun y : ℂ => (iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))) (y + lam) by
    rfl]
  have hcomp := congrFun
    (iteratedDeriv_comp_add_const j
      (iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))) lam) 0
  rw [show
      iteratedDeriv j (fun y : ℂ =>
        iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4)) (y + lam))
          ((Real.sqrt 2 : ℂ) * 0) =
        iteratedDeriv j (fun y : ℂ =>
          iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4)) (y + lam)) 0 by
    simp]
  rw [hcomp, iteratedDeriv_iteratedDeriv_add]
  simp only [zero_add, mul_eq_mul_left_iff, pow_eq_zero_iff', Complex.ofReal_eq_zero,
    Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero, ne_eq, false_and, or_false]
  rw [Nat.add_comm]

private theorem iteratedDeriv_neg_linear_exp_mul_shifted_iterated_at_zero
    (l i : ℕ) (x : ℝ) (lam : ℂ) :
    iteratedDeriv l
      (fun w : ℂ =>
        Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
          iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
            (lam + (Real.sqrt 2 : ℂ) * w)) 0 =
      (Real.sqrt 2 : ℂ) ^ l *
        (∑ j ∈ Finset.range (l + 1),
          (Nat.choose l j : ℂ) * (-(x : ℂ) / 2) ^ (l - j) *
            iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4)) lam) := by
  rw [show
      (fun w : ℂ =>
        Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
          iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
            (lam + (Real.sqrt 2 : ℂ) * w)) =
      fun w : ℂ =>
        iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
            (lam + (Real.sqrt 2 : ℂ) * w) *
          Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) by
    funext w
    ring]
  rw [iteratedDeriv_fun_mul]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [iteratedDeriv_shifted_iterated_cexp_sq_div_four]
    rw [show
        iteratedDeriv (l - j)
          (fun w : ℂ => Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2)) 0 =
          (-(Real.sqrt 2 : ℂ) * (x : ℂ) / 2) ^ (l - j) by
      rw [show
          (fun w : ℂ => Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2)) =
          fun w : ℂ => Complex.exp ((-(Real.sqrt 2 : ℂ) * (x : ℂ) / 2) * w) by
        funext w
        congr 1
        ring]
      simp [iteratedDeriv_cexp_const_mul]]
    have hj_le : j ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [show (-(Real.sqrt 2 : ℂ) * (x : ℂ) / 2) ^ (l - j) =
        (Real.sqrt 2 : ℂ) ^ (l - j) * (-(x : ℂ) / 2) ^ (l - j) by
      rw [show -(Real.sqrt 2 : ℂ) * (x : ℂ) / 2 =
          (Real.sqrt 2 : ℂ) * (-(x : ℂ) / 2) by ring]
      rw [mul_pow]]
    have hpow : j + (l - j) = l := by omega
    let D : ℂ := iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4)) lam
    let X : ℂ := (-(x : ℂ) / 2) ^ (l - j)
    calc
      (Nat.choose l j : ℂ) *
          ((Real.sqrt 2 : ℂ) ^ j * D) *
          ((Real.sqrt 2 : ℂ) ^ (l - j) * X) =
        ((Real.sqrt 2 : ℂ) ^ j * (Real.sqrt 2 : ℂ) ^ (l - j)) *
          ((Nat.choose l j : ℂ) * X * D) := by ring
      _ = (Real.sqrt 2 : ℂ) ^ l * ((Nat.choose l j : ℂ) * X * D) := by rw [← pow_add, hpow]
      _ = (Real.sqrt 2 : ℂ) ^ l *
          ((Nat.choose l j : ℂ) * (-(x : ℂ) / 2) ^ (l - j) *
            iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4)) lam) := by simp [D, X]
  · have hiter : ContDiffAt ℂ l
        (fun w : ℂ => iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
          (lam + (Real.sqrt 2 : ℂ) * w)) 0 := by
      have hFi := contDiff_iteratedDeriv_cexp_sq_div_four i l
      fun_prop
    exact hiter
  · fun_prop

private theorem iteratedDeriv_w_shifted_factor_expansion
    (m i : ℕ) (x : ℝ) (lam : ℂ) :
    iteratedDeriv m
      (fun w : ℂ =>
        Complex.exp (-(w ^ 2) / 2) *
          (Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
            iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
              (lam + (Real.sqrt 2 : ℂ) * w))) 0 =
      ∑ l ∈ Finset.range (m + 1),
        (Nat.choose m l : ℂ) * (Real.sqrt 2 : ℂ) ^ l *
          iteratedDeriv (m - l) (fun w : ℂ => Complex.exp (-(w ^ 2) / 2)) 0 *
            (∑ j ∈ Finset.range (l + 1),
              (Nat.choose l j : ℂ) * (-(x : ℂ) / 2) ^ (l - j) *
                iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4)) lam) := by
  rw [show
      (fun w : ℂ =>
        Complex.exp (-(w ^ 2) / 2) *
          (Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
            iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
              (lam + (Real.sqrt 2 : ℂ) * w))) =
      fun w : ℂ =>
        (Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
          iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
            (lam + (Real.sqrt 2 : ℂ) * w)) *
          Complex.exp (-(w ^ 2) / 2) by
    funext w
    ring]
  rw [iteratedDeriv_fun_mul]
  · apply Finset.sum_congr rfl
    intro l hl
    rw [iteratedDeriv_neg_linear_exp_mul_shifted_iterated_at_zero]
    ring
  · have hiter : ContDiffAt ℂ m
        (fun w : ℂ =>
          Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
            iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
              (lam + (Real.sqrt 2 : ℂ) * w)) 0 := by
      have hFi := contDiff_iteratedDeriv_cexp_sq_div_four i m
      fun_prop
    exact hiter
  · fun_prop

private theorem sum_reorder_left_mul
    (s t : Finset ℕ) (A : ℂ) (B C : ℕ → ℂ) (D : ℕ → ℕ → ℂ) :
    A * (∑ i ∈ s, B i * (∑ l ∈ t, C l * D i l)) =
      ∑ l ∈ t, (A * C l) * (∑ i ∈ s, B i * D i l) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem left_mul_nested_sum
    (s : Finset ℕ) (t : ℕ → Finset ℕ) (C : ℂ)
    (A : ℕ → ℂ) (B D : ℕ → ℕ → ℂ) :
    C * (∑ k ∈ s, A k * (∑ i ∈ t k, B k i * D k i)) =
      ∑ k ∈ s, A k * (∑ i ∈ t k, B k i * (C * D k i)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show C * (A k * (∑ i ∈ t k, B k i * D k i)) =
      A k * (C * (∑ i ∈ t k, B k i * D k i)) by
    ring]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem shifted_mgf_mixed_derivative_expansion_unscaled
    (n m : ℕ) (x ω : ℝ) :
    iteratedDeriv m
      (fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ =>
            Complex.exp
              (-(u ^ 2) / 2 - (w ^ 2) / 2 +
                (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
                (Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2 +
                ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) +
                    (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2) / 4)) 0) 0 =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
            iteratedDeriv (n - k) (fun u : ℂ => Complex.exp (-(u ^ 2) / 2)) 0) *
          ((Nat.choose m l : ℂ) * (Real.sqrt 2 : ℂ) ^ l *
            iteratedDeriv (m - l) (fun w : ℂ => Complex.exp (-(w ^ 2) / 2)) 0) *
            (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
              (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
                ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                  iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                    (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ))) := by
  let lam : ℂ := -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)
  have hfun :
      (fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ =>
            Complex.exp
              (-(u ^ 2) / 2 - (w ^ 2) / 2 +
                (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
                (Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2 +
                ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) +
                    (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2) / 4)) 0) =
      fun w : ℂ =>
        ∑ k ∈ Finset.range (n + 1),
          ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
            iteratedDeriv (n - k) (fun u : ℂ => Complex.exp (-(u ^ 2) / 2)) 0) *
            (∑ i ∈ Finset.range (k + 1),
              (Nat.choose k i : ℂ) * ((x : ℂ) / 2) ^ (k - i) *
                (Complex.exp (-(w ^ 2) / 2) *
                  (Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
                    iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                      (lam + (Real.sqrt 2 : ℂ) * w)))) := by
    funext w
    rw [show
        (fun u : ℂ =>
          Complex.exp
            (-(u ^ 2) / 2 - (w ^ 2) / 2 +
              (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
              (Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2 +
              ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) +
                  (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2) / 4)) =
        fun u : ℂ =>
          (Complex.exp (-(w ^ 2) / 2) *
            Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2)) *
            (Complex.exp (-(u ^ 2) / 2) *
              (Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2) *
                Complex.exp ((lam + (Real.sqrt 2 : ℂ) * u +
                  (Real.sqrt 2 : ℂ) * w) ^ 2 / 4))) by
      funext u
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp [lam]
      ring]
    rw [iteratedDeriv_const_mul_field,
      iteratedDeriv_u_shifted_factor_expansion,
      left_mul_nested_sum]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfun, iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_sum]
    · rw [show
          (∑ i ∈ Finset.range (k + 1),
            iteratedDeriv m
              (fun w : ℂ =>
                (Nat.choose k i : ℂ) * ((x : ℂ) / 2) ^ (k - i) *
                  (Complex.exp (-(w ^ 2) / 2) *
                    (Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
                      iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                        (lam + (Real.sqrt 2 : ℂ) * w)))) 0) =
          ∑ i ∈ Finset.range (k + 1),
            ((Nat.choose k i : ℂ) * ((x : ℂ) / 2) ^ (k - i)) *
              (∑ l ∈ Finset.range (m + 1),
                ((Nat.choose m l : ℂ) * (Real.sqrt 2 : ℂ) ^ l *
                  iteratedDeriv (m - l)
                    (fun w : ℂ => Complex.exp (-(w ^ 2) / 2)) 0) *
                  (∑ j ∈ Finset.range (l + 1),
                    (Nat.choose l j : ℂ) * (-(x : ℂ) / 2) ^ (l - j) *
                      iteratedDeriv (i + j)
                        (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                        (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)))) by
        apply Finset.sum_congr rfl
        intro i hi
        rw [iteratedDeriv_const_mul_field, iteratedDeriv_w_shifted_factor_expansion]
        ]
      rw [sum_reorder_left_mul]
      apply Finset.sum_congr rfl
      intro l hl
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    · intro i hi
      have hFi := contDiff_iteratedDeriv_cexp_sq_div_four i m
      fun_prop
  · intro k hk
    have hsum : ContDiffAt ℂ m
        (fun w : ℂ =>
          ∑ i ∈ Finset.range (k + 1),
            (Nat.choose k i : ℂ) * ((x : ℂ) / 2) ^ (k - i) *
              (Complex.exp (-(w ^ 2) / 2) *
                (Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
                  iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                    (lam + (Real.sqrt 2 : ℂ) * w)))) 0 := by
      apply ContDiffAt.sum
      intro i hi
      have hFi := contDiff_iteratedDeriv_cexp_sq_div_four i m
      fun_prop
    simpa using ContDiffAt.const_smul
      ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
        iteratedDeriv (n - k) (fun u : ℂ => Complex.exp (-(u ^ 2) / 2)) 0) hsum

private theorem scaled_moment_sum_eq_shifted_mgf_unscaled_sum
    (n m : ℕ) (x ω : ℝ) :
    (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)⁻¹) *
        (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
          (realHermiteGeneratingExpansionCoeff n k *
              realHermiteGeneratingExpansionCoeff m l) *
            (Complex.exp (-((x : ℂ) ^ 2 / 4)) *
              (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
                (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
                  ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                    iteratedDeriv (i + j)
                      (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                      (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ))))) =
      Complex.exp (-((x : ℂ) ^ 2 / 4)) *
        (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
          ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
              iteratedDeriv (n - k) (fun u : ℂ => Complex.exp (-(u ^ 2) / 2)) 0) *
            ((Nat.choose m l : ℂ) * (Real.sqrt 2 : ℂ) ^ l *
              iteratedDeriv (m - l) (fun w : ℂ => Complex.exp (-(w ^ 2) / 2)) 0) *
              (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
                (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
                  ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                    iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                      (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)))) := by
  have hcπ : (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0) := by
    exact_mod_cast (Real.rpow_pos_of_pos Real.pi_pos (-(1 / 2 : ℝ))).ne'
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  unfold realHermiteGeneratingExpansionCoeff
  let A : ℂ :=
    (Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
      iteratedDeriv (n - k) (fun u : ℂ => Complex.exp (-(u ^ 2) / 2)) 0
  let B : ℂ :=
    (Nat.choose m l : ℂ) * (Real.sqrt 2 : ℂ) ^ l *
      iteratedDeriv (m - l) (fun w : ℂ => Complex.exp (-(w ^ 2) / 2)) 0
  let S : ℂ :=
    ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
      (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
        ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
          iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4))
            (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ))
  have hscale :
      ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)⁻¹ *
          (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
            ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) = 1 := by
    have hmul : (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) =
        ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) :=
      by simpa [one_div] using realHermiteGenerating_pi_quarter_mul_self
    rw [hmul]
    exact inv_mul_cancel₀ hcπ
  calc
    ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)⁻¹ *
        (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * A *
          (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * B) *
          (Complex.exp (-((x : ℂ) ^ 2 / 4)) * S)) =
      (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)⁻¹ *
          (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
            ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ))) *
        (Complex.exp (-((x : ℂ) ^ 2 / 4)) * (A * B * S)) := by ring
    _ = Complex.exp (-((x : ℂ) ^ 2 / 4)) * (A * B * S) := by
        rw [hscale]
        ring
    _ = Complex.exp (-((x : ℂ) ^ 2 / 4)) *
        ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
          iteratedDeriv (n - k) (fun u : ℂ => Complex.exp (-(u ^ 2) / 2)) 0 *
            ((Nat.choose m l : ℂ) * (Real.sqrt 2 : ℂ) ^ l *
              iteratedDeriv (m - l) (fun w : ℂ => Complex.exp (-(w ^ 2) / 2)) 0) *
          (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
            (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
              ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                  (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)))) := by simp [A, B, S]

private theorem shifted_mgf_coefficient_eq_kernel_coefficient
    (n m : ℕ) (x ω : ℝ) :
    iteratedDeriv m
      (fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ =>
            Complex.exp (-((x : ℂ) ^ 2 / 4)) *
              Complex.exp
                (-(u ^ 2) / 2 - (w ^ 2) / 2 +
                  (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
                  (Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2 +
                  ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) +
                      (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2) / 4)) 0) 0 =
      ((-1 : ℂ) ^ m *
        complexHermite n m
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  let z : ℂ :=
    ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
      (Real.sqrt 2 : ℂ)
  let E : ℂ :=
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))
  have hfun :
      (fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ =>
            Complex.exp (-((x : ℂ) ^ 2 / 4)) *
              Complex.exp
                (-(u ^ 2) / 2 - (w ^ 2) / 2 +
                  (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
                  (Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2 +
                  ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) +
                      (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2) / 4)) 0) =
        fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ => Complex.exp (u * w + z * u - star z * w) * E) 0 := by
    funext w
    congr 1
    funext u
    simpa [z, E] using shifted_mgf_generating_eq_kernel x ω u w
  rw [hfun]
  have hinner :
      (fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ => Complex.exp (u * w + z * u - star z * w) * E) 0) =
        fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) 0 * E := by
    funext w
    rw [iteratedDeriv_mul_const_field]
  rw [hinner, iteratedDeriv_mul_const_field, iteratedDeriv_cexp_ambiguity_kernel_at_zero]

private theorem oneDWindowAmbiguityMonomialKernel_eq_shifted_monomial
    (k l : ℕ) (x ω t : ℝ) :
    oneDWindowAmbiguityMonomialKernel k l x ω t =
      (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
        ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l) *
        oneDWindowAmbiguityShiftedModulatedGaussian x ω t := by
  rw [oneDWindowAmbiguityMonomialKernel, star_complex_monomial_gaussian]
  unfold complexMonomialGaussian oneDWindowAmbiguityShiftedModulatedGaussian
  have hexp :
      Complex.exp (-((((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2)) *
          Complex.exp (-((((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2)) =
        Complex.exp (-((t : ℂ) ^ 2 + (x : ℂ) ^ 2 / 4)) := by
    rw [← Complex.exp_add]
    congr 1
    norm_num
    ring
  have hinner : ((inner ℝ ω t : ℝ) : ℂ) = (ω : ℂ) * (t : ℂ) := by
    simp [inner]
    ring
  rw [hinner]
  rw [show
      (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
          Complex.exp (-((((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2))) *
        (((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
          Complex.exp (-((((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2))) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) =
      (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
          ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l) *
        (Complex.exp (-((((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2)) *
          Complex.exp (-((((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2))) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) by
    ring]
  rw [hexp]
  ring

private theorem oneDWindowAmbiguityMonomialKernel_normalized_integral_eq_gaussian_moment
    (k l : ℕ) (x ω : ℝ) :
    (∫ t : ℝ,
      ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        oneDWindowAmbiguityMonomialKernel k l x ω t) =
      Complex.exp (-((x : ℂ) ^ 2 / 4)) *
        ∫ t : ℝ,
          (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
            ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))))
            ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)) := by
  let f : ℝ → ℂ := fun t =>
    (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
      ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))))
  rw [integral_gaussian_zero_half_eq_density f, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [oneDWindowAmbiguityMonomialKernel_eq_shifted_monomial]
  unfold oneDWindowAmbiguityShiftedModulatedGaussian f
  rw [show Complex.exp (-((t : ℂ) ^ 2 + (x : ℂ) ^ 2 / 4)) =
      Complex.exp (-((t : ℂ) ^ 2)) * Complex.exp (-((x : ℂ) ^ 2 / 4)) by
    rw [← Complex.exp_add]
    congr 1
    ring]
  ring

private theorem shifted_monomial_pair_expansion
    (k l : ℕ) (t a b E : ℂ) :
    (t + a) ^ k * (t + b) ^ l * E =
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
        (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
          a ^ (k - i) * b ^ (l - j) * (t ^ (i + j) * E) := by
  rw [add_pow, add_pow]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

private theorem shifted_monomial_pair_modulated_expansion
    (k l : ℕ) (x ω t : ℝ) :
    (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
        ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
        (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
          ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
            ((t : ℂ) ^ (i + j) *
              Complex.exp ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) * (t : ℂ))) := by
  let lam : ℂ := -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)
  let a : ℂ := (x : ℂ) / 2
  let b : ℂ := -(x : ℂ) / 2
  have hplus :
      ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) = (t : ℂ) + a := by
    simp [a]
    ring
  have hminus :
      ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) = (t : ℂ) + b := by
    simp [b]
    ring
  have hphase :
      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) =
        Complex.exp (lam * (t : ℂ)) := by
    congr 1
    simp [lam]
    ring
  rw [hplus, hminus, hphase]
  exact shifted_monomial_pair_expansion k l (t : ℂ) a b
    (Complex.exp (lam * (t : ℂ)))

private theorem gaussian_half_shifted_monomial_pair_exp_integrable
    (k l : ℕ) (x ω : ℝ) :
    Integrable
      (fun t : ℝ =>
        (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
          ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))))
      )
      (ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)) := by
  let lam : ℂ := -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)
  let a : ℂ := (x : ℂ) / 2
  let b : ℂ := -(x : ℂ) / 2
  have hpoint :
      (fun t : ℝ =>
        (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
          ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))))) =
      fun t : ℝ =>
        ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
          (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
            a ^ (k - i) * b ^ (l - j) *
              ((t : ℂ) ^ (i + j) * Complex.exp (lam * (t : ℂ))) := by
    funext t
    simpa [a, b, lam] using shifted_monomial_pair_modulated_expansion k l x ω t
  rw [hpoint]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact (gaussian_half_integrable_monomial_exp (i + j) lam).const_mul
    ((Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
      a ^ (k - i) * b ^ (l - j))

private theorem oneDWindowAmbiguityMonomialKernel_normalized_integrable
    (k l : ℕ) (x ω : ℝ) :
    Integrable
      (fun t : ℝ =>
        ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          oneDWindowAmbiguityMonomialKernel k l x ω t)
      (volume : Measure ℝ) := by
  let g : ℝ → ℂ := fun t =>
    (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
      ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))))
  let ex : ℂ := Complex.exp (-((x : ℂ) ^ 2 / 4))
  have hg_gauss :
      Integrable g (ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)) := by
    simpa [g] using gaussian_half_shifted_monomial_pair_exp_integrable k l x ω
  have hgauss_eq :
      ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal) =
        (volume : Measure ℝ).withDensity (ProbabilityTheory.gaussianPDF 0 (1 / 2 : NNReal)) :=
    ProbabilityTheory.gaussianReal_of_var_ne_zero 0
      (by norm_num : (1 / 2 : NNReal) ≠ 0)
  have hg_density :
      Integrable g
        ((volume : Measure ℝ).withDensity
          (ProbabilityTheory.gaussianPDF 0 (1 / 2 : NNReal))) := by
    rw [hgauss_eq] at hg_gauss
    exact hg_gauss
  have hpdf_meas :
      Measurable (ProbabilityTheory.gaussianPDF 0 (1 / 2 : NNReal)) :=
    ProbabilityTheory.measurable_gaussianPDF 0 (1 / 2 : NNReal)
  have hpdf_ne_top :
      ∀ᵐ t ∂(volume : Measure ℝ),
        ProbabilityTheory.gaussianPDF 0 (1 / 2 : NNReal) t < ∞ :=
    ae_of_all _ fun t => ProbabilityTheory.gaussianPDF_lt_top
  have hg_volume :
      Integrable
        (fun t : ℝ => (ProbabilityTheory.gaussianPDF 0 (1 / 2 : NNReal) t).toReal • g t)
        (volume : Measure ℝ) :=
    (integrable_withDensity_iff_integrable_smul' hpdf_meas hpdf_ne_top).1 hg_density
  refine (hg_volume.const_mul ex).congr ?_
  filter_upwards with t
  rw [oneDWindowAmbiguityMonomialKernel_eq_shifted_monomial]
  unfold oneDWindowAmbiguityShiftedModulatedGaussian g ex
  rw [show Complex.exp (-((t : ℂ) ^ 2 + (x : ℂ) ^ 2 / 4)) =
      Complex.exp (-((t : ℂ) ^ 2)) * Complex.exp (-((x : ℂ) ^ 2 / 4)) by
    rw [← Complex.exp_add]
    congr 1
    ring]
  rw [ProbabilityTheory.toReal_gaussianPDF]
  change Complex.exp (-((x : ℂ) ^ 2 / 4)) *
      (((ProbabilityTheory.gaussianPDFReal 0 (1 / 2 : NNReal) t : ℝ) : ℂ) *
        (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
          ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))))) =
    ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
        ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
          (Complex.exp (-((t : ℂ) ^ 2)) *
            Complex.exp (-((x : ℂ) ^ 2 / 4)) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))))
  rw [gaussianPDFReal_zero_half_eq]
  ring_nf

private theorem gaussian_half_shifted_monomial_pair_exp_integral
    (k l : ℕ) (x ω : ℝ) :
    (∫ t : ℝ,
        (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
          ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))))
        ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))) =
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
        (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
          ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
            iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4))
              (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) := by
  let lam : ℂ := -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)
  let a : ℂ := (x : ℂ) / 2
  let b : ℂ := -(x : ℂ) / 2
  have hpoint :
      (fun t : ℝ =>
        (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
          ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))))) =
      fun t : ℝ =>
        ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
          (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
            a ^ (k - i) * b ^ (l - j) *
              ((t : ℂ) ^ (i + j) * Complex.exp (lam * (t : ℂ))) := by
    funext t
    have hplus :
        ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) = (t : ℂ) + a := by
      simp [a]
      ring
    have hminus :
        ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) = (t : ℂ) + b := by
      simp [b]
      ring
    have hphase :
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) =
          Complex.exp (lam * (t : ℂ)) := by
      congr 1
      simp [lam]
      ring
    rw [hplus, hminus, hphase]
    exact shifted_monomial_pair_expansion k l (t : ℂ) a b
      (Complex.exp (lam * (t : ℂ)))
  rw [hpoint, MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      let c : ℂ :=
        (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
          a ^ (k - i) * b ^ (l - j)
      rw [show
          (∫ t : ℝ,
            (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
              a ^ (k - i) * b ^ (l - j) *
                ((t : ℂ) ^ (i + j) * Complex.exp (lam * (t : ℂ)))
              ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))) =
            c * ∫ t : ℝ,
              ((t : ℂ) ^ (i + j) * Complex.exp (lam * (t : ℂ)))
              ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)) by
        simp only [c]
        exact MeasureTheory.integral_const_mul ..]
      rw [gaussian_half_moment_eq_iteratedDeriv]
    · intro j hj
      exact (gaussian_half_integrable_monomial_exp (i + j) lam).const_mul
        ((Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
          a ^ (k - i) * b ^ (l - j))
  · intro i hi
    apply integrable_finsetSum
    intro j hj
    exact (gaussian_half_integrable_monomial_exp (i + j) lam).const_mul
      ((Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
        a ^ (k - i) * b ^ (l - j))

private theorem oneDWindowAmbiguityMonomialKernel_normalized_integral_eq_moment_sum
    (k l : ℕ) (x ω : ℝ) :
    (∫ t : ℝ,
      ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        oneDWindowAmbiguityMonomialKernel k l x ω t) =
      Complex.exp (-((x : ℂ) ^ 2 / 4)) *
        (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
          (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
            ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
              iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ))) := by
  rw [oneDWindowAmbiguityMonomialKernel_normalized_integral_eq_gaussian_moment,
    gaussian_half_shifted_monomial_pair_exp_integral]

private theorem oneDWindowAmbiguityFactor_two_finite_kernel_integrand_eq_shifted_polynomial
    (x ω t : ℝ) :
    (((1 / 2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        oneDWindowAmbiguityMonomialKernel 0 0 x ω t) -
      (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        oneDWindowAmbiguityMonomialKernel 0 2 x ω t) -
      (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        oneDWindowAmbiguityMonomialKernel 2 0 x ω t) +
      ((2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        oneDWindowAmbiguityMonomialKernel 2 2 x ω t)) =
      ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((1 / 2 : ℂ) -
          ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ (2 : Nat) -
          ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ (2 : Nat) +
          (2 : ℂ) *
            (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ (2 : Nat) *
              ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ (2 : Nat))) *
          oneDWindowAmbiguityShiftedModulatedGaussian x ω t := by
  rw [oneDWindowAmbiguityMonomialKernel_eq_shifted_monomial 0 0,
    oneDWindowAmbiguityMonomialKernel_eq_shifted_monomial 0 2,
    oneDWindowAmbiguityMonomialKernel_eq_shifted_monomial 2 0,
    oneDWindowAmbiguityMonomialKernel_eq_shifted_monomial 2 2]
  ring

private noncomputable def oneDWindowAmbiguityTwoShiftedFourthMoment
    (x ω : ℝ) : ℂ :=
  ∫ t : ℝ,
    ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      ((1 / 2 : ℂ) -
        ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ (2 : Nat) -
        ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ (2 : Nat) +
        (2 : ℂ) *
          (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ (2 : Nat) *
            ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ (2 : Nat))) *
        oneDWindowAmbiguityShiftedModulatedGaussian x ω t

private theorem oneDWindowAmbiguityFactor_two_finite_kernel_integral_eq_shifted_moment
    (x ω : ℝ) :
    (∫ t : ℝ,
      (((1 / 2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          oneDWindowAmbiguityMonomialKernel 0 0 x ω t) -
        (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          oneDWindowAmbiguityMonomialKernel 0 2 x ω t) -
        (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          oneDWindowAmbiguityMonomialKernel 2 0 x ω t) +
        ((2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          oneDWindowAmbiguityMonomialKernel 2 2 x ω t))) =
      oneDWindowAmbiguityTwoShiftedFourthMoment x ω := by
  unfold oneDWindowAmbiguityTwoShiftedFourthMoment
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [oneDWindowAmbiguityFactor_two_finite_kernel_integrand_eq_shifted_polynomial]

private theorem oneDWindowAmbiguityFactor_three_finite_kernel_integrand_eq_shifted_polynomial
    (x ω t : ℝ) :
    (((3 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        oneDWindowAmbiguityMonomialKernel 1 1 x ω t) -
      ((2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        oneDWindowAmbiguityMonomialKernel 1 3 x ω t) -
      ((2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        oneDWindowAmbiguityMonomialKernel 3 1 x ω t) +
      ((4 / 3 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        oneDWindowAmbiguityMonomialKernel 3 3 x ω t)) =
      ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((4 / 3 : ℂ) * (t : ℂ) ^ (6 : Nat) -
          ((4 : ℂ) + (x : ℂ) ^ (2 : Nat)) * (t : ℂ) ^ (4 : Nat) +
          ((3 : ℂ) + (x : ℂ) ^ (4 : Nat) / 4) * (t : ℂ) ^ (2 : Nat) -
          (3 / 4 : ℂ) * (x : ℂ) ^ (2 : Nat) +
          (1 / 4 : ℂ) * (x : ℂ) ^ (4 : Nat) -
          (1 / 48 : ℂ) * (x : ℂ) ^ (6 : Nat)) *
        oneDWindowAmbiguityShiftedModulatedGaussian x ω t := by
  rw [oneDWindowAmbiguityMonomialKernel_eq_shifted_monomial 1 1,
    oneDWindowAmbiguityMonomialKernel_eq_shifted_monomial 1 3,
    oneDWindowAmbiguityMonomialKernel_eq_shifted_monomial 3 1,
    oneDWindowAmbiguityMonomialKernel_eq_shifted_monomial 3 3]
  norm_num
  ring

private noncomputable def oneDWindowAmbiguityThreeShiftedSixthMoment
    (x ω : ℝ) : ℂ :=
  ∫ t : ℝ,
    ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      ((4 / 3 : ℂ) * (t : ℂ) ^ (6 : Nat) -
        ((4 : ℂ) + (x : ℂ) ^ (2 : Nat)) * (t : ℂ) ^ (4 : Nat) +
        ((3 : ℂ) + (x : ℂ) ^ (4 : Nat) / 4) * (t : ℂ) ^ (2 : Nat) -
        (3 / 4 : ℂ) * (x : ℂ) ^ (2 : Nat) +
        (1 / 4 : ℂ) * (x : ℂ) ^ (4 : Nat) -
        (1 / 48 : ℂ) * (x : ℂ) ^ (6 : Nat)) *
      oneDWindowAmbiguityShiftedModulatedGaussian x ω t

private theorem oneDWindowAmbiguityFactor_three_finite_kernel_integral_eq_shifted_moment
    (x ω : ℝ) :
    (∫ t : ℝ,
      (((3 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          oneDWindowAmbiguityMonomialKernel 1 1 x ω t) -
        ((2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          oneDWindowAmbiguityMonomialKernel 1 3 x ω t) -
        ((2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          oneDWindowAmbiguityMonomialKernel 3 1 x ω t) +
        ((4 / 3 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          oneDWindowAmbiguityMonomialKernel 3 3 x ω t))) =
      oneDWindowAmbiguityThreeShiftedSixthMoment x ω := by
  unfold oneDWindowAmbiguityThreeShiftedSixthMoment
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [oneDWindowAmbiguityFactor_three_finite_kernel_integrand_eq_shifted_polynomial]

private noncomputable def oneDWindowAmbiguityOneOneShiftedMoment
    (x ω : ℝ) : ℂ :=
  ∫ t : ℝ,
    ((2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (((t : ℂ) ^ 2 - (x : ℂ) ^ 2 / 4) *
        oneDWindowAmbiguityShiftedModulatedGaussian x ω t))

private theorem oneDWindowAmbiguityMonomialKernel_one_one_normalized_integral_eq_shifted_moment
    (x ω : ℝ) :
    (∫ t : ℝ,
        ((2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          oneDWindowAmbiguityMonomialKernel 1 1 x ω t)) =
      oneDWindowAmbiguityOneOneShiftedMoment x ω := by
  unfold oneDWindowAmbiguityOneOneShiftedMoment
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [oneDWindowAmbiguityMonomialKernel_one_one_eq_shifted_moment_integrand]
  unfold oneDWindowAmbiguityShiftedModulatedGaussian
  ring

private theorem oneDWindowAmbiguityFactor_finite_integrand_expansion
    (n : ℕ) (x ω t : ℝ) :
    realHermite1D n (t + (1 / 2 : ℝ) * x) *
        star (realHermite1D n (t - (1 / 2 : ℝ) * x)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ)) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        (realHermite1DExpansionScale n *
            realHermiteGeneratingExpansionCoeff n k *
              star (realHermite1DExpansionScale n *
                realHermiteGeneratingExpansionCoeff n l)) *
          oneDWindowAmbiguityMonomialKernel k l x ω t := by
  rw [realHermite1D_finite_monomial_expansion,
    realHermite1D_finite_monomial_expansion]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [star_sum (Finset.range (n + 1))
    (fun l =>
      realHermite1DExpansionScale n * realHermiteGeneratingExpansionCoeff n l *
        complexMonomialGaussian l (t - (1 / 2 : ℝ) * x))]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  simp [oneDWindowAmbiguityMonomialKernel]
  ring

private theorem oneDWindowAmbiguityFactor_finite_expansion_integral
    (n : ℕ) (x ω : ℝ) :
    oneDWindowAmbiguityFactor n x ω =
      ∫ t : ℝ,
        ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          (realHermite1DExpansionScale n *
              realHermiteGeneratingExpansionCoeff n k *
                star (realHermite1DExpansionScale n *
                  realHermiteGeneratingExpansionCoeff n l)) *
            oneDWindowAmbiguityMonomialKernel k l x ω t := by
  unfold oneDWindowAmbiguityFactor
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  exact oneDWindowAmbiguityFactor_finite_integrand_expansion n x ω t

private theorem real_pi_neg_half_complex_ne_zero :
    (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0) := by
  exact_mod_cast (Real.rpow_pos_of_pos Real.pi_pos (-(1 / 2 : ℝ))).ne'

private theorem iteratedDeriv_generating_cross_ambiguity_kernel_integral_coefficient
    (n m : ℕ) (x ω : ℝ) :
    iteratedDeriv m
        (fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ,
                realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
                  realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
                    Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ ω t : ℝ) : ℂ))) 0) 0 =
      ((-1 : ℂ) ^ m *
        complexHermite n m
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  rw [ambiguity_kernel_iteratedDeriv_factor n x ω, iteratedDeriv_mul_const_field,
    iteratedDeriv_cexp_ambiguity_kernel_at_zero]

private theorem iteratedDeriv_generating_cross_ambiguity_integrand_finite_expansion
    (n m : ℕ) (x ω t : ℝ) :
    iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
        iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ)) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          oneDWindowAmbiguityMonomialKernel k l x ω t := by
  rw [realHermiteGenerating_iteratedDeriv_zero_expansion_monomial,
    realHermiteGenerating_iteratedDeriv_zero_expansion_monomial]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  simp [oneDWindowAmbiguityMonomialKernel, star_complex_monomial_gaussian]
  ring

private theorem iteratedDeriv_generating_cross_ambiguity_normalized_integral_finite_sum
    (n m : ℕ) (x ω : ℝ) :
    (∫ t : ℝ,
      ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
          iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ)))) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          (∫ t : ℝ,
            ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              oneDWindowAmbiguityMonomialKernel k l x ω t) := by
  let cπ : ℂ := ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  calc
    (∫ t : ℝ,
      cπ *
        (iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
          iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ)))) =
        ∫ t : ℝ,
          ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
            (realHermiteGeneratingExpansionCoeff n k *
                realHermiteGeneratingExpansionCoeff m l) *
              (cπ * oneDWindowAmbiguityMonomialKernel k l x ω t) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          rw [iteratedDeriv_generating_cross_ambiguity_integrand_finite_expansion, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          ring
    _ = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        ∫ t : ℝ,
          (realHermiteGeneratingExpansionCoeff n k *
              realHermiteGeneratingExpansionCoeff m l) *
            (cπ * oneDWindowAmbiguityMonomialKernel k l x ω t) := by
          rw [MeasureTheory.integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro k hk
            rw [MeasureTheory.integral_finsetSum]
            intro l hl
            exact (oneDWindowAmbiguityMonomialKernel_normalized_integrable k l x ω).const_mul
              (realHermiteGeneratingExpansionCoeff n k *
                realHermiteGeneratingExpansionCoeff m l)
          · intro k hk
            apply integrable_finsetSum
            intro l hl
            exact (oneDWindowAmbiguityMonomialKernel_normalized_integrable k l x ω).const_mul
              (realHermiteGeneratingExpansionCoeff n k *
                realHermiteGeneratingExpansionCoeff m l)
    _ = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          (∫ t : ℝ, cπ * oneDWindowAmbiguityMonomialKernel k l x ω t) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          exact MeasureTheory.integral_const_mul ..

private theorem iteratedDeriv_generating_cross_ambiguity_normalized_integral_moment_sum
    (n m : ℕ) (x ω : ℝ) :
    (∫ t : ℝ,
      ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
          iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ)))) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          (Complex.exp (-((x : ℂ) ^ 2 / 4)) *
            (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
              (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
                ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                  iteratedDeriv (i + j)
                    (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                    (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)))) := by
  rw [iteratedDeriv_generating_cross_ambiguity_normalized_integral_finite_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [oneDWindowAmbiguityMonomialKernel_normalized_integral_eq_moment_sum]

private theorem iteratedDeriv_generating_cross_ambiguity_pi_neg_half_mul_integral_moment_sum
    (n m : ℕ) (x ω : ℝ) :
    ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
          iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ))) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          (Complex.exp (-((x : ℂ) ^ 2 / 4)) *
            (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
              (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
                ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                  iteratedDeriv (i + j)
                    (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                    (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)))) := by
  rw [← MeasureTheory.integral_const_mul]
  exact iteratedDeriv_generating_cross_ambiguity_normalized_integral_moment_sum n m x ω

private theorem iteratedDeriv_generating_cross_ambiguity_integral_moment_sum
    (n m : ℕ) (x ω : ℝ) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
        iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))) =
      (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)⁻¹) *
        (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
          (realHermiteGeneratingExpansionCoeff n k *
              realHermiteGeneratingExpansionCoeff m l) *
            (Complex.exp (-((x : ℂ) ^ 2 / 4)) *
              (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
                (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
                  ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                    iteratedDeriv (i + j)
                      (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                      (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ))))) := by
  let cπ : ℂ := ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  have hcπ : cπ ≠ 0 := by simpa [cπ] using real_pi_neg_half_complex_ne_zero
  have h :=
    iteratedDeriv_generating_cross_ambiguity_pi_neg_half_mul_integral_moment_sum n m x ω
  calc
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
        iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))) =
        cπ⁻¹ * (cπ *
          (∫ t : ℝ,
            iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
              iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
                Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                  ((inner ℝ ω t : ℝ) : ℂ)))) := by rw [← mul_assoc, inv_mul_cancel₀ hcπ, one_mul]
    _ = cπ⁻¹ *
        (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
          (realHermiteGeneratingExpansionCoeff n k *
              realHermiteGeneratingExpansionCoeff m l) *
            (Complex.exp (-((x : ℂ) ^ 2 / 4)) *
              (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
                (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
                  ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                    iteratedDeriv (i + j)
                      (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                      (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ))))) := by rw [h]

private theorem iteratedDeriv_generating_cross_ambiguity_moment_sum_eq_kernel_coefficient
    (n m : ℕ) (x ω : ℝ) :
    (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)⁻¹) *
        (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
          (realHermiteGeneratingExpansionCoeff n k *
              realHermiteGeneratingExpansionCoeff m l) *
            (Complex.exp (-((x : ℂ) ^ 2 / 4)) *
              (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
                (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
                  ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                    iteratedDeriv (i + j)
                      (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                      (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ))))) =
      ((-1 : ℂ) ^ m *
        complexHermite n m
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  /-
  Pure finite coefficient identity.  After expanding the two real-Hermite
  generating coefficients and evaluating shifted Gaussian half-moments, this is
  exactly the coefficient of `u^n w^m` in the closed kernel
  `Complex.exp (u * w + z * u - star z * w)` times the scalar Gaussian factor.
  -/
  rw [← shifted_mgf_coefficient_eq_kernel_coefficient n m x ω,
    scaled_moment_sum_eq_shifted_mgf_unscaled_sum,
    ← shifted_mgf_mixed_derivative_expansion_unscaled]
  rw [show
      (fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ =>
            Complex.exp (-((x : ℂ) ^ 2 / 4)) *
              Complex.exp
                (-(u ^ 2) / 2 - (w ^ 2) / 2 +
                  (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
                  (Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2 +
                  ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) +
                      (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2) / 4)) 0) =
      fun w : ℂ =>
        Complex.exp (-((x : ℂ) ^ 2 / 4)) *
          iteratedDeriv n
            (fun u : ℂ =>
              Complex.exp
                (-(u ^ 2) / 2 - (w ^ 2) / 2 +
                  (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
                  (Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2 +
                  ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) +
                      (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2) / 4)) 0 by
    funext w
    rw [iteratedDeriv_const_mul_field]]
  rw [iteratedDeriv_const_mul_field]

private theorem iteratedDeriv_generating_cross_ambiguity_integral_eq_kernel_coefficient
    (n m : ℕ) (x ω : ℝ) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
        iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))) =
      iteratedDeriv m
        (fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ,
                realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
                  realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
                    Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ ω t : ℝ) : ℂ))) 0) 0 := by
  rw [iteratedDeriv_generating_cross_ambiguity_integral_moment_sum,
    iteratedDeriv_generating_cross_ambiguity_kernel_integral_coefficient]
  exact iteratedDeriv_generating_cross_ambiguity_moment_sum_eq_kernel_coefficient n m x ω

private theorem realHermiteTensor_stft_integral_formula_of_oneD
    {d : Nat} (kappa alpha : MultiIndex d) (ξ : PhaseSpace d)
    (h1D : ∀ q : Fin d,
      (∫ s : ℝ,
        realHermite1D (alpha q) s *
          star (realHermite1D (kappa q) (s - ξ.1 q)) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ (ξ.2 q) s : ℝ) : ℂ))) =
        (-1 : ℂ) ^ kappa q *
          Complex.exp (-(Real.pi : ℂ) * Complex.I *
            (((ξ.1 q : ℝ) : ℂ) * (ξ.2 q : ℂ))) *
            (Complex.ofReal
              (Real.exp (-(((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4))) *
              phi1D (kappa q) (alpha q) (TKappa ξ q))) :
    (∫ t : RealVec d,
      realHermiteTensorRep alpha t *
        star (realHermiteTensorRep kappa (t - ξ.1)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ξ.2 t : ℝ) : ℂ))) =
      stftModelPhase kappa ξ *
        (((WKappa ξ : ℝ) : ℂ) *
          Phi kappa alpha (TKappa ξ)) := by
  rw [tensorRep_stft_integral_eq_prod_oneD]
  rw [show
      (∏ q : Fin d,
        ∫ s : ℝ,
          realHermite1D (alpha q) s *
            star (realHermite1D (kappa q) (s - ξ.1 q)) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                ((inner ℝ (ξ.2 q) s : ℝ) : ℂ))) =
        ∏ q : Fin d,
          (-1 : ℂ) ^ kappa q *
            Complex.exp (-(Real.pi : ℂ) * Complex.I *
              (((ξ.1 q : ℝ) : ℂ) * (ξ.2 q : ℂ))) *
              (Complex.ofReal
                (Real.exp (-(((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4))) *
                phi1D (kappa q) (alpha q) (TKappa ξ q)) by
    apply Finset.prod_congr rfl
    intro q _hq
    exact h1D q]
  exact prod_oneDRealHermiteSTFT_closed_eq_model kappa alpha ξ

private theorem realHermiteTensor_stft_integral_formula
    {d : Nat} (hd : 0 < d) (kappa alpha : MultiIndex d) (ξ : PhaseSpace d) :
    (∫ t : RealVec d,
      realHermiteTensorRep alpha t *
        star (realHermiteTensorRep kappa (t - ξ.1)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ξ.2 t : ℝ) : ℂ))) =
      stftModelPhase kappa ξ *
        (((WKappa ξ : ℝ) : ℂ) *
          Phi kappa alpha (TKappa ξ)) := by
  let _ := hd
  exact realHermiteTensor_stft_integral_formula_of_oneD kappa alpha ξ
    (fun q =>
      realHermite1D_stft_integral_formula_of_halfCentered_interchange
        (alpha q) (kappa q) (ξ.1 q) (ξ.2 q)
        (iteratedDeriv_generating_cross_ambiguity_integral_eq_kernel_coefficient
          (alpha q) (kappa q) (ξ.1 q) (ξ.2 q)))

private theorem stft_model_basis_formula
    {d : Nat} (hd : 0 < d) (kappa alpha : MultiIndex d) (ξ : PhaseSpace d) :
    stftRep (varphiKappa kappa) (realHermiteTensorL2 alpha) ξ =
      stftModelPhase kappa ξ *
        (((WKappa ξ : ℝ) : ℂ) *
          Phi kappa alpha (TKappa ξ)) := by
  rw [stftRep_varphiKappa_realHermiteTensorL2_eq_tensorRep_integral]
  exact realHermiteTensor_stft_integral_formula hd kappa alpha ξ

private theorem stft_model_global_phase_of_basis_formula
    {d : Nat} (kappa : MultiIndex d)
    (hbasis : ∀ (alpha : Idx d) (ξ : PhaseSpace d),
      stftRep (varphiKappa kappa) (realHermiteTensorL2 alpha) ξ =
        stftModelPhase kappa ξ *
          (((WKappa ξ : ℝ) : ℂ) *
            Phi kappa alpha (TKappa ξ))) :
    ∃ theta : PhaseSpace d -> ℂ,
      (∀ ξ : PhaseSpace d, ‖theta ξ‖ = 1) ∧
        ∀ (U : Skappa d kappa) (ξ : PhaseSpace d),
          stftRep (varphiKappa kappa) (bKappa kappa U) ξ =
            theta ξ * (((WKappa ξ : ℝ) : ℂ) *
              toFun kappa U (TKappa ξ)) := by
  refine ⟨stftModelPhase kappa, stftModelPhase_norm kappa, ?_⟩
  intro U ξ
  let y : L2Real d := modulateL2 ξ.2 (star (translateL2 (-ξ.1) (varphiKappa kappa)))
  let L : L2Real d →L[ℂ] ℂ :=
    ((ContinuousLinearMap.apply ℂ ℂ) y).comp
      (((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))
        2 2) : L2Real d →L[ℂ] L2Real d →L[ℂ] ℂ)
  have hsummable :
      Summable (fun alpha : Idx d =>
        coeffSkappa U alpha • realHermiteTensorL2 alpha) :=
    summable_realHermiteTensorL2_coeff_smul_of_orthonormal kappa
      (realHermiteTensorL2_orthonormal (d := d)) U
  have hmap :
      L (bKappa kappa U) =
        ∑' alpha : Idx d, L (coeffSkappa U alpha • realHermiteTensorL2 alpha) := by
    unfold bKappa
    exact ContinuousLinearMap.map_tsum L hsummable
  have hstft :
      ∀ f : L2Real d, stftRep (varphiKappa kappa) f ξ = L f := by
    intro f
    simpa [L, y] using stftRep_eq_lpPairing (varphiKappa kappa) f ξ
  calc
    stftRep (varphiKappa kappa) (bKappa kappa U) ξ =
        L (bKappa kappa U) := hstft (bKappa kappa U)
    _ = ∑' alpha : Idx d, L (coeffSkappa U alpha • realHermiteTensorL2 alpha) := hmap
    _ = ∑' alpha : Idx d,
        coeffSkappa U alpha *
          stftRep (varphiKappa kappa) (realHermiteTensorL2 alpha) ξ := by
          apply tsum_congr
          intro alpha
          rw [map_smul]
          simp [hstft]
    _ = ∑' alpha : Idx d,
        coeffSkappa U alpha *
          (stftModelPhase kappa ξ *
            (((WKappa ξ : ℝ) : ℂ) *
              Phi kappa alpha (TKappa ξ))) := by
          apply tsum_congr
          intro alpha
          rw [hbasis alpha ξ]
    _ = ∑' alpha : Idx d,
        (stftModelPhase kappa ξ * ((WKappa ξ : ℝ) : ℂ)) *
          (coeffSkappa U alpha * Phi kappa alpha (TKappa ξ)) := by
          apply tsum_congr
          intro alpha
          ring
    _ = (stftModelPhase kappa ξ * ((WKappa ξ : ℝ) : ℂ)) *
        ∑' alpha : Idx d, coeffSkappa U alpha * Phi kappa alpha (TKappa ξ) := by rw [tsum_mul_left]
    _ = stftModelPhase kappa ξ *
        (((WKappa ξ : ℝ) : ℂ) * toFun kappa U (TKappa ξ)) := by
          simp [toFun]
          ring

private theorem stft_model_global_phase
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    ∃ theta : PhaseSpace d -> ℂ,
      (∀ ξ : PhaseSpace d, ‖theta ξ‖ = 1) ∧
        ∀ (U : Skappa d kappa) (ξ : PhaseSpace d),
          stftRep (varphiKappa kappa) (bKappa kappa U) ξ =
            theta ξ * (((WKappa ξ : ℝ) : ℂ) *
              toFun kappa U (TKappa ξ)) := stft_model_global_phase_of_basis_formula kappa
    (fun alpha ξ => stft_model_basis_formula hd kappa alpha ξ)

private theorem stft_model_modulus_of_global_phase_formula
    {d : Nat} (kappa : MultiIndex d) (theta : PhaseSpace d -> ℂ)
    (htheta : ∀ ξ : PhaseSpace d, ‖theta ξ‖ = 1)
    (hmodel : ∀ (U : Skappa d kappa) (ξ : PhaseSpace d),
      stftRep (varphiKappa kappa) (bKappa kappa U) ξ =
        theta ξ * (((WKappa ξ : ℝ) : ℂ) *
          toFun kappa U (TKappa ξ)))
    (U : Skappa d kappa) (ξ : PhaseSpace d) :
    ‖stftRep (varphiKappa kappa) (bKappa kappa U) ξ‖ =
      WKappa ξ * ‖toFun kappa U (TKappa ξ)‖ := by
  rw [hmodel U ξ]
  have hW_nonneg : 0 ≤ WKappa ξ := le_of_lt (WKappa_pos ξ)
  calc
    ‖theta ξ * (((WKappa ξ : ℝ) : ℂ) *
        toFun kappa U (TKappa ξ))‖ =
        ‖theta ξ‖ * ‖((WKappa ξ : ℝ) : ℂ)‖ *
          ‖toFun kappa U (TKappa ξ)‖ := by rw [norm_mul, norm_mul, mul_assoc]
    _ = WKappa ξ * ‖toFun kappa U (TKappa ξ)‖ := by
          rw [htheta ξ]
          simp [hW_nonneg]

theorem stft_model_modulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (U : Skappa d kappa) (ξ : PhaseSpace d) :
    ‖stftRep (varphiKappa kappa) (bKappa kappa U) ξ‖ =
      WKappa ξ * ‖toFun kappa U (TKappa ξ)‖ := by
  let _ := hd
  have hphase_model :
      ∃ theta : PhaseSpace d -> ℂ,
        (∀ ξ : PhaseSpace d, ‖theta ξ‖ = 1) ∧
          ∀ (U : Skappa d kappa) (ξ : PhaseSpace d),
            stftRep (varphiKappa kappa) (bKappa kappa U) ξ =
              theta ξ * (((WKappa ξ : ℝ) : ℂ) *
                toFun kappa U (TKappa ξ)) :=
    stft_model_global_phase hd kappa
  rcases hphase_model with ⟨theta, htheta, hmodel⟩
  exact stft_model_modulus_of_global_phase_formula kappa theta htheta hmodel U ξ

private theorem oneDWindowAmbiguityFactor_one_finite_expansion_integral
    (x ω : ℝ) :
    oneDWindowAmbiguityFactor 1 x ω =
      ∫ t : ℝ,
        ∑ k ∈ Finset.range 2, ∑ l ∈ Finset.range 2,
          (realHermite1DExpansionScale 1 *
              realHermiteGeneratingExpansionCoeff 1 k *
                star (realHermite1DExpansionScale 1 *
                  realHermiteGeneratingExpansionCoeff 1 l)) *
            oneDWindowAmbiguityMonomialKernel k l x ω t := by
  simpa using oneDWindowAmbiguityFactor_finite_expansion_integral 1 x ω

private theorem oneDWindowAmbiguityFactor_two_finite_expansion_integral
    (x ω : ℝ) :
    oneDWindowAmbiguityFactor 2 x ω =
      ∫ t : ℝ,
        ∑ k ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
          (realHermite1DExpansionScale 2 *
              realHermiteGeneratingExpansionCoeff 2 k *
                star (realHermite1DExpansionScale 2 *
                  realHermiteGeneratingExpansionCoeff 2 l)) *
            oneDWindowAmbiguityMonomialKernel k l x ω t := by
  simpa using oneDWindowAmbiguityFactor_finite_expansion_integral 2 x ω

private theorem oneDWindowAmbiguityFactor_one_eq_normalized_monomial_kernel_integral
    (x ω : ℝ) :
    oneDWindowAmbiguityFactor 1 x ω =
      ∫ t : ℝ,
        ((2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          oneDWindowAmbiguityMonomialKernel 1 1 x ω t) := by
  rw [oneDWindowAmbiguityFactor_one_finite_expansion_integral]
  simp only [realHermite1DExpansionScale, Nat.factorial_one, Nat.cast_one, Real.sqrt_one,
    Complex.ofReal_one, ne_eq, one_ne_zero, not_false_eq_true, div_self, one_mul, RCLike.star_def,
    mul_assoc, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    realHermiteGeneratingExpansionCoeff_one_zero, map_zero, zero_mul, mul_zero,
    realHermiteGeneratingExpansionCoeff_one_one, one_div, map_mul, Complex.conj_ofReal, zero_add]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [show ((Real.pi ^ (-(4 : ℝ)⁻¹) : ℝ) : ℂ) * ((Real.sqrt 2 : ℂ) *
        (((Real.pi ^ (-(4 : ℝ)⁻¹) : ℝ) : ℂ) * ((Real.sqrt 2 : ℂ) *
          oneDWindowAmbiguityMonomialKernel 1 1 x ω t))) =
      ((((Real.pi ^ (-(4 : ℝ)⁻¹) : ℝ) : ℂ) *
        ((Real.pi ^ (-(4 : ℝ)⁻¹) : ℝ) : ℂ)) *
          ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) *
            oneDWindowAmbiguityMonomialKernel 1 1 x ω t) by
    ring]
  rw [realHermiteGenerating_pi_quarter_mul_self]
  rw [show ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) = 2 by
    norm_num [← Complex.ofReal_mul, Real.sq_sqrt]]
  ring

private theorem oneDWindowAmbiguityFactor_two_eq_finite_monomial_kernel_integral
    (x ω : ℝ) :
    oneDWindowAmbiguityFactor 2 x ω =
      ∫ t : ℝ,
        (((1 / 2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            oneDWindowAmbiguityMonomialKernel 0 0 x ω t) -
          (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            oneDWindowAmbiguityMonomialKernel 0 2 x ω t) -
          (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            oneDWindowAmbiguityMonomialKernel 2 0 x ω t) +
          ((2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            oneDWindowAmbiguityMonomialKernel 2 2 x ω t)) := by
  rw [oneDWindowAmbiguityFactor_two_finite_expansion_integral]
  simp only [realHermite1DExpansionScale, Nat.factorial_two, Nat.cast_ofNat, star_mul', star_div₀,
    RCLike.star_def, Complex.conj_ofReal, star_ofNat, mul_assoc, Finset.sum_range_succ,
    Finset.range_one, Finset.sum_singleton, realHermiteGeneratingExpansionCoeff_two_zero, one_div,
    map_neg, neg_mul, mul_neg, realHermiteGeneratingExpansionCoeff_two_one, map_zero, zero_mul,
    mul_zero, add_zero, realHermiteGeneratingExpansionCoeff_two_two, map_mul, neg_neg, neg_zero]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  have hsqrt2 := sqrtTwoC_sq
  have hpi := piPowQuarterC_sq
  simp only [map_ofNat]
  ring_nf at hsqrt2 hpi ⊢
  rw [hsqrt2, hpi]
  ring

private theorem oneDWindowAmbiguityFactor_three_eq_finite_monomial_kernel_integral
    (x ω : ℝ) :
    oneDWindowAmbiguityFactor 3 x ω =
      ∫ t : ℝ,
        (((3 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            oneDWindowAmbiguityMonomialKernel 1 1 x ω t) -
          ((2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            oneDWindowAmbiguityMonomialKernel 1 3 x ω t) -
          ((2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            oneDWindowAmbiguityMonomialKernel 3 1 x ω t) +
          ((4 / 3 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            oneDWindowAmbiguityMonomialKernel 3 3 x ω t)) := by
  rw [oneDWindowAmbiguityFactor_finite_expansion_integral]
  simp only [Nat.reduceAdd, realHermite1DExpansionScale, star_mul', star_div₀, RCLike.star_def,
    Complex.conj_ofReal, star_natCast, mul_assoc, Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton, realHermiteGeneratingExpansionCoeff_three_zero, map_zero, zero_mul,
    mul_zero, realHermiteGeneratingExpansionCoeff_three_one, one_div, map_neg, map_mul, neg_mul,
    mul_neg, zero_add, realHermiteGeneratingExpansionCoeff_three_two, add_zero,
    realHermiteGeneratingExpansionCoeff_three_three, neg_zero, neg_neg]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  have hsqrt2 := sqrtTwoC_sq
  have hsqrt6_sq :
      (Real.sqrt (Nat.factorial 3 : ℝ) : ℂ) ^ 2 = (6 : ℂ) := by
    norm_num [← Complex.ofReal_pow, Real.sq_sqrt]
  have hpi :
      (((Real.pi ^ (-(4 : ℝ)⁻¹) : ℝ) : ℂ) ^ 2) =
        (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt Real.pi_pos)]
    norm_num
  ring_nf at hsqrt2 hsqrt6_sq hpi ⊢
  rw [hsqrt2, hsqrt6_sq, hpi]
  have hstar_two : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
  have hstar_three : (starRingEnd ℂ) (3 : ℂ) = 3 := Complex.conj_ofReal 3
  rw [hstar_two, hstar_three]
  ring

private theorem oneDWindowAmbiguityFactor_two_eq_normalized_kernel_coefficient_of_finite_kernel
    (x ω : ℝ)
    (hfinite :
      (∫ t : ℝ,
        (((1 / 2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            oneDWindowAmbiguityMonomialKernel 0 0 x ω t) -
          (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            oneDWindowAmbiguityMonomialKernel 0 2 x ω t) -
          (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            oneDWindowAmbiguityMonomialKernel 2 0 x ω t) +
          ((2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            oneDWindowAmbiguityMonomialKernel 2 2 x ω t))) =
        ((Nat.factorial 2 : ℂ)⁻¹) *
          (iteratedDeriv 2
            (fun w : ℂ =>
              iteratedDeriv 2
                (fun u : ℂ =>
                  Complex.exp
                    (u * w +
                      (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                          (Real.sqrt 2 : ℂ)) * u -
                        star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                          (Real.sqrt 2 : ℂ)) * w)) 0) 0 *
            Complex.ofReal
              (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))))) :
    oneDWindowAmbiguityFactor 2 x ω =
      ((Nat.factorial 2 : ℂ)⁻¹) *
        (iteratedDeriv 2
          (fun w : ℂ =>
            iteratedDeriv 2
              (fun u : ℂ =>
                Complex.exp
                  (u * w +
                    (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * u -
                      star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * w)) 0) 0 *
          Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))) := by
  rw [oneDWindowAmbiguityFactor_two_eq_finite_monomial_kernel_integral]
  exact hfinite

private theorem oneDWindowAmbiguityFactor_one_closed_of_monomial_kernel_one_one
    (x ω : ℝ)
    (h11 :
      (∫ t : ℝ,
        ((2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          oneDWindowAmbiguityMonomialKernel 1 1 x ω t)) =
        (-1 : ℂ) ^ (1 : Nat) *
          phi1D 1 1
            (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) *
          Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))) :
    oneDWindowAmbiguityFactor 1 x ω =
      (-1 : ℂ) ^ (1 : Nat) *
        phi1D 1 1
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  rw [oneDWindowAmbiguityFactor_one_eq_normalized_monomial_kernel_integral]
  exact h11

private theorem neg_one_pow_one_mul_phi1D_one_one (z : ℂ) :
    (-1 : ℂ) ^ (1 : Nat) * phi1D 1 1 z = 1 - z * star z := by
  simp [phi1D, complexHermite, Finset.sum_range_succ]
  ring

private theorem neg_one_pow_two_mul_phi1D_two_two (z : ℂ) :
    (-1 : ℂ) ^ (2 : Nat) * phi1D 2 2 z =
      1 - (2 : ℂ) * z * star z + (1 / 2 : ℂ) * (z * star z) ^ (2 : Nat) := by
  simp [phi1D, complexHermite, Finset.sum_range_succ]
  ring

private theorem neg_one_pow_three_mul_phi1D_three_three (z : ℂ) :
    (-1 : ℂ) ^ (3 : Nat) * phi1D 3 3 z =
      1 - (3 : ℂ) * (z * star z) + (3 / 2 : ℂ) * (z * star z) ^ (2 : Nat) -
        (1 / 6 : ℂ) * (z * star z) ^ (3 : Nat) := by
  simp [phi1D, complexHermite, Finset.sum_range_succ]
  ring

private theorem oneDWindowAmbiguityFactor_one_closed_of_shifted_moment
    (x ω : ℝ)
    (hmoment :
      oneDWindowAmbiguityOneOneShiftedMoment x ω =
        (-1 : ℂ) ^ (1 : Nat) *
          phi1D 1 1
            (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) *
          Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))) :
    oneDWindowAmbiguityFactor 1 x ω =
      (-1 : ℂ) ^ (1 : Nat) *
        phi1D 1 1
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  apply oneDWindowAmbiguityFactor_one_closed_of_monomial_kernel_one_one
  rw [oneDWindowAmbiguityMonomialKernel_one_one_normalized_integral_eq_shifted_moment]
  exact hmoment

private theorem oneDWindowAmbiguityFactor_one_closed_of_shifted_moment_simplified
    (x ω : ℝ)
    (hmoment :
      oneDWindowAmbiguityOneOneShiftedMoment x ω =
        (1 -
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ)) *
            star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ))) *
          Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))) :
    oneDWindowAmbiguityFactor 1 x ω =
      (-1 : ℂ) ^ (1 : Nat) *
        phi1D 1 1
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  apply oneDWindowAmbiguityFactor_one_closed_of_shifted_moment
  rw [neg_one_pow_one_mul_phi1D_one_one]
  exact hmoment

private theorem oneDWindowAmbiguityOneOneShiftedMoment_eq_closed
    (x ω : ℝ) :
    oneDWindowAmbiguityOneOneShiftedMoment x ω =
      (1 -
        (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ)) *
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  let zeta : ℂ :=
    ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
      (Real.sqrt 2 : ℂ)
  let E : ℂ :=
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))
  let phi : ℝ → ℂ := fun t =>
    ((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ)) *
      realHermiteGenerating (t - (1 / 2 : ℝ) * x) 0
  let F : ℂ → ℂ := fun u =>
    ∫ t : ℝ,
      (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u * phi t) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ ω t : ℝ) : ℂ))
  have hzero_mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp [Metric.mem_ball, dist_self]
  have hF_meas : ∀ᶠ u in 𝓝 (0 : ℂ),
      AEStronglyMeasurable
        (fun t : ℝ =>
          (phi t * realHermiteGenerating (t - (1 / 2 : ℝ) * (-x)) u) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ)))
        (volume : Measure ℝ) := by
    refine Filter.Eventually.of_forall fun u => ?_
    exact Continuous.aestronglyMeasurable (by
      simp only [phi]
      unfold realHermiteGenerating
      fun_prop)
  have hF_int_meas : AEStronglyMeasurable
      (fun t : ℝ =>
        (phi t * realHermiteGenerating (t - (1 / 2 : ℝ) * (-x)) 0) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      (volume : Measure ℝ) := Continuous.aestronglyMeasurable (by
      simp only [phi]
      unfold realHermiteGenerating
      fun_prop)
  have hF_int_bound : ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ),
      ‖(phi t * realHermiteGenerating (t - (1 / 2 : ℝ) * (-x)) 0) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))‖ ≤
        shiftedGeneratingRightDerivBound 0 0 x 1 t :=
    ae_of_all _ fun t => by
      simpa [phi, sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc,
        mul_comm, mul_left_comm] using
        shifted_generating_right_deriv_bound_of_mem_ball
          (u := 0) (w0 := 0) x ω (R := 1) zero_lt_one t (z := 0) hzero_mem
  have hF_int : Integrable
      (fun t : ℝ =>
        (phi t * realHermiteGenerating (t - (1 / 2 : ℝ) * (-x)) 0) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      (volume : Measure ℝ) :=
    (shiftedGeneratingRightDerivBound_integrable 0 0 x 1).mono'
      hF_int_meas hF_int_bound
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ =>
        (phi t *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * (-x) : ℝ) : ℂ) - 0) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * (-x)) 0)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      (volume : Measure ℝ) := Continuous.aestronglyMeasurable (by
      simp only [phi]
      unfold realHermiteGenerating
      fun_prop)
  have h_bound : ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ), ∀ u : ℂ,
      u ∈ Metric.ball (0 : ℂ) 1 →
      ‖(phi t *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * (-x) : ℝ) : ℂ) - u) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * (-x)) u)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))‖ ≤
        shiftedGeneratingLeftRightDerivBound x t :=
    ae_of_all _ fun t u hu => by
      simpa [phi, sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc,
        mul_comm, mul_left_comm] using
        shifted_generating_left_right_deriv_bound_of_mem_ball x ω t (z := u) hu
  have hderiv_raw : HasDerivAt F
      (∫ t : ℝ,
        (phi t *
            (((Real.sqrt 2 : ℂ) * ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ)) *
              realHermiteGenerating (t + (1 / 2 : ℝ) * x) 0)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      0 := by
    have h :=
      hasDerivAt_integral_fixed_mul_shifted_modulated_realHermiteGenerating_right_of_bound
        (phi := phi) (x := -x) (ω := ω) (w0 := 0)
        (s := Metric.ball (0 : ℂ) 1)
        (bound := shiftedGeneratingLeftRightDerivBound x)
        (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
        hF_meas hF_int hF'_meas h_bound
        (shiftedGeneratingLeftRightDerivBound_integrable x)
    simpa [F, sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc,
      mul_comm, mul_left_comm] using h
  have hmoment_integral :
      (∫ t : ℝ,
        (phi t *
            (((Real.sqrt 2 : ℂ) * ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ)) *
              realHermiteGenerating (t + (1 / 2 : ℝ) * x) 0)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))) =
        oneDWindowAmbiguityOneOneShiftedMoment x ω := by
    calc
      (∫ t : ℝ,
        (phi t *
            (((Real.sqrt 2 : ℂ) * ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ)) *
              realHermiteGenerating (t + (1 / 2 : ℝ) * x) 0)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))) =
          ∫ t : ℝ,
            ((2 : ℂ) * ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              oneDWindowAmbiguityMonomialKernel 1 1 x ω t) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          simp only [phi]
          rw [oneDWindowAmbiguityMonomialKernel, star_complex_monomial_gaussian]
          unfold realHermiteGenerating complexMonomialGaussian
          simp only [pow_one]
          ring_nf
          rw [sqrtTwoC_sq]
          have hpi :
              (((Real.pi ^ (-1 / 4 : ℝ) : ℝ) : ℂ) ^ 2) =
                (((Real.pi ^ (-1 / 2 : ℝ) : ℝ) : ℂ)) := by
            rw [← Complex.ofReal_pow]
            congr 1
            rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt Real.pi_pos)]
            norm_num
          rw [hpi]
          ring_nf
      _ = oneDWindowAmbiguityOneOneShiftedMoment x ω :=
          oneDWindowAmbiguityMonomialKernel_one_one_normalized_integral_eq_shifted_moment x ω
  have hderiv_moment : HasDerivAt F (oneDWindowAmbiguityOneOneShiftedMoment x ω) 0 := by
    convert hderiv_raw using 1
    exact hmoment_integral.symm
  have hF_closed :
      F = fun u : ℂ => (u - star zeta) * Complex.exp (zeta * u) * E := by
    funext u
    have h := integral_shifted_generating_right_deriv_eq_closed u 0 x ω
    calc
      F u = ∫ t : ℝ,
          (realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
              (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - 0) *
                realHermiteGenerating (t - (1 / 2 : ℝ) * x) 0)) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        simp only [phi, sub_zero]
      _ = (u - star zeta) * Complex.exp (zeta * u) * E := by
        rw [h]
        simp only [zeta, E, zero_add, mul_zero, sub_zero]
  have hclosed_deriv :
      HasDerivAt (fun u : ℂ => (u - star zeta) * Complex.exp (zeta * u) * E)
        ((1 - zeta * star zeta) * E) 0 := by
    have hlin : HasDerivAt (fun u : ℂ => u - star zeta) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).sub_const (star zeta)
    have harg : HasDerivAt (fun u : ℂ => zeta * u) zeta 0 :=
      hasDerivAt_const_mul zeta
    have hprod := hlin.mul harg.cexp
    have hd := hprod.mul_const E
    rw [show (1 * Complex.exp (zeta * 0) +
        (0 - star zeta) * (Complex.exp (zeta * 0) * zeta)) * E
        = (1 - zeta * star zeta) * E by
      simp only [mul_zero, Complex.exp_zero, mul_one, zero_sub]; ring] at hd
    exact hd
  have hclosed_F : HasDerivAt F ((1 - zeta * star zeta) * E) 0 := by
    simpa [hF_closed] using hclosed_deriv
  simpa [zeta, E] using hderiv_moment.unique hclosed_F

private theorem oneDWindowAmbiguityFactor_one_closed
    (x ω : ℝ) :
    oneDWindowAmbiguityFactor 1 x ω =
      (-1 : ℂ) ^ (1 : Nat) *
        phi1D 1 1
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) :=
  oneDWindowAmbiguityFactor_one_closed_of_shifted_moment_simplified x ω
    (oneDWindowAmbiguityOneOneShiftedMoment_eq_closed x ω)

private theorem normalized_kernel_coefficient_eq_closed
    (k : Nat) (x ω : ℝ) :
    ((Nat.factorial k : ℂ)⁻¹) *
      (iteratedDeriv k
        (fun w : ℂ =>
          iteratedDeriv k
            (fun u : ℂ =>
              Complex.exp
                (u * w +
                  (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                      (Real.sqrt 2 : ℂ)) * u -
                    star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                      (Real.sqrt 2 : ℂ)) * w)) 0) 0 *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))) =
      (-1 : ℂ) ^ k *
        phi1D k k
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  let z : ℂ :=
    ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
      (Real.sqrt 2 : ℂ)
  let E : ℂ :=
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))
  change ((Nat.factorial k : ℂ)⁻¹) *
      (iteratedDeriv k
        (fun w : ℂ =>
          iteratedDeriv k
            (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) 0) 0 * E) =
    (-1 : ℂ) ^ k * phi1D k k z * E
  rw [iteratedDeriv_cexp_ambiguity_kernel_diag_at_zero,
    ← inv_factorial_mul_complexHermite_self_eq_phi1D k z]
  ring

private theorem normalized_kernel_coefficient_two_eq_closed_simplified
    (x ω : ℝ) :
    ((Nat.factorial 2 : ℂ)⁻¹) *
      (iteratedDeriv 2
        (fun w : ℂ =>
          iteratedDeriv 2
            (fun u : ℂ =>
              Complex.exp
                (u * w +
                  (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                      (Real.sqrt 2 : ℂ)) * u -
                    star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                      (Real.sqrt 2 : ℂ)) * w)) 0) 0 *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))) =
      (1 -
          (2 : ℂ) *
            (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) *
              star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                (Real.sqrt 2 : ℂ)) +
          (1 / 2 : ℂ) *
            ((((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                (Real.sqrt 2 : ℂ)) *
              star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                (Real.sqrt 2 : ℂ))) ^ (2 : Nat)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  rw [normalized_kernel_coefficient_eq_closed 2 x ω, neg_one_pow_two_mul_phi1D_two_two]

private theorem normalized_kernel_coefficient_three_eq_closed_simplified
    (x ω : ℝ) :
    ((Nat.factorial 3 : ℂ)⁻¹) *
      (iteratedDeriv 3
        (fun w : ℂ =>
          iteratedDeriv 3
            (fun u : ℂ =>
              Complex.exp
                (u * w +
                  (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                      (Real.sqrt 2 : ℂ)) * u -
                    star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                      (Real.sqrt 2 : ℂ)) * w)) 0) 0 *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))) =
      (1 -
          (3 : ℂ) *
            ((((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) *
              star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                (Real.sqrt 2 : ℂ))) +
          (3 / 2 : ℂ) *
            ((((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) *
              star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                (Real.sqrt 2 : ℂ))) ^ (2 : Nat) -
          (1 / 6 : ℂ) *
            ((((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) *
              star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                (Real.sqrt 2 : ℂ))) ^ (3 : Nat)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  rw [normalized_kernel_coefficient_eq_closed 3 x ω, neg_one_pow_three_mul_phi1D_three_three]

private noncomputable def oneDWindowAmbiguityTwoClosedCoefficient
    (x ω : ℝ) : ℂ :=
  (1 -
      (2 : ℂ) *
        (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ)) *
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ)) +
      (1 / 2 : ℂ) *
        ((((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ)) *
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) ^ (2 : Nat)) *
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))

private noncomputable def oneDWindowAmbiguityThreeClosedCoefficient
    (x ω : ℝ) : ℂ :=
  (1 -
      (3 : ℂ) *
        ((((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ)) *
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) +
      (3 / 2 : ℂ) *
        ((((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ)) *
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) ^ (2 : Nat) -
      (1 / 6 : ℂ) *
        ((((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ)) *
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) ^ (3 : Nat)) *
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))

private theorem oneDWindowAmbiguityTwoShiftedFourthMoment_eq_closed
    (x ω : ℝ) :
    oneDWindowAmbiguityTwoShiftedFourthMoment x ω =
      oneDWindowAmbiguityTwoClosedCoefficient x ω := by
  let lam : ℂ := -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)
  let A : ℂ := (2 : ℂ) + (x : ℂ) ^ 2
  let C : ℂ := (1 / 2 : ℂ) - (x : ℂ) ^ 2 / 2 + (x : ℂ) ^ 4 / 8
  let ex : ℂ := Complex.exp (-((x : ℂ) ^ 2 / 4))
  let E : ℂ :=
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))
  let P : ℂ :=
    (1 - (2 : ℂ) *
      (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
        (Real.sqrt 2 : ℂ)) *
        star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ)) +
      (1 / 2 : ℂ) *
        ((((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ)) *
        star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ))) ^ (2 : Nat))
  let μ := ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)
  have h_to_gauss :
      oneDWindowAmbiguityTwoShiftedFourthMoment x ω =
        ex * ∫ t : ℝ,
          ((2 : ℂ) * (t : ℂ) ^ 4 - A * (t : ℂ) ^ 2 + C) *
            Complex.exp (lam * (t : ℂ)) ∂μ := by
    unfold oneDWindowAmbiguityTwoShiftedFourthMoment
    rw [show
        (∫ t : ℝ,
          ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ((1 / 2 : ℂ) -
              ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ (2 : Nat) -
              ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ (2 : Nat) +
              (2 : ℂ) *
                (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ (2 : Nat) *
                  ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ (2 : Nat))) *
              oneDWindowAmbiguityShiftedModulatedGaussian x ω t) =
          ∫ t : ℝ,
            ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              Complex.exp (-((t : ℂ) ^ 2)) *
                (((2 : ℂ) * (t : ℂ) ^ 4 - A * (t : ℂ) ^ 2 + C) * ex *
                  Complex.exp (lam * (t : ℂ))) by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        rw [oneDWindowAmbiguityTwoShiftedPolynomial_eq]
        unfold oneDWindowAmbiguityShiftedModulatedGaussian
        simp only [A, C, ex, lam]
        rw [show Complex.exp (-((t : ℂ) ^ 2 + (x : ℂ) ^ 2 / 4)) =
            Complex.exp (-((t : ℂ) ^ 2)) * Complex.exp (-((x : ℂ) ^ 2 / 4)) by
          rw [← Complex.exp_add]
          congr 1
          ring]
        ring_nf]
    rw [← integral_gaussian_zero_half_eq_density
      (fun t : ℝ =>
        ((2 : ℂ) * (t : ℂ) ^ 4 - A * (t : ℂ) ^ 2 + C) * ex *
          Complex.exp (lam * (t : ℂ)))]
    rw [show (∫ t : ℝ,
        ((2 : ℂ) * (t : ℂ) ^ 4 - A * (t : ℂ) ^ 2 + C) * ex *
          Complex.exp (lam * (t : ℂ)) ∂μ) =
        ex * ∫ t : ℝ,
          ((2 : ℂ) * (t : ℂ) ^ 4 - A * (t : ℂ) ^ 2 + C) *
            Complex.exp (lam * (t : ℂ)) ∂μ by
      rw [show (fun t : ℝ =>
          ((2 : ℂ) * (t : ℂ) ^ 4 - A * (t : ℂ) ^ 2 + C) * ex *
            Complex.exp (lam * (t : ℂ))) =
          fun t : ℝ => ex *
            (((2 : ℂ) * (t : ℂ) ^ 4 - A * (t : ℂ) ^ 2 + C) *
              Complex.exp (lam * (t : ℂ))) by
        funext t
        ring]
      exact MeasureTheory.integral_const_mul (r := ex)
        (f := fun t : ℝ =>
          ((2 : ℂ) * (t : ℂ) ^ 4 - A * (t : ℂ) ^ 2 + C) *
            Complex.exp (lam * (t : ℂ)))]
  have hclosed_poly :
      (2 : ℂ) * ((3 / 4 : ℂ) + (3 / 4 : ℂ) * lam ^ 2 + lam ^ 4 / 16) -
          A * ((1 / 2 : ℂ) + lam ^ 2 / 4) + C = P := by
    simpa [P, lam, A, C] using oneDWindowAmbiguityTwoClosedPolynomial_eq x ω
  have hexp : ex * Complex.exp (lam ^ 2 / 4) = E := by
    simpa [ex, lam, E] using gaussian_half_exp_factor_eq_closed_exp x ω
  rw [h_to_gauss, gaussian_half_quartic_exp_integral, hclosed_poly]
  unfold oneDWindowAmbiguityTwoClosedCoefficient
  change ex * (P * Complex.exp (lam ^ 2 / 4)) = P * E
  rw [mul_left_comm, hexp]

private theorem oneDWindowAmbiguityThreeShiftedSixthMoment_eq_closed
    (x ω : ℝ) :
    oneDWindowAmbiguityThreeShiftedSixthMoment x ω =
      oneDWindowAmbiguityThreeClosedCoefficient x ω := by
  let lam : ℂ := -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)
  let A : ℂ := (4 : ℂ) + (x : ℂ) ^ 2
  let B : ℂ := (3 : ℂ) + (x : ℂ) ^ 4 / 4
  let C : ℂ :=
    -(3 / 4 : ℂ) * (x : ℂ) ^ 2 + (1 / 4 : ℂ) * (x : ℂ) ^ 4 -
      (1 / 48 : ℂ) * (x : ℂ) ^ 6
  let ex : ℂ := Complex.exp (-((x : ℂ) ^ 2 / 4))
  let E : ℂ :=
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))
  let P : ℂ :=
    (1 - (3 : ℂ) *
      ((((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
        (Real.sqrt 2 : ℂ)) *
        star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ))) +
      (3 / 2 : ℂ) *
        ((((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ)) *
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) ^ (2 : Nat) -
      (1 / 6 : ℂ) *
        ((((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ)) *
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) ^ (3 : Nat))
  let μ := ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)
  have h_to_gauss :
      oneDWindowAmbiguityThreeShiftedSixthMoment x ω =
        ex * ∫ t : ℝ,
          ((4 / 3 : ℂ) * (t : ℂ) ^ 6 - A * (t : ℂ) ^ 4 +
              B * (t : ℂ) ^ 2 + C) *
            Complex.exp (lam * (t : ℂ)) ∂μ := by
    unfold oneDWindowAmbiguityThreeShiftedSixthMoment
    rw [show
        (∫ t : ℝ,
          ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ((4 / 3 : ℂ) * (t : ℂ) ^ (6 : Nat) -
              ((4 : ℂ) + (x : ℂ) ^ (2 : Nat)) * (t : ℂ) ^ (4 : Nat) +
              ((3 : ℂ) + (x : ℂ) ^ (4 : Nat) / 4) * (t : ℂ) ^ (2 : Nat) -
              (3 / 4 : ℂ) * (x : ℂ) ^ (2 : Nat) +
              (1 / 4 : ℂ) * (x : ℂ) ^ (4 : Nat) -
              (1 / 48 : ℂ) * (x : ℂ) ^ (6 : Nat)) *
            oneDWindowAmbiguityShiftedModulatedGaussian x ω t) =
          ∫ t : ℝ,
            ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              Complex.exp (-((t : ℂ) ^ 2)) *
                (((4 / 3 : ℂ) * (t : ℂ) ^ 6 - A * (t : ℂ) ^ 4 +
                    B * (t : ℂ) ^ 2 + C) * ex *
                  Complex.exp (lam * (t : ℂ))) by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        unfold oneDWindowAmbiguityShiftedModulatedGaussian
        simp only [A, B, C, ex, lam]
        rw [show Complex.exp (-((t : ℂ) ^ 2 + (x : ℂ) ^ 2 / 4)) =
            Complex.exp (-((t : ℂ) ^ 2)) * Complex.exp (-((x : ℂ) ^ 2 / 4)) by
          rw [← Complex.exp_add]
          congr 1
          ring]
        ring_nf]
    rw [← integral_gaussian_zero_half_eq_density
      (fun t : ℝ =>
        ((4 / 3 : ℂ) * (t : ℂ) ^ 6 - A * (t : ℂ) ^ 4 +
            B * (t : ℂ) ^ 2 + C) * ex *
          Complex.exp (lam * (t : ℂ)))]
    rw [show (∫ t : ℝ,
        ((4 / 3 : ℂ) * (t : ℂ) ^ 6 - A * (t : ℂ) ^ 4 +
            B * (t : ℂ) ^ 2 + C) * ex *
          Complex.exp (lam * (t : ℂ)) ∂μ) =
        ex * ∫ t : ℝ,
          ((4 / 3 : ℂ) * (t : ℂ) ^ 6 - A * (t : ℂ) ^ 4 +
              B * (t : ℂ) ^ 2 + C) *
            Complex.exp (lam * (t : ℂ)) ∂μ by
      rw [show (fun t : ℝ =>
          ((4 / 3 : ℂ) * (t : ℂ) ^ 6 - A * (t : ℂ) ^ 4 +
              B * (t : ℂ) ^ 2 + C) * ex *
            Complex.exp (lam * (t : ℂ))) =
          fun t : ℝ => ex *
            (((4 / 3 : ℂ) * (t : ℂ) ^ 6 - A * (t : ℂ) ^ 4 +
                B * (t : ℂ) ^ 2 + C) *
              Complex.exp (lam * (t : ℂ))) by
        funext t
        ring]
      exact MeasureTheory.integral_const_mul (r := ex)
        (f := fun t : ℝ =>
          ((4 / 3 : ℂ) * (t : ℂ) ^ 6 - A * (t : ℂ) ^ 4 +
              B * (t : ℂ) ^ 2 + C) *
            Complex.exp (lam * (t : ℂ)))]
  have hclosed_poly :
      (4 / 3 : ℂ) *
          ((15 / 8 : ℂ) + (45 / 16 : ℂ) * lam ^ 2 +
            (15 / 32 : ℂ) * lam ^ 4 + lam ^ 6 / 64) -
        A * ((3 / 4 : ℂ) + (3 / 4 : ℂ) * lam ^ 2 + lam ^ 4 / 16) +
        B * ((1 / 2 : ℂ) + lam ^ 2 / 4) + C = P := by
    simpa [P, lam, A, B, C, mul_assoc] using
      oneDWindowAmbiguityThreeClosedPolynomial_eq x ω
  have hexp : ex * Complex.exp (lam ^ 2 / 4) = E := by
    simpa [ex, lam, E] using gaussian_half_exp_factor_eq_closed_exp x ω
  rw [h_to_gauss, gaussian_half_sextic_exp_integral, hclosed_poly]
  unfold oneDWindowAmbiguityThreeClosedCoefficient
  change ex * (P * Complex.exp (lam ^ 2 / 4)) = P * E
  rw [mul_left_comm, hexp]

private theorem oneDWindowAmbiguityFactor_two_eq_normalized_kernel_coefficient_of_shifted_moment
    (x ω : ℝ)
    (hmoment :
      oneDWindowAmbiguityTwoShiftedFourthMoment x ω =
        oneDWindowAmbiguityTwoClosedCoefficient x ω) :
    oneDWindowAmbiguityFactor 2 x ω =
      ((Nat.factorial 2 : ℂ)⁻¹) *
        (iteratedDeriv 2
          (fun w : ℂ =>
            iteratedDeriv 2
              (fun u : ℂ =>
                Complex.exp
                  (u * w +
                    (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * u -
                      star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * w)) 0) 0 *
          Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))) := by
  apply oneDWindowAmbiguityFactor_two_eq_normalized_kernel_coefficient_of_finite_kernel
  rw [oneDWindowAmbiguityFactor_two_finite_kernel_integral_eq_shifted_moment, hmoment]
  unfold oneDWindowAmbiguityTwoClosedCoefficient
  exact (normalized_kernel_coefficient_two_eq_closed_simplified x ω).symm

private theorem oneDWindowAmbiguityFactor_three_eq_normalized_kernel_coefficient_of_shifted_moment
    (x ω : ℝ)
    (hmoment :
      oneDWindowAmbiguityThreeShiftedSixthMoment x ω =
        oneDWindowAmbiguityThreeClosedCoefficient x ω) :
    oneDWindowAmbiguityFactor 3 x ω =
      ((Nat.factorial 3 : ℂ)⁻¹) *
        (iteratedDeriv 3
          (fun w : ℂ =>
            iteratedDeriv 3
              (fun u : ℂ =>
                Complex.exp
                  (u * w +
                    (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * u -
                      star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * w)) 0) 0 *
          Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))) := by
  rw [oneDWindowAmbiguityFactor_three_eq_finite_monomial_kernel_integral,
    oneDWindowAmbiguityFactor_three_finite_kernel_integral_eq_shifted_moment, hmoment]
  unfold oneDWindowAmbiguityThreeClosedCoefficient
  exact (normalized_kernel_coefficient_three_eq_closed_simplified x ω).symm

private theorem oneDWindowAmbiguityFactor_eq_normalized_kernel_coefficient_of_interchange
    (k : Nat) (x ω : ℝ)
    (hinterchange :
      (∫ t : ℝ,
        iteratedDeriv k (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
          iteratedDeriv k (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ))) =
        iteratedDeriv k
          (fun w : ℂ =>
            iteratedDeriv k
              (fun u : ℂ =>
                ∫ t : ℝ,
                  realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
                    realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
                      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                        ((inner ℝ ω t : ℝ) : ℂ))) 0) 0) :
    oneDWindowAmbiguityFactor k x ω =
      ((Nat.factorial k : ℂ)⁻¹) *
        (iteratedDeriv k
          (fun w : ℂ =>
            iteratedDeriv k
              (fun u : ℂ =>
                Complex.exp
                  (u * w +
                    (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * u -
                      star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * w)) 0) 0 *
          Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))) := by
  rw [oneDWindowAmbiguityFactor_eq_scaled_iteratedDeriv_integral, hinterchange]
  rw [ambiguity_kernel_iteratedDeriv_factor k x ω, iteratedDeriv_mul_const_field]

private theorem oneDWindowAmbiguityFactor_eq_normalized_kernel_coefficient_of_closed
    (k : Nat) (x ω : ℝ)
    (hclosed :
      oneDWindowAmbiguityFactor k x ω =
        (-1 : ℂ) ^ k *
          phi1D k k
            (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) *
          Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))) :
    oneDWindowAmbiguityFactor k x ω =
      ((Nat.factorial k : ℂ)⁻¹) *
        (iteratedDeriv k
          (fun w : ℂ =>
            iteratedDeriv k
              (fun u : ℂ =>
                Complex.exp
                  (u * w +
                    (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * u -
                      star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * w)) 0) 0 *
          Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))) := by
  rw [hclosed, normalized_kernel_coefficient_eq_closed k x ω]

private theorem oneDWindowAmbiguityFactor_zero_eq_normalized_kernel_coefficient
    (x ω : ℝ) :
    oneDWindowAmbiguityFactor 0 x ω =
      ((Nat.factorial 0 : ℂ)⁻¹) *
        (iteratedDeriv 0
          (fun w : ℂ =>
            iteratedDeriv 0
              (fun u : ℂ =>
                Complex.exp
                  (u * w +
                    (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * u -
                      star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * w)) 0) 0 *
          Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))) := by
  rw [oneDWindowAmbiguityFactor_zero]
  simp

private theorem oneDWindowAmbiguityFactor_one_eq_normalized_kernel_coefficient
    (x ω : ℝ) :
    oneDWindowAmbiguityFactor 1 x ω =
      ((Nat.factorial 1 : ℂ)⁻¹) *
        (iteratedDeriv 1
          (fun w : ℂ =>
            iteratedDeriv 1
              (fun u : ℂ =>
                Complex.exp
                  (u * w +
                    (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * u -
                      star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * w)) 0) 0 *
          Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))) :=
  oneDWindowAmbiguityFactor_eq_normalized_kernel_coefficient_of_closed 1 x ω
    (oneDWindowAmbiguityFactor_one_closed x ω)

private theorem oneDWindowAmbiguityFactor_eq_normalized_kernel_coefficient
    (k : Nat) (x ω : ℝ) :
    oneDWindowAmbiguityFactor k x ω =
      ((Nat.factorial k : ℂ)⁻¹) *
        (iteratedDeriv k
          (fun w : ℂ =>
            iteratedDeriv k
              (fun u : ℂ =>
                Complex.exp
                  (u * w +
                    (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * u -
                      star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * w)) 0) 0 *
          Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))) := by
  /-
  Analytic coefficient extraction from
  `realHermiteGenerating_ambiguity_integral_conj_kernel`.

  The missing proof should justify passing the `u` and independent conjugate
  window coefficient extractions through the Lebesgue integral.  Equivalently,
  prove the finite coefficient identity for
  `realHermiteGenerating (t + x / 2) u *
   star (realHermiteGenerating (t - x / 2) v)` after setting `w = star v`.
  -/
  have h3 :=
    oneDWindowAmbiguityFactor_three_eq_normalized_kernel_coefficient_of_shifted_moment
  cases k with
  | zero =>
      exact oneDWindowAmbiguityFactor_zero_eq_normalized_kernel_coefficient x ω
  | succ k =>
      cases k with
      | zero =>
          exact oneDWindowAmbiguityFactor_one_eq_normalized_kernel_coefficient x ω
      | succ k =>
          cases k with
          | zero =>
              exact oneDWindowAmbiguityFactor_two_eq_normalized_kernel_coefficient_of_shifted_moment
                x ω (oneDWindowAmbiguityTwoShiftedFourthMoment_eq_closed x ω)
          | succ k =>
              cases k with
              | zero =>
                  exact h3 x ω (oneDWindowAmbiguityThreeShiftedSixthMoment_eq_closed x ω)
              | succ k =>
                  apply oneDWindowAmbiguityFactor_eq_normalized_kernel_coefficient_of_interchange
                  exact iteratedDeriv_generating_cross_ambiguity_integral_eq_kernel_coefficient
                    (k + 1 + 1 + 1 + 1) (k + 1 + 1 + 1 + 1) x ω

private theorem oneDWindowAmbiguityFactor_eq_of_normalized_kernel_coefficient
    (k : Nat) (x ω : ℝ)
    (hcoeff :
      oneDWindowAmbiguityFactor k x ω =
        ((Nat.factorial k : ℂ)⁻¹) *
          (iteratedDeriv k
            (fun w : ℂ =>
              iteratedDeriv k
                (fun u : ℂ =>
                  Complex.exp
                    (u * w +
                      (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                          (Real.sqrt 2 : ℂ)) * u -
                        star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                          (Real.sqrt 2 : ℂ)) * w)) 0) 0 *
            Complex.ofReal
              (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))))) :
    oneDWindowAmbiguityFactor k x ω =
      (-1 : ℂ) ^ k *
        phi1D k k
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  let z : ℂ :=
    ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
      (Real.sqrt 2 : ℂ)
  let E : ℂ :=
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))
  change oneDWindowAmbiguityFactor k x ω =
    (-1 : ℂ) ^ k * phi1D k k z * E
  rw [hcoeff]
  change ((Nat.factorial k : ℂ)⁻¹) *
      (iteratedDeriv k
        (fun w : ℂ =>
          iteratedDeriv k
            (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) 0) 0 * E) =
    (-1 : ℂ) ^ k * phi1D k k z * E
  rw [iteratedDeriv_cexp_ambiguity_kernel_diag_at_zero,
    ← inv_factorial_mul_complexHermite_self_eq_phi1D k z]
  ring

private theorem oneDWindowAmbiguityFactor_closed
    (k : Nat) (x ω : ℝ) :
    oneDWindowAmbiguityFactor k x ω =
      (-1 : ℂ) ^ k *
        phi1D k k
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) :=
  oneDWindowAmbiguityFactor_eq_of_normalized_kernel_coefficient k x ω
    (oneDWindowAmbiguityFactor_eq_normalized_kernel_coefficient k x ω)

private theorem tensorRep_windowAmbiguity_integral_eq_prod_oneD
    {d : Nat} (kappa : MultiIndex d) (ξ : PhaseSpace d) :
    (∫ t : RealVec d,
      realHermiteTensorRep kappa (t + ((1 / 2 : ℝ) • ξ.1)) *
        star (realHermiteTensorRep kappa (t - ((1 / 2 : ℝ) • ξ.1))) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ξ.2 t : ℝ) : ℂ))) =
      ∏ q : Fin d, oneDWindowAmbiguityFactor (kappa q) (ξ.1 q) (ξ.2 q) := by
  classical
  let f : (q : Fin d) → ℝ → ℂ := fun q t =>
    realHermite1D (kappa q) (t + (1 / 2 : ℝ) * ξ.1 q) *
      star (realHermite1D (kappa q) (t - (1 / 2 : ℝ) * ξ.1 q)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ (ξ.2 q) t : ℝ) : ℂ))
  have h_real_to_pi :
      (∫ t : RealVec d,
        realHermiteTensorRep kappa (t + ((1 / 2 : ℝ) • ξ.1)) *
          star (realHermiteTensorRep kappa (t - ((1 / 2 : ℝ) • ξ.1))) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ξ.2 t : ℝ) : ℂ))) =
        ∫ y : Fin d → ℝ, ∏ q : Fin d, f q (y q) := by
    calc
      (∫ t : RealVec d,
        realHermiteTensorRep kappa (t + ((1 / 2 : ℝ) • ξ.1)) *
          star (realHermiteTensorRep kappa (t - ((1 / 2 : ℝ) • ξ.1))) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ξ.2 t : ℝ) : ℂ))) =
          ∫ t : RealVec d,
            (fun y : Fin d → ℝ => ∏ q : Fin d, f q (y q)) (WithLp.ofLp t) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with t
            simp only [f, realHermiteTensorRep, Finset.prod_mul_distrib]
            rw [star_prod]
            have hphase :
                Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                    ((inner ℝ ξ.2 t : ℝ) : ℂ)) =
                  ∏ q : Fin d,
                    Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ (ξ.2 q) (WithLp.ofLp t q) : ℝ) : ℂ)) := by
              rw [show
                  -(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ ξ.2 t : ℝ) : ℂ) =
                    ∑ q : Fin d,
                      -(2 * Real.pi : ℂ) * Complex.I *
                        ((inner ℝ (ξ.2 q) (WithLp.ofLp t q) : ℝ) : ℂ) by
                simp only [PiLp.inner_apply, Complex.ofReal_sum, Finset.mul_sum]]
              rw [Complex.exp_sum]
            rw [hphase]
            simp [mul_assoc, mul_comm, sub_eq_add_neg]
      _ = ∫ y : Fin d → ℝ, ∏ q : Fin d, f q (y q) := by
            simpa [MeasurableEquiv.coe_toLp_symm] using
              (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp'
                (g := fun y : Fin d → ℝ => ∏ q : Fin d, f q (y q))
  rw [h_real_to_pi]
  exact
    MeasureTheory.integral_fintype_prod_volume_eq_prod
      (f := fun q (t : ℝ) => f q t)

private theorem prod_oneDWindowAmbiguity_closed_eq_PKappa_exp
    {d : Nat} (kappa : MultiIndex d) (ξ : PhaseSpace d) :
    (∏ q : Fin d,
      ((-1 : ℂ) ^ kappa q * phi1D (kappa q) (kappa q) (TKappa ξ q) *
        Complex.ofReal
          (Real.exp
            (-(((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4))))) =
      PKappa kappa ξ * Complex.ofReal (Real.exp (-(QKappa ξ))) := by
  classical
  let coordQ : Fin d → ℝ := fun q =>
    (((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4)
  have hQsum : QKappa ξ = ∑ q : Fin d, coordQ q := by
    simp only [QKappa, coordQ, EuclideanSpace.real_norm_sq_eq]
    ring_nf
    rw [Finset.sum_add_distrib]
    simp only [one_div, Finset.sum_mul]
    rw [add_comm, Finset.mul_sum]
  have hprod_pow :
      (∏ q : Fin d, (-1 : ℂ) ^ kappa q) =
        (-1 : ℂ) ^ ((Finset.univ : Finset (Fin d)).sum fun q => kappa q) := by
    simpa using
      (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin d))
        (fun q : Fin d => kappa q) (-1 : ℂ))
  have hprod_exp :
      (∏ q : Fin d, Complex.ofReal (Real.exp (-(coordQ q)))) =
        Complex.ofReal (Real.exp (-(QKappa ξ))) := by
    calc
      (∏ q : Fin d, Complex.ofReal (Real.exp (-(coordQ q)))) =
          ∏ q : Fin d, Complex.exp (((-(coordQ q) : ℝ) : ℂ)) := by
            apply Finset.prod_congr rfl
            intro q _hq
            rw [Complex.ofReal_exp]
      _ = Complex.exp (∑ q : Fin d, (((-(coordQ q) : ℝ) : ℂ))) := by rw [Complex.exp_sum]
      _ = Complex.ofReal (Real.exp (-(QKappa ξ))) := by
            rw [Complex.ofReal_exp]
            congr 1
            rw [← Complex.ofReal_sum]
            congr 1
            rw [hQsum, Finset.sum_neg_distrib]
  calc
    (∏ q : Fin d,
      ((-1 : ℂ) ^ kappa q * phi1D (kappa q) (kappa q) (TKappa ξ q) *
        Complex.ofReal
          (Real.exp
            (-(((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4))))) =
        (∏ q : Fin d, (-1 : ℂ) ^ kappa q) *
          (∏ q : Fin d, phi1D (kappa q) (kappa q) (TKappa ξ q)) *
            (∏ q : Fin d, Complex.ofReal (Real.exp (-(coordQ q)))) := by
          simp [coordQ, Finset.prod_mul_distrib, mul_assoc]
    _ = PKappa kappa ξ * Complex.ofReal (Real.exp (-(QKappa ξ))) := by
          rw [hprod_pow, hprod_exp]
          simp [PKappa, Phi, mul_assoc]

private theorem tensorRep_windowAmbiguity_integral_eq_PKappa_exp_of_oneD
    {d : Nat} (kappa : MultiIndex d) (ξ : PhaseSpace d)
    (h1D : ∀ q : Fin d,
      oneDWindowAmbiguityFactor (kappa q) (ξ.1 q) (ξ.2 q) =
        (-1 : ℂ) ^ kappa q * phi1D (kappa q) (kappa q) (TKappa ξ q) *
          Complex.ofReal
            (Real.exp
              (-(((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4)))) :
    (∫ t : RealVec d,
      realHermiteTensorRep kappa (t + ((1 / 2 : ℝ) • ξ.1)) *
        star (realHermiteTensorRep kappa (t - ((1 / 2 : ℝ) • ξ.1))) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ξ.2 t : ℝ) : ℂ))) =
      PKappa kappa ξ * Complex.ofReal (Real.exp (-(QKappa ξ))) := by
  rw [tensorRep_windowAmbiguity_integral_eq_prod_oneD]
  rw [show
      (∏ q : Fin d, oneDWindowAmbiguityFactor (kappa q) (ξ.1 q) (ξ.2 q)) =
        ∏ q : Fin d,
          ((-1 : ℂ) ^ kappa q * phi1D (kappa q) (kappa q) (TKappa ξ q) *
            Complex.ofReal
              (Real.exp
                (-(((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4)))) by
    apply Finset.prod_congr rfl
    intro q _hq
    exact h1D q]
  exact prod_oneDWindowAmbiguity_closed_eq_PKappa_exp kappa ξ

theorem windowAmbiguity_factorization
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (ξ : PhaseSpace d) :
    ambiguityRep (varphiKappa kappa) (varphiKappa kappa) ξ =
      PKappa kappa ξ * Complex.ofReal (Real.exp (-(QKappa ξ))) := by
  let _ := hd
  rw [ambiguityRep_varphiKappa_eq_tensorRep_integral]
  apply tensorRep_windowAmbiguity_integral_eq_PKappa_exp_of_oneD
  intro q
  simpa [TKappa] using
    oneDWindowAmbiguityFactor_closed (kappa q) (ξ.1 q) (ξ.2 q)

theorem windowAmbiguity_polynomial_nonzero
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    PKappa kappa ≠ 0 := by
  let _ := hd
  intro hzero
  have hval := congrFun hzero ((0, 0) : PhaseSpace d)
  have hnonzero : PKappa kappa ((0, 0) : PhaseSpace d) ≠ 0 := by
    simp [PKappa, TKappa_zero, Phi_self_zero_ne]
  exact hnonzero hval

private lemma dense_ne_zero_of_phaseSpace_polynomial
    {d : Nat} {P : PhaseSpace d -> ℂ}
    (hpoly : IsPhaseSpacePolynomial P)
    (hne : ∃ ξ0, P ξ0 ≠ 0) :
    Dense {ξ : PhaseSpace d | P ξ ≠ 0} := by
  classical
  rcases hpoly with ⟨p, hp⟩
  rcases hne with ⟨ξ0, hξ0⟩
  rw [Metric.dense_iff]
  intro ξ ε hε
  let line : ℝ -> PhaseSpace d := fun t =>
    (ξ.1 + t • (ξ0.1 - ξ.1), ξ.2 + t • (ξ0.2 - ξ.2))
  let affineCoord : (Fin d ⊕ Fin d) -> Polynomial ℂ
    | Sum.inl q => Polynomial.C (ξ.1 q : ℂ) +
        Polynomial.C (((ξ0.1 q - ξ.1 q : ℝ) : ℂ)) * Polynomial.X
    | Sum.inr q => Polynomial.C (ξ.2 q : ℂ) +
        Polynomial.C (((ξ0.2 q - ξ.2 q : ℝ) : ℂ)) * Polynomial.X
  let qpoly : Polynomial ℂ := MvPolynomial.eval₂Hom Polynomial.C affineCoord p
  have hqeval : ∀ t : ℝ, qpoly.eval (t : ℂ) = P (line t) := by
    intro t
    calc
      qpoly.eval (t : ℂ) =
          MvPolynomial.eval (fun s => Polynomial.eval (t : ℂ) (affineCoord s)) p := by
            change (Polynomial.evalRingHom (t : ℂ))
                ((MvPolynomial.eval₂Hom Polynomial.C affineCoord) p) = _
            rw [MvPolynomial.map_eval₂Hom]
            have hC : (Polynomial.evalRingHom (t : ℂ)).comp Polynomial.C = RingHom.id ℂ := by
              ext z
              simp
            rw [hC]
            rfl
      _ = MvPolynomial.eval (phaseSpacePolyEval (line t)) p := by
            have hev : (fun s => Polynomial.eval (t : ℂ) (affineCoord s)) =
                phaseSpacePolyEval (line t) := by
              funext s
              cases s with
              | inl q =>
                  simp [affineCoord, phaseSpacePolyEval, line]
                  ring
              | inr q =>
                  simp [affineCoord, phaseSpacePolyEval, line]
                  ring
            rw [hev]
      _ = P (line t) := by rw [hp]
  have hline1 : line 1 = ξ0 := by ext q <;> simp [line]
  have hq_ne : qpoly ≠ 0 := by
    intro hzero
    have hq1 := hqeval 1
    rw [hzero] at hq1
    simp [hline1] at hq1
    exact hξ0 hq1.symm
  let rootsReal : Set ℝ := {t : ℝ | qpoly.eval (t : ℂ) = 0}
  have hroots_countable : rootsReal.Countable := by
    have hroots_complex : ({z : ℂ | qpoly.IsRoot z}).Finite :=
      Polynomial.finite_setOf_isRoot hq_ne
    have hroots_complex_countable : ({z : ℂ | qpoly.IsRoot z}).Countable :=
      hroots_complex.countable
    have hpre : rootsReal = Complex.ofReal ⁻¹' {z : ℂ | qpoly.IsRoot z} := by
      ext t
      simp [rootsReal, Polynomial.IsRoot]
    rw [hpre]
    exact hroots_complex_countable.preimage Complex.ofReal_injective
  have hnonroots_dense : Dense {t : ℝ | qpoly.eval (t : ℂ) ≠ 0} := by
    simpa [rootsReal, Set.compl_setOf] using hroots_countable.dense_compl ℝ
  have hline_cont : Continuous line := by fun_prop
  have hline0 : line 0 = ξ := by ext q <;> simp [line]
  have hpre_ball : line ⁻¹' Metric.ball ξ ε ∈ nhds (0 : ℝ) := by
    have hball : Metric.ball ξ ε ∈ nhds (line 0) := by
      simpa [hline0] using Metric.ball_mem_nhds ξ hε
    exact hline_cont.continuousAt hball
  rcases hnonroots_dense.inter_nhds_nonempty hpre_ball with ⟨t, ht_nonroot, ht_ball⟩
  refine ⟨line t, ?_⟩
  constructor
  · exact ht_ball
  · simpa [hqeval t] using ht_nonroot

theorem windowAmbiguity_dense_nonvanishing
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    Dense {ξ : PhaseSpace d |
      ambiguityRep (varphiKappa kappa) (varphiKappa kappa) ξ ≠ 0} := by
  refine (dense_ne_zero_of_phaseSpace_polynomial (PKappa_isPolynomial hd kappa) ?_).mono ?_
  · exact ⟨(0, 0), by simp [PKappa, TKappa_zero, Phi_self_zero_ne]⟩
  · intro ξ hP
    change ambiguityRep (varphiKappa kappa) (varphiKappa kappa) ξ ≠ 0
    change PKappa kappa ξ ≠ 0 at hP
    rw [windowAmbiguity_factorization hd kappa ξ]
    exact mul_ne_zero hP (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

theorem spectrogram_eq_of_equal_modulus_to_ambiguity_eq
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {f g : L2Real d}
    (hmod : ∀ ξ : PhaseSpace d,
      ‖stftRep (varphiKappa kappa) f ξ‖ =
        ‖stftRep (varphiKappa kappa) g ξ‖) :
    ∀ ξ : PhaseSpace d, ambiguityRep f f ξ = ambiguityRep g g ξ := by
  let hwin := varphiKappa kappa
  let s : Set (PhaseSpace d) :=
    {ξ | ambiguityRep hwin hwin ξ ≠ 0}
  have h_on : Set.EqOn (ambiguityRep f f) (ambiguityRep g g) s := by
    intro ξ hξ
    have hspec_eq :
        symplecticFourierRep
            (fun η : PhaseSpace d => ((‖stftRep hwin f η‖ ^ 2 : ℝ) : ℂ)) ξ =
          symplecticFourierRep
            (fun η : PhaseSpace d => ((‖stftRep hwin g η‖ ^ 2 : ℝ) : ℂ)) ξ := by
      congr 1
      funext η
      rw [hmod η]
    have hf_id := spectrogram_ambiguity_identity hwin f ξ
    have hg_id := spectrogram_ambiguity_identity hwin g ξ
    have hprod :
        ambiguityRep f f ξ * star (ambiguityRep hwin hwin ξ) =
          ambiguityRep g g ξ * star (ambiguityRep hwin hwin ξ) := by
      rw [← hf_id, ← hg_id]
      exact hspec_eq
    exact mul_right_cancel₀ (star_ne_zero.mpr hξ) hprod
  have hs_dense : Dense s := by simpa [s, hwin] using windowAmbiguity_dense_nonvanishing hd kappa
  have hamb : ambiguityRep f f = ambiguityRep g g :=
    Continuous.ext_on hs_dense (continuous_ambiguityRep f f)
      (continuous_ambiguityRep g g) h_on
  intro ξ
  exact congrFun hamb ξ

private lemma integral_fourier_schwartz_mul_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    {h : V -> ℂ} (hh1 : Integrable h) (phi : 𝓢(V, ℂ)) :
    ∫ x : V, ((𝓕 phi) x) * h x =
      ∫ ξ : V, phi ξ * ((𝓕 h) ξ) := by
  have hswap := VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (M := ContinuousLinearMap.mul ℂ ℂ)
      (e := Real.fourierChar)
      (μ := (volume : Measure V))
      (ν := (volume : Measure V))
      (L := innerₗ V)
      Real.continuous_fourierChar
      continuous_inner
      hh1
      phi.integrable
  calc
    ∫ x : V, ((𝓕 phi) x) * h x =
        ∫ x : V, h x * ((𝓕 (phi : V -> ℂ)) x) := by simp [SchwartzMap.fourier_coe, mul_comm]
    _ = ∫ ξ : V, ((𝓕 h) ξ) * phi ξ := by
          have hflip :
              (fun x : V => h x * (𝓕 (⇑phi)) x) =
                fun x : V => ((ContinuousLinearMap.mul ℂ ℂ) (h x))
                  (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ V).flip
                    (⇑phi) x) := by
            funext x
            rw [ContinuousLinearMap.mul_apply', Real.fourier_eq]
            simp only [VectorFourier.fourierIntegral]
            congr 1
            refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
            simp only [LinearMap.flip_apply, innerₗ_apply_apply]
            rw [real_inner_comm]
          rw [hflip]
          simpa [ContinuousLinearMap.mul_apply', Real.fourier_eq,
            VectorFourier.fourierIntegral] using hswap.symm
    _ = ∫ ξ : V, phi ξ * ((𝓕 h) ξ) := by simp [mul_comm]

private theorem fourier_l1_l2_eq_zero_ae
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    {h : V -> ℂ}
    (hh1 : Integrable h) (hh2 : MemLp h 2 (volume : Measure V))
    (hFourier : ∀ ξ : V, (𝓕 h) ξ = 0) :
    h =ᵐ[(volume : Measure V)] fun _ => (0 : ℂ) := by
  let H : Lp ℂ 2 (volume : Measure V) := hh2.toLp h
  have hH_coe :
      ((H : Lp ℂ 2 (volume : Measure V)) : V -> ℂ)
        =ᵐ[(volume : Measure V)] h := by simpa [H] using hh2.coeFn_toLp
  have hdist_fourier_zero :
      ((𝓕 H : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) = 0 := by
    calc
      ((𝓕 H : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) =
          𝓕 (H : 𝓢'(V, ℂ)) := by rw [MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
      _ = 0 := by
            ext phi
            calc
              (𝓕 (H : 𝓢'(V, ℂ))) phi =
                  (H : 𝓢'(V, ℂ)) (𝓕 phi) := by simp
              _ = ∫ x : V, ((𝓕 phi) x) * h x := by
                    rw [MeasureTheory.Lp.toTemperedDistribution_apply]
                    apply integral_congr_ae
                    filter_upwards [hH_coe] with x hx
                    simp [hx, smul_eq_mul]
              _ = ∫ ξ : V, phi ξ * ((𝓕 h) ξ) :=
                    integral_fourier_schwartz_mul_eq hh1 phi
              _ = 0 := by simp [hFourier]
  have hFH_zero : 𝓕 H = 0 := by
    have hker :
        𝓕 H ∈
          (MeasureTheory.Lp.toTemperedDistributionCLM
            ℂ (volume : Measure V) 2).ker := by
      change
        (MeasureTheory.Lp.toTemperedDistributionCLM
          ℂ (volume : Measure V) 2) (𝓕 H) = 0
      simpa using hdist_fourier_zero
    have hker_bot :=
      MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
        (F := ℂ) (μ := (volume : Measure V)) (p := (2 : ℝ≥0∞))
    rw [hker_bot] at hker
    simpa using hker
  have hH_zero : H = 0 := by
    have h :=
      congrArg (fun G : Lp ℂ 2 (volume : Measure V) => 𝓕⁻ G)
        hFH_zero
    simpa using h
  have hH_zero_ae :
      ((H : Lp ℂ 2 (volume : Measure V)) : V -> ℂ)
        =ᵐ[(volume : Measure V)] fun _ => (0 : ℂ) := by
    rw [hH_zero]
    exact MeasureTheory.Lp.coeFn_zero ℂ 2 (volume : Measure V)
  exact hH_coe.symm.trans hH_zero_ae

private lemma rankOneKernel_memLp_two
    {d : Nat} {f g : RealVec d -> ℂ}
    (hf : MemLp f 2 (volume : Measure (RealVec d)))
    (hg : MemLp g 2 (volume : Measure (RealVec d))) :
    MemLp (fun p : RealVec d × RealVec d => f p.1 * star (g p.2)) 2
      ((volume : Measure (RealVec d)).prod
        (volume : Measure (RealVec d))) := by
  have hint :
      Integrable
        (fun p : RealVec d × RealVec d =>
          ‖f p.1 * star (g p.2)‖ ^ 2)
        ((volume : Measure (RealVec d)).prod
          (volume : Measure (RealVec d))) := by
    have hf2 :
        Integrable (fun x => ‖f x‖ ^ 2)
          (volume : Measure (RealVec d)) := by
      simpa using hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    have hg2 :
        Integrable (fun y => ‖g y‖ ^ 2)
          (volume : Measure (RealVec d)) := by
      simpa using hg.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    have hprod :
        Integrable
          (fun p : RealVec d × RealVec d =>
            (‖f p.1‖ ^ 2) * (‖g p.2‖ ^ 2))
          ((volume : Measure (RealVec d)).prod
            (volume : Measure (RealVec d))) := by simpa using Integrable.mul_prod hf2 hg2
    convert hprod using 1 with p
    simp [mul_pow]
  have hmeas :
      AEStronglyMeasurable
        (fun p : RealVec d × RealVec d => f p.1 * star (g p.2))
        ((volume : Measure (RealVec d)).prod
          (volume : Measure (RealVec d))) := by
    exact
      (hf.1.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst).mul
        ((hg.1.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_snd).star)
  exact
    (integrable_norm_rpow_iff
      (μ := (volume : Measure (RealVec d)).prod
        (volume : Measure (RealVec d)))
      (p := (2 : ℝ≥0∞)) hmeas (by norm_num) (by simp)).1
      (by simpa using hint)

private lemma shifted_conj_mul_integrable
    {d : Nat} {f g : RealVec d -> ℂ}
    (hf : MemLp f 2 (volume : Measure (RealVec d)))
    (hg : MemLp g 2 (volume : Measure (RealVec d)))
    (a b : RealVec d) :
    Integrable (fun t : RealVec d => f (t + a) * star (g (t + b)))
      (volume : Measure (RealVec d)) := by
  have hf_shift :
      MemLp (fun t : RealVec d => f (t + a)) 2
        (volume : Measure (RealVec d)) := by
    simpa [Function.comp_def] using
      hf.comp_measurePreserving
        (MeasureTheory.measurePreserving_add_right
          (volume : Measure (RealVec d)) a)
  have hg_shift :
      MemLp (fun t : RealVec d => star (g (t + b))) 2
        (volume : Measure (RealVec d)) := by
    have hg0 :
        MemLp (fun t : RealVec d => g (t + b)) 2
          (volume : Measure (RealVec d)) := by
      simpa [Function.comp_def] using
        hg.comp_measurePreserving
          (MeasureTheory.measurePreserving_add_right
            (volume : Measure (RealVec d)) b)
    exact hg0.star
  exact MemLp.integrable_mul hf_shift hg_shift

private lemma l2rep_ae_eq_coe
    {d : Nat} {f : L2Real d} {fRep : RealVec d -> ℂ}
    (hf_rep : IsL2Rep f fRep) :
    ((f : L2Real d) : RealVec d -> ℂ)
      =ᵐ[(volume : Measure (RealVec d))] fRep := by
  rcases hf_rep with ⟨hf_mem, hf_eq⟩
  rw [← hf_eq]
  exact hf_mem.coeFn_toLp

private noncomputable def centerToEndpointsLinearEquiv (d : Nat) :
    PhaseSpace d ≃ₗ[ℝ] PhaseSpace d where
  toFun p := (p.2 + ((1 / 2 : ℝ) • p.1), p.2 - ((1 / 2 : ℝ) • p.1))
  invFun p := (p.1 - p.2, ((1 / 2 : ℝ) • (p.1 + p.2)))
  left_inv := by
    intro p
    ext q <;> simp
    · ring
    · ring
  right_inv := by
    intro p
    ext q <;> simp
    · ring
    · ring
  map_add' := by
    intro p q
    ext r <;> simp [add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
  map_smul' := by
    intro c p
    ext r <;> simp [smul_add, smul_sub, mul_left_comm]

private lemma centerKernel_memLp_two
    {d : Nat} {f : RealVec d -> ℂ}
    (hf : MemLp f 2 (volume : Measure (RealVec d))) :
    MemLp (fun p : PhaseSpace d =>
      f (p.2 + ((1 / 2 : ℝ) • p.1)) *
        star (f (p.2 - ((1 / 2 : ℝ) • p.1)))) 2
      (volume : Measure (PhaseSpace d)) := by
  let L := centerToEndpointsLinearEquiv d
  let μ : Measure (RealVec d) := volume
  let K : PhaseSpace d -> ℂ := fun p => f p.1 * star (f p.2)
  have hK : MemLp K 2 (μ.prod μ) := by
    simpa [K, μ] using
      (rankOneKernel_memLp_two (d := d) (f := f) (g := f) hf hf)
  have hdet : LinearMap.det (L : PhaseSpace d →ₗ[ℝ] PhaseSpace d) ≠ 0 :=
    (LinearEquiv.isUnit_det' L).ne_zero
  have hmap :
      Measure.map (L : PhaseSpace d -> PhaseSpace d)
        (μ.prod μ) =
      ENNReal.ofReal
          |(LinearMap.det (L : PhaseSpace d →ₗ[ℝ] PhaseSpace d))⁻¹| •
        (μ.prod μ) := by
    simpa using
      (MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
        (μ := μ.prod μ)
        (f := (L : PhaseSpace d →ₗ[ℝ] PhaseSpace d)) hdet)
  have hK_map :
      MemLp K 2
        (Measure.map (L : PhaseSpace d -> PhaseSpace d)
          (μ.prod μ)) := by
    rw [hmap]
    exact hK.smul_measure (by simp)
  have hcomp :
      MemLp (K ∘ (L : PhaseSpace d -> PhaseSpace d)) 2
        (μ.prod μ) := by
    have hL_aemeasurable :
        AEMeasurable (L : PhaseSpace d -> PhaseSpace d)
          (μ.prod μ) :=
      (LinearMap.continuous_of_finiteDimensional
        (L : PhaseSpace d →ₗ[ℝ] PhaseSpace d)).measurable.aemeasurable
    exact hK_map.comp_of_map hL_aemeasurable
  simpa [K, L, μ, centerToEndpointsLinearEquiv, Function.comp_def,
    MeasureTheory.Measure.volume_eq_prod] using hcomp

private lemma memLp_two_prod_right_ae
    {d : Nat} {F : PhaseSpace d -> ℂ}
    (hF : MemLp F 2 (volume : Measure (PhaseSpace d))) :
    ∀ᵐ x ∂(volume : Measure (RealVec d)),
      MemLp (fun t : RealVec d => F (x, t)) 2
        (volume : Measure (RealVec d)) := by
  let μ : Measure (RealVec d) := volume
  have hF_prod : MemLp F 2 (μ.prod μ) := by simpa [μ, MeasureTheory.Measure.volume_eq_prod] using hF
  have hmeas_sec :
      ∀ᵐ x ∂μ,
        AEStronglyMeasurable (fun t : RealVec d => F (x, t)) μ := hF_prod.1.prodMk_left
  have hint_global :
      Integrable (fun p : PhaseSpace d => ‖F p‖ ^ 2) (μ.prod μ) := by
    simpa using hF_prod.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hint_sec :
      ∀ᵐ x ∂μ,
        Integrable (fun t : RealVec d => ‖F (x, t)‖ ^ 2) μ := hint_global.prod_right_ae
  filter_upwards [hmeas_sec, hint_sec] with x hx_meas hx_int
  exact
    (integrable_norm_rpow_iff
      (μ := μ) (p := (2 : ℝ≥0∞)) hx_meas (by norm_num) (by simp)).1
      (by simpa using hx_int)

private lemma ae_prod_of_ae_ae_of_aestronglyMeasurable
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {F : α × β -> E}
    (hF_meas : AEStronglyMeasurable F (μ.prod ν))
    (hsec : ∀ᵐ x ∂μ, (fun y : β => F (x, y)) =ᵐ[ν] fun _ => (0 : E)) :
    F =ᵐ[μ.prod ν] fun _ => (0 : E) := by
  let Fm : α × β -> E := hF_meas.mk F
  have hF_eq_mk_sections :
      ∀ᵐ x ∂μ, (fun y : β => F (x, y)) =ᵐ[ν] fun y => Fm (x, y) :=
    MeasureTheory.Measure.ae_ae_of_ae_prod hF_meas.ae_eq_mk
  have hmk_sec_zero :
      ∀ᵐ x ∂μ, (fun y : β => Fm (x, y)) =ᵐ[ν] fun _ => (0 : E) := by
    filter_upwards [hsec, hF_eq_mk_sections] with x hx hxm
    exact hxm.symm.trans hx
  have hmeas_zero : MeasurableSet {p : α × β | Fm p = 0} :=
    hF_meas.stronglyMeasurable_mk.measurable (measurableSet_singleton (0 : E))
  have hmk_prod : Fm =ᵐ[μ.prod ν] fun _ => (0 : E) :=
    (MeasureTheory.Measure.ae_prod_iff_ae_ae hmeas_zero).2 hmk_sec_zero
  exact hF_meas.ae_eq_mk.trans hmk_prod

private lemma sectionDiff_fourier_eq_ambiguity_sub
    {d : Nat} (f g : L2Real d) (x ω : RealVec d)
    (hf_int : Integrable (fun t : RealVec d =>
      ((f : RealVec d -> ℂ) (t + ((1 / 2 : ℝ) • x))) *
        star ((f : RealVec d -> ℂ) (t - ((1 / 2 : ℝ) • x))))
      (volume : Measure (RealVec d)))
    (hg_int : Integrable (fun t : RealVec d =>
      ((g : RealVec d -> ℂ) (t + ((1 / 2 : ℝ) • x))) *
        star ((g : RealVec d -> ℂ) (t - ((1 / 2 : ℝ) • x))))
      (volume : Measure (RealVec d))) :
    (𝓕 (fun t : RealVec d =>
      ((f : RealVec d -> ℂ) (t + ((1 / 2 : ℝ) • x))) *
        star ((f : RealVec d -> ℂ) (t - ((1 / 2 : ℝ) • x))) -
      ((g : RealVec d -> ℂ) (t + ((1 / 2 : ℝ) • x))) *
        star ((g : RealVec d -> ℂ) (t - ((1 / 2 : ℝ) • x))))) ω =
      ambiguityRep f f (x, ω) - ambiguityRep g g (x, ω) := by
  let phase : RealVec d -> ℂ := fun t =>
    Complex.exp ((↑(-2 * Real.pi * ⟪t, ω⟫) * Complex.I))
  let Fsec : RealVec d -> ℂ := fun t =>
    ((f : RealVec d -> ℂ) (t + ((1 / 2 : ℝ) • x))) *
      star ((f : RealVec d -> ℂ) (t - ((1 / 2 : ℝ) • x)))
  let Gsec : RealVec d -> ℂ := fun t =>
    ((g : RealVec d -> ℂ) (t + ((1 / 2 : ℝ) • x))) *
      star ((g : RealVec d -> ℂ) (t - ((1 / 2 : ℝ) • x)))
  have hFphase :
      Integrable (fun t : RealVec d => phase t * Fsec t)
        (volume : Measure (RealVec d)) := by
    have h := (Real.fourierIntegral_convergent_iff
      (μ := (volume : Measure (RealVec d))) (f := Fsec) ω).2
        (by simpa [Fsec] using hf_int)
    simpa [phase, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul] using h
  have hGphase :
      Integrable (fun t : RealVec d => phase t * Gsec t)
        (volume : Measure (RealVec d)) := by
    have h := (Real.fourierIntegral_convergent_iff
      (μ := (volume : Measure (RealVec d))) (f := Gsec) ω).2
        (by simpa [Gsec] using hg_int)
    simpa [phase, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul] using h
  rw [Real.fourier_eq']
  simp_rw [smul_eq_mul]
  change (∫ v : RealVec d, phase v * (Fsec v - Gsec v)) =
    ambiguityRep f f (x, ω) - ambiguityRep g g (x, ω)
  rw [show (fun v : RealVec d => phase v * (Fsec v - Gsec v)) =
    (fun v : RealVec d => phase v * Fsec v - phase v * Gsec v) by
      funext v
      ring]
  rw [integral_sub hFphase hGphase]
  simp [ambiguityRep, Fsec, Gsec, phase, real_inner_comm, mul_assoc, mul_comm]

theorem equalAmbiguity_to_rankOneKernel_ae
    {d : Nat} {f g : L2Real d} {fRep gRep : RealVec d -> ℂ}
    (hf_rep : IsL2Rep f fRep) (hg_rep : IsL2Rep g gRep)
    (hAmb : ∀ ξ : PhaseSpace d, ambiguityRep f f ξ = ambiguityRep g g ξ) :
    (fun p : RealVec d × RealVec d => fRep p.1 * star (fRep p.2))
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d × RealVec d))]
        fun p => gRep p.1 * star (gRep p.2) := by
  let μ : Measure (RealVec d) := volume
  let f0 : RealVec d -> ℂ := (f : RealVec d -> ℂ)
  let g0 : RealVec d -> ℂ := (g : RealVec d -> ℂ)
  let centerDiff : PhaseSpace d -> ℂ := fun p =>
    f0 (p.2 + ((1 / 2 : ℝ) • p.1)) *
        star (f0 (p.2 - ((1 / 2 : ℝ) • p.1))) -
      g0 (p.2 + ((1 / 2 : ℝ) • p.1)) *
        star (g0 (p.2 - ((1 / 2 : ℝ) • p.1)))
  let endpointDiff : PhaseSpace d -> ℂ := fun p =>
    f0 p.1 * star (f0 p.2) - g0 p.1 * star (g0 p.2)
  have hf_mem : MemLp f0 2 μ := by simpa [f0, μ] using MeasureTheory.Lp.memLp f
  have hg_mem : MemLp g0 2 μ := by simpa [g0, μ] using MeasureTheory.Lp.memLp g
  have hf_center :
      MemLp (fun p : PhaseSpace d =>
        f0 (p.2 + ((1 / 2 : ℝ) • p.1)) *
          star (f0 (p.2 - ((1 / 2 : ℝ) • p.1)))) 2
        (volume : Measure (PhaseSpace d)) := by
    simpa [f0, μ] using centerKernel_memLp_two (d := d) hf_mem
  have hg_center :
      MemLp (fun p : PhaseSpace d =>
        g0 (p.2 + ((1 / 2 : ℝ) • p.1)) *
          star (g0 (p.2 - ((1 / 2 : ℝ) • p.1)))) 2
        (volume : Measure (PhaseSpace d)) := by
    simpa [g0, μ] using centerKernel_memLp_two (d := d) hg_mem
  have hcenter_mem :
      MemLp centerDiff 2 (volume : Measure (PhaseSpace d)) := by
    refine MeasureTheory.MemLp.ae_eq ?_ (hf_center.sub hg_center)
    filter_upwards with p
    rfl
  have hcenter_sections :
      ∀ᵐ x ∂μ,
        MemLp (fun t : RealVec d => centerDiff (x, t)) 2 μ := by
    simpa [μ] using memLp_two_prod_right_ae (d := d) hcenter_mem
  have hcenter_zero_sections :
      ∀ᵐ x ∂μ,
        (fun t : RealVec d => centerDiff (x, t)) =ᵐ[μ] fun _ => (0 : ℂ) := by
    filter_upwards [hcenter_sections] with x hx_l2
    have hf_int :
        Integrable (fun t : RealVec d =>
          f0 (t + ((1 / 2 : ℝ) • x)) *
            star (f0 (t - ((1 / 2 : ℝ) • x))) ) μ := by
      refine (shifted_conj_mul_integrable (d := d) hf_mem hf_mem
          (((1 / 2 : ℝ) • x)) (-((1 / 2 : ℝ) • x))).congr ?_
      filter_upwards with t
      simp only [f0, sub_eq_add_neg]
    have hg_int :
        Integrable (fun t : RealVec d =>
          g0 (t + ((1 / 2 : ℝ) • x)) *
            star (g0 (t - ((1 / 2 : ℝ) • x))) ) μ := by
      refine (shifted_conj_mul_integrable (d := d) hg_mem hg_mem
          (((1 / 2 : ℝ) • x)) (-((1 / 2 : ℝ) • x))).congr ?_
      filter_upwards with t
      simp only [g0, sub_eq_add_neg]
    have hdiff_int :
        Integrable (fun t : RealVec d => centerDiff (x, t)) μ := by
      refine (hf_int.sub hg_int).congr ?_
      filter_upwards with t
      simp only [centerDiff, Pi.sub_apply, sub_eq_add_neg]
    have hfourier :
        ∀ ω : RealVec d,
          (𝓕 (fun t : RealVec d => centerDiff (x, t))) ω = 0 := by
      intro ω
      calc
        (𝓕 (fun t : RealVec d => centerDiff (x, t))) ω =
            ambiguityRep f f (x, ω) - ambiguityRep g g (x, ω) := by
              simpa [centerDiff, f0, g0, μ] using
                sectionDiff_fourier_eq_ambiguity_sub f g x ω
                  (by simpa [f0, μ] using hf_int)
                  (by simpa [g0, μ] using hg_int)
        _ = 0 := by
              rw [hAmb (x, ω)]
              simp
    exact fourier_l1_l2_eq_zero_ae hdiff_int hx_l2 hfourier
  have hcenter_zero_prod :
      centerDiff =ᵐ[μ.prod μ] fun _ => (0 : ℂ) := by
    exact
      ae_prod_of_ae_ae_of_aestronglyMeasurable
        (by
          have hcenter_prod : MemLp centerDiff 2 (μ.prod μ) := by
            simpa [μ, MeasureTheory.Measure.volume_eq_prod] using hcenter_mem
          exact hcenter_prod.1)
        hcenter_zero_sections
  have hendpoint_zero :
      endpointDiff =ᵐ[μ.prod μ] fun _ => (0 : ℂ) := by
    let L := centerToEndpointsLinearEquiv d
    have hdet_symm :
        LinearMap.det (L.symm : PhaseSpace d →ₗ[ℝ] PhaseSpace d) ≠ 0 :=
      (LinearEquiv.isUnit_det' L.symm).ne_zero
    have hqmp_symm :=
      MeasureTheory.Measure.LinearMap.quasiMeasurePreserving (μ.prod μ)
        (L.symm : PhaseSpace d →ₗ[ℝ] PhaseSpace d) hdet_symm
    have hcomp :=
      hqmp_symm.ae hcenter_zero_prod
    have hendpoint_eq : endpointDiff = fun p : PhaseSpace d => centerDiff (L.symm p) := by
      funext p
      have hplus :
          (2⁻¹ : ℝ) • p.1 + (2⁻¹ : ℝ) • p.2 +
              (2⁻¹ : ℝ) • (p.1 - p.2) = p.1 := by
        ext q
        simp
        ring
      have hminus :
          (2⁻¹ : ℝ) • p.1 + (2⁻¹ : ℝ) • p.2 -
              (2⁻¹ : ℝ) • (p.1 - p.2) = p.2 := by
        ext q
        simp
        ring
      simp [endpointDiff, centerDiff, L, centerToEndpointsLinearEquiv, hplus, hminus]
    filter_upwards [hcomp] with p hp
    simpa [hendpoint_eq] using hp
  have hf_ae : f0 =ᵐ[μ] fRep := by simpa [f0, μ] using l2rep_ae_eq_coe hf_rep
  have hg_ae : g0 =ᵐ[μ] gRep := by simpa [g0, μ] using l2rep_ae_eq_coe hg_rep
  have hendpoint_prod :
      endpointDiff =ᵐ[μ.prod μ] fun _ => (0 : ℂ) := by simpa using hendpoint_zero
  have hf_fst :
      (fun p : PhaseSpace d => f0 p.1)
        =ᵐ[μ.prod μ] fun p => fRep p.1 :=
    MeasureTheory.Measure.quasiMeasurePreserving_fst.ae hf_ae
  have hf_snd :
      (fun p : PhaseSpace d => f0 p.2)
        =ᵐ[μ.prod μ] fun p => fRep p.2 :=
    MeasureTheory.Measure.quasiMeasurePreserving_snd.ae hf_ae
  have hg_fst :
      (fun p : PhaseSpace d => g0 p.1)
        =ᵐ[μ.prod μ] fun p => gRep p.1 :=
    MeasureTheory.Measure.quasiMeasurePreserving_fst.ae hg_ae
  have hg_snd :
      (fun p : PhaseSpace d => g0 p.2)
        =ᵐ[μ.prod μ] fun p => gRep p.2 :=
    MeasureTheory.Measure.quasiMeasurePreserving_snd.ae hg_ae
  have hrep_prod :
      (fun p : PhaseSpace d => fRep p.1 * star (fRep p.2))
        =ᵐ[μ.prod μ] fun p => gRep p.1 * star (gRep p.2) := by
    filter_upwards [hendpoint_prod, hf_fst, hf_snd, hg_fst, hg_snd] with
      p hp hff hfs hgf hgs
    have h0 : f0 p.1 * star (f0 p.2) - g0 p.1 * star (g0 p.2) = 0 := hp
    have heq : f0 p.1 * star (f0 p.2) = g0 p.1 * star (g0 p.2) :=
      sub_eq_zero.mp h0
    calc
      fRep p.1 * star (fRep p.2) =
          f0 p.1 * star (f0 p.2) := by rw [hff, hfs]
      _ = g0 p.1 * star (g0 p.2) := heq
      _ = gRep p.1 * star (gRep p.2) := by rw [hgf, hgs]
  simpa [μ, MeasureTheory.Measure.volume_eq_prod] using hrep_prod

private lemma exists_eventually_and_ne_zero
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {P : α -> Prop} {a : α -> ℂ}
    (hP : ∀ᵐ x ∂μ, P x)
    (hnot : ¬ a =ᵐ[μ] fun _ => (0 : ℂ)) :
    ∃ x, P x ∧ a x ≠ 0 := by
  by_contra hnone
  apply hnot
  filter_upwards [hP] with x hxP
  by_contra hx
  exact hnone ⟨x, hxP, hx⟩

private lemma norm_eq_one_of_mul_star_eq_one {w : ℂ}
    (h : w * star w = 1) :
    ‖w‖ = 1 := by
  have h' := congrArg norm h
  simp at h'
  have hw_nonneg : 0 ≤ ‖w‖ := norm_nonneg w
  nlinarith

theorem rankOneKernel_ae_to_unimodular_phase
    {d : Nat} {f g : L2Real d} {fRep gRep : RealVec d -> ℂ}
    (hf_rep : IsL2Rep f fRep) (hg_rep : IsL2Rep g gRep)
    (hkernel :
      (fun p : RealVec d × RealVec d => fRep p.1 * star (fRep p.2))
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d × RealVec d))]
          fun p => gRep p.1 * star (gRep p.2)) :
    (f = 0 ∧ g = 0) ∨ ∃ w : ℂ, ‖w‖ = 1 ∧ g = w • f := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  have hkernel_prod :
      (fun p : RealVec d × RealVec d => fRep p.1 * star (fRep p.2))
        =ᵐ[μ.prod μ] fun p => gRep p.1 * star (gRep p.2) := by
    simpa [μ, MeasureTheory.Measure.volume_eq_prod (RealVec d) (RealVec d)]
      using hkernel
  have hrow_ae :
      ∀ᵐ u ∂μ, ∀ᵐ v ∂μ,
        fRep u * star (fRep v) = gRep u * star (gRep v) := by
    simpa using MeasureTheory.Measure.ae_ae_of_ae_prod hkernel_prod
  by_cases hf_zero : f = 0
  · left
    refine ⟨hf_zero, ?_⟩
    by_contra hg_ne
    have hfRep_zero : fRep =ᵐ[μ] fun _ => (0 : ℂ) :=
      rep_ae_eq_zero_of_L2_eq_zero hf_rep hf_zero
    have hgRep_not_zero : ¬ gRep =ᵐ[μ] fun _ => (0 : ℂ) := by
      intro hzero
      exact hg_ne (L2_eq_zero_of_rep_ae_eq_zero hg_rep hzero)
    have hgood : ∀ᵐ u ∂μ,
        (∀ᵐ v ∂μ, fRep u * star (fRep v) = gRep u * star (gRep v)) ∧
          fRep u = 0 := hrow_ae.and hfRep_zero
    rcases exists_eventually_and_ne_zero hgood hgRep_not_zero with
      ⟨u0, hgood_u0, hg0_ne⟩
    rcases hgood_u0 with ⟨hrow_u0, hf0⟩
    have hgRep_zero : gRep =ᵐ[μ] fun _ => (0 : ℂ) := by
      filter_upwards [hrow_u0] with v hv
      have hmul : gRep u0 * star (gRep v) = 0 := by simpa [hf0] using hv.symm
      have hstar : star (gRep v) = 0 :=
        (mul_eq_zero.mp hmul).resolve_left hg0_ne
      exact star_eq_zero.mp hstar
    exact hg_ne (L2_eq_zero_of_rep_ae_eq_zero hg_rep hgRep_zero)
  · right
    have hfRep_not_zero : ¬ fRep =ᵐ[μ] fun _ => (0 : ℂ) := by
      intro hzero
      exact hf_zero (L2_eq_zero_of_rep_ae_eq_zero hf_rep hzero)
    rcases exists_eventually_and_ne_zero hrow_ae hfRep_not_zero with
      ⟨u0, hrow_u0, hf0_ne⟩
    have hg0_ne : gRep u0 ≠ 0 := by
      by_contra hg0
      apply hfRep_not_zero
      filter_upwards [hrow_u0] with v hv
      have hmul : fRep u0 * star (fRep v) = 0 := by simpa [hg0] using hv
      have hstar : star (fRep v) = 0 :=
        (mul_eq_zero.mp hmul).resolve_left hf0_ne
      exact star_eq_zero.mp hstar
    let w : ℂ := star (fRep u0 / gRep u0)
    have hphase : gRep =ᵐ[μ] fun v => w * fRep v := by
      filter_upwards [hrow_u0] with v hv
      have hstar :
          star (gRep v) = (fRep u0 / gRep u0) * star (fRep v) := by
        calc
          star (gRep v) =
              ((gRep u0)⁻¹ * gRep u0) * star (gRep v) := by rw [inv_mul_cancel₀ hg0_ne, one_mul]
          _ = (gRep u0)⁻¹ * (gRep u0 * star (gRep v)) := by ring
          _ = (gRep u0)⁻¹ * (fRep u0 * star (fRep v)) := by rw [← hv]
          _ = (fRep u0 / gRep u0) * star (fRep v) := by field_simp [div_eq_mul_inv]
      have hconj := congrArg star hstar
      calc
        gRep v = fRep v * star (fRep u0 / gRep u0) := by simpa [star_mul] using hconj
        _ = w * fRep v := by ring
    have hL2 : g = w • f :=
      ae_unimodular_phase_to_L2_eq hf_rep hg_rep hphase
    have hphase_fst :
        (fun p : RealVec d × RealVec d => gRep p.1)
          =ᵐ[μ.prod μ] fun p => w * fRep p.1 :=
      MeasureTheory.Measure.quasiMeasurePreserving_fst.ae hphase
    have hphase_snd :
        (fun p : RealVec d × RealVec d => gRep p.2)
          =ᵐ[μ.prod μ] fun p => w * fRep p.2 :=
      MeasureTheory.Measure.quasiMeasurePreserving_snd.ae hphase
    have hscale_prod :
        (fun p : RealVec d × RealVec d => fRep p.1 * star (fRep p.2))
          =ᵐ[μ.prod μ]
            fun p => (w * star w) * (fRep p.1 * star (fRep p.2)) := by
      filter_upwards [hkernel_prod, hphase_fst, hphase_snd] with p hp hp1 hp2
      calc
        fRep p.1 * star (fRep p.2) = gRep p.1 * star (gRep p.2) := hp
        _ = (w * fRep p.1) * star (w * fRep p.2) := by rw [hp1, hp2]
        _ = (w * star w) * (fRep p.1 * star (fRep p.2)) := by
              rw [star_mul]
              ring
    have hscale_rows :
        ∀ᵐ u ∂μ, ∀ᵐ v ∂μ,
          fRep u * star (fRep v) =
            (w * star w) * (fRep u * star (fRep v)) := by
      simpa using MeasureTheory.Measure.ae_ae_of_ae_prod hscale_prod
    rcases exists_eventually_and_ne_zero hscale_rows hfRep_not_zero with
      ⟨u1, hscale_u1, hu1_ne⟩
    rcases exists_eventually_and_ne_zero hscale_u1 hfRep_not_zero with
      ⟨v1, hscale_u1v1, hv1_ne⟩
    have hF_ne : fRep u1 * star (fRep v1) ≠ 0 :=
      mul_ne_zero hu1_ne (star_ne_zero.mpr hv1_ne)
    have hunit_mul : w * star w = 1 := by
      have hc : (w * star w) * (fRep u1 * star (fRep v1)) =
          1 * (fRep u1 * star (fRep v1)) := by simpa [one_mul] using hscale_u1v1.symm
      exact mul_right_cancel₀ hF_ne hc
    exact ⟨w, norm_eq_one_of_mul_star_eq_one hunit_mul, hL2⟩

theorem rankOneRecoveryFromAmbiguity
    {d : Nat} {f g : L2Real d} {fRep gRep : RealVec d -> ℂ}
    (hf_rep : IsL2Rep f fRep) (hg_rep : IsL2Rep g gRep)
    (hAmb : ∀ ξ : PhaseSpace d, ambiguityRep f f ξ = ambiguityRep g g ξ) :
    (f = 0 ∧ g = 0) ∨ ∃ w : ℂ, ‖w‖ = 1 ∧ g = w • f :=
  rankOneKernel_ae_to_unimodular_phase hf_rep hg_rep
    (equalAmbiguity_to_rankOneKernel_ae hf_rep hg_rep hAmb)

theorem lift_unimodular_phase_L2_to_Skappa
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {U V : Skappa d kappa} {w : ℂ}
    (hL2 : bKappa kappa V = w • bKappa kappa U) :
    V = w • U := by
  let _ := hd
  apply bKappa_injective kappa
  rw [hL2, bKappa_smul]

theorem ae_modulus_to_pointwise_modulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {U V : Skappa d kappa}
    (hmod :
      (fun z => ‖toFun kappa U z‖) =ᵐ[gammaD d]
        fun z => ‖toFun kappa V z‖) :
    ∀ z, ‖toFun kappa U z‖ = ‖toFun kappa V z‖ := by
  have hmodC :
      (fun z => ((‖toFun kappa U z‖ : ℝ) : ℂ)) =ᵐ[gammaD d]
        fun z => ((‖toFun kappa V z‖ : ℝ) : ℂ) := by
    filter_upwards [hmod] with z hz
    rw [hz]
  have hcontU : Continuous (fun z => ((‖toFun kappa U z‖ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_toFun hd kappa U).norm)
  have hcontV : Continuous (fun z => ((‖toFun kappa V z‖ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_toFun hd kappa V).norm)
  have hC := continuous_eq_of_ae_eq_gamma hd hcontU hcontV hmodC
  intro z
  exact Complex.ofReal_injective (congrFun hC z)

theorem ae_modulus_to_stft_modulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {U V : Skappa d kappa}
    (hmod :
      (fun z => ‖toFun kappa U z‖) =ᵐ[gammaD d]
        fun z => ‖toFun kappa V z‖) :
    ∀ ξ, ‖stftRep (varphiKappa kappa) (bKappa kappa U) ξ‖ =
      ‖stftRep (varphiKappa kappa) (bKappa kappa V) ξ‖ := by
  have hpoint := ae_modulus_to_pointwise_modulus hd kappa hmod
  intro ξ
  rw [stft_model_modulus hd kappa U ξ, stft_model_modulus hd kappa V ξ,
    hpoint (TKappa ξ)]

theorem ae_modulus_to_ambiguity_eq
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {U V : Skappa d kappa}
    (hmod :
      (fun z => ‖toFun kappa U z‖) =ᵐ[gammaD d]
        fun z => ‖toFun kappa V z‖) :
    ∀ ξ, ambiguityRep (bKappa kappa U) (bKappa kappa U) ξ =
      ambiguityRep (bKappa kappa V) (bKappa kappa V) ξ := by
  exact spectrogram_eq_of_equal_modulus_to_ambiguity_eq hd kappa
    (ae_modulus_to_stft_modulus hd kappa hmod)

private theorem toFun_ofPkappa_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) :
    toFun kappa (ofPkappa kappa F) = evalPkappa kappa F := by
  let _ := hd
  ext z
  rw [toFun, evalPkappa, Finsupp.sum]
  have hzero :
      ∀ alpha ∉ F.support,
        coeffSkappa (ofPkappa kappa F) alpha * Phi kappa alpha z = 0 := by
    intro alpha halpha
    simp [coeffSkappa, ofPkappa, Finsupp.notMem_support_iff.mp halpha]
  rw [tsum_eq_sum hzero]
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  simp [coeffSkappa, ofPkappa]

private theorem norm_sq_eq_sum_coeff_exact_wip
    {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) :
    ‖F‖ ^ 2 = Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2) := by
  change (Real.sqrt (Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2))) ^ 2 = _
  rw [Real.sq_sqrt]
  positivity

private theorem pkappa_eq_zero_of_norm_sq_eq_zero_wip
    {d : Nat} {kappa : MultiIndex d} {F : Pkappa d kappa}
    (hF_norm_sq : ‖F‖ ^ 2 = 0) :
    F = 0 := by
  ext alpha
  by_cases hmem : alpha ∈ F.support
  · have hsum_zero :
        Finset.sum F.support (fun beta => ‖F beta‖ ^ 2) = 0 := by
      simpa [norm_sq_eq_sum_coeff_exact_wip F] using hF_norm_sq
    have hle :
        ‖F alpha‖ ^ 2 ≤ Finset.sum F.support (fun beta => ‖F beta‖ ^ 2) := by
      simpa using
        (Finset.single_le_sum
          (f := fun beta : Idx d => ‖F beta‖ ^ 2) (s := F.support) (a := alpha)
          (fun beta _ => by positivity) hmem)
    have hnorm_sq_zero : ‖F alpha‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖F alpha‖]
    have hnorm_zero : ‖F alpha‖ = 0 := by nlinarith [norm_nonneg (F alpha)]
    exact norm_eq_zero.mp hnorm_zero
  · exact Finsupp.notMem_support_iff.mp hmem

private theorem pkappa_eq_zero_of_eval_zero_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {F : Pkappa d kappa} (hF_eval : ∀ z, evalPkappa kappa F z = 0) :
    F = 0 := by
  have hmass := evalPkappa_total_mass hd kappa F
  have hintegral_zero :
      (∫ z, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) = 0 := by simp [hF_eval]
  have hnorm_sq : ‖F‖ ^ 2 = 0 := by linarith
  exact pkappa_eq_zero_of_norm_sq_eq_zero_wip hnorm_sq

private theorem skappa_ext_coeff_exact_wip
    {d : Nat} {kappa : MultiIndex d} {U V : Skappa d kappa}
    (hcoeff : ∀ alpha, coeffSkappa U alpha = coeffSkappa V alpha) :
    U = V := by
  cases U
  cases V
  simp only [coeffSkappa] at hcoeff
  congr
  funext alpha
  exact hcoeff alpha

private theorem bKappa_zero_exact_wip
    {d : Nat} (kappa : MultiIndex d) :
    bKappa kappa (0 : Skappa d kappa) = 0 := by
  have h := bKappa_smul kappa (0 : ℂ) (0 : Skappa d kappa)
  have hzero_smul : (0 : ℂ) • (0 : Skappa d kappa) = 0 := by
    apply skappa_ext_coeff_exact_wip
    intro alpha
    change (0 : ℂ) * 0 = 0
    simp
  simpa [hzero_smul] using h

private theorem skappa_eq_zero_of_bKappa_eq_zero_exact_wip
    {d : Nat} {kappa : MultiIndex d} {U : Skappa d kappa}
    (hU : bKappa kappa U = 0) :
    U = 0 := by
  apply bKappa_injective kappa
  rw [hU, bKappa_zero_exact_wip]

private theorem skappa_eq_zero_of_coeff_zero_exact_wip
    {d : Nat} {kappa : MultiIndex d} {U : Skappa d kappa}
    (hcoeff : ∀ alpha, coeffSkappa U alpha = 0) :
    U = 0 := by
  apply skappa_ext_coeff_exact_wip
  intro alpha
  rw [hcoeff alpha]
  change (0 : ℂ) = (0 : Skappa d kappa).coeff alpha
  rfl

private theorem toFun_zero_exact_wip
    {d : Nat} (kappa : MultiIndex d) :
    toFun kappa (0 : Skappa d kappa) = 0 := by
  ext z
  unfold toFun coeffSkappa
  change (∑' alpha : Idx d, (0 : ℂ) * Phi kappa alpha z) = 0
  simp

private theorem skappa_eq_zero_of_toFun_zero_exact_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) {U : Skappa d kappa}
    (hU : ∀ z, toFun kappa U z = 0) :
    U = 0 := by
  apply skappa_eq_zero_of_coeff_zero_exact_wip
  intro beta
  have hL2 : toL2 kappa U = toL2 kappa (0 : Skappa d kappa) := by
    exact toL2_eq_of_toFun_eq hd (fun z => by
      rw [hU z, toFun_zero_exact_wip kappa]
      rfl)
  calc
    coeffSkappa U beta = inner ℂ (PhiL2 kappa beta) (toL2 kappa U) := coeff_recovery hd kappa U beta
    _ = inner ℂ (PhiL2 kappa beta) (toL2 kappa (0 : Skappa d kappa)) := by rw [hL2]
    _ = coeffSkappa (0 : Skappa d kappa) beta :=
      (coeff_recovery hd kappa (0 : Skappa d kappa) beta).symm
    _ = 0 := rfl

private theorem coeff_eq_zero_of_self_kernel_zero_exact_wip {z : ℂ}
    (h : z * star z = 0) :
    z = 0 := by
  have hnormSq_c : ((Complex.normSq z : ℝ) : ℂ) = 0 := by simpa [Complex.mul_conj] using h
  have hnormSq : Complex.normSq z = 0 := Complex.ofReal_eq_zero.mp hnormSq_c
  exact Complex.normSq_eq_zero.mp hnormSq

private theorem norm_eq_of_self_kernel_eq_exact_wip {x y : ℂ}
    (h : x * star x = y * star y) :
    ‖x‖ = ‖y‖ := by
  have hmul_norm : ‖x‖ * ‖x‖ = ‖y‖ * ‖y‖ := by simpa [norm_mul, norm_star] using congrArg norm h
  have hsq : ‖x‖ ^ 2 = ‖y‖ ^ 2 := by simpa [sq] using hmul_norm
  have hcases := (sq_eq_sq_iff_eq_or_eq_neg (a := ‖x‖) (b := ‖y‖)).mp hsq
  rcases hcases with hxy | hxy
  · exact hxy
  · have hx_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
    have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg _
    have hy_zero : ‖y‖ = 0 := by
      apply le_antisymm
      · linarith [hxy, hx_nonneg]
      · exact hy_nonneg
    have hx_zero : ‖x‖ = 0 := by simpa [hy_zero] using hxy
    rw [hx_zero, hy_zero]

private theorem scalar_multiple_of_coeff_kernel_exact_wip
    {d : Nat} {kappa : MultiIndex d} {U V : Skappa d kappa}
    (hker : ∀ alpha beta,
      coeffSkappa V alpha * star (coeffSkappa V beta) =
        coeffSkappa U alpha * star (coeffSkappa U beta)) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ V = w • U := by
  by_cases hU_zero : U = 0
  · have hV_coeff_zero : ∀ alpha, coeffSkappa V alpha = 0 := by
      intro alpha
      have hU_alpha_zero : coeffSkappa U alpha = 0 := by
        rw [hU_zero]
        rfl
      have hself : coeffSkappa V alpha * star (coeffSkappa V alpha) = 0 := by
        rw [hker alpha alpha, hU_alpha_zero]
        simp
      exact coeff_eq_zero_of_self_kernel_zero_exact_wip hself
    have hV_zero : V = 0 := skappa_eq_zero_of_coeff_zero_exact_wip hV_coeff_zero
    refine ⟨1, by norm_num, ?_⟩
    rw [hU_zero, hV_zero]
    apply skappa_ext_coeff_exact_wip
    intro alpha
    change (0 : ℂ) = (1 : ℂ) * 0
    simp
  · have hU_coeff_nonzero : ∃ alpha0, coeffSkappa U alpha0 ≠ 0 := by
      by_contra hnone
      have hzero : ∀ alpha, coeffSkappa U alpha = 0 := by
        intro alpha
        by_contra hα
        exact hnone ⟨alpha, hα⟩
      exact hU_zero (skappa_eq_zero_of_coeff_zero_exact_wip hzero)
    rcases hU_coeff_nonzero with ⟨alpha0, hU0⟩
    let u0 : ℂ := coeffSkappa U alpha0
    let v0 : ℂ := coeffSkappa V alpha0
    let w : ℂ := v0 / u0
    have hnorm_eq : ‖v0‖ = ‖u0‖ := by
      dsimp [u0, v0]
      exact norm_eq_of_self_kernel_eq_exact_wip (hker alpha0 alpha0)
    have hu0_ne : u0 ≠ 0 := by simpa [u0] using hU0
    have hu0_norm_ne : ‖u0‖ ≠ 0 := norm_ne_zero_iff.mpr hu0_ne
    have hw_norm : ‖w‖ = 1 := by
      calc
        ‖w‖ = ‖v0‖ / ‖u0‖ := by simp [w]
        _ = ‖u0‖ / ‖u0‖ := by rw [hnorm_eq]
        _ = 1 := div_self hu0_norm_ne
    have hv0_eq : v0 = w * u0 := by
      dsimp [w]
      exact (div_mul_cancel₀ v0 hu0_ne).symm
    have hcoeff : ∀ alpha, coeffSkappa V alpha = w * coeffSkappa U alpha := by
      intro alpha
      let u : ℂ := coeffSkappa U alpha
      let v : ℂ := coeffSkappa V alpha
      have hrel : v * star v0 = u * star u0 := by
        dsimp [u, v, u0, v0]
        exact hker alpha alpha0
      have hstar_v0 : star v0 = star w * star u0 := by
        rw [hv0_eq]
        simp [star_mul, mul_comm]
      have hcancel : v * star w = u := by
        apply mul_right_cancel₀ (star_ne_zero.mpr hu0_ne)
        calc
          (v * star w) * star u0 = v * (star w * star u0) := by ring
          _ = v * star v0 := by rw [← hstar_v0]
          _ = u * star u0 := hrel
      have hw_conj : w * star w = 1 := by simpa [hw_norm] using (RCLike.mul_conj w)
      have hstarw_mul_w : star w * w = 1 := by simpa [mul_comm] using hw_conj
      calc
        coeffSkappa V alpha = v := rfl
        _ = v * (star w * w) := by rw [hstarw_mul_w, mul_one]
        _ = (v * star w) * w := by ring
        _ = u * w := by rw [hcancel]
        _ = w * u := by ring
        _ = w * coeffSkappa U alpha := rfl
    refine ⟨w, hw_norm, ?_⟩
    apply skappa_ext_coeff_exact_wip
    intro alpha
    exact hcoeff alpha

private theorem coeff_kernel_of_scalar_multiple_exact_wip
    {d : Nat} {kappa : MultiIndex d} {U V : Skappa d kappa} {w : ℂ}
    (hw : ‖w‖ = 1) (hVU : V = w • U) :
    ∀ alpha beta,
      coeffSkappa V alpha * star (coeffSkappa V beta) =
        coeffSkappa U alpha * star (coeffSkappa U beta) := by
  intro alpha beta
  rw [hVU]
  change (w * coeffSkappa U alpha) * star (w * coeffSkappa U beta) =
    coeffSkappa U alpha * star (coeffSkappa U beta)
  have hw_conj : w * star w = 1 := by simpa [hw] using (RCLike.mul_conj w)
  calc
    (w * coeffSkappa U alpha) * star (w * coeffSkappa U beta) =
        (w * star w) * (coeffSkappa U alpha * star (coeffSkappa U beta)) := by
          rw [star_mul]
          ring
    _ = coeffSkappa U alpha * star (coeffSkappa U beta) := by
          rw [hw_conj]
          ring

theorem ambiguity_eq_to_skappa_phase
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {U V : Skappa d kappa}
    (hAmb : ∀ ξ,
      ambiguityRep (bKappa kappa U) (bKappa kappa U) ξ =
        ambiguityRep (bKappa kappa V) (bKappa kappa V) ξ) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ V = w • U := by
  let fRep := bKappaRep kappa U
  let gRep := bKappaRep kappa V
  have hf_rep : IsL2Rep (bKappa kappa U) fRep :=
    bKappaRep_isL2Rep kappa U
  have hg_rep : IsL2Rep (bKappa kappa V) gRep :=
    bKappaRep_isL2Rep kappa V
  rcases rankOneRecoveryFromAmbiguity hf_rep hg_rep hAmb with hzero | hphase
  · rcases hzero with ⟨hU_zero, hV_zero⟩
    have hU0 : U = 0 := skappa_eq_zero_of_bKappa_eq_zero_exact_wip hU_zero
    have hV0 : V = 0 := skappa_eq_zero_of_bKappa_eq_zero_exact_wip hV_zero
    refine ⟨1, by norm_num, ?_⟩
    rw [hU0, hV0]
    apply skappa_ext_coeff_exact_wip
    intro alpha
    change (0 : ℂ) = (1 : ℂ) * 0
    simp
  · rcases hphase with ⟨w, hw, hL2⟩
    exact ⟨w, hw, lift_unimodular_phase_L2_to_Skappa hd kappa hL2⟩

private theorem coeff_kernel_of_exact_modulus_recovery_skappa_ae_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {U V : Skappa d kappa}
    (hmod :
      (fun z => ‖toFun kappa U z‖) =ᵐ[gammaD d]
        fun z => ‖toFun kappa V z‖) :
    ∀ alpha beta,
      coeffSkappa V alpha * star (coeffSkappa V beta) =
        coeffSkappa U alpha * star (coeffSkappa U beta) := by
  rcases ambiguity_eq_to_skappa_phase hd kappa
      (ae_modulus_to_ambiguity_eq hd kappa hmod) with ⟨w, hw, hVU⟩
  exact coeff_kernel_of_scalar_multiple_exact_wip hw hVU

theorem exact_modulus_recovery_skappa_ae
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {U V : Skappa d kappa}
    (hmod :
      (fun z => ‖toFun kappa U z‖) =ᵐ[gammaD d]
        fun z => ‖toFun kappa V z‖) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ V = w • U := by
  have hpoint := ae_modulus_to_pointwise_modulus hd kappa hmod
  by_cases hU_zero : U = 0
  · have hV_toFun_zero : ∀ z, toFun kappa V z = 0 := by
      intro z
      have hz_norm : ‖toFun kappa V z‖ = 0 := by
        simpa [hU_zero, toFun_zero_exact_wip] using (hpoint z).symm
      exact norm_eq_zero.mp hz_norm
    have hV_zero : V = 0 :=
      skappa_eq_zero_of_toFun_zero_exact_wip hd kappa hV_toFun_zero
    refine ⟨1, by norm_num, ?_⟩
    rw [hU_zero, hV_zero]
    apply skappa_ext_coeff_exact_wip
    intro alpha
    change (0 : ℂ) = (1 : ℂ) * 0
    simp
  by_cases hV_zero : V = 0
  · have hU_toFun_zero : ∀ z, toFun kappa U z = 0 := by
      intro z
      have hz_norm : ‖toFun kappa U z‖ = 0 := by
        simpa [hV_zero, toFun_zero_exact_wip] using hpoint z
      exact norm_eq_zero.mp hz_norm
    exact False.elim
      (hU_zero (skappa_eq_zero_of_toFun_zero_exact_wip hd kappa hU_toFun_zero))
  exact scalar_multiple_of_coeff_kernel_exact_wip
    (coeff_kernel_of_exact_modulus_recovery_skappa_ae_wip hd kappa hmod)

theorem exact_modulus_recovery_skappa
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {U V : Skappa d kappa}
    (hmod : ∀ z, ‖toFun kappa U z‖ = ‖toFun kappa V z‖) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ V = w • U := exact_modulus_recovery_skappa_ae hd kappa (by
    filter_upwards with z
    exact hmod z)

theorem exact_modulus_recovery_pkappa
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {U V : Pkappa d kappa}
    (hmod : ∀ z, ‖evalPkappa kappa U z‖ = ‖evalPkappa kappa V z‖) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ V = w • U := by
  let _ := hd
  by_cases hU_zero : U = 0
  · subst U
    have hV_eval : ∀ z, evalPkappa kappa V z = 0 := by
      intro z
      have hz : ‖evalPkappa kappa V z‖ = 0 := by
        simpa [evalPkappa_zero hd kappa] using (hmod z).symm
      exact norm_eq_zero.mp hz
    have hV_zero : V = 0 := pkappa_eq_zero_of_eval_zero_wip hd kappa hV_eval
    refine ⟨1, by norm_num, ?_⟩
    simp [hV_zero]
  by_cases hV_zero : V = 0
  · subst V
    have hU_eval : ∀ z, evalPkappa kappa U z = 0 := by
      intro z
      have hz : ‖evalPkappa kappa U z‖ = 0 := by simpa [evalPkappa_zero hd kappa] using hmod z
      exact norm_eq_zero.mp hz
    have hU_zero' : U = 0 := pkappa_eq_zero_of_eval_zero_wip hd kappa hU_eval
    exact False.elim (hU_zero hU_zero')
  have hmod' : ∀ z, ‖toFun kappa (ofPkappa kappa U) z‖ =
      ‖toFun kappa (ofPkappa kappa V) z‖ := by
    intro z
    simpa [toFun_ofPkappa_wip hd kappa U, toFun_ofPkappa_wip hd kappa V] using hmod z
  rcases exact_modulus_recovery_skappa hd kappa hmod' with ⟨w, hw, hVU⟩
  refine ⟨w, hw, ?_⟩
  ext alpha
  have hcoeff := congrArg (fun S : Skappa d kappa => coeffSkappa S alpha) hVU
  simp only [coeffSkappa] at hcoeff
  rw [show ((w • ofPkappa kappa U).coeff alpha) = w * (ofPkappa kappa U).coeff alpha from rfl]
    at hcoeff
  simpa [coeff_ofPkappa, hd, ofPkappa] using hcoeff

end DimdPolyLEAN
