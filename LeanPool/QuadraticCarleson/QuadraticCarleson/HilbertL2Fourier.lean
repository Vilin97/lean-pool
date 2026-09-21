/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.PVFourierIdentity
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# The ordinary Hilbert transform on `L²`

This file constructs the Fourier-multiplier realization of convolution with
the project's kernel `p.v. (1 / x)`.  Mathlib's Fourier normalization makes
the multiplier `-π i sign(ξ)`, so its `L²` operator norm is at most `π`.
-/

open Filter Function MeasureTheory Set FourierTransform
open scoped ENNReal NNReal SchwartzMap

namespace QuadraticCarleson
namespace HilbertL2Fourier


noncomputable section

/-- The multiplier dictated by `fourier_principalValueOneDiv`. -/
def ordinaryHilbertMultiplier (ξ : ℝ) : ℂ :=
  -((Real.pi : ℂ) * Complex.I) * (Real.sign ξ : ℂ)

theorem measurable_real_sign : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id)
      measurable_const measurable_const)

theorem measurable_ordinaryHilbertMultiplier :
    Measurable ordinaryHilbertMultiplier :=
  measurable_const.mul (Complex.measurable_ofReal.comp measurable_real_sign)

theorem norm_real_sign_le_one (ξ : ℝ) : ‖Real.sign ξ‖ ≤ 1 := by
  rcases Real.sign_apply_eq ξ with h | h | h <;> rw [h] <;> norm_num

theorem norm_ordinaryHilbertMultiplier_le (ξ : ℝ) :
    ‖ordinaryHilbertMultiplier ξ‖ ≤ Real.pi := by
  unfold ordinaryHilbertMultiplier
  rw [norm_mul, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_pos.le, norm_real_sign_le_one ξ,
    norm_nonneg (Real.sign ξ)]

/-- Test-function form of the already-proved distributional identity
`𝓕(p.v. 1/x) = -π i sign`.  This explicitly identifies the pointwise
multiplier used below with the two half-line integrals defining the project's
`signTemperedDistribution`. -/
theorem fourier_principalValueOneDiv_apply_eq_multiplier_halfLines
    (φ : 𝓢(ℝ, ℂ)) :
    (𝓕 principalValueOneDiv) φ =
      (∫ ξ in Ioi (0 : ℝ), ordinaryHilbertMultiplier ξ * φ ξ) +
        ∫ ξ in Iio (0 : ℝ), ordinaryHilbertMultiplier ξ * φ ξ := by
  have hpos : (∫ ξ in Ioi (0 : ℝ), ordinaryHilbertMultiplier ξ * φ ξ) =
      (-((Real.pi : ℂ) * Complex.I)) * ∫ ξ in Ioi (0 : ℝ), φ ξ := by
    calc
      _ = ∫ ξ in Ioi (0 : ℝ),
          (-((Real.pi : ℂ) * Complex.I)) * φ ξ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
        rw [ordinaryHilbertMultiplier, Real.sign_of_pos hξ]
        simp
      _ = _ := integral_const_mul _ _
  have hneg : (∫ ξ in Iio (0 : ℝ), ordinaryHilbertMultiplier ξ * φ ξ) =
      -(-((Real.pi : ℂ) * Complex.I)) * ∫ ξ in Iio (0 : ℝ), φ ξ := by
    calc
      _ = ∫ ξ in Iio (0 : ℝ),
          (-(-((Real.pi : ℂ) * Complex.I))) * φ ξ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Iio] with ξ hξ
        rw [ordinaryHilbertMultiplier, Real.sign_of_neg hξ]
        norm_num
      _ = _ := integral_const_mul _ _
  rw [fourier_principalValueOneDiv]
  change (-((Real.pi : ℂ) * Complex.I)) * signTemperedDistribution φ = _
  rw [signTemperedDistribution_apply, hpos, hneg]
  ring

/-- A fixed measurable representative of the `L²` Fourier transform. -/
def fourierL2Representative (f : Lp (α := ℝ) ℂ 2) : ℝ → ℂ :=
  ⇑(Lp.fourierTransformₗᵢ ℝ ℂ f)

theorem memLp_fourierL2Representative (f : Lp (α := ℝ) ℂ 2) :
    MemLp (fourierL2Representative f) 2 volume :=
  Lp.memLp (Lp.fourierTransformₗᵢ ℝ ℂ f)

def multipliedFourierRepresentative (f : Lp (α := ℝ) ℂ 2) : ℝ → ℂ :=
  fun ξ ↦ ordinaryHilbertMultiplier ξ * fourierL2Representative f ξ

theorem memLp_ordinaryHilbertMultiplier_mul_fourier
    (f : Lp (α := ℝ) ℂ 2) :
    MemLp (multipliedFourierRepresentative f) 2 volume := by
  apply MemLp.of_le_mul (c := Real.pi) (memLp_fourierL2Representative f)
  · exact measurable_ordinaryHilbertMultiplier.aestronglyMeasurable.mul
      (memLp_fourierL2Representative f).1
  · filter_upwards with ξ
    unfold multipliedFourierRepresentative
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_ordinaryHilbertMultiplier_le ξ)
      (norm_nonneg _)

/-- Fourier-side multiplication by `-π i sign(ξ)`. -/
def ordinaryHilbertMultiplierL2 (f : Lp (α := ℝ) ℂ 2) :
    Lp (α := ℝ) ℂ 2 :=
  MemLp.toLp (μ := volume)
    (multipliedFourierRepresentative f)
    (memLp_ordinaryHilbertMultiplier_mul_fourier f)

/-- The ordinary Hilbert transform on `L²`, obtained by inverse Fourier
transforming the canonical multiplier. -/
def ordinaryHilbertTransformL2 (f : Lp (α := ℝ) ℂ 2) :
    Lp (α := ℝ) ℂ 2 :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm (ordinaryHilbertMultiplierL2 f)

theorem eLpNorm_multipliedFourierRepresentative_le
    (f : Lp (α := ℝ) ℂ 2) :
    eLpNorm (multipliedFourierRepresentative f) 2 volume ≤
      ENNReal.ofReal Real.pi * eLpNorm (fourierL2Representative f) 2 volume := by
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
  filter_upwards with ξ
  unfold multipliedFourierRepresentative
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_ordinaryHilbertMultiplier_le ξ)
    (norm_nonneg _)

theorem eLpNorm_multipliedFourierRepresentative_eq
    (f : Lp (α := ℝ) ℂ 2 volume) :
    eLpNorm (multipliedFourierRepresentative f) 2 volume =
      ENNReal.ofReal Real.pi * eLpNorm (fourierL2Representative f) 2 volume := by
  have hne : ∀ᵐ ξ : ℝ ∂volume, ξ ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hnorm : ∀ᵐ ξ : ℝ ∂volume,
      ‖multipliedFourierRepresentative f ξ‖ =
        ‖(Real.pi : ℂ) * fourierL2Representative f ξ‖ := by
    filter_upwards [hne] with ξ hξ
    rcases Real.sign_apply_eq_of_ne_zero ξ hξ with hs | hs
    · simp [multipliedFourierRepresentative, ordinaryHilbertMultiplier, hs]
    · simp [multipliedFourierRepresentative, ordinaryHilbertMultiplier, hs]
  calc
    eLpNorm (multipliedFourierRepresentative f) 2 volume =
        eLpNorm (fun ξ ↦ (Real.pi : ℂ) * fourierL2Representative f ξ) 2 volume :=
      eLpNorm_congr_norm_ae hnorm
    _ = ‖(Real.pi : ℂ)‖ₑ * eLpNorm (fourierL2Representative f) 2 volume := by
      change eLpNorm ((Real.pi : ℂ) • fourierL2Representative f) 2 volume = _
      exact eLpNorm_const_smul (Real.pi : ℂ) (fourierL2Representative f) 2 volume
    _ = _ := by
      congr 1
      rw [← ofReal_norm]
      simp [Real.pi_pos.le]

theorem enorm_ordinaryHilbertMultiplierL2_le (f : Lp (α := ℝ) ℂ 2) :
    ‖ordinaryHilbertMultiplierL2 f‖ₑ ≤
      ENNReal.ofReal Real.pi * ‖f‖ₑ := by
  calc
    ‖ordinaryHilbertMultiplierL2 f‖ₑ =
        eLpNorm (multipliedFourierRepresentative f) 2 volume := by
      exact Lp.enorm_toLp (memLp_ordinaryHilbertMultiplier_mul_fourier f)
    _ ≤ ENNReal.ofReal Real.pi * eLpNorm (fourierL2Representative f) 2 volume :=
      eLpNorm_multipliedFourierRepresentative_le f
    _ = ENNReal.ofReal Real.pi * ‖Lp.fourierTransformₗᵢ ℝ ℂ f‖ₑ := by
      have heq : MemLp.toLp (fourierL2Representative f)
          (memLp_fourierL2Representative f) = Lp.fourierTransformₗᵢ ℝ ℂ f := by
        exact Lp.toLp_coeFn _ _
      rw [← Lp.enorm_toLp (memLp_fourierL2Representative f), heq]
    _ = _ := by simp

theorem norm_ordinaryHilbertMultiplierL2_le (f : Lp (α := ℝ) ℂ 2) :
    ‖ordinaryHilbertMultiplierL2 f‖ ≤ Real.pi * ‖f‖ := by
  have h := enorm_ordinaryHilbertMultiplierL2_le f
  have hreal := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).2 h
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal Real.pi_pos.le] using hreal

theorem norm_ordinaryHilbertMultiplierL2_eq (f : Lp (α := ℝ) ℂ 2 volume) :
    ‖ordinaryHilbertMultiplierL2 f‖ = Real.pi * ‖f‖ := by
  have henorm : ‖ordinaryHilbertMultiplierL2 f‖ₑ =
      ENNReal.ofReal Real.pi * ‖f‖ₑ := by
    calc
      ‖ordinaryHilbertMultiplierL2 f‖ₑ =
          eLpNorm (multipliedFourierRepresentative f) 2 volume :=
        Lp.enorm_toLp (memLp_ordinaryHilbertMultiplier_mul_fourier f)
      _ = ENNReal.ofReal Real.pi * eLpNorm (fourierL2Representative f) 2 volume :=
        eLpNorm_multipliedFourierRepresentative_eq f
      _ = ENNReal.ofReal Real.pi * ‖Lp.fourierTransformₗᵢ ℝ ℂ f‖ₑ := by
        have heq : MemLp.toLp (fourierL2Representative f)
            (memLp_fourierL2Representative f) = Lp.fourierTransformₗᵢ ℝ ℂ f :=
          Lp.toLp_coeFn _ _
        rw [← Lp.enorm_toLp (memLp_fourierL2Representative f), heq]
      _ = _ := by simp
  have hreal := congrArg ENNReal.toReal henorm
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal Real.pi_pos.le] using hreal

theorem norm_ordinaryHilbertTransformL2_le (f : Lp (α := ℝ) ℂ 2) :
    ‖ordinaryHilbertTransformL2 f‖ ≤ Real.pi * ‖f‖ := by
  rw [ordinaryHilbertTransformL2]
  change ‖(Lp.fourierTransformₗᵢ ℝ ℂ).symm (ordinaryHilbertMultiplierL2 f)‖ ≤ _
  rw [(Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map]
  exact norm_ordinaryHilbertMultiplierL2_le f

theorem norm_ordinaryHilbertTransformL2_eq (f : Lp (α := ℝ) ℂ 2 volume) :
    ‖ordinaryHilbertTransformL2 f‖ = Real.pi * ‖f‖ := by
  rw [ordinaryHilbertTransformL2]
  change ‖(Lp.fourierTransformₗᵢ ℝ ℂ).symm (ordinaryHilbertMultiplierL2 f)‖ = _
  rw [(Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map,
    norm_ordinaryHilbertMultiplierL2_eq]

theorem multipliedFourierRepresentative_add_ae
    (f g : Lp (α := ℝ) ℂ 2 volume) :
    multipliedFourierRepresentative (f + g) =ᵐ[volume]
      multipliedFourierRepresentative f + multipliedFourierRepresentative g := by
  have hF : Lp.fourierTransformₗᵢ ℝ ℂ (f + g) =
      Lp.fourierTransformₗᵢ ℝ ℂ f + Lp.fourierTransformₗᵢ ℝ ℂ g :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).map_add f g
  have hcoe := Lp.coeFn_add (Lp.fourierTransformₗᵢ ℝ ℂ f)
    (Lp.fourierTransformₗᵢ ℝ ℂ g)
  filter_upwards [hcoe] with ξ hξ
  unfold multipliedFourierRepresentative fourierL2Representative
  rw [hF]
  change ordinaryHilbertMultiplier ξ *
      ((⇑(Lp.fourierTransformₗᵢ ℝ ℂ f + Lp.fourierTransformₗᵢ ℝ ℂ g)) ξ) = _
  rw [hξ]
  simp only [Pi.add_apply]
  ring

theorem multipliedFourierRepresentative_smul_ae
    (c : ℂ) (f : Lp (α := ℝ) ℂ 2 volume) :
    multipliedFourierRepresentative (c • f) =ᵐ[volume]
      c • multipliedFourierRepresentative f := by
  have hF : Lp.fourierTransformₗᵢ ℝ ℂ (c • f) =
      c • Lp.fourierTransformₗᵢ ℝ ℂ f :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).map_smul c f
  have hcoe := Lp.coeFn_smul c (Lp.fourierTransformₗᵢ ℝ ℂ f)
  filter_upwards [hcoe] with ξ hξ
  unfold multipliedFourierRepresentative fourierL2Representative
  rw [hF]
  change ordinaryHilbertMultiplier ξ *
      ((⇑(c • Lp.fourierTransformₗᵢ ℝ ℂ f)) ξ) = _
  rw [hξ]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem ordinaryHilbertMultiplierL2_add (f g : Lp (α := ℝ) ℂ 2 volume) :
    ordinaryHilbertMultiplierL2 (f + g) =
      ordinaryHilbertMultiplierL2 f + ordinaryHilbertMultiplierL2 g := by
  calc
    ordinaryHilbertMultiplierL2 (f + g) =
        MemLp.toLp
          (multipliedFourierRepresentative f + multipliedFourierRepresentative g)
          ((memLp_ordinaryHilbertMultiplier_mul_fourier f).add
            (memLp_ordinaryHilbertMultiplier_mul_fourier g)) := by
      exact MemLp.toLp_congr
        (memLp_ordinaryHilbertMultiplier_mul_fourier (f + g))
        ((memLp_ordinaryHilbertMultiplier_mul_fourier f).add
          (memLp_ordinaryHilbertMultiplier_mul_fourier g))
        (multipliedFourierRepresentative_add_ae f g)
    _ = ordinaryHilbertMultiplierL2 f + ordinaryHilbertMultiplierL2 g :=
      MemLp.toLp_add (memLp_ordinaryHilbertMultiplier_mul_fourier f)
        (memLp_ordinaryHilbertMultiplier_mul_fourier g)

theorem ordinaryHilbertMultiplierL2_smul (c : ℂ)
    (f : Lp (α := ℝ) ℂ 2 volume) :
    ordinaryHilbertMultiplierL2 (c • f) = c • ordinaryHilbertMultiplierL2 f := by
  calc
    ordinaryHilbertMultiplierL2 (c • f) =
        MemLp.toLp (c • multipliedFourierRepresentative f)
          ((memLp_ordinaryHilbertMultiplier_mul_fourier f).const_smul c) := by
      exact MemLp.toLp_congr
        (memLp_ordinaryHilbertMultiplier_mul_fourier (c • f))
        ((memLp_ordinaryHilbertMultiplier_mul_fourier f).const_smul c)
        (multipliedFourierRepresentative_smul_ae c f)
    _ = c • ordinaryHilbertMultiplierL2 f :=
      MemLp.toLp_const_smul c (memLp_ordinaryHilbertMultiplier_mul_fourier f)

theorem ordinaryHilbertTransformL2_add (f g : Lp (α := ℝ) ℂ 2 volume) :
    ordinaryHilbertTransformL2 (f + g) =
      ordinaryHilbertTransformL2 f + ordinaryHilbertTransformL2 g := by
  unfold ordinaryHilbertTransformL2
  rw [ordinaryHilbertMultiplierL2_add, map_add]

theorem ordinaryHilbertTransformL2_smul (c : ℂ)
    (f : Lp (α := ℝ) ℂ 2 volume) :
    ordinaryHilbertTransformL2 (c • f) = c • ordinaryHilbertTransformL2 f := by
  unfold ordinaryHilbertTransformL2
  rw [ordinaryHilbertMultiplierL2_smul, map_smul]

def ordinaryHilbertTransformL2LinearMap :
    Lp (α := ℝ) ℂ 2 →ₗ[ℂ] Lp (α := ℝ) ℂ 2 where
  toFun := ordinaryHilbertTransformL2
  map_add' := ordinaryHilbertTransformL2_add
  map_smul' := ordinaryHilbertTransformL2_smul

/-- The Fourier realization of `p.v. (1/x)` as a genuine continuous linear
operator on `L²`. -/
def ordinaryHilbertTransformL2CLM :
    Lp (α := ℝ) ℂ 2 →L[ℂ] Lp (α := ℝ) ℂ 2 :=
  ordinaryHilbertTransformL2LinearMap.mkContinuous Real.pi
    norm_ordinaryHilbertTransformL2_le

@[simp] theorem ordinaryHilbertTransformL2CLM_apply
    (f : Lp (α := ℝ) ℂ 2) :
    ordinaryHilbertTransformL2CLM f = ordinaryHilbertTransformL2 f := rfl

theorem norm_ordinaryHilbertTransformL2CLM_le :
    ‖ordinaryHilbertTransformL2CLM‖ ≤ Real.pi :=
  LinearMap.mkContinuous_norm_le (f := ordinaryHilbertTransformL2LinearMap)
    Real.pi_pos.le norm_ordinaryHilbertTransformL2_le

/-- Fourier transforming the constructed Hilbert operator recovers exactly
the canonical multiplier class. -/
theorem fourier_ordinaryHilbertTransformL2
    (f : Lp (α := ℝ) ℂ 2 volume) :
    Lp.fourierTransformₗᵢ ℝ ℂ (ordinaryHilbertTransformL2 f) =
      ordinaryHilbertMultiplierL2 f := by
  unfold ordinaryHilbertTransformL2
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _

/-- Representative-level form of the multiplier identity. -/
theorem coe_fourier_ordinaryHilbertTransformL2_ae
    (f : Lp (α := ℝ) ℂ 2 volume) :
    (⇑(Lp.fourierTransformₗᵢ ℝ ℂ (ordinaryHilbertTransformL2 f)) : ℝ → ℂ)
      =ᵐ[volume] multipliedFourierRepresentative f := by
  rw [fourier_ordinaryHilbertTransformL2]
  exact MemLp.coeFn_toLp (memLp_ordinaryHilbertMultiplier_mul_fourier f)

theorem ordinaryHilbertMultiplier_sq {ξ : ℝ} (hξ : ξ ≠ 0) :
    ordinaryHilbertMultiplier ξ * ordinaryHilbertMultiplier ξ =
      -((Real.pi : ℂ) ^ 2) := by
  rcases Real.sign_apply_eq_of_ne_zero ξ hξ with hs | hs
  · simp only [ordinaryHilbertMultiplier, hs, Complex.ofReal_neg, Complex.ofReal_one,
      mul_neg, mul_one, neg_neg, ← pow_two, mul_pow, Complex.I_sq]
  · simp only [ordinaryHilbertMultiplier, hs, Complex.ofReal_one, mul_one, ← pow_two]
    rw [neg_sq, mul_pow, Complex.I_sq]
    ring

theorem multipliedFourierRepresentative_hilbert_ae
    (f : Lp (α := ℝ) ℂ 2 volume) :
    multipliedFourierRepresentative (ordinaryHilbertTransformL2 f) =ᵐ[volume]
      (-((Real.pi : ℂ) ^ 2)) • fourierL2Representative f := by
  have hne : ∀ᵐ ξ : ℝ ∂volume, ξ ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hF := coe_fourier_ordinaryHilbertTransformL2_ae f
  filter_upwards [hne, hF] with ξ hξ hFξ
  unfold multipliedFourierRepresentative fourierL2Representative
  rw [hFξ]
  unfold multipliedFourierRepresentative
  rw [← mul_assoc, ordinaryHilbertMultiplier_sq hξ]
  simp only [Pi.smul_apply, smul_eq_mul]
  rfl

theorem ordinaryHilbertMultiplierL2_hilbert
    (f : Lp (α := ℝ) ℂ 2 volume) :
    ordinaryHilbertMultiplierL2 (ordinaryHilbertTransformL2 f) =
      (-((Real.pi : ℂ) ^ 2)) • Lp.fourierTransformₗᵢ ℝ ℂ f := by
  calc
    ordinaryHilbertMultiplierL2 (ordinaryHilbertTransformL2 f) =
        MemLp.toLp
          ((-((Real.pi : ℂ) ^ 2)) • fourierL2Representative f)
          ((memLp_fourierL2Representative f).const_smul (-((Real.pi : ℂ) ^ 2))) := by
      exact MemLp.toLp_congr
        (memLp_ordinaryHilbertMultiplier_mul_fourier (ordinaryHilbertTransformL2 f))
        ((memLp_fourierL2Representative f).const_smul (-((Real.pi : ℂ) ^ 2)))
        (multipliedFourierRepresentative_hilbert_ae f)
    _ = (-((Real.pi : ℂ) ^ 2)) •
        MemLp.toLp (fourierL2Representative f) (memLp_fourierL2Representative f) :=
      MemLp.toLp_const_smul _ (memLp_fourierL2Representative f)
    _ = _ := by
      have heq : MemLp.toLp (fourierL2Representative f)
          (memLp_fourierL2Representative f) = Lp.fourierTransformₗᵢ ℝ ℂ f := by
        exact Lp.toLp_coeFn _ _
      rw [heq]

/-- With the project's unnormalized kernel `p.v. (1/x)`, the `L²` Hilbert
operator squares to `-π²` times the identity. -/
theorem ordinaryHilbertTransformL2_sq
    (f : Lp (α := ℝ) ℂ 2 volume) :
    ordinaryHilbertTransformL2 (ordinaryHilbertTransformL2 f) =
      (-((Real.pi : ℂ) ^ 2)) • f := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [fourier_ordinaryHilbertTransformL2,
    ordinaryHilbertMultiplierL2_hilbert, map_smul]


end
end HilbertL2Fourier
end QuadraticCarleson
