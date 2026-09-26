/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.Interpolation
public import Mathlib.Analysis.Convolution

/-!
# Strong bounds supplied by the two endpoint estimates

This file records the assembly step for a second Newtonian derivative.  The
operator is left as the operator supplied by the endpoint development: the
only inputs here are its sublinearity, measurability, weak `(1,1)` estimate,
and global `(2,2)` estimate.
-/

public section

open scoped ENNReal NNReal Topology Convolution

open MeasureTheory MeasureTheory.Measure Set Filter


noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

/-- The explicit integral constant furnished by weak-to-strong interpolation. -/
@[expose]
def rieszSecondInterpolationConstant (A₁ A₂ p : ℝ) : ℝ :=
  p * (2 ^ p * (A₁ / (p - 1) + A₂ ^ 2 / (2 - p)))

/- A linear operator has the pointwise sublinearity required by interpolation. -/
/-- Convert pointwise additivity into the exact sublinearity interface. -/
theorem rieszSecond_sublinear_of_additive
    {T : (Vec3 → ℝ) → (Vec3 → ℝ)}
    (hTadd : ∀ f g (x : Vec3), T (f + g) x = T f x + T g x) :
    ∀ f g (x : Vec3), |T (f + g) x| ≤ |T f x| + |T g x| := by
  intro f g x
  rw [hTadd]
  exact abs_add_le _ _

/- The measurable convolution proof is independent of the endpoint estimates. -/
/-- A measurable scalar convolution kernel gives a measurable convolution output. -/
theorem rieszSecond_measurable_of_convolution
    {K : Vec3 → ℝ} (hK : Measurable K) :
    ∀ f, Measurable f →
      Measurable (MeasureTheory.convolution f K
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) := by
  intro f hf
  have hf' : StronglyMeasurable (fun p : Vec3 × Vec3 => f p.2) :=
    hf.stronglyMeasurable.comp_measurable measurable_snd
  have hK' : StronglyMeasurable (fun p : Vec3 × Vec3 => K (p.1 - p.2)) :=
    hK.stronglyMeasurable.comp_measurable (measurable_fst.sub measurable_snd)
  have hprod : StronglyMeasurable
      (fun p : Vec3 × Vec3 => f p.2 * K (p.1 - p.2)) := hf'.mul hK'
  have hi : StronglyMeasurable (fun x : Vec3 =>
      ∫ t : Vec3, f t * K (x - t)) := hprod.integral_prod_right'
  exact hi.measurable

/-- Convolution respects almost-everywhere equality of its input. -/
theorem rieszSecond_convolution_congr
    {K f g : Vec3 → ℝ} (hfg : f =ᵐ[volume] g) :
    MeasureTheory.convolution f K
        (ContinuousLinearMap.lsmul ℝ ℝ) volume =
      MeasureTheory.convolution g K
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  exact MeasureTheory.convolution_congr
    (ContinuousLinearMap.lsmul ℝ ℝ) hfg (Eventually.of_forall (fun _ => rfl))

/- The pointwise convolution estimate records the integrability needed for the
   literal Bochner convolution; the endpoint operator may instead be its Lp
   extension, whose additivity is supplied to the preceding bridge. -/
/-- The literal convolution is sublinear wherever the two input integrals exist. -/
theorem rieszSecond_convolution_sublinear_of_integrable
    {K f g : Vec3 → ℝ} {x : Vec3}
    (hf : Integrable (fun y => f y * K (x - y)) volume)
    (hg : Integrable (fun y => g y * K (x - y)) volume) :
    |MeasureTheory.convolution (f + g) K
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x| ≤
      |MeasureTheory.convolution f K
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x| +
        |MeasureTheory.convolution g K
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x| := by
  rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def,
    MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hfun : (fun y => (f + g) y * K (x - y)) =
      (fun y => f y * K (x - y) + g y * K (x - y)) := by
    funext y
    simp only [Pi.add_apply]
    ring
  rw [hfun, integral_add hf hg]
  exact abs_add_le _ _

/-- The strong `(p,p)` integral estimate from the two endpoint estimates. -/
theorem rieszSecond_strong_type_of_inputs
    {T : (Vec3 → ℝ) → (Vec3 → ℝ)} {A₁ A₂ p : ℝ}
    (hTsub : ∀ f g (x : Vec3), |T (f + g) x| ≤ |T f x| + |T g x|)
    (hTmeas : ∀ f, Measurable f → Measurable (T f))
    (hWeak11 : ∀ f, Measurable f → ∀ l : ℝ, 0 < l →
      volume {x | l < |T f x|} ≤
        ENNReal.ofReal A₁ * (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hL2 : ∀ f, Measurable f →
      ∫⁻ x, absE (T f) x ^ 2 ≤
        ENNReal.ofReal (A₂ ^ 2) * ∫⁻ x, absE f x ^ 2)
    (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (hp2 : p < 2)
    {g : Vec3 → ℝ} (hg : Measurable g) :
    ∫⁻ x, absE (T g) x ^ p ≤
      ENNReal.ofReal (rieszSecondInterpolationConstant A₁ A₂ p) *
        ∫⁻ x, absE g x ^ p := by
  simpa only [rieszSecondInterpolationConstant] using
    (interpolation_weak11_strong22 hTsub hTmeas hWeak11 hL2 hA₁ hp1 hp2 hg)

/- The power estimate is converted to the extended-valued Lp seminorm in a
   separate helper so the endpoint assembly above stays in the form used by
   the interpolation theorem. -/
private theorem eLpNorm_bound_of_absE_power_bound
    {T : (Vec3 → ℝ) → (Vec3 → ℝ)} {C p : ℝ}
    (hTmeas : ∀ f, Measurable f → Measurable (T f))
    (hp : 0 < p) {g : Vec3 → ℝ} (hg : Measurable g)
    (hbound : ∫⁻ x, absE (T g) x ^ p ≤
      ENNReal.ofReal C * ∫⁻ x, absE g x ^ p) :
    eLpNorm (T g) (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal C) ^ (1 / p) *
        eLpNorm g (ENNReal.ofReal p) volume := by
  have hTg : Measurable (T g) := hTmeas g hg
  have hTga : AEStronglyMeasurable (T g) volume := hTg.aestronglyMeasurable
  have hga : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_eLpNorm' hpne hptop hTga,
    eLpNorm_eq_eLpNorm' hpne hptop hga]
  have hpow : eLpNorm' (T g) p volume ^ p ≤
      ENNReal.ofReal C * eLpNorm' g p volume ^ p := by
    rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp,
      ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp]
    simpa only [absE, Real.enorm_eq_ofReal_abs] using hbound
  have hnorm : eLpNorm' (T g) p volume ≤
      (ENNReal.ofReal C) ^ (1 / p) * eLpNorm' g p volume := by
    calc
      eLpNorm' (T g) p volume =
          (eLpNorm' (T g) p volume ^ p) ^ (1 / p) := by
        rw [← ENNReal.rpow_mul]
        field_simp
        simp
      _ ≤ (ENNReal.ofReal C * eLpNorm' g p volume ^ p) ^ (1 / p) := by
        exact ENNReal.rpow_le_rpow hpow (by positivity)
      _ = (ENNReal.ofReal C) ^ (1 / p) * eLpNorm' g p volume := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
        field_simp
        simp
  simpa only [ENNReal.toReal_ofReal hp.le] using hnorm

/-- The strong Lp seminorm estimate assembled from the two endpoint inputs. -/
theorem rieszSecond_eLpNorm_bound_of_inputs
    {T : (Vec3 → ℝ) → (Vec3 → ℝ)} {A₁ A₂ p : ℝ}
    (hTsub : ∀ f g (x : Vec3), |T (f + g) x| ≤ |T f x| + |T g x|)
    (hTmeas : ∀ f, Measurable f → Measurable (T f))
    (hWeak11 : ∀ f, Measurable f → ∀ l : ℝ, 0 < l →
      volume {x | l < |T f x|} ≤
        ENNReal.ofReal A₁ * (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hL2 : ∀ f, Measurable f →
      ∫⁻ x, absE (T f) x ^ 2 ≤
        ENNReal.ofReal (A₂ ^ 2) * ∫⁻ x, absE f x ^ 2)
    (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (hp2 : p < 2)
    {g : Vec3 → ℝ} (hg : Measurable g) :
    eLpNorm (T g) (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal (rieszSecondInterpolationConstant A₁ A₂ p)) ^ (1 / p) *
        eLpNorm g (ENNReal.ofReal p) volume := by
  apply eLpNorm_bound_of_absE_power_bound hTmeas (lt_trans zero_lt_one hp1) hg
  exact rieszSecond_strong_type_of_inputs hTsub hTmeas hWeak11 hL2 hA₁ hp1 hp2 hg

/-- The integral estimate at exponent `3 / 2`. -/
theorem rieszSecond_strong_type_threeHalves
    {T : (Vec3 → ℝ) → (Vec3 → ℝ)} {A₁ A₂ : ℝ}
    (hTsub : ∀ f g (x : Vec3), |T (f + g) x| ≤ |T f x| + |T g x|)
    (hTmeas : ∀ f, Measurable f → Measurable (T f))
    (hWeak11 : ∀ f, Measurable f → ∀ l : ℝ, 0 < l →
      volume {x | l < |T f x|} ≤
        ENNReal.ofReal A₁ * (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hL2 : ∀ f, Measurable f →
      ∫⁻ x, absE (T f) x ^ 2 ≤
        ENNReal.ofReal (A₂ ^ 2) * ∫⁻ x, absE f x ^ 2)
    (hA₁ : 0 ≤ A₁) {g : Vec3 → ℝ} (hg : Measurable g) :
    ∫⁻ x, absE (T g) x ^ ((3 : ℝ) / 2) ≤
      ENNReal.ofReal (rieszSecondInterpolationConstant A₁ A₂ ((3 : ℝ) / 2)) *
        ∫⁻ x, absE g x ^ ((3 : ℝ) / 2) := by
  exact rieszSecond_strong_type_of_inputs hTsub hTmeas hWeak11 hL2 hA₁
    (by norm_num) (by norm_num) hg

/-- The integral estimate at exponent `6 / 5`. -/
theorem rieszSecond_strong_type_sixFifths
    {T : (Vec3 → ℝ) → (Vec3 → ℝ)} {A₁ A₂ : ℝ}
    (hTsub : ∀ f g (x : Vec3), |T (f + g) x| ≤ |T f x| + |T g x|)
    (hTmeas : ∀ f, Measurable f → Measurable (T f))
    (hWeak11 : ∀ f, Measurable f → ∀ l : ℝ, 0 < l →
      volume {x | l < |T f x|} ≤
        ENNReal.ofReal A₁ * (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hL2 : ∀ f, Measurable f →
      ∫⁻ x, absE (T f) x ^ 2 ≤
        ENNReal.ofReal (A₂ ^ 2) * ∫⁻ x, absE f x ^ 2)
    (hA₁ : 0 ≤ A₁) {g : Vec3 → ℝ} (hg : Measurable g) :
    ∫⁻ x, absE (T g) x ^ ((6 : ℝ) / 5) ≤
      ENNReal.ofReal (rieszSecondInterpolationConstant A₁ A₂ ((6 : ℝ) / 5)) *
        ∫⁻ x, absE g x ^ ((6 : ℝ) / 5) := by
  exact rieszSecond_strong_type_of_inputs hTsub hTmeas hWeak11 hL2 hA₁
    (by norm_num) (by norm_num) hg

end CKN.Foundation.Euclidean
