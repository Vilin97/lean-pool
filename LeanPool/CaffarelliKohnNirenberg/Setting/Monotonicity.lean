/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.Alpha
public import LeanPool.CaffarelliKohnNirenberg.Statements.Beta
public import LeanPool.CaffarelliKohnNirenberg.Statements.Gamma
public import LeanPool.CaffarelliKohnNirenberg.Statements.Delta
public import LeanPool.CaffarelliKohnNirenberg.Statements.Lambda
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Scaling

/-!
# Monotonicity of the scale quantities in the radius

This module formalizes Lemma `lem:monotonicity` of `paper/ckn.tex`.  For a fixed
centre `z` and radii `0 < r₁ ≤ r₂`, the five quantities `alpha`, `beta`, `gamma`,
`delta` and `lambda` of `paper/ckn.tex` grow at most like the powers of `r₂ / r₁`
printed in the lemma.  The paper's statement of the fourth inequality is the
squared form `δ(z,r₁)² ≤ (r₂/r₁)^{4/3} δ(z,r₂)²`; the companion Remark
`rem:kukavica-monotonicity` also records the equivalent unsquared form with the
exponent `2/3`.  The theorem `delta_sq_mono_radius` below proves the squared
form used by the iteration estimates.

Each inequality has two ingredients.  Enlarging the cylinder (or the time-slice
domain) makes the underlying nonnegative integral, respectively time-slice
essential supremum, monotone; this is supplied by the radius-monotonicity
lemmas of the parabolic integration library.  The remaining step is elementary
real algebra with `Real.rpow`, isolated below as lemmas over abstract reals so
that the `rpow` atoms stay opaque.

The definitions evaluate the underlying nonnegative integral with
`ENNReal.toReal`, which sends `⊤` to `0`.  The paper's inequalities therefore
require the relevant quantity at the larger radius to be finite: this is the
`hfin` hypothesis below, and it holds for the suitable weak solutions considered
in `paper/ckn.tex`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal


noncomputable section

namespace CKN

open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

/-- If `0 < r₁ ≤ r₂`, the ratio `(r₂/r₁)^k` converts the weight `r₁^{-k}` into
the weight `r₂^{-k}`. -/
private lemma rpow_ratio_mul {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (k : ℝ) :
    (r₂ / r₁) ^ k * r₂ ^ (-k) = r₁ ^ (-k) := by
  calc
    (r₂ / r₁) ^ k * r₂ ^ (-k) = (r₂ ^ k / r₁ ^ k) * r₂ ^ (-k) := by
      rw [Real.div_rpow hr₂.le hr₁.le]
    _ = (r₂ ^ k * r₂ ^ (-k)) / r₁ ^ k := by ring
    _ = r₂ ^ (k + (-k)) / r₁ ^ k := by rw [Real.rpow_add hr₂]
    _ = 1 / r₁ ^ k := by simp
    _ = r₁ ^ (-k) := by rw [Real.rpow_neg hr₁.le]; ring

/-- The abstract real-algebra step behind `alpha`, `beta`, `gamma` and `delta`:
an integral that is monotone in the radius, carrying the weight `r^{-k}` and
raised to a nonnegative power `e`, gains exactly the prefactor `(r₂/r₁)^{k e}`. -/
private lemma rpow_mono_div_radius_factor {r₁ r₂ I₁ I₂ : ℝ} {k e : ℝ}
    (hr₁ : 0 < r₁) (hrr : r₁ ≤ r₂) (hI₁ : 0 ≤ I₁) (hI : I₁ ≤ I₂) (he : 0 ≤ e) :
    (r₁ ^ (-k) * I₁) ^ e ≤ (r₂ / r₁) ^ (k * e) * (r₂ ^ (-k) * I₂) ^ e := by
  have hr₂ : 0 < r₂ := lt_of_lt_of_le hr₁ hrr
  have hI₂ : 0 ≤ I₂ := hI₁.trans hI
  have hr₁k : 0 ≤ r₁ ^ (-k) := Real.rpow_nonneg hr₁.le _
  have hr₂k : 0 ≤ r₂ ^ (-k) := Real.rpow_nonneg hr₂.le _
  have hratio : 0 ≤ r₂ / r₁ := (div_pos hr₂ hr₁).le
  have h1 : (r₁ ^ (-k) * I₁) ^ e ≤ (r₁ ^ (-k) * I₂) ^ e :=
    Real.rpow_le_rpow (mul_nonneg hr₁k hI₁) (mul_le_mul_of_nonneg_left hI hr₁k) he
  have hkey : r₁ ^ (-k) = (r₂ / r₁) ^ k * r₂ ^ (-k) :=
    (rpow_ratio_mul hr₁ hr₂ k).symm
  calc
    (r₁ ^ (-k) * I₁) ^ e ≤ (r₁ ^ (-k) * I₂) ^ e := h1
    _ = (((r₂ / r₁) ^ k * r₂ ^ (-k)) * I₂) ^ e := by rw [hkey]
    _ = ((r₂ / r₁) ^ k * (r₂ ^ (-k) * I₂)) ^ e := by rw [mul_assoc]
    _ = ((r₂ / r₁) ^ k) ^ e * (r₂ ^ (-k) * I₂) ^ e :=
      Real.mul_rpow (Real.rpow_nonneg hratio k) (mul_nonneg hr₂k hI₂)
    _ = (r₂ / r₁) ^ (k * e) * (r₂ ^ (-k) * I₂) ^ e := by
      rw [← Real.rpow_mul hratio k e]

/-- The abstract real-algebra step behind `lambda`: an `L^q` integral that is
monotone in the radius, weighted by `r^σ` and raised to the power `1/q` with
`q > 0`, gains the prefactor `(r₁/r₂)^σ`. -/
private lemma lambda_factor {r₁ r₂ A₁ A₂ σ q : ℝ} (hr₁ : 0 < r₁) (hrr : r₁ ≤ r₂)
    (hA₁ : 0 ≤ A₁) (hA : A₁ ≤ A₂) (hq : 0 < q) :
    r₁ ^ σ * A₁ ^ (1 / q) ≤ (r₁ / r₂) ^ σ * (r₂ ^ σ * A₂ ^ (1 / q)) := by
  have hr₂ : 0 < r₂ := lt_of_lt_of_le hr₁ hrr
  have h1 : A₁ ^ (1 / q) ≤ A₂ ^ (1 / q) :=
    Real.rpow_le_rpow hA₁ hA (by positivity)
  have h2 : r₂ ^ σ * A₁ ^ (1 / q) ≤ r₂ ^ σ * A₂ ^ (1 / q) :=
    mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hr₂.le σ)
  have hratio : 0 ≤ r₁ / r₂ := (div_pos hr₁ hr₂).le
  have h3 : (r₁ / r₂) ^ σ * (r₂ ^ σ * A₁ ^ (1 / q)) = r₁ ^ σ * A₁ ^ (1 / q) := by
    rw [← mul_assoc, ← Real.mul_rpow hratio hr₂.le, div_mul_cancel₀ _ hr₂.ne']
  calc
    r₁ ^ σ * A₁ ^ (1 / q) = (r₁ / r₂) ^ σ * (r₂ ^ σ * A₁ ^ (1 / q)) := h3.symm
    _ ≤ (r₁ / r₂) ^ σ * (r₂ ^ σ * A₂ ^ (1 / q)) :=
      mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hratio σ)

/-- Lemma `lem:monotonicity` of `paper/ckn.tex` for the velocity energy `alpha`:
`α(z,r₁) ≤ (r₂/r₁)^{1/2} α(z,r₂)`.  The hypothesis `hfin` records that the
time-slice energy at the larger radius is finite, as it is for the suitable weak
solutions of the paper. -/
theorem alpha_mono_radius (u : ParabolicPoint → Vec3) (z : ParabolicPoint)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hrr : r₁ ≤ r₂)
    (hfin : timeSliceEnergyEssSup z.1 z.2 r₂ (fun w => vec3EuclideanNorm (u w)) ≠ ⊤) :
    alpha u z r₁ ≤ (r₂ / r₁) ^ (1 / 2 : ℝ) * alpha u z r₂ := by
  have hE : timeSliceEnergyEssSup z.1 z.2 r₁ (fun w => vec3EuclideanNorm (u w)) ≤
      timeSliceEnergyEssSup z.1 z.2 r₂ (fun w => vec3EuclideanNorm (u w)) :=
    timeSliceEnergyEssSup_mono_radius hr₁.le hrr _
  have hA : (timeSliceEnergyEssSup z.1 z.2 r₁ (fun w => vec3EuclideanNorm (u w))).toReal ≤
      (timeSliceEnergyEssSup z.1 z.2 r₂ (fun w => vec3EuclideanNorm (u w))).toReal :=
    ENNReal.toReal_mono hfin hE
  have h := rpow_mono_div_radius_factor (k := (1 : ℝ)) (e := (1 / 2 : ℝ))
    hr₁ hrr ENNReal.toReal_nonneg hA (by norm_num)
  simpa [alpha, Real.rpow_neg_one] using h

/-- Lemma `lem:monotonicity` of `paper/ckn.tex` for the gradient quantity `beta`:
`β(z,r₁) ≤ (r₂/r₁)^{1/2} β(z,r₂)`. -/
theorem beta_mono_radius (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hrr : r₁ ≤ r₂)
    (hfin : (∫⁻ w in parabolicCylinder z.1 z.2 r₂,
        ENNReal.ofReal (spatialGradientSq u Du w)) ≠ ⊤) :
    beta u Du z r₁ ≤ (r₂ / r₁) ^ (1 / 2 : ℝ) * beta u Du z r₂ := by
  have hI : (∫⁻ w in parabolicCylinder z.1 z.2 r₁,
        ENNReal.ofReal (spatialGradientSq u Du w)) ≤
      (∫⁻ w in parabolicCylinder z.1 z.2 r₂,
        ENNReal.ofReal (spatialGradientSq u Du w)) :=
    lintegral_mono_set (parabolicCylinder_mono hr₁.le hrr)
  have hA := ENNReal.toReal_mono hfin hI
  have h := rpow_mono_div_radius_factor (k := (1 : ℝ)) (e := (1 / 2 : ℝ))
    hr₁ hrr ENNReal.toReal_nonneg hA (by norm_num)
  simpa [beta, Real.rpow_neg_one] using h

/-- Lemma `lem:monotonicity` of `paper/ckn.tex` for the velocity cubic quantity
`gamma`: `γ(z,r₁) ≤ (r₂/r₁)^{2/3} γ(z,r₂)`. -/
theorem gamma_mono_radius (u : ParabolicPoint → Vec3) (z : ParabolicPoint)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hrr : r₁ ≤ r₂)
    (hfin : (∫⁻ w in parabolicCylinder z.1 z.2 r₂,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ⊤) :
    gamma u z r₁ ≤ (r₂ / r₁) ^ (2 / 3 : ℝ) * gamma u z r₂ := by
  have hI : (∫⁻ w in parabolicCylinder z.1 z.2 r₁,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≤
      (∫⁻ w in parabolicCylinder z.1 z.2 r₂,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) :=
    lintegral_mono_set (parabolicCylinder_mono hr₁.le hrr)
  have hA := ENNReal.toReal_mono hfin hI
  have h := rpow_mono_div_radius_factor (k := (2 : ℝ)) (e := (1 / 3 : ℝ))
    hr₁ hrr ENNReal.toReal_nonneg hA (by norm_num)
  have he : (2 : ℝ) * (1 / 3) = 2 / 3 := by norm_num
  rw [he] at h
  simpa [gamma] using h

/-- Lemma `lem:monotonicity` of `paper/ckn.tex` for the pressure quantity
`delta`, in the squared form stated in the paper:
`δ(z,r₁)² ≤ (r₂/r₁)^{4/3} δ(z,r₂)²`. -/
theorem delta_sq_mono_radius (p : ParabolicPoint → ℝ) (z : ParabolicPoint)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hrr : r₁ ≤ r₂)
    (hfin : (∫⁻ w in parabolicCylinder z.1 z.2 r₂,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≠ ⊤) :
    delta p z r₁ ^ 2 ≤ (r₂ / r₁) ^ (4 / 3 : ℝ) * delta p z r₂ ^ 2 := by
  have hI : (∫⁻ w in parabolicCylinder z.1 z.2 r₁,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≤
      (∫⁻ w in parabolicCylinder z.1 z.2 r₂,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) :=
    lintegral_mono_set (parabolicCylinder_mono hr₁.le hrr)
  have hA := ENNReal.toReal_mono hfin hI
  have h := rpow_mono_div_radius_factor (k := (2 : ℝ)) (e := (2 / 3 : ℝ))
    hr₁ hrr ENNReal.toReal_nonneg hA (by norm_num)
  have he : (2 : ℝ) * (2 / 3) = 4 / 3 := by norm_num
  rw [he] at h
  have hX₁ : 0 ≤ r₁ ^ (-2 : ℝ) *
      (∫⁻ w in parabolicCylinder z.1 z.2 r₁, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal :=
    mul_nonneg (Real.rpow_nonneg hr₁.le _) ENNReal.toReal_nonneg
  have hX₂ : 0 ≤ r₂ ^ (-2 : ℝ) *
      (∫⁻ w in parabolicCylinder z.1 z.2 r₂, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal :=
    mul_nonneg (Real.rpow_nonneg (lt_of_lt_of_le hr₁ hrr).le _) ENNReal.toReal_nonneg
  have hsq₁ : delta p z r₁ ^ 2 =
      (r₁ ^ (-2 : ℝ) *
        (∫⁻ w in parabolicCylinder z.1 z.2 r₁,
          ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal) ^ (2 / 3 : ℝ) := by
    rw [delta, ← Real.rpow_natCast, ← Real.rpow_mul hX₁]
    norm_num
  have hsq₂ : delta p z r₂ ^ 2 =
      (r₂ ^ (-2 : ℝ) *
        (∫⁻ w in parabolicCylinder z.1 z.2 r₂,
          ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal) ^ (2 / 3 : ℝ) := by
    rw [delta, ← Real.rpow_natCast, ← Real.rpow_mul hX₂]
    norm_num
  rw [hsq₁, hsq₂]
  exact h

/-- Lemma `lem:monotonicity` of `paper/ckn.tex` for the force quantity `lambda`:
for `q > 0`, `λ(z,r₁) ≤ (r₁/r₂)^{3-5/q} λ(z,r₂)`.  Here `3 - 5/q` is the
exponent `σ` appearing in the paper. -/
theorem lambda_mono_radius (q : ℝ) (f : ParabolicPoint → Vec3) (z : ParabolicPoint)
    {r₁ r₂ : ℝ} (hq : 0 < q) (hr₁ : 0 < r₁) (hrr : r₁ ≤ r₂)
    (hfin : (∫⁻ w in parabolicCylinder z.1 z.2 r₂,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≠ ⊤) :
    lambda q f z r₁ ≤ (r₁ / r₂) ^ (3 - 5 / q) * lambda q f z r₂ := by
  have hI : (∫⁻ w in parabolicCylinder z.1 z.2 r₁,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤
      (∫⁻ w in parabolicCylinder z.1 z.2 r₂,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) :=
    lintegral_mono_set (parabolicCylinder_mono hr₁.le hrr)
  have hA := ENNReal.toReal_mono hfin hI
  have h := lambda_factor (σ := 3 - 5 / q) hr₁ hrr ENNReal.toReal_nonneg hA hq
  simpa [lambda, mul_assoc] using h

end CKN
