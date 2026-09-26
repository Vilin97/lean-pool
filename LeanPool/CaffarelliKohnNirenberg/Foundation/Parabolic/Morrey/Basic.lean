/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Scaling
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Doubling
public import Mathlib.Analysis.Normed.Group.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Parabolic Morrey cells and norms

This module records the extended-real Morrey seminorm on the backward
parabolic cylinders already defined by the parabolic geometry module.  The
metric-ball version is kept alongside it; the two versions are compared by
the inclusions between cylinders and metric balls.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology


noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- Homogeneous dimension of three-dimensional parabolic space-time. -/
abbrev Q := (5 : ℝ)

/-- The integral part of a Morrey cell on a parabolic cylinder. -/
@[expose]
def cylinderPowerIntegral (p : ℝ) (f : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal |f w| ^ p

/-- The integral part of a Morrey cell on a metric ball. -/
@[expose]
def ballPowerIntegral (p : ℝ) (f : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ w in Metric.ball z r, ENNReal.ofReal |f w| ^ p

/-- The Morrey cell attached to a positive-radius cylinder. -/
@[expose]
def morreyCell (p q : ℝ) (f : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal r) ^ (-(Q * (1 - p / q) / p)) *
    (cylinderPowerIntegral p f z r) ^ (1 / p)

/-! The fixed homogeneous dimension in the cylinder normalization. -/
theorem morreyCell_eq (p q : ℝ) (f : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) :
    morreyCell p q f z r =
      (ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
        (cylinderPowerIntegral p f z r) ^ (1 / p) := by
  rfl

/-- The Morrey cell attached to a positive-radius metric ball. -/
@[expose]
def morreyBallCell (p q : ℝ) (f : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal r) ^ (-(Q * (1 - p / q) / p)) *
    (ballPowerIntegral p f z r) ^ (1 / p)

/-- The parabolic Morrey seminorm, with homogeneous dimension `Q = 5`. -/
@[expose]
def morreyNorm (p q : ℝ) (f : ParabolicPoint → ℝ) : ℝ≥0∞ :=
  ⨆ z : ParabolicPoint, ⨆ r : {r : ℝ // 0 < r}, morreyCell p q f z r.1

/-- The metric-ball version of the parabolic Morrey seminorm. -/
@[expose]
def morreyBallNorm (p q : ℝ) (f : ParabolicPoint → ℝ) : ℝ≥0∞ :=
  ⨆ z : ParabolicPoint, ⨆ r : {r : ℝ // 0 < r}, morreyBallCell p q f z r.1

/-- The pointwise truncation used in the monotonicity statements. -/
def truncate (A : ℝ) (f : ParabolicPoint → ℝ) : ParabolicPoint → ℝ :=
  fun z => max (-A) (min A (f z))

private lemma holder_exponents {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    (q / p).HolderConjugate (q / (q - p)) := by
  apply Real.holderConjugate_iff.mpr
  constructor
  · exact (one_lt_div hp).mpr hpq
  · have hq : q ≠ 0 := (lt_of_lt_of_le hp hpq.le).ne'
    field_simp [hp.ne', hq, sub_ne_zero.mpr hpq.ne']
    ring

private lemma cylinderPowerIntegral_holder {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    {f : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    (z : ParabolicPoint) (r : ℝ) :
    cylinderPowerIntegral p f z r ≤
      (cylinderPowerIntegral q f z r) ^ (p / q) *
        (volume (parabolicCylinder z.1 z.2 r)) ^ (1 - p / q) := by
  let μ : Measure ParabolicPoint := volume.restrict (parabolicCylinder z.1 z.2 r)
  let F : ParabolicPoint → ℝ≥0∞ := fun w => ENNReal.ofReal |f w|
  have hF : AEMeasurable F μ := by
    simpa only [F, Real.norm_eq_abs] using hf.norm.restrict.ennreal_ofReal
  have hone : AEMeasurable (fun _ : ParabolicPoint => (1 : ℝ≥0∞)) μ := aemeasurable_const
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (holder_exponents hp hpq)
    (hF.pow_const p) hone
  have hpqpow : ∀ w, (F w ^ p) ^ (q / p) = F w ^ q := by
    intro w
    rw [← ENNReal.rpow_mul]
    field_simp [hp.ne']
  have hleft : (∫⁻ w, F w ^ p ∂μ) = cylinderPowerIntegral p f z r := by
    simp only [μ, F, cylinderPowerIntegral]
  have hq : (∫⁻ w, F w ^ q ∂μ) = cylinderPowerIntegral q f z r := by
    rfl
  have hq' : (∫⁻ w, (F w ^ p) ^ (q / p) ∂μ) =
      cylinderPowerIntegral q f z r := by
    calc
      _ = ∫⁻ w, F w ^ q ∂μ := by
        apply lintegral_congr
        exact hpqpow
      _ = _ := hq
  have honeint : (∫⁻ _w, (1 : ℝ≥0∞) ^ (q / (q - p)) ∂μ) =
      volume (parabolicCylinder z.1 z.2 r) := by
    simp [μ]
  simp only [Pi.mul_apply, mul_one] at hH
  rw [hleft, hq', honeint] at hH
  have hq0 : q ≠ 0 := (lt_of_lt_of_le hp hpq.le).ne'
  have h_exp1 : 1 / (q / p) = p / q := by
    field_simp [hp.ne', hq0]
  have h_exp2 : 1 / (q / (q - p)) = 1 - p / q := by
    field_simp [hq0, sub_ne_zero.mpr hpq.ne']
  rw [h_exp1, h_exp2] at hH
  exact hH

private lemma morreyCell_le_globalLpNorm {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    {f : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    morreyCell p q f z r ≤
      (volume (parabolicCylinder 0 0 1)) ^ (1 / p - 1 / q) *
        eLpNorm' f q volume := by
  let V : ℝ≥0∞ := volume (parabolicCylinder z.1 z.2 r)
  let V₁ : ℝ≥0∞ := volume (parabolicCylinder 0 0 1)
  let G : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal |f w| ^ q
  have hlocal := cylinderPowerIntegral_holder hp hpq hf z r
  have hglobal : cylinderPowerIntegral q f z r ≤ G := by
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  have hroot : (cylinderPowerIntegral p f z r) ^ (1 / p) ≤
      G ^ (1 / q) * V ^ (1 / p - 1 / q) := by
    have hlocal' := ENNReal.rpow_le_rpow hlocal (one_div_nonneg.mpr hp.le)
    have hglobal' := ENNReal.rpow_le_rpow hglobal
      (one_div_nonneg.mpr (lt_of_lt_of_le hp hpq.le).le)
    calc
      (cylinderPowerIntegral p f z r) ^ (1 / p) ≤
          ((cylinderPowerIntegral q f z r) ^ (p / q) *
            V ^ (1 - p / q)) ^ (1 / p) := hlocal'
      _ = (cylinderPowerIntegral q f z r) ^ (1 / q) *
          V ^ (1 / p - 1 / q) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        congr 1
        · field_simp [hp.ne', (lt_of_lt_of_le hp hpq.le).ne']
        · field_simp [hp.ne', (lt_of_lt_of_le hp hpq.le).ne']
      _ ≤ G ^ (1 / q) * V ^ (1 / p - 1 / q) := by
        simpa [mul_comm] using
          (mul_le_mul_left hglobal' (V ^ (1 / p - 1 / q)))
  have hV : V = V₁ * (ENNReal.ofReal r) ^ (5 : ℝ) := by
    dsimp [V, V₁]
    have ht := Integration.volume_parabolicCylinder_translate
      z.1 (0 : Vec3) z.2 0 r
    have hs := volume_parabolicCylinder_radius_scale
      (x := (0 : Vec3)) (t := 0) (r := 1) (a := r) hr
    have ht' : volume (parabolicCylinder z.1 z.2 r) =
        volume (parabolicCylinder 0 0 r) := by
      simpa using ht
    have hs' : volume (parabolicCylinder 0 0 r) =
        ENNReal.ofReal (r ^ 5) * volume (parabolicCylinder 0 0 1) := by
      calc
        volume (parabolicCylinder 0 0 r) =
            volume (parabolicCylinder 0 0 (r * 1)) := by rw [mul_one]
        _ = _ := hs
    calc
      volume (parabolicCylinder z.1 z.2 r) =
          volume (parabolicCylinder 0 0 r) := ht'
      _ = ENNReal.ofReal (r ^ 5) * V₁ := hs'
      _ = V₁ * (ENNReal.ofReal r) ^ (5 : ℝ) := by
        rw [ENNReal.ofReal_pow hr.le, ← ENNReal.rpow_natCast]
        ac_rfl
  have hrpow : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hrpowtop : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  have hd : 0 ≤ 1 / p - 1 / q := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hp hpq.le)
  have hVpow : (ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
      V ^ (1 / p - 1 / q) = V₁ ^ (1 / p - 1 / q) := by
    rw [hV, ENNReal.mul_rpow_of_nonneg _ _ hd, ← ENNReal.rpow_mul]
    let e : ℝ := -(5 * (1 - p / q) / p)
    let d : ℝ := 1 / p - 1 / q
    have hed : e + 5 * d = 0 := by
      dsimp [e, d]
      field_simp [hp.ne', (lt_of_lt_of_le hp hpq.le).ne']
      ring
    calc
      (ENNReal.ofReal r) ^ e * (V₁ ^ d * (ENNReal.ofReal r) ^ (5 * d)) =
          ((ENNReal.ofReal r) ^ e * (ENNReal.ofReal r) ^ (5 * d)) * V₁ ^ d := by
            ac_rfl
      _ = (ENNReal.ofReal r) ^ (e + 5 * d) * V₁ ^ d := by
            exact congrArg (fun x => x * V₁ ^ d)
              (ENNReal.rpow_add e (5 * d) hrpow hrpowtop).symm
      _ = V₁ ^ d := by rw [hed, ENNReal.rpow_zero, one_mul]
  unfold morreyCell
  calc
    (ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
        (cylinderPowerIntegral p f z r) ^ (1 / p) ≤
      (ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
        (G ^ (1 / q) * V ^ (1 / p - 1 / q)) :=
      mul_le_mul_right hroot _
    _ = V₁ ^ (1 / p - 1 / q) * G ^ (1 / q) := by
      calc
        _ = ((ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
          V ^ (1 / p - 1 / q)) * G ^ (1 / q) := by ac_rfl
        _ = _ := by rw [hVpow]
    _ = V₁ ^ (1 / p - 1 / q) * eLpNorm' f q volume := by
      change V₁ ^ (1 / p - 1 / q) *
          (∫⁻ w, ENNReal.ofReal |f w| ^ q) ^ (1 / q) = _
      simp only [eLpNorm', Real.enorm_eq_ofReal_abs]

theorem morreyNorm_le_eLpNorm' {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q)
    {f : ParabolicPoint → ℝ} (hf : AEMeasurable f volume) :
    morreyNorm p q f ≤
      (volume (parabolicCylinder 0 0 1)) ^ (1 / p - 1 / q) *
        eLpNorm' f q volume := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  unfold morreyNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  rcases hpq.eq_or_lt with rfl | hpq
  · have hglobal : cylinderPowerIntegral p f z r.1 ≤
        ∫⁻ w, ENNReal.ofReal |f w| ^ p :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    have hroot := ENNReal.rpow_le_rpow hglobal (one_div_nonneg.mpr hp0.le)
    unfold morreyCell
    simp only [sub_self, ENNReal.rpow_zero, one_mul]
    have hexp : -(Q * (1 - p / p) / p) = 0 := by simp [hp0.ne']
    rw [hexp, ENNReal.rpow_zero, one_mul]
    calc
      (cylinderPowerIntegral p f z r.1) ^ (1 / p) ≤
          (∫⁻ w, ENNReal.ofReal |f w| ^ p) ^ (1 / p) := hroot
      _ = eLpNorm' f p volume := by
        simp only [eLpNorm', Real.enorm_eq_ofReal_abs]
  · exact morreyCell_le_globalLpNorm hp0 hpq hf z r.2

private lemma morreyCell_lower_p {p' p q : ℝ} (hp' : 0 < p') (hpp : p' < p)
    {f : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    morreyCell p' q f z r ≤
      (volume (parabolicCylinder 0 0 1)) ^ (1 / p' - 1 / p) *
        morreyCell p q f z r := by
  let V : ℝ≥0∞ := volume (parabolicCylinder z.1 z.2 r)
  let V₁ : ℝ≥0∞ := volume (parabolicCylinder 0 0 1)
  have hlocal := cylinderPowerIntegral_holder hp' hpp hf z r
  have hroot : (cylinderPowerIntegral p' f z r) ^ (1 / p') ≤
      (cylinderPowerIntegral p f z r) ^ (1 / p) *
        V ^ (1 / p' - 1 / p) := by
    have hlocal' := ENNReal.rpow_le_rpow hlocal (one_div_nonneg.mpr hp'.le)
    calc
      (cylinderPowerIntegral p' f z r) ^ (1 / p') ≤
          ((cylinderPowerIntegral p f z r) ^ (p' / p) *
            V ^ (1 - p' / p)) ^ (1 / p') := hlocal'
      _ = (cylinderPowerIntegral p f z r) ^ (1 / p) *
          V ^ (1 / p' - 1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp'.le),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        congr 1
        · field_simp [hp'.ne', (lt_of_lt_of_le hp' hpp.le).ne']
        · field_simp [hp'.ne', (lt_of_lt_of_le hp' hpp.le).ne']
  have hV : V = V₁ * (ENNReal.ofReal r) ^ (5 : ℝ) := by
    dsimp [V, V₁]
    have ht := Integration.volume_parabolicCylinder_translate
      z.1 (0 : Vec3) z.2 0 r
    have hs := volume_parabolicCylinder_radius_scale
      (x := (0 : Vec3)) (t := 0) (r := 1) (a := r) hr
    have ht' : volume (parabolicCylinder z.1 z.2 r) =
        volume (parabolicCylinder 0 0 r) := by
      simpa using ht
    have hs' : volume (parabolicCylinder 0 0 r) =
        ENNReal.ofReal (r ^ 5) * volume (parabolicCylinder 0 0 1) := by
      calc
        volume (parabolicCylinder 0 0 r) =
            volume (parabolicCylinder 0 0 (r * 1)) := by rw [mul_one]
        _ = _ := hs
    calc
      volume (parabolicCylinder z.1 z.2 r) =
          volume (parabolicCylinder 0 0 r) := ht'
      _ = ENNReal.ofReal (r ^ 5) * V₁ := hs'
      _ = V₁ * (ENNReal.ofReal r) ^ (5 : ℝ) := by
        rw [ENNReal.ofReal_pow hr.le, ← ENNReal.rpow_natCast]
        ac_rfl
  have hrpow : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hrpowtop : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  have hd : 0 ≤ 1 / p' - 1 / p := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hp' hpp.le)
  have hfactor : (ENNReal.ofReal r) ^
      (-(5 * (1 - p' / q) / p')) * V ^ (1 / p' - 1 / p) =
      V₁ ^ (1 / p' - 1 / p) *
        (ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) := by
    rw [hV, ENNReal.mul_rpow_of_nonneg _ _ hd, ← ENNReal.rpow_mul]
    let d : ℝ := 1 / p' - 1 / p
    have he : -(5 * (1 - p' / q) / p') + 5 * d =
        -(5 * (1 - p / q) / p) := by
      dsimp [d]
      field_simp [hp'.ne', (lt_of_lt_of_le hp' hpp.le).ne']
      ring
    calc
      (ENNReal.ofReal r) ^ (-(5 * (1 - p' / q) / p')) *
          (V₁ ^ d * (ENNReal.ofReal r) ^ (5 * d)) =
          V₁ ^ d * ((ENNReal.ofReal r) ^
            (-(5 * (1 - p' / q) / p')) *
            (ENNReal.ofReal r) ^ (5 * d)) := by ac_rfl
      _ = V₁ ^ d * (ENNReal.ofReal r) ^
          (-(5 * (1 - p' / q) / p') + 5 * d) := by
        exact congrArg (fun x => V₁ ^ d * x)
          (ENNReal.rpow_add _ _ hrpow hrpowtop).symm
      _ = _ := by rw [he]
  unfold morreyCell
  calc
    (ENNReal.ofReal r) ^ (-(5 * (1 - p' / q) / p')) *
        (cylinderPowerIntegral p' f z r) ^ (1 / p') ≤
      (ENNReal.ofReal r) ^ (-(5 * (1 - p' / q) / p')) *
        ((cylinderPowerIntegral p f z r) ^ (1 / p) *
          V ^ (1 / p' - 1 / p)) := mul_le_mul_right hroot _
    _ = V₁ ^ (1 / p' - 1 / p) *
        ((ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
          (cylinderPowerIntegral p f z r) ^ (1 / p)) := by
      calc
        _ = ((ENNReal.ofReal r) ^ (-(5 * (1 - p' / q) / p')) *
          V ^ (1 / p' - 1 / p)) *
          (cylinderPowerIntegral p f z r) ^ (1 / p) := by ac_rfl
        _ = _ := by rw [hfactor]; ac_rfl

theorem cylinderPowerIntegral_parabolicPullback {a : ℝ} (ha : 0 < a)
    (x : Vec3) (t r p : ℝ) (u : ParabolicPoint → ℝ) (hp : 0 ≤ p)
    (hsource : IntegrableOn
      (fun z => |u (parabolicTranslate x t (parabolicScale a z))| ^ p)
      (parabolicCylinder 0 0 r) volume)
    (htarget : IntegrableOn (fun z => |u z| ^ p)
      (parabolicCylinder x t (a * r)) volume) :
    cylinderPowerIntegral p
        (fun z => u (parabolicTranslate x t (parabolicScale a z)))
        ((0 : Vec3), 0) r =
      (ENNReal.ofReal a) ^ (-5 : ℝ) *
        cylinderPowerIntegral p u (x, t) (a * r) := by
  have hbase := Integration.cylinder_setIntegral_comp_parabolicRescale ha x t r
    (fun z => |u z| ^ p) hsource htarget
  have hsource' : ENNReal.ofReal
      (∫ z in parabolicCylinder 0 0 r,
        |u (parabolicTranslate x t (parabolicScale a z))| ^ p) =
      cylinderPowerIntegral p
        (fun z => u (parabolicTranslate x t (parabolicScale a z)))
        ((0 : Vec3), 0) r := by
    symm
    calc
      cylinderPowerIntegral p
          (fun z => u (parabolicTranslate x t (parabolicScale a z)))
          ((0 : Vec3), 0) r =
          ∫⁻ z in parabolicCylinder 0 0 r,
            ENNReal.ofReal
              (|u (parabolicTranslate x t (parabolicScale a z))| ^ p) := by
        unfold cylinderPowerIntegral
        apply lintegral_congr
        intro z
        exact ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp
      _ = ENNReal.ofReal
          (∫ z in parabolicCylinder 0 0 r,
            |u (parabolicTranslate x t (parabolicScale a z))| ^ p) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hsource
          (Filter.Eventually.of_forall fun z =>
            Real.rpow_nonneg (abs_nonneg _) p)
  have htarget' : ENNReal.ofReal
      (∫ z in parabolicCylinder x t (a * r), |u z| ^ p) =
      cylinderPowerIntegral p u (x, t) (a * r) := by
    symm
    calc
      cylinderPowerIntegral p u (x, t) (a * r) =
          ∫⁻ z in parabolicCylinder x t (a * r),
            ENNReal.ofReal (|u z| ^ p) := by
        unfold cylinderPowerIntegral
        apply lintegral_congr
        intro z
        exact ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp
      _ = ENNReal.ofReal
          (∫ z in parabolicCylinder x t (a * r), |u z| ^ p) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal htarget
          (Filter.Eventually.of_forall fun z =>
            Real.rpow_nonneg (abs_nonneg _) p)
  rw [← hsource', ← htarget', hbase]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ a⁻¹ ^ 5)]
  rw [ENNReal.ofReal_pow (by positivity : 0 ≤ a⁻¹) 5]
  rw [ENNReal.ofReal_inv_of_pos ha, ← ENNReal.inv_pow]
  have hfactor : (ENNReal.ofReal a ^ (5 : ℕ))⁻¹ =
      ENNReal.ofReal a ^ (-5 : ℝ) := by
    calc
      (ENNReal.ofReal a ^ (5 : ℕ))⁻¹ =
          (ENNReal.ofReal a ^ (5 : ℝ))⁻¹ := by
            norm_num [ENNReal.rpow_natCast]
      _ = ENNReal.ofReal a ^ (-5 : ℝ) := (ENNReal.rpow_neg _ _).symm
  rw [hfactor]

theorem cylinderPowerIntegral_translate {x : Vec3} {t r p : ℝ}
    (u : ParabolicPoint → ℝ) (hp : 0 ≤ p)
    (hsource : IntegrableOn
      (fun z => |u (parabolicTranslate x t z)| ^ p)
      (parabolicCylinder 0 0 r) volume)
    (htarget : IntegrableOn (fun z => |u z| ^ p)
      (parabolicCylinder x t r) volume) :
    cylinderPowerIntegral p (fun z => u (parabolicTranslate x t z))
        ((0 : Vec3), 0) r = cylinderPowerIntegral p u (x, t) r := by
  have hsource' : IntegrableOn
      (fun z => |u (parabolicTranslate x t (parabolicScale 1 z))| ^ p)
      (parabolicCylinder 0 0 r) volume := by
    convert hsource using 1
    funext z
    cases z
    simp [parabolicScale]
  have h := cylinderPowerIntegral_parabolicPullback (a := 1) (by norm_num) x t r p u hp
    hsource' (by simpa using htarget)
  convert h using 1
  · congr 1
    funext z
    cases z
    simp [parabolicScale]
  · simp

private lemma product_holder_exponents {p p₁ p₂ : ℝ}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hrel : 1 / p = 1 / p₁ + 1 / p₂) :
    (p₁ / p).HolderConjugate (p₂ / p) := by
  have hp : 0 < p := by
    have hsum : 0 < 1 / p₁ + 1 / p₂ :=
      add_pos (one_div_pos.mpr hp₁) (one_div_pos.mpr hp₂)
    exact one_div_pos.mp (hrel ▸ hsum)
  have hpp₁ : p < p₁ := by
    by_contra h
    have hle : p₁ ≤ p := le_of_not_gt h
    have hle' : 1 / p ≤ 1 / p₁ := one_div_le_one_div_of_le hp₁ hle
    have hlt : 1 / p₁ < 1 / p := by
      rw [hrel]
      exact lt_add_of_pos_right _ (one_div_pos.mpr hp₂)
    exact (not_lt_of_ge hle') hlt
  have hpp₂ : p < p₂ := by
    by_contra h
    have hle : p₂ ≤ p := le_of_not_gt h
    have hle' : 1 / p ≤ 1 / p₂ := one_div_le_one_div_of_le hp₂ hle
    have hlt : 1 / p₂ < 1 / p := by
      rw [hrel, add_comm]
      exact lt_add_of_pos_right _ (one_div_pos.mpr hp₁)
    exact (not_lt_of_ge hle') hlt
  apply Real.holderConjugate_iff.mpr
  constructor
  · exact (one_lt_div hp).mpr hpp₁
  · calc
      (p₁ / p)⁻¹ + (p₂ / p)⁻¹ = p / p₁ + p / p₂ := by
        field_simp [hp.ne', hp₁.ne', hp₂.ne']
      _ = p * (1 / p₁ + 1 / p₂) := by ring
      _ = 1 := by rw [← hrel]; field_simp [hp.ne']

private lemma cylinderPowerIntegral_mul_holder {p p₁ p₂ : ℝ}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hrel : 1 / p = 1 / p₁ + 1 / p₂)
    {f g : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) (z : ParabolicPoint) (r : ℝ) :
    cylinderPowerIntegral p (fun w => f w * g w) z r ≤
      (cylinderPowerIntegral p₁ f z r) ^ (p / p₁) *
        (cylinderPowerIntegral p₂ g z r) ^ (p / p₂) := by
  let μ : Measure ParabolicPoint := volume.restrict (parabolicCylinder z.1 z.2 r)
  let F : ParabolicPoint → ℝ≥0∞ := fun w => ENNReal.ofReal |f w|
  let G : ParabolicPoint → ℝ≥0∞ := fun w => ENNReal.ofReal |g w|
  have hF : AEMeasurable F μ := by
    simpa only [F, Real.norm_eq_abs] using hf.norm.restrict.ennreal_ofReal
  have hG : AEMeasurable G μ := by
    simpa only [G, Real.norm_eq_abs] using hg.norm.restrict.ennreal_ofReal
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (product_holder_exponents hp₁ hp₂ hrel) (hF.pow_const p) (hG.pow_const p)
  have hp : 0 < p := by
    have hsum : 0 < 1 / p₁ + 1 / p₂ :=
      add_pos (one_div_pos.mpr hp₁) (one_div_pos.mpr hp₂)
    exact one_div_pos.mp (hrel ▸ hsum)
  have hprod : ∀ w, (F w ^ p) * (G w ^ p) =
      ENNReal.ofReal |f w * g w| ^ p := by
    intro w
    have hfg : F w * G w = ENNReal.ofReal |f w * g w| := by
      dsimp [F, G]
      rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_mul]
    calc
      F w ^ p * G w ^ p = (F w * G w) ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
      _ = ENNReal.ofReal |f w * g w| ^ p := by rw [hfg]
  have hleft : (∫⁻ w, ENNReal.ofReal |f w * g w| ^ p ∂μ) =
      cylinderPowerIntegral p (fun w => f w * g w) z r := by
    rfl
  have h₁ : (∫⁻ w, (F w ^ p) ^ (p₁ / p) ∂μ) =
      cylinderPowerIntegral p₁ f z r := by
    have hpow : ∀ w, (F w ^ p) ^ (p₁ / p) = F w ^ p₁ := by
      intro w
      rw [← ENNReal.rpow_mul]
      field_simp [hp.ne']
    calc
      _ = ∫⁻ w, F w ^ p₁ ∂μ := by
        apply lintegral_congr
        exact hpow
      _ = _ := by rfl
  have h₂ : (∫⁻ w, (G w ^ p) ^ (p₂ / p) ∂μ) =
      cylinderPowerIntegral p₂ g z r := by
    have hpow : ∀ w, (G w ^ p) ^ (p₂ / p) = G w ^ p₂ := by
      intro w
      rw [← ENNReal.rpow_mul]
      field_simp [hp.ne']
    calc
      _ = ∫⁻ w, G w ^ p₂ ∂μ := by
        apply lintegral_congr
        exact hpow
      _ = _ := by rfl
  simp only [Pi.mul_apply] at hH
  rw [show ∫⁻ w, (F w ^ p) * (G w ^ p) ∂μ =
      ∫⁻ w, ENNReal.ofReal |f w * g w| ^ p ∂μ by
        apply lintegral_congr
        exact hprod, hleft, h₁, h₂] at hH
  have h_exp1 : 1 / (p₁ / p) = p / p₁ := by field_simp [hp.ne', hp₁.ne']
  have h_exp2 : 1 / (p₂ / p) = p / p₂ := by field_simp [hp.ne', hp₂.ne']
  rw [h_exp1, h_exp2] at hH
  exact hH

theorem morreyNorm_mul_le {p p₁ p₂ q q₁ q₂ : ℝ}
    (hp₁ : 1 ≤ p₁) (hp₂ : 1 ≤ p₂)
    (hrelp : 1 / p = 1 / p₁ + 1 / p₂)
    (hrelq : 1 / q = 1 / q₁ + 1 / q₂)
    {f g : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) :
    morreyNorm p q (fun z => f z * g z) ≤
      morreyNorm p₁ q₁ f * morreyNorm p₂ q₂ g := by
  have hp₁0 : 0 < p₁ := lt_of_lt_of_le zero_lt_one hp₁
  have hp₂0 : 0 < p₂ := lt_of_lt_of_le zero_lt_one hp₂
  have hp0 : 0 < p := by
    have hsum : 0 < 1 / p₁ + 1 / p₂ :=
      add_pos (one_div_pos.mpr hp₁0) (one_div_pos.mpr hp₂0)
    exact one_div_pos.mp (hrelp ▸ hsum)
  unfold morreyNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  have hlocal := cylinderPowerIntegral_mul_holder hp₁0 hp₂0 hrelp hf hg z r.1
  have hroot := ENNReal.rpow_le_rpow hlocal (one_div_nonneg.mpr hp0.le)
  have hcell₁ : morreyCell p₁ q₁ f z r.1 ≤ morreyNorm p₁ q₁ f := by
    unfold morreyNorm
    exact le_iSup_of_le z
      (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell p₁ q₁ f z s.1) r)
  have hcell₂ : morreyCell p₂ q₂ g z r.1 ≤ morreyNorm p₂ q₂ g := by
    unfold morreyNorm
    exact le_iSup_of_le z
      (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell p₂ q₂ g z s.1) r)
  unfold morreyCell at hcell₁ hcell₂ ⊢
  calc
    (ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
        (cylinderPowerIntegral p (fun w => f w * g w) z r.1) ^ (1 / p) ≤
      (ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
        ((cylinderPowerIntegral p₁ f z r.1) ^ (p / p₁) *
          (cylinderPowerIntegral p₂ g z r.1) ^ (p / p₂)) ^ (1 / p) :=
      mul_le_mul_right hroot _
    _ = ((ENNReal.ofReal r) ^ (-(5 * (1 - p₁ / q₁) / p₁)) *
          (cylinderPowerIntegral p₁ f z r.1) ^ (1 / p₁)) *
        ((ENNReal.ofReal r) ^ (-(5 * (1 - p₂ / q₂) / p₂)) *
          (cylinderPowerIntegral p₂ g z r.1) ^ (1 / p₂)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp0.le),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      have hrel : -(5 * (1 - p / q) / p) =
          -(5 * (1 - p₁ / q₁) / p₁) -
            (5 * (1 - p₂ / q₂) / p₂) := by
        calc
          _ = -5 * (1 / p - 1 / q) := by
            field_simp [hp0.ne']
          _ = -5 * ((1 / p₁ + 1 / p₂) - (1 / q₁ + 1 / q₂)) := by
            rw [← hrelp, ← hrelq]
          _ = _ := by
            field_simp [hp0.ne', hp₁0.ne', hp₂0.ne']
            ring
      have h_exp1 : (p / p₁) * (1 / p) = 1 / p₁ := by
        field_simp [hp0.ne', hp₁0.ne']
      have h_exp2 : (p / p₂) * (1 / p) = 1 / p₂ := by
        field_simp [hp0.ne', hp₂0.ne']
      rw [hrel]
      calc
        (ENNReal.ofReal r) ^
              (-(5 * (1 - p₁ / q₁) / p₁) -
                5 * (1 - p₂ / q₂) / p₂) *
            (cylinderPowerIntegral p₁ f z r.1 ^ (p / p₁ * (1 / p)) *
              cylinderPowerIntegral p₂ g z r.1 ^ (p / p₂ * (1 / p))) =
            ((ENNReal.ofReal r) ^ (-(5 * (1 - p₁ / q₁) / p₁)) *
              (ENNReal.ofReal r) ^ (-(5 * (1 - p₂ / q₂) / p₂))) *
              (cylinderPowerIntegral p₁ f z r.1 ^ (p / p₁ * (1 / p)) *
              cylinderPowerIntegral p₂ g z r.1 ^ (p / p₂ * (1 / p))) := by
                have hsum :
                    -(5 * (1 - p₁ / q₁) / p₁) -
                        5 * (1 - p₂ / q₂) / p₂ =
                      -(5 * (1 - p₁ / q₁) / p₁) +
                        (-(5 * (1 - p₂ / q₂) / p₂)) := by ring
                rw [hsum]
                calc
                  _ = ((ENNReal.ofReal r) ^
                      (-(5 * (1 - p₁ / q₁) / p₁)) *
                    (ENNReal.ofReal r) ^
                      (-(5 * (1 - p₂ / q₂) / p₂))) *
                    (cylinderPowerIntegral p₁ f z r.1 ^ (p / p₁ * (1 / p)) *
                      cylinderPowerIntegral p₂ g z r.1 ^ (p / p₂ * (1 / p))) := by
                        rw [ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr r.2).ne'
                          ENNReal.ofReal_ne_top]
                  _ = _ := by ac_rfl
        _ = ((ENNReal.ofReal r) ^ (-(5 * (1 - p₁ / q₁) / p₁)) *
              cylinderPowerIntegral p₁ f z r.1 ^ (1 / p₁)) *
            ((ENNReal.ofReal r) ^ (-(5 * (1 - p₂ / q₂) / p₂)) *
              cylinderPowerIntegral p₂ g z r.1 ^ (1 / p₂)) := by
                rw [h_exp1, h_exp2]
                ac_rfl
    _ ≤ morreyNorm p₁ q₁ f * morreyNorm p₂ q₂ g := by
      exact mul_le_mul hcell₁ hcell₂ (by positivity) (by positivity)

theorem morreyNorm_lower_p {p' p q : ℝ} (hp' : 1 ≤ p') (hpp : p' ≤ p)
    (hpq : p ≤ q) {f : ParabolicPoint → ℝ} (hf : AEMeasurable f volume) :
    morreyNorm p' q f ≤
      (volume (parabolicCylinder 0 0 1)) ^ (1 / p' - 1 / p) *
        morreyNorm p q f := by
  have hp'0 : 0 < p' := lt_of_lt_of_le zero_lt_one hp'
  unfold morreyNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  rcases hpp.eq_or_lt with rfl | hpp
  · simp only [sub_self, ENNReal.rpow_zero, one_mul]
    exact le_iSup_of_le z
      (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell p' q f z s.1) r)
  · exact (morreyCell_lower_p hp'0 hpp hf z r.2).trans
      (mul_le_mul_right (le_iSup_of_le z
        (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell p q f z s.1) r)) _)

theorem cylinderPowerIntegral_mono {p : ℝ} (hp : 0 ≤ p)
    {f g : ParabolicPoint → ℝ} {z : ParabolicPoint} {r : ℝ}
    (hfg : ∀ w ∈ parabolicCylinder z.1 z.2 r, |f w| ≤ |g w|) :
    cylinderPowerIntegral p f z r ≤ cylinderPowerIntegral p g z r := by
  unfold cylinderPowerIntegral
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (by
    exact (vec3Ball_measurable z.1 r).prod measurableSet_Ioc)] with w hw
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hfg w hw)) hp

theorem ballPowerIntegral_mono {p : ℝ} (hp : 0 ≤ p)
    {f g : ParabolicPoint → ℝ} {z : ParabolicPoint} {r : ℝ}
    (hfg : ∀ w ∈ Metric.ball z r, |f w| ≤ |g w|) :
    ballPowerIntegral p f z r ≤ ballPowerIntegral p g z r := by
  unfold ballPowerIntegral
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hfg w hw)) hp

theorem morreyCell_mono {p q : ℝ} (hp : 0 ≤ p)
    {f g : ParabolicPoint → ℝ} {z : ParabolicPoint} {r : ℝ}
    (hfg : ∀ w ∈ parabolicCylinder z.1 z.2 r, |f w| ≤ |g w|) :
    morreyCell p q f z r ≤ morreyCell p q g z r := by
  unfold morreyCell
  exact mul_le_mul_right (ENNReal.rpow_le_rpow
    (cylinderPowerIntegral_mono hp hfg) (by positivity)) _

theorem morreyBallCell_mono {p q : ℝ} (hp : 0 ≤ p)
    {f g : ParabolicPoint → ℝ} {z : ParabolicPoint} {r : ℝ}
    (hfg : ∀ w ∈ Metric.ball z r, |f w| ≤ |g w|) :
    morreyBallCell p q f z r ≤ morreyBallCell p q g z r := by
  unfold morreyBallCell
  exact mul_le_mul_right (ENNReal.rpow_le_rpow
    (ballPowerIntegral_mono hp hfg) (by positivity)) _

/-- Pointwise domination passes to the cylinder Morrey seminorm. -/
theorem morreyNorm_mono {p q : ℝ} (hp : 0 ≤ p)
    {f g : ParabolicPoint → ℝ}
    (hfg : ∀ w, |f w| ≤ |g w|) :
    morreyNorm p q f ≤ morreyNorm p q g := by
  unfold morreyNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  exact (morreyCell_mono hp fun w _ => hfg w).trans
    (le_iSup_of_le z (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell p q g z s.1) r))

/-- Pointwise domination passes to the metric-ball Morrey seminorm. -/
theorem morreyBallNorm_mono {p q : ℝ} (hp : 0 ≤ p)
    {f g : ParabolicPoint → ℝ}
    (hfg : ∀ w, |f w| ≤ |g w|) :
    morreyBallNorm p q f ≤ morreyBallNorm p q g := by
  unfold morreyBallNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  exact (morreyBallCell_mono hp fun w _ => hfg w).trans
    (le_iSup_of_le z (le_iSup (fun s : {s : ℝ // 0 < s} => morreyBallCell p q g z s.1) r))

/-- Indicator truncation cannot increase a Morrey seminorm. -/
theorem morreyNorm_indicator_le {p q : ℝ} (hp : 0 ≤ p)
    (s : Set ParabolicPoint) (f : ParabolicPoint → ℝ) :
    morreyNorm p q (s.indicator f) ≤ morreyNorm p q f := by
  apply morreyNorm_mono hp
  intro w
  simpa only [Real.norm_eq_abs] using (norm_indicator_le_norm_self (s := s) (f := f) w)

/-- A nonnegative truncation cannot increase a Morrey seminorm. -/
theorem morreyNorm_truncate_le {p q : ℝ} (hp : 0 ≤ p)
    {A : ℝ} (hA : 0 ≤ A) (f : ParabolicPoint → ℝ) :
    morreyNorm p q (truncate A f) ≤ morreyNorm p q f := by
  apply morreyNorm_mono hp
  intro w
  unfold truncate
  by_cases hf : 0 ≤ f w
  · have hmin_nonneg : 0 ≤ min A (f w) := le_min hA hf
    rw [abs_of_nonneg hf, abs_of_nonneg (hmin_nonneg.trans (le_max_right _ _))]
    exact max_le (by linarith only [hA, hf]) (min_le_right _ _)
  · have hf' : f w ≤ 0 := le_of_not_ge hf
    have hmin : min A (f w) = f w := min_eq_right (hf'.trans hA)
    rw [hmin]
    apply abs_le.mpr
    constructor
    · simpa only [abs_of_nonpos hf', neg_neg] using le_max_right (-A) (f w)
    · rw [abs_of_nonpos hf']
      exact max_le (by linarith only [hA, hf']) (by linarith only [hf'])

theorem morreyNorm_le_morreyBallNorm {p q : ℝ} (hp : 0 ≤ p) (_ : p ≤ q)
    (f : ParabolicPoint → ℝ) :
    morreyNorm p q f ≤ morreyBallNorm p q f := by
  unfold morreyNorm morreyBallNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  let z' : ParabolicPoint := (z.1, z.2 - r.1 ^ 2 / 2)
  have hsubset : parabolicCylinder z.1 z.2 r.1 ⊆ Metric.ball z' r.1 := by
    simpa [z'] using parabolicCylinder_subset_metricBall r.2
  have hroot :
      (cylinderPowerIntegral p f z r.1) ^ (1 / p) ≤
        (ballPowerIntegral p f z' r.1) ^ (1 / p) := by
    apply ENNReal.rpow_le_rpow
    · exact lintegral_mono_set hsubset
    · exact one_div_nonneg.mpr hp
  unfold morreyCell morreyBallCell
  exact (mul_le_mul_right hroot _).trans
    (le_iSup_of_le z' (le_iSup (fun s : {s : ℝ // 0 < s} =>
      morreyBallCell p q f z' s.1) r))

theorem ballPowerIntegral_le_cylinderPowerIntegral {p : ℝ} (_ : 0 ≤ p)
    {x : Vec3} {t R : ℝ} (hR : 0 < R) (f : ParabolicPoint → ℝ) :
    ballPowerIntegral p f (x, t) R ≤
      cylinderPowerIntegral p f (x, t + 2 * R ^ 2) (2 * R) := by
  have h := metricBall_subset_parabolicCylinder
    (x := x) (t := t + 2 * R ^ 2) (r := 2 * R)
    (by positivity : 0 < 2 * R)
  have hcenter :
      (x, (t + 2 * R ^ 2) - (2 * R) ^ 2 / 2) = (x, t) := by
    congr 1
    ring
  rw [hcenter] at h
  have hsubset : @Metric.ball ParabolicPoint parabolicPseudoMetricSpace (x, t) R ⊆
      parabolicCylinder x (t + 2 * R ^ 2) (2 * R) := by
    have hradius : (2 * R) / 2 = R := by ring
    simpa only [hradius] using h
  unfold ballPowerIntegral cylinderPowerIntegral
  apply lintegral_mono' (Measure.restrict_mono hsubset le_rfl)
  exact le_rfl

end CKN.Foundation.Parabolic.Morrey
