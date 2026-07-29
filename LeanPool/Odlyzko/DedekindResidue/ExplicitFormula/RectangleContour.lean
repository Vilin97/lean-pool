/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib
public import LeanPool.Odlyzko.DedekindResidue.ExplicitFormula.PhiTransform

/-!
# Rectangle contour integrals and the rectangle Cauchy formula  (SP2-RECT R-c)

The explicit-formula contour is Poitou's rectangle `[-a, 1+a] × [-T, T]` (p. 6-01).
Mathlib provides Cauchy–Goursat on rectangles (`integral_boundary_rect_eq_zero_…`) but
no winding/Cauchy *formula*; this file supplies it:

* `rectangleIntegral f z w` — the counterclockwise boundary combination
  bottom − top + i·right − i·left used by mathlib's Goursat theorem;
* `rectangleIntegral_eq_zero` — the Goursat wrapper (countable exceptional set);
* `rectangleIntegral_inv_sub` — the winding integral `∮ (ζ−ρ)⁻¹ dζ = 2πi` for `ρ`
  inside, by explicit `log`-antiderivatives on the four sides (the left side through
  the reflected branch `log(−(ζ−ρ))`) and the jump identities
  `log(−u) = log u ∓ πi` (`log_neg_of_im_pos`/`log_neg_of_im_neg`);
* `rectangleIntegral_cauchy` — the Cauchy formula
  `∮ Φ(ζ)·(ζ−ρ)⁻¹ dζ = 2πi·Φ(ρ)`, by peeling `dslope Φ ρ` (continuous on the closed
  rectangle, differentiable off `ρ` — Goursat kills it) from `Φ(ρ)·(ζ−ρ)⁻¹`.

Route: `.mathlib-quality/decomposition-sp2.md`, leaf SP2-RECT (R-b, R-c).
-/

@[expose] public section

namespace DedekindResidue

open MeasureTheory Complex intervalIntegral

/-- The (counterclockwise) boundary integral over the axis-parallel rectangle with
corners `z` (bottom-left) and `w` (top-right), in the combination used by mathlib's
rectangle Cauchy–Goursat theorem: bottom − top + i·right − i·left. -/
noncomputable def rectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I))
    - (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I))
    + Complex.I • (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I))
    - Complex.I • (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I))

/-- `log(-u) = log u - πi` in the upper half-plane. -/
theorem log_neg_of_im_pos {u : ℂ} (hu : 0 < u.im) :
    Complex.log (-u) = Complex.log u - Real.pi * Complex.I := by
  rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hu]
  push_cast
  ring

/-- `log(-u) = log u + πi` in the lower half-plane. -/
theorem log_neg_of_im_neg {u : ℂ} (hu : u.im < 0) :
    Complex.log (-u) = Complex.log u + Real.pi * Complex.I := by
  have h := log_neg_of_im_pos (u := -u) (by simp only [Complex.neg_im]; linarith)
  rw [neg_neg] at h
  linear_combination -h

/-- FTC on a horizontal segment staying in the slit plane:
`∫_{a}^{b} (x + ci − ρ)⁻¹ dx = log(b + ci − ρ) − log(a + ci − ρ)`. -/
theorem integral_horizontal_inv_sub {a b c : ℝ} {ρ : ℂ}
    (h : ∀ x ∈ Set.uIcc a b, ((x:ℂ) + (c:ℂ) * Complex.I - ρ) ∈ Complex.slitPlane) :
    ∫ x : ℝ in a..b, ((x:ℂ) + (c:ℂ) * Complex.I - ρ)⁻¹
      = Complex.log ((b:ℂ) + (c:ℂ) * Complex.I - ρ)
        - Complex.log ((a:ℂ) + (c:ℂ) * Complex.I - ρ) := by
  have hne : ∀ x ∈ Set.uIcc a b, ((x:ℂ) + (c:ℂ) * Complex.I - ρ) ≠ 0 :=
    fun x hx => Complex.slitPlane_ne_zero (h x hx)
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => Complex.log ((t:ℂ) + (c:ℂ) * Complex.I - ρ))
        (((x:ℂ) + (c:ℂ) * Complex.I - ρ)⁻¹) x := by
    intro x hx
    have hlin : HasDerivAt (fun t : ℝ => (t:ℂ) + (c:ℂ) * Complex.I - ρ) 1 x := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const
        ((c:ℂ) * Complex.I)).sub_const ρ
    have := hlin.clog_real (h x hx)
    simpa using this
  have hcont : IntervalIntegrable
      (fun x : ℝ => ((x:ℂ) + (c:ℂ) * Complex.I - ρ)⁻¹) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ ?_ hne
    fun_prop
  exact integral_eq_sub_of_hasDerivAt hderiv hcont

/-- FTC on a vertical segment staying in the slit plane:
`i·∫_{c}^{d} (b + yi − ρ)⁻¹ dy = log(b + di − ρ) − log(b + ci − ρ)`. -/
theorem smul_integral_vertical_inv_sub {b c d : ℝ} {ρ : ℂ}
    (h : ∀ y ∈ Set.uIcc c d, ((b:ℂ) + (y:ℂ) * Complex.I - ρ) ∈ Complex.slitPlane) :
    Complex.I • (∫ y : ℝ in c..d, ((b:ℂ) + (y:ℂ) * Complex.I - ρ)⁻¹)
      = Complex.log ((b:ℂ) + (d:ℂ) * Complex.I - ρ)
        - Complex.log ((b:ℂ) + (c:ℂ) * Complex.I - ρ) := by
  have hne : ∀ y ∈ Set.uIcc c d, ((b:ℂ) + (y:ℂ) * Complex.I - ρ) ≠ 0 :=
    fun y hy => Complex.slitPlane_ne_zero (h y hy)
  have hderiv : ∀ y ∈ Set.uIcc c d,
      HasDerivAt (fun t : ℝ => Complex.log ((b:ℂ) + (t:ℂ) * Complex.I - ρ))
        (Complex.I * ((b:ℂ) + (y:ℂ) * Complex.I - ρ)⁻¹) y := by
    intro y hy
    have hlin : HasDerivAt (fun t : ℝ => (b:ℂ) + (t:ℂ) * Complex.I - ρ) Complex.I y := by
      have h1 : HasDerivAt (fun t : ℝ => (t:ℂ) * Complex.I) Complex.I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I
      simpa using (h1.const_add ((b:ℂ))).sub_const ρ
    have := hlin.clog_real (h y hy)
    rw [div_eq_mul_inv] at this
    simpa [mul_comm] using this
  have hcont : IntervalIntegrable
      (fun y : ℝ => Complex.I * ((b:ℂ) + (y:ℂ) * Complex.I - ρ)⁻¹) volume c d := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.inv₀ ?_ hne
    fun_prop
  have hint := integral_eq_sub_of_hasDerivAt hderiv hcont
  rw [intervalIntegral.integral_const_mul] at hint
  rw [smul_eq_mul]
  exact hint

/-- **The rectangle winding integral** (SP2-RECT R-c core): for `ρ` in the open
rectangle with corners `z` (bottom-left) and `w` (top-right),
`∮_{∂R} (ζ − ρ)⁻¹ dζ = 2πi`. -/
theorem rectangleIntegral_inv_sub {z w ρ : ℂ}
    (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im) (h4 : ρ.im < w.im) :
    rectangleIntegral (fun ζ => (ζ - ρ)⁻¹) z w = 2 * Real.pi * Complex.I := by
  rw [rectangleIntegral]
  -- the four segments
  have hbot : ∀ x ∈ Set.uIcc z.re w.re,
      ((x:ℂ) + (z.im:ℂ) * Complex.I - ρ) ∈ Complex.slitPlane := by
    intro x _
    refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    have him : ((x:ℂ) + (z.im:ℂ) * Complex.I - ρ).im = z.im - ρ.im := by simp
    rw [him]
    exact ne_of_lt (by linarith)
  have htop : ∀ x ∈ Set.uIcc z.re w.re,
      ((x:ℂ) + (w.im:ℂ) * Complex.I - ρ) ∈ Complex.slitPlane := by
    intro x _
    refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    have him : ((x:ℂ) + (w.im:ℂ) * Complex.I - ρ).im = w.im - ρ.im := by simp
    rw [him]
    exact ne_of_gt (by linarith)
  have hright : ∀ y ∈ Set.uIcc z.im w.im,
      ((w.re:ℂ) + (y:ℂ) * Complex.I - ρ) ∈ Complex.slitPlane := by
    intro y _
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have hre : ((w.re:ℂ) + (y:ℂ) * Complex.I - ρ).re = w.re - ρ.re := by simp
    rw [hre]
    linarith
  -- rewrite the four integrals; the left segment needs the reflected branch
  have hB := integral_horizontal_inv_sub (a := z.re) (b := w.re) (c := z.im) (ρ := ρ) hbot
  have hT := integral_horizontal_inv_sub (a := z.re) (b := w.re) (c := w.im) (ρ := ρ) htop
  have hR := smul_integral_vertical_inv_sub (b := w.re) (c := z.im) (d := w.im) (ρ := ρ) hright
  -- left segment: reflect through -(ζ - ρ), which has positive real part
  have hleftpt : ∀ y ∈ Set.uIcc z.im w.im,
      (-((z.re:ℂ) + (y:ℂ) * Complex.I - ρ)) ∈ Complex.slitPlane := by
    intro y _
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have hre : (-((z.re:ℂ) + (y:ℂ) * Complex.I - ρ)).re = ρ.re - z.re := by simp
    rw [hre]
    linarith
  have hLderiv : ∀ y ∈ Set.uIcc z.im w.im,
      HasDerivAt (fun t : ℝ => Complex.log (-((z.re:ℂ) + (t:ℂ) * Complex.I - ρ)))
        (Complex.I * ((z.re:ℂ) + (y:ℂ) * Complex.I - ρ)⁻¹) y := by
    intro y hy
    have hlin : HasDerivAt (fun t : ℝ => -((z.re:ℂ) + (t:ℂ) * Complex.I - ρ))
        (-Complex.I) y := by
      have h1 : HasDerivAt (fun t : ℝ => (t:ℂ) * Complex.I) Complex.I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I
      exact ((h1.const_add ((z.re:ℂ))).sub_const ρ).neg
    have := hlin.clog_real (hleftpt y hy)
    have hne : ((z.re:ℂ) + (y:ℂ) * Complex.I - ρ) ≠ 0 := by
      intro h0
      have := hleftpt y hy
      rw [h0] at this
      simp [Complex.slitPlane] at this
    rw [show -Complex.I / -((z.re:ℂ) + (y:ℂ) * Complex.I - ρ)
        = Complex.I * ((z.re:ℂ) + (y:ℂ) * Complex.I - ρ)⁻¹ by
      field_simp] at this
    exact this
  have hLcont : IntervalIntegrable
      (fun y : ℝ => Complex.I * ((z.re:ℂ) + (y:ℂ) * Complex.I - ρ)⁻¹)
      volume z.im w.im := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.inv₀ ?_ ?_
    · fun_prop
    · intro y hy h0
      have := hleftpt y hy
      rw [h0] at this
      simp [Complex.slitPlane] at this
  have hL0 := integral_eq_sub_of_hasDerivAt hLderiv hLcont
  rw [intervalIntegral.integral_const_mul] at hL0
  -- assemble: name the four corner values
  set u₁ : ℂ := (z.re:ℂ) + (z.im:ℂ) * Complex.I - ρ with hu₁
  set u₂ : ℂ := (w.re:ℂ) + (z.im:ℂ) * Complex.I - ρ with hu₂
  set u₃ : ℂ := (w.re:ℂ) + (w.im:ℂ) * Complex.I - ρ with hu₃
  set u₄ : ℂ := (z.re:ℂ) + (w.im:ℂ) * Complex.I - ρ with hu₄
  -- the left integral in terms of the reflected logs
  have hL : Complex.I • (∫ y : ℝ in z.im..w.im, ((z.re:ℂ) + (y:ℂ) * Complex.I - ρ)⁻¹)
      = Complex.log (-u₄) - Complex.log (-u₁) := by
    rw [smul_eq_mul, hL0]
  -- the corner half-plane facts
  have hu₁im : u₁.im < 0 := by
    rw [hu₁]
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re]
    simp
    linarith
  have hu₄im : 0 < u₄.im := by
    rw [hu₄]
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re]
    simp
    linarith
  rw [hB, hT, hR, hL, log_neg_of_im_pos hu₄im, log_neg_of_im_neg hu₁im]
  ring



/-- **Rectangle Cauchy–Goursat** (wrapper of mathlib's off-countable version in the
`rectangleIntegral` packaging): the boundary integral of a function continuous on the
closed rectangle and differentiable off a countable set vanishes. -/
theorem rectangleIntegral_eq_zero {f : ℂ → ℂ} {z w : ℂ} {s : Set ℂ} (hs : s.Countable)
    (Hc : ContinuousOn f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im))
    (Hd : ∀ x ∈ (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
      Set.Ioo (min z.im w.im) (max z.im w.im)) \ s, DifferentiableAt ℂ f x) :
    rectangleIntegral f z w = 0 := by
  rw [rectangleIntegral]
  exact Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    f z w s hs Hc Hd

/-- Horizontal-segment split of `Φ(ζ)(ζ-ρ)⁻¹` into `dslope + Φ(ρ)·(ζ-ρ)⁻¹`. -/
theorem integral_horizontal_split {Φ : ℂ → ℂ} {ρ : ℂ} {a b c : ℝ} {R : Set ℂ}
    (hcont : ContinuousOn (dslope Φ ρ) R)
    (hseg : ∀ x ∈ Set.uIcc a b, ((x:ℂ) + (c:ℂ) * Complex.I) ∈ R)
    (hne : ∀ x ∈ Set.uIcc a b, ((x:ℂ) + (c:ℂ) * Complex.I) ≠ ρ) :
    ∫ x : ℝ in a..b, Φ ((x:ℂ) + (c:ℂ) * Complex.I) * (((x:ℂ) + (c:ℂ) * Complex.I) - ρ)⁻¹
      = (∫ x : ℝ in a..b, dslope Φ ρ ((x:ℂ) + (c:ℂ) * Complex.I))
        + Φ ρ * ∫ x : ℝ in a..b, (((x:ℂ) + (c:ℂ) * Complex.I) - ρ)⁻¹ := by
  have hpath : ContinuousOn (fun x : ℝ => (x:ℂ) + (c:ℂ) * Complex.I) (Set.uIcc a b) := by
    fun_prop
  have hds_int : IntervalIntegrable
      (fun x : ℝ => dslope Φ ρ ((x:ℂ) + (c:ℂ) * Complex.I)) volume a b :=
    (hcont.comp hpath hseg).intervalIntegrable
  have hinv_int : IntervalIntegrable
      (fun x : ℝ => (((x:ℂ) + (c:ℂ) * Complex.I) - ρ)⁻¹) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro x hx
    exact sub_ne_zero_of_ne (hne x hx)
  have hsplit : ∀ x ∈ Set.uIcc a b,
      Φ ((x:ℂ) + (c:ℂ) * Complex.I) * (((x:ℂ) + (c:ℂ) * Complex.I) - ρ)⁻¹
        = dslope Φ ρ ((x:ℂ) + (c:ℂ) * Complex.I)
          + Φ ρ * (((x:ℂ) + (c:ℂ) * Complex.I) - ρ)⁻¹ := by
    intro x hx
    rw [dslope_of_ne Φ (hne x hx), slope_def_field, div_eq_mul_inv]
    ring
  rw [intervalIntegral.integral_congr hsplit, intervalIntegral.integral_add hds_int
    (hinv_int.const_mul (Φ ρ)), intervalIntegral.integral_const_mul]

/-- Vertical-segment split of `Φ(ζ)(ζ-ρ)⁻¹` into `dslope + Φ(ρ)·(ζ-ρ)⁻¹`. -/
theorem integral_vertical_split {Φ : ℂ → ℂ} {ρ : ℂ} {b c d : ℝ} {R : Set ℂ}
    (hcont : ContinuousOn (dslope Φ ρ) R)
    (hseg : ∀ y ∈ Set.uIcc c d, ((b:ℂ) + (y:ℂ) * Complex.I) ∈ R)
    (hne : ∀ y ∈ Set.uIcc c d, ((b:ℂ) + (y:ℂ) * Complex.I) ≠ ρ) :
    ∫ y : ℝ in c..d, Φ ((b:ℂ) + (y:ℂ) * Complex.I) * (((b:ℂ) + (y:ℂ) * Complex.I) - ρ)⁻¹
      = (∫ y : ℝ in c..d, dslope Φ ρ ((b:ℂ) + (y:ℂ) * Complex.I))
        + Φ ρ * ∫ y : ℝ in c..d, (((b:ℂ) + (y:ℂ) * Complex.I) - ρ)⁻¹ := by
  have hpath : ContinuousOn (fun y : ℝ => (b:ℂ) + (y:ℂ) * Complex.I) (Set.uIcc c d) := by
    fun_prop
  have hds_int : IntervalIntegrable
      (fun y : ℝ => dslope Φ ρ ((b:ℂ) + (y:ℂ) * Complex.I)) volume c d :=
    (hcont.comp hpath hseg).intervalIntegrable
  have hinv_int : IntervalIntegrable
      (fun y : ℝ => (((b:ℂ) + (y:ℂ) * Complex.I) - ρ)⁻¹) volume c d := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro y hy
    exact sub_ne_zero_of_ne (hne y hy)
  have hsplit : ∀ y ∈ Set.uIcc c d,
      Φ ((b:ℂ) + (y:ℂ) * Complex.I) * (((b:ℂ) + (y:ℂ) * Complex.I) - ρ)⁻¹
        = dslope Φ ρ ((b:ℂ) + (y:ℂ) * Complex.I)
          + Φ ρ * (((b:ℂ) + (y:ℂ) * Complex.I) - ρ)⁻¹ := by
    intro y hy
    rw [dslope_of_ne Φ (hne y hy), slope_def_field, div_eq_mul_inv]
    ring
  rw [intervalIntegral.integral_congr hsplit, intervalIntegral.integral_add hds_int
    (hinv_int.const_mul (Φ ρ)), intervalIntegral.integral_const_mul]

/-- **The rectangle Cauchy integral formula** (SP2-RECT R-c): for `Φ` differentiable
on (a neighbourhood of each point of) the closed rectangle and `ρ` in the open
rectangle, `∮_{∂R} Φ(ζ)(ζ − ρ)⁻¹ dζ = 2πi·Φ(ρ)`. -/
theorem rectangleIntegral_cauchy {Φ : ℂ → ℂ} {z w ρ : ℂ}
    (hΦ : ∀ ζ ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im, DifferentiableAt ℂ Φ ζ)
    (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im) (h4 : ρ.im < w.im) :
    rectangleIntegral (fun ζ => Φ ζ * (ζ - ρ)⁻¹) z w
      = 2 * Real.pi * Complex.I * Φ ρ := by
  set R : Set ℂ := Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im with hR
  -- ρ is interior to the closed rectangle
  have hρR : R ∈ nhds ρ := by
    rw [← mem_interior_iff_mem_nhds, hR, Complex.interior_reProdIm]
    rw [Set.uIcc_of_le (by linarith : z.re ≤ w.re), Set.uIcc_of_le (by linarith : z.im ≤ w.im),
      interior_Icc, interior_Icc]
    rw [Complex.mem_reProdIm]
    exact ⟨Set.mem_Ioo.mpr ⟨h1, h2⟩, Set.mem_Ioo.mpr ⟨h3, h4⟩⟩
  -- the dslope is continuous on the rectangle, differentiable off ρ
  have hcont : ContinuousOn (dslope Φ ρ) R :=
    (continuousOn_dslope hρR).mpr
      ⟨fun ζ hζ => (hΦ ζ hζ).continuousAt.continuousWithinAt,
        hΦ ρ (mem_of_mem_nhds hρR)⟩
  have hzero : rectangleIntegral (dslope Φ ρ) z w = 0 := by
    refine rectangleIntegral_eq_zero (Set.countable_singleton ρ) hcont ?_
    intro x hx
    obtain ⟨hxmem, hxne⟩ := hx
    rw [Set.mem_singleton_iff] at hxne
    refine (differentiableAt_dslope_of_ne hxne).mpr ?_
    refine hΦ x ?_
    rw [hR]
    rw [Complex.mem_reProdIm] at hxmem ⊢
    rw [Set.uIcc_of_le (by linarith : z.re ≤ w.re), Set.uIcc_of_le (by linarith : z.im ≤ w.im)]
    obtain ⟨hx1, hx2⟩ := hxmem
    rw [min_eq_left (by linarith : z.re ≤ w.re), max_eq_right (by linarith : z.re ≤ w.re)]
      at hx1
    rw [min_eq_left (by linarith : z.im ≤ w.im), max_eq_right (by linarith : z.im ≤ w.im)]
      at hx2
    exact ⟨Set.Ioo_subset_Icc_self hx1, Set.Ioo_subset_Icc_self hx2⟩
  -- segment membership and non-hitting facts
  have hsegB : ∀ x ∈ Set.uIcc z.re w.re, ((x:ℂ) + (z.im:ℂ) * Complex.I) ∈ R := by
    intro x hx
    rw [hR, Complex.mem_reProdIm]
    constructor
    · simpa using hx
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re]
      simp
  have hsegT : ∀ x ∈ Set.uIcc z.re w.re, ((x:ℂ) + (w.im:ℂ) * Complex.I) ∈ R := by
    intro x hx
    rw [hR, Complex.mem_reProdIm]
    constructor
    · simpa using hx
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re]
      simp
  have hsegR : ∀ y ∈ Set.uIcc z.im w.im, ((w.re:ℂ) + (y:ℂ) * Complex.I) ∈ R := by
    intro y hy
    rw [hR, Complex.mem_reProdIm]
    constructor
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      simp
    · simpa using hy
  have hsegL : ∀ y ∈ Set.uIcc z.im w.im, ((z.re:ℂ) + (y:ℂ) * Complex.I) ∈ R := by
    intro y hy
    rw [hR, Complex.mem_reProdIm]
    constructor
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      simp
    · simpa using hy
  have hneB : ∀ x ∈ Set.uIcc z.re w.re, ((x:ℂ) + (z.im:ℂ) * Complex.I) ≠ ρ := by
    intro x _ h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hneT : ∀ x ∈ Set.uIcc z.re w.re, ((x:ℂ) + (w.im:ℂ) * Complex.I) ≠ ρ := by
    intro x _ h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hneR : ∀ y ∈ Set.uIcc z.im w.im, ((w.re:ℂ) + (y:ℂ) * Complex.I) ≠ ρ := by
    intro y _ h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  have hneL : ∀ y ∈ Set.uIcc z.im w.im, ((z.re:ℂ) + (y:ℂ) * Complex.I) ≠ ρ := by
    intro y _ h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  -- split all four segments
  have hB := integral_horizontal_split (a := z.re) (b := w.re) (c := z.im) hcont hsegB hneB
  have hT := integral_horizontal_split (a := z.re) (b := w.re) (c := w.im) hcont hsegT hneT
  have hRt := integral_vertical_split (b := w.re) (c := z.im) (d := w.im) hcont hsegR hneR
  have hLt := integral_vertical_split (b := z.re) (c := z.im) (d := w.im) hcont hsegL hneL
  -- assemble
  have hwind := rectangleIntegral_inv_sub h1 h2 h3 h4
  rw [rectangleIntegral] at hzero hwind ⊢
  rw [hB, hT, hRt, hLt]
  rw [smul_eq_mul, smul_eq_mul] at hzero hwind ⊢
  linear_combination hzero + Φ ρ * hwind

/-- The four boundary segments of the rectangle with corners `z`, `w`, as a set. -/
def rectangleBoundary (z w : ℂ) : Set ℂ :=
  (Set.uIcc z.re w.re ×ℂ {z.im, w.im}) ∪ ({z.re, w.re} ×ℂ Set.uIcc z.im w.im)

theorem horizontal_mem_rectangleBoundary_bot {z w : ℂ} {x : ℝ}
    (hx : x ∈ Set.uIcc z.re w.re) :
    ((x:ℂ) + (z.im:ℂ) * Complex.I) ∈ rectangleBoundary z w := by
  refine Set.mem_union_left _ ?_
  rw [Complex.mem_reProdIm]
  constructor
  · simpa using hx
  · simp

theorem horizontal_mem_rectangleBoundary_top {z w : ℂ} {x : ℝ}
    (hx : x ∈ Set.uIcc z.re w.re) :
    ((x:ℂ) + (w.im:ℂ) * Complex.I) ∈ rectangleBoundary z w := by
  refine Set.mem_union_left _ ?_
  rw [Complex.mem_reProdIm]
  constructor
  · simpa using hx
  · simp

theorem vertical_mem_rectangleBoundary_left {z w : ℂ} {y : ℝ}
    (hy : y ∈ Set.uIcc z.im w.im) :
    ((z.re:ℂ) + (y:ℂ) * Complex.I) ∈ rectangleBoundary z w := by
  refine Set.mem_union_right _ ?_
  rw [Complex.mem_reProdIm]
  constructor
  · simp
  · simpa using hy

theorem vertical_mem_rectangleBoundary_right {z w : ℂ} {y : ℝ}
    (hy : y ∈ Set.uIcc z.im w.im) :
    ((w.re:ℂ) + (y:ℂ) * Complex.I) ∈ rectangleBoundary z w := by
  refine Set.mem_union_right _ ?_
  rw [Complex.mem_reProdIm]
  constructor
  · simp
  · simpa using hy

/-- The boundary integral only sees boundary values. -/
theorem rectangleIntegral_congr {f g : ℂ → ℂ} {z w : ℂ}
    (h : Set.EqOn f g (rectangleBoundary z w)) :
    rectangleIntegral f z w = rectangleIntegral g z w := by
  rw [rectangleIntegral, rectangleIntegral]
  congr 1
  · congr 1
    · congr 1
      · refine intervalIntegral.integral_congr (fun x hx => ?_)
        exact h (horizontal_mem_rectangleBoundary_bot hx)
      · refine intervalIntegral.integral_congr (fun x hx => ?_)
        exact h (horizontal_mem_rectangleBoundary_top hx)
    · congr 1
      refine intervalIntegral.integral_congr (fun y hy => ?_)
      exact h (vertical_mem_rectangleBoundary_right hy)
  · congr 1
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    exact h (vertical_mem_rectangleBoundary_left hy)

/-- Scalar multiples pass through the boundary integral. -/
theorem rectangleIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectangleIntegral (fun ζ => c * f ζ) z w = c * rectangleIntegral f z w := by
  rw [rectangleIntegral, rectangleIntegral]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- Finite sums pass through the boundary integral, given continuity of each summand
on the boundary. -/
theorem rectangleIntegral_finset_sum {ι : Type*} (F : Finset ι) (f : ι → ℂ → ℂ)
    {z w : ℂ} (hf : ∀ i ∈ F, ContinuousOn (f i) (rectangleBoundary z w)) :
    rectangleIntegral (fun ζ => ∑ i ∈ F, f i ζ) z w
      = ∑ i ∈ F, rectangleIntegral (f i) z w := by
  have hpathB : ContinuousOn (fun x : ℝ => (x:ℂ) + (z.im:ℂ) * Complex.I)
      (Set.uIcc z.re w.re) := by fun_prop
  have hpathT : ContinuousOn (fun x : ℝ => (x:ℂ) + (w.im:ℂ) * Complex.I)
      (Set.uIcc z.re w.re) := by fun_prop
  have hpathR : ContinuousOn (fun y : ℝ => (w.re:ℂ) + (y:ℂ) * Complex.I)
      (Set.uIcc z.im w.im) := by fun_prop
  have hpathL : ContinuousOn (fun y : ℝ => (z.re:ℂ) + (y:ℂ) * Complex.I)
      (Set.uIcc z.im w.im) := by fun_prop
  have hiB : ∀ i ∈ F, IntervalIntegrable
      (fun x : ℝ => f i ((x:ℂ) + (z.im:ℂ) * Complex.I)) volume z.re w.re := fun i hi =>
    (((hf i hi).comp hpathB (fun x hx =>
      horizontal_mem_rectangleBoundary_bot hx))).intervalIntegrable
  have hiT : ∀ i ∈ F, IntervalIntegrable
      (fun x : ℝ => f i ((x:ℂ) + (w.im:ℂ) * Complex.I)) volume z.re w.re := fun i hi =>
    (((hf i hi).comp hpathT (fun x hx =>
      horizontal_mem_rectangleBoundary_top hx))).intervalIntegrable
  have hiR : ∀ i ∈ F, IntervalIntegrable
      (fun y : ℝ => f i ((w.re:ℂ) + (y:ℂ) * Complex.I)) volume z.im w.im := fun i hi =>
    (((hf i hi).comp hpathR (fun y hy =>
      vertical_mem_rectangleBoundary_right hy))).intervalIntegrable
  have hiL : ∀ i ∈ F, IntervalIntegrable
      (fun y : ℝ => f i ((z.re:ℂ) + (y:ℂ) * Complex.I)) volume z.im w.im := fun i hi =>
    (((hf i hi).comp hpathL (fun y hy =>
      vertical_mem_rectangleBoundary_left hy))).intervalIntegrable
  rw [rectangleIntegral]
  rw [intervalIntegral.integral_finsetSum hiB, intervalIntegral.integral_finsetSum hiT,
    intervalIntegral.integral_finsetSum hiR, intervalIntegral.integral_finsetSum hiL]
  rw [Finset.smul_sum, Finset.smul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [rectangleIntegral]

/-- Sums pass through the boundary integral, given continuity on the boundary. -/
theorem rectangleIntegral_add {f g : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (rectangleBoundary z w))
    (hg : ContinuousOn g (rectangleBoundary z w)) :
    rectangleIntegral (fun ζ => f ζ + g ζ) z w
      = rectangleIntegral f z w + rectangleIntegral g z w := by
  have key := rectangleIntegral_finset_sum (F := ({0, 1} : Finset ℕ))
    (f := fun i => if i = 0 then f else g) (z := z) (w := w) ?_
  · have h1 : (fun ζ => ∑ i ∈ ({0, 1} : Finset ℕ), (if i = 0 then f else g) ζ)
        = fun ζ => f ζ + g ζ := by
      funext ζ
      simp
    have h2 : ∑ i ∈ ({0, 1} : Finset ℕ), rectangleIntegral (if i = 0 then f else g) z w
        = rectangleIntegral f z w + rectangleIntegral g z w := by
      simp
    rw [h1, h2] at key
    exact key
  · intro i _
    by_cases hi : i = 0 <;> simp [hi, hf, hg]

/-- The logarithmic derivative of a peeled factorization, pointwise: away from the
zeros, `H'/H = ∑ dᵤ/(ζ−u) + g'/g`. -/
theorem logDeriv_eq_sum_add_of_factorization {U : Set ℂ} (hUo : IsOpen U)
    {H g : ℂ → ℂ} {F : Finset ℂ} {d : ℂ → ℤ}
    (hfac : ∀ z ∈ U, H z = (∏ u ∈ F, (z - u) ^ d u) * g z)
    (hd : ∀ u, 0 ≤ d u)
    (hganal : AnalyticOnNhd ℂ g U)
    {ζ : ℂ} (hζ : ζ ∈ U) (hgζ : g ζ ≠ 0) (hζne : ∀ u ∈ F, ζ ≠ u) :
    logDeriv H ζ = ∑ u ∈ F, (d u : ℂ) * (ζ - u)⁻¹ + logDeriv g ζ := by
  have hPζ : (∏ u ∈ F, (ζ - u) ^ d u) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun u hu => ?_)
    exact zpow_ne_zero _ (sub_ne_zero_of_ne (hζne u hu))
  have hpolydiff : DifferentiableAt ℂ (fun z => ∏ u ∈ F, (z - u) ^ d u) ζ := by
    refine DifferentiableAt.fun_finsetProd (fun u _ => ?_)
    exact (differentiableAt_id.sub_const u).zpow (Or.inr (hd u))
  have hgdiff : DifferentiableAt ℂ g ζ := (hganal ζ hζ).differentiableAt
  have hHev : H =ᶠ[nhds ζ] fun z => (∏ u ∈ F, (z - u) ^ d u) * g z := by
    filter_upwards [hUo.mem_nhds hζ] with z hz
    exact hfac z hz
  have hld : logDeriv H ζ = logDeriv (fun z => (∏ u ∈ F, (z - u) ^ d u) * g z) ζ := by
    rw [logDeriv, logDeriv, Pi.div_apply, Pi.div_apply, hHev.deriv_eq, hHev.eq_of_nhds]
  rw [hld, logDeriv_mul ζ hPζ hgζ hpolydiff hgdiff]
  congr 1
  have h1 : logDeriv (fun z => ∏ u ∈ F, (fun w : ℂ => w - u) z ^ d u) ζ
      = ∑ u ∈ F, logDeriv (fun z => (fun w : ℂ => w - u) z ^ d u) ζ := by
    refine logDeriv_prod (fun u hu => ?_) (fun u hu => ?_)
    · exact zpow_ne_zero _ (sub_ne_zero_of_ne (hζne u hu))
    · exact (differentiableAt_id.sub_const u).zpow (Or.inr (hd u))
  refine Eq.trans h1 ?_
  refine Finset.sum_congr rfl (fun u hu => ?_)
  have h2 : logDeriv (fun z : ℂ => (z - u) ^ d u) ζ
      = (d u : ℂ) * logDeriv (fun z : ℂ => z - u) ζ :=
    logDeriv_fun_zpow (differentiableAt_id.sub_const u) _
  have h3 : logDeriv (fun z : ℂ => z - u) ζ = 1 / (ζ - u) := by
    rw [logDeriv, Pi.div_apply]
    simp
  rw [h2, h3]
  rw [mul_one_div, div_eq_mul_inv]

end DedekindResidue

end
