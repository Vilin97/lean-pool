/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Adapted from [PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
by Alex Kontorovich and Terence Tao:
`ResidueCalcOnRectangles.lean`, commit
`be5e07e04cde20c5ceabf63759bd097a9c88173f` (Apache-2.0). -/

@[expose] public section

noncomputable section

open Complex intervalIntegral MeasureTheory Real Set
open scoped Interval

namespace NumberField.Odlyzko

/-- A horizontal integral used in the Odlyzko-bound argument. -/
noncomputable def horizontalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
  ∫ x in x₁..x₂, f (x + y * I)

/-- A vertical segment integral used in the Odlyzko-bound argument. -/
noncomputable def verticalSegmentIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
  I • ∫ y in y₁..y₂, f (x + y * I)

/-- A rectangle integral used in the Odlyzko-bound argument. -/
noncomputable def rectangleIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (z w : ℂ) : E :=
  horizontalIntegral f z.re w.re z.im -
    horizontalIntegral f z.re w.re w.im +
    verticalSegmentIntegral f w.re z.im w.im -
    verticalSegmentIntegral f z.re z.im w.im

theorem rectangleIntegral_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : ℂ → E} {z w : ℂ}
    (hbottom : ∀ x ∈ uIcc z.re w.re,
      f (x + z.im * I) = g (x + z.im * I))
    (htop : ∀ x ∈ uIcc z.re w.re,
      f (x + w.im * I) = g (x + w.im * I))
    (hright : ∀ y ∈ uIcc z.im w.im,
      f (w.re + y * I) = g (w.re + y * I))
    (hleft : ∀ y ∈ uIcc z.im w.im,
      f (z.re + y * I) = g (z.re + y * I)) :
    rectangleIntegral f z w = rectangleIntegral g z w := by
  unfold rectangleIntegral horizontalIntegral verticalSegmentIntegral
  rw [intervalIntegral.integral_congr hbottom,
    intervalIntegral.integral_congr htop,
    intervalIntegral.integral_congr hright,
    intervalIntegral.integral_congr hleft]

/-- A normalized rectangle integral used in the Odlyzko-bound argument. -/
noncomputable def normalizedRectangleIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (z w : ℂ) : E :=
  (1 / (2 * Real.pi * I)) • rectangleIntegral f z w

/-- A rectangle border integrable used in the Odlyzko-bound argument. -/
def RectangleBorderIntegrable {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (z w : ℂ) : Prop :=
  IntervalIntegrable (fun x ↦ f (x + z.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun x ↦ f (x + w.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun y ↦ f (w.re + y * I)) volume z.im w.im ∧
  IntervalIntegrable (fun y ↦ f (z.re + y * I)) volume z.im w.im

theorem RectangleBorderIntegrable.add_integrable {E : Type*} [NormedAddCommGroup E]
    {f g : ℂ → E} {z w : ℂ}
    (hf : RectangleBorderIntegrable f z w)
    (hg : RectangleBorderIntegrable g z w) :
    RectangleBorderIntegrable (fun s ↦ f s + g s) z w :=
  ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    hf.2.2.1.add hg.2.2.1, hf.2.2.2.add hg.2.2.2⟩

theorem rectangleBorderIntegrable_fun_sum {E : Type*} [NormedAddCommGroup E]
    {ι : Type*} {T : Finset ι} {f : ι → ℂ → E} {z w : ℂ}
    (hf : ∀ i ∈ T, RectangleBorderIntegrable (f i) z w) :
    RectangleBorderIntegrable (fun s ↦ ∑ i ∈ T, f i s) z w := by
  classical
  induction T using Finset.induction with
  | empty =>
      simp [RectangleBorderIntegrable]
  | @insert i T hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i T)).add_integrable
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

theorem RectangleBorderIntegrable.add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : ℂ → E} {z w : ℂ}
    (hf : RectangleBorderIntegrable f z w)
    (hg : RectangleBorderIntegrable g z w) :
    rectangleIntegral (fun s ↦ f s + g s) z w =
      rectangleIntegral f z w + rectangleIntegral g z w := by
  simp only [rectangleIntegral, horizontalIntegral, verticalSegmentIntegral]
  rw [intervalIntegral.integral_add hf.1 hg.1,
    intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  simp only [smul_add]
  grind

theorem RectangleBorderIntegrable.sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : ℂ → E} {z w : ℂ}
    (hf : RectangleBorderIntegrable f z w)
    (hg : RectangleBorderIntegrable g z w) :
    rectangleIntegral (fun s ↦ f s - g s) z w =
      rectangleIntegral f z w - rectangleIntegral g z w := by
  simp only [rectangleIntegral, horizontalIntegral, verticalSegmentIntegral]
  rw [intervalIntegral.integral_sub hf.1 hg.1,
    intervalIntegral.integral_sub hf.2.1 hg.2.1,
    intervalIntegral.integral_sub hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_sub hf.2.2.2 hg.2.2.2]
  simp only [smul_sub]
  grind

theorem rectangleIntegral_fun_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} {T : Finset ι} {f : ι → ℂ → E} {z w : ℂ}
    (hf : ∀ i ∈ T, RectangleBorderIntegrable (f i) z w) :
    rectangleIntegral (fun s ↦ ∑ i ∈ T, f i s) z w =
      ∑ i ∈ T, rectangleIntegral (f i) z w := by
  classical
  induction T using Finset.induction with
  | empty =>
      simp [rectangleIntegral, horizontalIntegral, verticalSegmentIntegral]
  | @insert i T hi ih =>
      simp only [Finset.sum_insert hi]
      change rectangleIntegral
        (fun s ↦ f i s + ∑ j ∈ T, f j s) z w =
          rectangleIntegral (f i) z w +
            ∑ j ∈ T, rectangleIntegral (f j) z w
      rw [(hf i (Finset.mem_insert_self i T)).add]
      · simp_all
      · exact rectangleBorderIntegrable_fun_sum fun j hj ↦
          hf j (Finset.mem_insert_of_mem hj)

theorem rectangleIntegral_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (z w p : ℂ) :
    rectangleIntegral (fun s ↦ f (s - p)) z w =
      rectangleIntegral f (z - p) (w - p) := by
  simp_rw [rectangleIntegral, horizontalIntegral, verticalSegmentIntegral,
    sub_re, sub_im, ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]

theorem normalizedRectangleIntegral_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (z w p : ℂ) :
    normalizedRectangleIntegral (fun s ↦ f (s - p)) z w =
      normalizedRectangleIntegral f (z - p) (w - p) := by
  simp [normalizedRectangleIntegral, rectangleIntegral_translate]

private lemma sq_add_sq_ne_zero {x y : ℝ} (hy : y ≠ 0) :
    x ^ 2 + y ^ 2 ≠ 0 := by
  nlinarith [sq_nonneg x, sq_pos_of_ne_zero hy]

private lemma continuous_self_div_sq_add_sq {y : ℝ} (hy : y ≠ 0) :
    Continuous fun x : ℝ ↦ x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const)
    fun _ ↦ sq_add_sq_ne_zero hy

private lemma integral_self_div_sq_add_sq {x₁ x₂ y : ℝ} (hy : y ≠ 0) :
    ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
      Real.log (x₂ ^ 2 + y ^ 2) / 2 -
        Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let F (x : ℝ) : ℝ := Real.log (x ^ 2 + y ^ 2) / 2
  have hderiv {x : ℝ} :
      HasDerivAt F (x / (x ^ 2 + y ^ 2)) x := by
    have hpow :=
      HasDerivAt.add_const (y ^ 2)
        (by simpa using hasDerivAt_pow 2 x)
    convert! (hpow.log (sq_add_sq_ne_zero hy)).div_const 2 using 1
    grind
  have hderiv_eq :
      deriv F = fun x ↦ x / (x ^ 2 + y ^ 2) :=
    funext fun _ ↦ hderiv.deriv
  simp_rw [← hderiv.deriv]
  exact integral_deriv_eq_sub
    (fun _ _ ↦ hderiv.differentiableAt)
    (by simpa only [hderiv_eq] using
      (continuous_self_div_sq_add_sq hy).intervalIntegrable x₁ x₂)

private lemma integral_const_div_sq_add_sq {x₁ x₂ y : ℝ} (hy : y ≠ 0) :
    ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) =
      Real.arctan (x₂ / y) - Real.arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← intervalIntegral.integral_const_mul,
    ← integral_one_div_one_add_sq]
  grind

private lemma integral_const_div_re_add_im
    {x₁ x₂ y : ℝ} {A : ℂ} (hy : y ≠ 0) :
    ∫ x : ℝ in x₁..x₂, A / (x + y * I) =
      A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 -
        Real.log (x₁ ^ 2 + y ^ 2) / 2) -
      A * I * (Real.arctan (x₂ / y) - Real.arctan (x₁ / y)) := by
  have hpoint {x : ℝ} :
      A / (x + y * I) =
        A * x / (x ^ 2 + y ^ 2) -
          A * I * y / (x ^ 2 + y ^ 2) := by
    have hinv :
        ((x : ℂ) + y * I)⁻¹ =
          (x - I * y) / (x ^ 2 + y ^ 2) := by
      rw [Complex.inv_def, div_eq_mul_inv]
      congr <;> simp [Complex.conj_ofReal, Complex.normSq] <;> ring
    ring_nf
    rw [hinv]
    ring
  have h₁ :
      IntervalIntegrable (fun x : ℝ ↦ A * x / (x ^ 2 + y ^ 2))
        volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul
      (continuous_ofReal.comp (continuous_self_div_sq_add_sq hy))
  have h₂ :
      IntervalIntegrable (fun x : ℝ ↦ A * I * y / (x ^ 2 + y ^ 2))
        volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) fun x ↦ ?_
    norm_cast
    exact sq_add_sq_ne_zero hy
  simp_rw [intervalIntegral.integral_congr (fun _ _ ↦ hpoint),
    intervalIntegral.integral_sub h₁ h₂, mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal,
    integral_self_div_sq_add_sq hy,
    integral_const_div_sq_add_sq hy]

private lemma integral_const_div_re_add_self
    {y₁ y₂ x : ℝ} {A : ℂ} (hx : x ≠ 0) :
    ∫ y : ℝ in y₁..y₂, A / (x + y * I) =
      A / I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 -
        Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
      A / I * I *
        (Real.arctan (y₂ / -x) - Real.arctan (y₁ / -x)) := by
  have hpoint {y : ℝ} :
      A / (x + y * I) = A / I / (y + (-x : ℂ) * I) := by
    have h₁ : (x : ℂ) + y * I ≠ 0 := by
      contrapose! hx
      simpa using congrArg re hx
    have h₂ : (y : ℂ) + (-x : ℂ) * I ≠ 0 := by
      contrapose! hx
      simpa using congrArg im hx
    have hden : -(I * (x : ℂ)) + (y : ℂ) ≠ 0 := by grind
    ring_nf
    field_simp [h₁, h₂, hden]
    rw [show (x : ℂ) + y * I =
        I * (-(x * I) + y) by
      have hIx : I * ((x : ℂ) * I) = -x := by
        calc
          I * ((x : ℂ) * I) = x * (I * I) := by ring
          _ = -x := by simp
      grind]
    grind
  have hneg : -x ≠ 0 := neg_ne_zero.mpr hx
  rw [show (fun y : ℝ ↦ A / (x + y * I)) =
      (fun y : ℝ ↦ A / I / (y + (-x : ℂ) * I)) by
        simp_all]
  simpa only [ofReal_neg] using
    (integral_const_div_re_add_im
      (x₁ := y₁) (x₂ := y₂) (A := A / I) hneg)

theorem rectangleIntegral_const_div_id
    {z w c : ℂ}
    (hzre : z.re < 0) (hzim : z.im < 0)
    (hwre : 0 < w.re) (hwim : 0 < w.im) :
    rectangleIntegral (fun s ↦ c / s) z w =
      2 * I * Real.pi * c := by
  simp only [rectangleIntegral, horizontalIntegral, verticalSegmentIntegral,
    smul_eq_mul]
  rw [integral_const_div_re_add_self hzre.ne,
    integral_const_div_re_add_self hwre.ne.symm,
    integral_const_div_re_add_im hzim.ne,
    integral_const_div_re_add_im hwim.ne.symm]
  have h₁ : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
  have h₂ := Real.arctan_inv_of_neg
    (mul_neg_of_pos_of_neg hwre (inv_lt_zero.mpr hzim))
  have h₃ : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
  have h₄ := Real.arctan_inv_of_neg
    (mul_neg_of_neg_of_pos hzre (inv_pos.mpr hwim))
  have h₅ : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
  have h₆ := Real.arctan_inv_of_pos
    (mul_pos_of_neg_of_neg hzre (inv_lt_zero.mpr hzim))
  have h₇ : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
  have h₈ := Real.arctan_inv_of_pos
    (mul_pos hwre (inv_pos.mpr hwim))
  ring_nf
  simp only [one_div, inv_I, mul_neg, neg_mul, I_sq, neg_neg,
    Real.arctan_neg, ofReal_neg, sub_neg_eq_add]
  rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]
  ring_nf
  simp only [I_sq, ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_div,
    ofReal_neg, ofReal_one]
  grind

theorem normalizedRectangleIntegral_principal
    {z w p c : ℂ}
    (hzpre : z.re < p.re) (hprew : p.re < w.re)
    (hzpim : z.im < p.im) (hpimw : p.im < w.im) :
    normalizedRectangleIntegral (fun s ↦ c / (s - p)) z w = c := by
  rw [normalizedRectangleIntegral_translate,
    normalizedRectangleIntegral,
    rectangleIntegral_const_div_id]
  · simp only [smul_eq_mul]
    field_simp
  all_goals simp [*]

theorem rectangleIntegral_principal
    {z w p c : ℂ}
    (hzpre : z.re < p.re) (hprew : p.re < w.re)
    (hzpim : z.im < p.im) (hpimw : p.im < w.im) :
    rectangleIntegral (fun s ↦ c / (s - p)) z w =
      2 * Real.pi * I * c := by
  have h :=
    normalizedRectangleIntegral_principal
      (z := z) (w := w) (p := p) (c := c)
      hzpre hprew hzpim hpimw
  rw [normalizedRectangleIntegral] at h
  simp only [smul_eq_mul] at h
  have hconst : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp
  grind

end NumberField.Odlyzko
