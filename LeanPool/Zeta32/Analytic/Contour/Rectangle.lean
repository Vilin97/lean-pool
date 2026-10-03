/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Analytic.Contour.Kernel
public import LeanPool.Zeta32.Analytic.Contour.RectangleResidue
public import Mathlib.Analysis.Complex.RemovableSingularity

/-! Rectangle identity behind the shift rule of the proof notes, §0/§5.1:
for `F` holomorphic on the strip `0 < Re t < 2`,
`∮_{∂([1/2,3/2]×[-T,T])} F(t) π²/sin²(πt) dt = 2πi F'(1)`.
Proof: `π²/sin²(πt) = -(π cot πt)'`, so by the fundamental theorem of calculus on the
four edges the boundary integral equals that of `F'(t) π cot(πt)`, which has the single
simple pole `t = 1` in the rectangle with residue `F'(1)`. -/

public section

open MeasureTheory Set Filter Topology
open scoped Interval

namespace Zeta32.Analytic.Contour

noncomputable section

/-- `K(t) = π²/sin²(πt)`. -/
@[expose]
def Kc (t : ℂ) : ℂ := (Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * t) ^ 2

/-- `π cot(πt)`. -/
def cotK (t : ℂ) : ℂ :=
  (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * t) / Complex.sin ((Real.pi : ℂ) * t)

/-- The open strip `0 < Re t < 2`. -/
@[expose]
def strip : Set ℂ := {t | 0 < t.re ∧ t.re < 2}

lemma isOpen_strip : IsOpen strip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

lemma one_mem_strip : (1 : ℂ) ∈ strip := by
  constructor <;> norm_num

lemma sin_pi_ne_zero_of_mem_strip {t : ℂ} (ht : t ∈ strip) (h1 : t ≠ 1) :
    Complex.sin ((Real.pi : ℂ) * t) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have htk : t = (k : ℂ) := by
    have := hk
    rw [mul_comm] at this
    exact mul_right_cancel₀ hpi this
  have hre : t.re = k := by rw [htk]; simp
  obtain ⟨h0, h2⟩ := ht
  rw [hre] at h0 h2
  have hk1 : k = 1 := by
    have : (0 : ℤ) < k := by exact_mod_cast h0
    have : k < (2 : ℤ) := by exact_mod_cast h2
    omega
  apply h1
  rw [htk, hk1]
  simp

lemma hasDerivAt_sin_pi (t : ℂ) :
    HasDerivAt (fun u : ℂ => Complex.sin ((Real.pi : ℂ) * u))
      (Complex.cos ((Real.pi : ℂ) * t) * (Real.pi : ℂ)) t := by
  simpa using ((hasDerivAt_id t).const_mul (Real.pi : ℂ)).csin

lemma hasDerivAt_cos_pi (t : ℂ) :
    HasDerivAt (fun u : ℂ => Complex.cos ((Real.pi : ℂ) * u))
      (-Complex.sin ((Real.pi : ℂ) * t) * (Real.pi : ℂ)) t := by
  simpa using ((hasDerivAt_id t).const_mul (Real.pi : ℂ)).ccos

lemma hasDerivAt_cotK {t : ℂ} (hs : Complex.sin ((Real.pi : ℂ) * t) ≠ 0) :
    HasDerivAt cotK (-Kc t) t := by
  have h := ((hasDerivAt_cos_pi t).const_mul (Real.pi : ℂ)).div (hasDerivAt_sin_pi t) hs
  unfold cotK Kc
  convert h using 1
  have hsc := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * t)
  field_simp
  linear_combination hsc

lemma continuousAt_Kc {t : ℂ} (hs : Complex.sin ((Real.pi : ℂ) * t) ≠ 0) :
    ContinuousAt Kc t := by
  unfold Kc
  exact continuousAt_const.div (by fun_prop) (pow_ne_zero 2 hs)

lemma continuousAt_cotK {t : ℂ} (hs : Complex.sin ((Real.pi : ℂ) * t) ≠ 0) :
    ContinuousAt cotK t := by
  unfold cotK
  exact (continuousAt_const.mul (by fun_prop)).div (by fun_prop) hs

/-! ### Edges of a rectangle avoiding an interior point -/

section Edges

variable {z w p : ℂ}

/-- The closed rectangle `[z, w]` with the point `p` removed. -/
def rectMinus (z w p : ℂ) : Set ℂ := ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) \ {p}

lemma mem_rectMinus_bottom (hp : p.im ∈ Ioo z.im w.im) {x : ℝ} (hx : x ∈ [[z.re, w.re]]) :
    (x : ℂ) + (z.im : ℂ) * Complex.I ∈ rectMinus z w p := by
  refine ⟨?_, ?_⟩
  · rw [Complex.mem_reProdIm]; simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
    refine ⟨by simpa using hx, ?_⟩
    simp
  · intro h
    have := congrArg Complex.im (Set.mem_singleton_iff.mp h)
    simp at this
    linarith [hp.1]

lemma mem_rectMinus_top (hp : p.im ∈ Ioo z.im w.im) {x : ℝ} (hx : x ∈ [[z.re, w.re]]) :
    (x : ℂ) + (w.im : ℂ) * Complex.I ∈ rectMinus z w p := by
  refine ⟨?_, ?_⟩
  · rw [Complex.mem_reProdIm]
    refine ⟨by simpa using hx, ?_⟩
    simp
  · intro h
    have := congrArg Complex.im (Set.mem_singleton_iff.mp h)
    simp at this
    linarith [hp.2]

lemma mem_rectMinus_right (hp : p.re ∈ Ioo z.re w.re) {y : ℝ} (hy : y ∈ [[z.im, w.im]]) :
    (w.re : ℂ) + (y : ℂ) * Complex.I ∈ rectMinus z w p := by
  refine ⟨?_, ?_⟩
  · rw [Complex.mem_reProdIm]
    refine ⟨by simp, by simpa using hy⟩
  · intro h
    have := congrArg Complex.re (Set.mem_singleton_iff.mp h)
    simp at this
    linarith [hp.2]

lemma mem_rectMinus_left (hp : p.re ∈ Ioo z.re w.re) {y : ℝ} (hy : y ∈ [[z.im, w.im]]) :
    (z.re : ℂ) + (y : ℂ) * Complex.I ∈ rectMinus z w p := by
  refine ⟨?_, ?_⟩
  · rw [Complex.mem_reProdIm]
    refine ⟨by simp, by simpa using hy⟩
  · intro h
    have := congrArg Complex.re (Set.mem_singleton_iff.mp h)
    simp at this
    linarith [hp.1]

/-- The four edge integrals of a function continuous on the rectangle minus an interior point. -/
lemma edges_intervalIntegrable {f : ℂ → ℂ} (hre : p.re ∈ Ioo z.re w.re)
    (him : p.im ∈ Ioo z.im w.im) (hf : ContinuousOn f (rectMinus z w p)) :
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (z.im : ℂ) * Complex.I)) volume z.re w.re ∧
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (w.im : ℂ) * Complex.I)) volume z.re w.re ∧
    IntervalIntegrable (fun y : ℝ => f ((w.re : ℂ) + (y : ℂ) * Complex.I)) volume z.im w.im ∧
    IntervalIntegrable (fun y : ℝ => f ((z.re : ℂ) + (y : ℂ) * Complex.I)) volume z.im w.im := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hf.comp (by fun_prop : Continuous fun x : ℝ =>
      (x : ℂ) + (z.im : ℂ) * Complex.I).continuousOn
      fun x hx => mem_rectMinus_bottom him hx).intervalIntegrable
  · exact (hf.comp (by fun_prop : Continuous fun x : ℝ =>
      (x : ℂ) + (w.im : ℂ) * Complex.I).continuousOn
      fun x hx => mem_rectMinus_top him hx).intervalIntegrable
  · exact (hf.comp (by fun_prop : Continuous fun y : ℝ =>
      (w.re : ℂ) + (y : ℂ) * Complex.I).continuousOn
      fun y hy => mem_rectMinus_right hre hy).intervalIntegrable
  · exact (hf.comp (by fun_prop : Continuous fun y : ℝ =>
      (z.re : ℂ) + (y : ℂ) * Complex.I).continuousOn
      fun y hy => mem_rectMinus_left hre hy).intervalIntegrable

lemma boundaryIntegral_add_of_continuousOn {f g : ℂ → ℂ} (hre : p.re ∈ Ioo z.re w.re)
    (him : p.im ∈ Ioo z.im w.im) (hf : ContinuousOn f (rectMinus z w p))
    (hg : ContinuousOn g (rectMinus z w p)) :
    boundaryIntegral (fun s => f s + g s) z w = boundaryIntegral f z w + boundaryIntegral g z w
      := by
  obtain ⟨f1, f2, f3, f4⟩ := edges_intervalIntegrable hre him hf
  obtain ⟨g1, g2, g3, g4⟩ := edges_intervalIntegrable hre him hg
  exact Zeta32.Analytic.Contour.boundaryIntegral_add f g z w f1 g1 f2 g2 f3 g3 f4 g4

/-- **Fundamental theorem of calculus on a rectangle**: the boundary integral of a
derivative vanishes. -/
theorem boundaryIntegral_eq_zero_of_hasDerivAt {G f : ℂ → ℂ} (hre : p.re ∈ Ioo z.re w.re)
    (him : p.im ∈ Ioo z.im w.im) (hG : ∀ t ∈ rectMinus z w p, HasDerivAt G (f t) t)
    (hf : ContinuousOn f (rectMinus z w p)) :
    boundaryIntegral f z w = 0 := by
  obtain ⟨f1, f2, f3, f4⟩ := edges_intervalIntegrable hre him hf
  have hh : ∀ c : ℝ, (∀ x ∈ [[z.re, w.re]], (x : ℂ) + (c : ℂ) * Complex.I ∈ rectMinus z w p) →
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I)) volume z.re w.re →
      (∫ x : ℝ in z.re..w.re, f ((x : ℂ) + (c : ℂ) * Complex.I)) =
        G ((w.re : ℂ) + (c : ℂ) * Complex.I) - G ((z.re : ℂ) + (c : ℂ) * Complex.I) := by
    intro c hmem hint
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => G ((x : ℂ) + (c : ℂ) * Complex.I)) (fun x hx => ?_) hint
    have h1 : HasDerivAt (fun u : ℂ => u + (c : ℂ) * Complex.I) 1 (x : ℂ) :=
      (hasDerivAt_id _).add_const _
    have h2 := (hG _ (hmem x hx)).comp (x : ℂ) h1
    simpa using h2.comp_ofReal
  have hv : ∀ a : ℝ, (∀ y ∈ [[z.im, w.im]], (a : ℂ) + (y : ℂ) * Complex.I ∈ rectMinus z w p) →
      IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) volume z.im w.im →
      Complex.I • (∫ y : ℝ in z.im..w.im, f ((a : ℂ) + (y : ℂ) * Complex.I)) =
        G ((a : ℂ) + (w.im : ℂ) * Complex.I) - G ((a : ℂ) + (z.im : ℂ) * Complex.I) := by
    intro a hmem hint
    rw [smul_eq_mul, mul_comm, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => G ((a : ℂ) + (y : ℂ) * Complex.I)) (fun y hy => ?_) (hint.mul_const _)
    have h1 : HasDerivAt (fun u : ℂ => (a : ℂ) + u * Complex.I) Complex.I (y : ℂ) := by
      simpa using ((hasDerivAt_id (y : ℂ)).mul_const Complex.I).const_add (a : ℂ)
    have h2 := (hG _ (hmem y hy)).comp (y : ℂ) h1
    exact h2.comp_ofReal
  unfold Zeta32.Analytic.Contour.boundaryIntegral
  rw [hh z.im (fun x hx => mem_rectMinus_bottom him hx) f1,
    hh w.im (fun x hx => mem_rectMinus_top him hx) f2,
    hv w.re (fun y hy => mem_rectMinus_right hre hy) f3,
    hv z.re (fun y hy => mem_rectMinus_left hre hy) f4]
  ring

end Edges

/-! ### The rectangle `[1/2, 3/2] × [-T, T]` -/

/-- Lower-left corner. -/
@[expose]
def zT (T : ℝ) : ℂ := ⟨1/2, -T⟩
/-- Upper-right corner. -/
@[expose]
def wT (T : ℝ) : ℂ := ⟨3/2, T⟩

lemma one_re_mem (T : ℝ) : (1 : ℂ).re ∈ Ioo (zT T).re (wT T).re := by
  simp only [zT, wT, Complex.one_re]; constructor <;> norm_num

lemma one_im_mem {T : ℝ} (hT : 0 < T) : (1 : ℂ).im ∈ Ioo (zT T).im (wT T).im := by
  simp only [zT, wT, Complex.one_im]; constructor <;> linarith

lemma rect_subset_strip (T : ℝ) :
    ([[(zT T).re, (wT T).re]] ×ℂ [[(zT T).im, (wT T).im]]) ⊆ strip := by
  intro t ht
  rw [Complex.mem_reProdIm] at ht
  obtain ⟨h1, _⟩ := ht
  simp only [zT, wT] at h1
  rw [Set.uIcc_of_le (by norm_num)] at h1
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

lemma rectMinus_subset (T : ℝ) : rectMinus (zT T) (wT T) 1 ⊆ strip \ {1} :=
  fun _ ht => ⟨rect_subset_strip T ht.1, ht.2⟩

lemma sin_ne_zero_of_mem_rectMinus {T : ℝ} {t : ℂ} (ht : t ∈ rectMinus (zT T) (wT T) 1) :
    Complex.sin ((Real.pi : ℂ) * t) ≠ 0 :=
  sin_pi_ne_zero_of_mem_strip (rectMinus_subset T ht).1 (rectMinus_subset T ht).2

/-- `S₁(t) = sin(πt)/(t-1)`, extended holomorphically by `S₁(1) = -π`. -/
def sinSlope : ℂ → ℂ := dslope (fun u : ℂ => Complex.sin ((Real.pi : ℂ) * u)) 1

lemma sin_eq_mul_sinSlope (t : ℂ) :
    Complex.sin ((Real.pi : ℂ) * t) = (t - 1) * sinSlope t := by
  have h := sub_smul_dslope (fun u : ℂ => Complex.sin ((Real.pi : ℂ) * u)) 1 t
  have hs : Complex.sin ((Real.pi : ℂ) * 1) = 0 := by
    rw [mul_one]; exact Complex.sin_pi
  rw [smul_eq_mul, hs, sub_zero] at h
  exact h.symm

lemma sinSlope_one : sinSlope 1 = -(Real.pi : ℂ) := by
  unfold sinSlope
  rw [dslope_same, (hasDerivAt_sin_pi 1).deriv, mul_one, Complex.cos_pi]
  ring

lemma differentiable_sinSlope : Differentiable ℂ sinSlope := by
  have h : DifferentiableOn ℂ (fun u : ℂ => Complex.sin ((Real.pi : ℂ) * u)) univ :=
    (Differentiable.differentiableOn (by fun_prop))
  exact differentiableOn_univ.mp ((Complex.differentiableOn_dslope univ_mem).mpr h)

lemma sinSlope_ne_zero {t : ℂ} (ht : t ∈ strip) : sinSlope t ≠ 0 := by
  by_cases h1 : t = 1
  · rw [h1, sinSlope_one]
    exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  · intro h
    apply sin_pi_ne_zero_of_mem_strip ht h1
    rw [sin_eq_mul_sinSlope, h, mul_zero]

/-- **Rectangle identity.** -/
theorem boundaryIntegral_mul_Kc {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F strip) {T : ℝ}
    (hT : 0 < T) :
    boundaryIntegral (fun t => F t * Kc t) (zT T) (wT T) =
      2 * (Real.pi : ℂ) * Complex.I * deriv F 1 := by
  have hre := one_re_mem T
  have him := one_im_mem hT
  set F' := deriv F with hF'def
  have hF'd : DifferentiableOn ℂ F' strip := hF.deriv isOpen_strip
  have hFc : ContinuousOn F (rectMinus (zT T) (wT T) 1) :=
    hF.continuousOn.mono fun t ht => (rectMinus_subset T ht).1
  have hF'c : ContinuousOn F' (rectMinus (zT T) (wT T) 1) :=
    hF'd.continuousOn.mono fun t ht => (rectMinus_subset T ht).1
  have hKc : ContinuousOn Kc (rectMinus (zT T) (wT T) 1) := fun t ht =>
    (continuousAt_Kc (sin_ne_zero_of_mem_rectMinus ht)).continuousWithinAt
  have hcotc : ContinuousOn cotK (rectMinus (zT T) (wT T) 1) := fun t ht =>
    (continuousAt_cotK (sin_ne_zero_of_mem_rectMinus ht)).continuousWithinAt
  -- Step A: FTC for `F · π cot(πt)`.
  have hA : boundaryIntegral (fun t => F' t * cotK t + -(F t * Kc t)) (zT T) (wT T) = 0 := by
    apply boundaryIntegral_eq_zero_of_hasDerivAt (G := fun t => F t * cotK t) hre him
    · intro t ht
      have hs := sin_ne_zero_of_mem_rectMinus ht
      have hFt : HasDerivAt F (F' t) t :=
        (hF.differentiableAt (isOpen_strip.mem_nhds (rectMinus_subset T ht).1)).hasDerivAt
      convert hFt.mul (hasDerivAt_cotK hs) using 1
      ring
    · exact (hF'c.mul hcotc).add (hFc.mul hKc).neg
  have hsplit : boundaryIntegral (fun t => F' t * cotK t + -(F t * Kc t)) (zT T) (wT T) =
      boundaryIntegral (fun t => F' t * cotK t) (zT T) (wT T) +
        boundaryIntegral (fun t => -(F t * Kc t)) (zT T) (wT T) :=
    boundaryIntegral_add_of_continuousOn (f := fun t => F' t * cotK t)
      (g := fun t => -(F t * Kc t)) hre him (hF'c.mul hcotc) (hFc.mul hKc).neg
  -- Step B: the simple pole of `F' · π cot(πt)`.
  set Ψ : ℂ → ℂ := fun t => F' t * ((Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * t)) /
    sinSlope t with hΨ
  have hΨd : DifferentiableOn ℂ Ψ strip := by
    refine (hF'd.mul ?_).div differentiable_sinSlope.differentiableOn
      fun t ht => sinSlope_ne_zero ht
    exact (Differentiable.differentiableOn (by fun_prop))
  set Ψ₁ := dslope Ψ 1 with hΨ₁
  have hΨ₁d : DifferentiableOn ℂ Ψ₁ strip :=
    (Complex.differentiableOn_dslope (isOpen_strip.mem_nhds one_mem_strip)).mpr hΨd
  have hΨ1 : Ψ 1 = F' 1 := by
    simp only [hΨ, sinSlope_one, mul_one, Complex.cos_pi]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  have hB : ∀ t : ℂ, t ≠ 1 → F' t * cotK t = Ψ 1 * (t - 1)⁻¹ + Ψ₁ t := by
    intro t ht
    have h1 : t - 1 ≠ 0 := sub_ne_zero.mpr ht
    have hs := sub_smul_dslope Ψ 1 t
    rw [smul_eq_mul] at hs
    have hΨt : Ψ t = Ψ 1 + (t - 1) * Ψ₁ t := by rw [hΨ₁, hs]; ring
    have hcot : F' t * cotK t = Ψ t / (t - 1) := by
      simp only [cotK, hΨ, sin_eq_mul_sinSlope t]
      by_cases hS : sinSlope t = 0
      · simp [hS]
      field_simp
    rw [hcot, hΨt]
    field_simp
  have hcongr : boundaryIntegral (fun t => F' t * cotK t) (zT T) (wT T) =
      boundaryIntegral (fun t => Ψ 1 * (t - 1)⁻¹ + Ψ₁ t) (zT T) (wT T) := by
    have hne : ∀ t ∈ rectMinus (zT T) (wT T) 1, F' t * cotK t = Ψ 1 * (t - 1)⁻¹ + Ψ₁ t :=
      fun t ht => hB t ht.2
    unfold Zeta32.Analytic.Contour.boundaryIntegral
    congr 1
    · congr 1
      · congr 1
        · exact intervalIntegral.integral_congr fun x hx =>
            hne _ (mem_rectMinus_bottom him hx)
        · exact intervalIntegral.integral_congr fun x hx =>
            hne _ (mem_rectMinus_top him hx)
      · congr 1
        exact intervalIntegral.integral_congr fun y hy => hne _ (mem_rectMinus_right hre hy)
    · congr 1
      exact intervalIntegral.integral_congr fun y hy => hne _ (mem_rectMinus_left hre hy)
  have hinvc : ContinuousOn (fun t : ℂ => (t - 1)⁻¹) (rectMinus (zT T) (wT T) 1) :=
    fun t ht => ((continuousAt_id.sub continuousAt_const).inv₀
      (sub_ne_zero.mpr ht.2)).continuousWithinAt
  obtain ⟨p1, p2, p3, p4⟩ := edges_intervalIntegrable hre him hinvc
  have hΨ₁c : ContinuousOn Ψ₁ (rectMinus (zT T) (wT T) 1) :=
    hΨ₁d.continuousOn.mono fun t ht => (rectMinus_subset T ht).1
  obtain ⟨h1, h2, h3, h4⟩ := edges_intervalIntegrable hre him hΨ₁c
  have hpole : boundaryIntegral (fun t => Ψ 1 * (t - 1)⁻¹ + Ψ₁ t) (zT T) (wT T) =
      2 * (Real.pi : ℂ) * Complex.I * Ψ 1 :=
    Zeta32.Analytic.Contour.boundaryIntegral_single_pole
      (Zeta32.Analytic.Contour.boundaryIntegral_inv_sub_eq_two_pi_I hre him)
      (hΨ₁d.continuousOn.mono (rect_subset_strip T)) ∅ countable_empty
      (fun x hx => hΨ₁d.differentiableAt (isOpen_strip.mem_nhds
        (rect_subset_strip T (by
          obtain ⟨hx, -⟩ := hx
          rw [Complex.mem_reProdIm] at hx ⊢
          exact ⟨Ioo_subset_Icc_self hx.1, Ioo_subset_Icc_self hx.2⟩))))
      p1 p2 p3 p4 h1 h2 h3 h4
  rw [hA, hcongr, hpole, hΨ1] at hsplit
  have : boundaryIntegral (fun t => -(F t * Kc t)) (zT T) (wT T) =
      -boundaryIntegral (fun t => F t * Kc t) (zT T) (wT T) := by
    have h := Zeta32.Analytic.Contour.boundaryIntegral_const_mul (-1) (fun t => F t * Kc t) (zT
      T) (wT T)
    simpa using h
  rw [this] at hsplit
  linear_combination hsplit

end

end Zeta32.Analytic.Contour

end
