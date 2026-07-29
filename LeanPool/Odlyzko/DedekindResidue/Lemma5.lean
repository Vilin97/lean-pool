/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
/-
DedekindResidue: B–F Lemma 5 (Landau–Stark) — the zero-sum estimate
`Σ_ρ 1/(¼+γ_ρ²) ≤ (2σ−1)(log Δ_K + 2/(σ−1) − d_{K,σ})`.

Route (B–F lines 523–562 + the footnote at 549–553): apply the Weil–Poitou explicit
formula to the **Landau–Stark test function** `F_h(x) = e^{−h|x|}` (`h = σ − 1/2`),
whose transform is the exact rational `Φ(z) = 1/(h−(z−1/2)) + 1/(h+(z−1/2))`.
The zero side is `Σ_ρ m_ρ·2h/(h²+γ_ρ²)`, the prime side collapses to the Dirichlet
series of `−ζ'_K/ζ_K(σ)`, and the archimedean side evaluates in digamma values.
This file: the admissibility suite for `F_h` (every hypothesis of
`weil_explicit_formula`), its packaged instance, and the eq:Stark display.
-/
module

public import Mathlib
public import LeanPool.Odlyzko.DedekindResidue.Lemma4

@[expose] public section

namespace DedekindResidue

open Complex NumberField Filter MeasureTheory Real
open scoped ENNReal NNReal

variable (K : Type*) [Field K] [NumberField K]

/-! ### The Landau–Stark test function `F_h(x) = e^{−h|x|}` -/

/-- **The Landau–Stark test function** `F_h(x) = e^{−h|x|}` (B–F footnote, line 551):
the two-sided exponential whose Poitou transform is `2h/(h² − (z−1/2)²)`. -/
noncomputable def expTest (h : ℝ) (x : ℝ) : ℂ := ((Real.exp (-h * |x|) : ℝ) : ℂ)

theorem expTest_neg (h x : ℝ) : expTest h (-x) = expTest h x := by
  unfold expTest
  rw [abs_neg]

theorem expTest_zero (h : ℝ) : expTest h 0 = 1 := by
  unfold expTest
  simp

theorem continuous_expTest (h : ℝ) : Continuous (expTest h) := by
  unfold expTest
  fun_prop

theorem norm_expTest (h x : ℝ) : ‖expTest h x‖ = Real.exp (-h * |x|) := by
  unfold expTest
  rw [Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]

/-- **`hF` at the Landau–Stark function.** -/
theorem integrable_expTest {h : ℝ} (hh : 0 < h) : Integrable (expTest h) := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-h * |x|)) :=
    integrable_exp_neg_mul_abs hh
  exact h1.ofReal

/-- **`hFa` at the Landau–Stark function**: the `c`-weighted function is integrable
for `|c| < h`. -/
theorem integrable_expTest_mul_exp {h : ℝ} {c : ℝ} (hc : |c| < h) :
    Integrable (fun x : ℝ => expTest h x * ((Real.exp (c * x) : ℝ) : ℂ)) := by
  refine Integrable.mono'
    (g := fun x : ℝ => Real.exp (-(h - |c|) * |x|))
    (integrable_exp_neg_mul_abs (by linarith)) ?_ ?_
  · exact ((continuous_expTest h).mul
      (Complex.continuous_ofReal.comp (by fun_prop))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [norm_mul, norm_expTest, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
      ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 : c * x ≤ |c| * |x| := by
      calc c * x ≤ |c * x| := le_abs_self _
        _ = |c| * |x| := abs_mul c x
    nlinarith [abs_nonneg x]

/-! ### Bounded variation of the weighted Landau–Stark function -/

/-- On the positive ray, `F_h·e^{cx} = e^{(c−h)x}` has an integrable derivative,
hence bounded variation. -/
theorem expTest_mul_exp_bv_Ici {h : ℝ} {c : ℝ} (hc : c < h) :
    BoundedVariationOn (fun x : ℝ => expTest h x * ((Real.exp (c * x) : ℝ) : ℂ))
      (Set.Ici 0) := by
  refine boundedVariationOn_of_deriv_integrable
    (f' := fun x : ℝ => (((c - h) * Real.exp ((c - h) * x) : ℝ) : ℂ))
    Set.ordConnected_Ici
    (Continuous.continuousOn ((continuous_expTest h).mul
      (Complex.continuous_ofReal.comp (by fun_prop)))) ?_ ?_
  · rw [interior_Ici]
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    have hev : (fun y : ℝ => expTest h y * ((Real.exp (c * y) : ℝ) : ℂ))
        =ᶠ[nhds x] fun y : ℝ => ((Real.exp ((c - h) * y) : ℝ) : ℂ) := by
      filter_upwards [eventually_gt_nhds hx0] with y hy
      unfold expTest
      rw [abs_of_pos hy, ← Complex.ofReal_mul, ← Real.exp_add,
        show -h * y + c * y = (c - h) * y by ring]
    have hbase : HasDerivAt (fun y : ℝ => ((Real.exp ((c - h) * y) : ℝ) : ℂ))
        (((c - h) * Real.exp ((c - h) * x) : ℝ) : ℂ) x := by
      have h1 := (((hasDerivAt_id x).const_mul (c - h)).exp).ofReal_comp
      refine h1.congr_deriv ?_
      simp only [id_eq]
      push_cast
      ring
    exact hbase.congr_of_eventuallyEq hev
  · have h1 : IntegrableOn (fun x : ℝ => Real.exp ((c - h) * x)) (Set.Ici 0) := by
      have h2 := exp_neg_integrableOn_Ioi (0:ℝ) (show 0 < -(c - h) by linarith)
      have h3 : IntegrableOn (fun x : ℝ => Real.exp ((c - h) * x)) (Set.Ioi 0) := by
        refine h2.congr_fun (fun x _ => ?_) measurableSet_Ioi
        simp only [neg_neg]
      exact h3.congr_set_ae (Ioi_ae_eq_Ici (a := (0:ℝ))).symm
    have h4 : IntegrableOn
        (fun x : ℝ => (((c - h) * Real.exp ((c - h) * x) : ℝ) : ℂ)) (Set.Ici 0) :=
      (h1.const_mul (c - h)).ofReal
    exact h4

/-- **BV of the weighted Landau–Stark function on the line** for `|c| < h`. -/
theorem boundedVariationOn_expTest_mul_exp {h : ℝ} {c : ℝ}
    (hcl : -h < c) (hcr : c < h) :
    BoundedVariationOn (fun x : ℝ => expTest h x * ((Real.exp (c * x) : ℝ) : ℂ))
      Set.univ := by
  have hpos := expTest_mul_exp_bv_Ici hcr
  have hneg' := expTest_mul_exp_bv_Ici (h := h) (c := -c) (by linarith)
  have hcomp : (fun x : ℝ => expTest h x * ((Real.exp (c * x) : ℝ) : ℂ))
      = (fun x : ℝ => expTest h x * ((Real.exp ((-c) * x) : ℝ) : ℂ))
        ∘ (fun x : ℝ => -x) := by
    funext x
    show expTest h x * ((Real.exp (c * x) : ℝ) : ℂ)
        = expTest h (-x) * ((Real.exp ((-c) * (-x)) : ℝ) : ℂ)
    rw [expTest_neg, neg_mul_neg]
  have hIic : eVariationOn
      (fun x : ℝ => expTest h x * ((Real.exp (c * x) : ℝ) : ℂ)) (Set.Iic 0) ≠ ⊤ := by
    rw [hcomp]
    refine ne_top_of_le_ne_top hneg' (eVariationOn.comp_le_of_antitoneOn _ _ ?_ ?_)
    · exact fun x _ y _ hxy => neg_le_neg hxy
    · exact fun x hx => Set.mem_Ici.mpr (neg_nonneg.mpr hx)
  unfold BoundedVariationOn at hpos ⊢
  rw [show (Set.univ : Set ℝ) = Set.Iic 0 ∪ Set.Ici 0 from
      (Set.Iic_union_Ici (a := (0:ℝ))).symm,
    eVariationOn.union _ ⟨Set.self_mem_Iic, fun x hx => hx⟩
      ⟨Set.self_mem_Ici, fun x hx => hx⟩]
  exact ENNReal.add_ne_top.mpr ⟨hIic, hpos⟩

/-- **BV of the Landau–Stark function on the line.** -/
theorem boundedVariationOn_expTest {h : ℝ} (hh : 0 < h) :
    BoundedVariationOn (expTest h) Set.univ := by
  have h1 := boundedVariationOn_expTest_mul_exp (h := h) (c := 0) (by linarith) hh
  have h2 : (fun x : ℝ => expTest h x * ((Real.exp (0 * x) : ℝ) : ℂ)) = expTest h := by
    funext x
    rw [zero_mul, Real.exp_zero, Complex.ofReal_one, mul_one]
  rwa [h2] at h1

/-- **`hre` at the Landau–Stark function.** -/
theorem locallyBoundedVariationOn_expTest_re {h : ℝ} (hh : 0 < h) :
    LocallyBoundedVariationOn (fun u : ℝ => (expTest h u).re) Set.univ :=
  (lipschitzWith_complex_re.comp_boundedVariationOn
    (boundedVariationOn_expTest hh)).locallyBoundedVariationOn

/-- **`him` at the Landau–Stark function.** -/
theorem locallyBoundedVariationOn_expTest_im {h : ℝ} (hh : 0 < h) :
    LocallyBoundedVariationOn (fun u : ℝ => (expTest h u).im) Set.univ :=
  (lipschitzWith_complex_im.comp_boundedVariationOn
    (boundedVariationOn_expTest hh)).locallyBoundedVariationOn

/-- **`hGre` at the Landau–Stark function** (`c = 1/2+a < h`). -/
theorem locallyBoundedVariationOn_expTest_mul_exp_re {h : ℝ} {a : ℝ}
    (ha : 0 < a) (hah : 1/2 + a < h) :
    LocallyBoundedVariationOn (fun x : ℝ =>
      ((expTest h x * ((Real.exp ((1/2 + a) * x) : ℝ) : ℂ))).re) Set.univ :=
  (lipschitzWith_complex_re.comp_boundedVariationOn
    (boundedVariationOn_expTest_mul_exp (by linarith) hah)).locallyBoundedVariationOn

/-- **`hGim` at the Landau–Stark function.** -/
theorem locallyBoundedVariationOn_expTest_mul_exp_im {h : ℝ} {a : ℝ}
    (ha : 0 < a) (hah : 1/2 + a < h) :
    LocallyBoundedVariationOn (fun x : ℝ =>
      ((expTest h x * ((Real.exp ((1/2 + a) * x) : ℝ) : ℂ))).im) Set.univ :=
  (lipschitzWith_complex_im.comp_boundedVariationOn
    (boundedVariationOn_expTest_mul_exp (by linarith) hah)).locallyBoundedVariationOn

/-! ### The divided difference `(F_h(0) − F_h(x))/x` -/

/-- The divided difference of the Landau–Stark function is bounded by `h`
(mean value bound `1 − e^{−t} ≤ t`). -/
theorem norm_expTest_diffQuot_le {h : ℝ} (hh : 0 < h) (x : ℝ) :
    ‖(expTest h 0 - expTest h x)/(x:ℂ)‖ ≤ h := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [Complex.ofReal_zero, div_zero, norm_zero]
    linarith
  · rw [expTest_zero, norm_div, Complex.norm_real, Real.norm_eq_abs]
    unfold expTest
    rw [show (1 : ℂ) - ((Real.exp (-h * |x|) : ℝ) : ℂ)
        = (((1 - Real.exp (-h * |x|)) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    have hexple : Real.exp (-h * |x|) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have h0 := abs_pos.mpr hx
      nlinarith
    rw [abs_of_nonneg (by linarith)]
    rw [div_le_iff₀ (abs_pos.mpr hx)]
    have h2 := Real.add_one_le_exp (-(h * |x|))
    have h3 : -h * |x| = -(h * |x|) := by ring
    rw [h3]
    linarith

/-- The divided difference `(F_h(0) − F_h(x))/x` is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_expTest_diffQuot (h : ℝ) :
    AEStronglyMeasurable (fun x : ℝ => (expTest h 0 - expTest h x)/(x:ℂ))
      (volume : Measure ℝ) := by
  refine AEStronglyMeasurable.congr
    (f := fun x : ℝ => (expTest h 0 - expTest h x) * ((x:ℂ))⁻¹) ?_ ?_
  · exact (aestronglyMeasurable_const.sub
      (continuous_expTest h).aestronglyMeasurable).mul
      ((Complex.measurable_ofReal.inv).aestronglyMeasurable)
  · refine Filter.Eventually.of_forall (fun x => ?_)
    show (expTest h 0 - expTest h x) * ((x:ℂ))⁻¹ = (expTest h 0 - expTest h x)/(x:ℂ)
    rw [div_eq_mul_inv]

/-- **`hFdiv` at the Landau–Stark function**: the divided difference is integrable
on the window. -/
theorem integrableOn_expTest_diffQuot_window {h : ℝ} (hh : 0 < h) :
    IntegrableOn (fun x : ℝ => (expTest h 0 - expTest h x)/(x:ℂ))
      (Set.Ioc (-1) 1) := by
  have hmeas := aestronglyMeasurable_expTest_diffQuot h
  refine Integrable.mono' (g := fun _ : ℝ => h) ?_ hmeas.restrict ?_
  · exact integrableOn_const (by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top.ne)
  · exact Filter.Eventually.of_forall (fun x => norm_expTest_diffQuot_le hh x)

/-- **`hFdiv2` at the Landau–Stark function**: the divided difference is
square-integrable on the line (`≤ h` near `0`, `O(1/|x|)` beyond). -/
theorem memLp_two_expTest_diffQuot {h : ℝ} (hh : 0 < h) :
    MemLp (fun x : ℝ => (expTest h 0 - expTest h x)/(x:ℂ)) 2 (volume : Measure ℝ) := by
  have hmeas := aestronglyMeasurable_expTest_diffQuot h
  have hfar : ∀ x : ℝ, x ≠ 0 → ‖(expTest h 0 - expTest h x)/(x:ℂ)‖ ≤ 1/|x| := by
    intro x hx
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    rw [div_le_div_iff_of_pos_right (abs_pos.mpr hx)]
    have h1 : Real.exp (-h * |x|) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have h0 := abs_nonneg x
      nlinarith [hh, h0]
    have h2 := Real.exp_pos (-h * |x|)
    rw [expTest_zero]
    unfold expTest
    rw [show (1 : ℂ) - ((Real.exp (-h * |x|) : ℝ) : ℂ)
        = (((1 - Real.exp (-h * |x|)) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hraypos : IntegrableOn
      (fun x : ℝ => ‖(expTest h 0 - expTest h x)/(x:ℂ)‖^2) (Set.Ioi 1) := by
    refine Integrable.mono' (g := fun x : ℝ => x^(-2 : ℝ))
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos) ?_ ?_
    · exact ((hmeas.norm.pow 2).restrict)
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall (fun x hx => ?_))
      rw [Set.mem_Ioi] at hx
      have hx0 : (0:ℝ) < x := lt_trans one_pos hx
      have h1 := hfar x hx0.ne'
      rw [abs_of_pos hx0] at h1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg hx0.le,
        show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      calc ‖(expTest h 0 - expTest h x)/(x:ℂ)‖^2 ≤ (1/x)^2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = (x^2)⁻¹ := by
            rw [div_pow, one_pow, one_div]
  have hwindow : IntegrableOn
      (fun x : ℝ => ‖(expTest h 0 - expTest h x)/(x:ℂ)‖^2) (Set.Ioc (-1) 1) := by
    refine Integrable.mono' (g := fun _ : ℝ => h^2) ?_
      ((hmeas.norm.pow 2).restrict) ?_
    · exact integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top.ne)
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_expTest_diffQuot_le hh x) 2
  have hrayneg : IntegrableOn
      (fun x : ℝ => ‖(expTest h 0 - expTest h x)/(x:ℂ)‖^2) (Set.Iic (-1)) := by
    have A : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
    have hmap : (volume : Measure ℝ).restrict (Set.Iic (-1))
        = Measure.map (fun x : ℝ => -x)
            ((volume : Measure ℝ).restrict (Set.Ici 1)) := by
      rw [show Set.Ici (1:ℝ) = (fun x : ℝ => -x) ⁻¹' (Set.Iic (-1)) by
          ext x
          simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
          constructor <;> intro hy <;> linarith,
        ← Measure.restrict_map A.measurable measurableSet_Iic,
        Measure.map_neg_eq_self (volume : Measure ℝ)]
    rw [IntegrableOn, hmap, A.integrable_map_iff]
    have hIci : IntegrableOn
        (fun x : ℝ => ‖(expTest h 0 - expTest h x)/(x:ℂ)‖^2) (Set.Ici 1) :=
      hraypos.congr_set_ae (Ioi_ae_eq_Ici (a := (1:ℝ))).symm
    refine hIci.congr (Filter.Eventually.of_forall (fun x => ?_))
    show ‖(expTest h 0 - expTest h x)/(x:ℂ)‖^2
        = ‖(expTest h 0 - expTest h (-x))/((-x : ℝ):ℂ)‖^2
    rw [expTest_neg]
    have hnorm : ‖(expTest h 0 - expTest h x)/(x:ℂ)‖
        = ‖(expTest h 0 - expTest h x)/((-x : ℝ):ℂ)‖ := by
      rw [norm_div, norm_div]
      congr 1
      rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_neg]
    rw [hnorm]
  have hcover : (Set.univ : Set ℝ) = Set.Iic (-1) ∪ (Set.Ioc (-1) 1 ∪ Set.Ioi 1) := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Ioc, Set.mem_Ioi,
      true_iff]
    rcases le_or_gt x (-1) with h1 | h1
    · exact Or.inl h1
    · rcases le_or_gt x 1 with h2 | h2
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact Or.inr (Or.inr h2)
  rw [← MeasureTheory.integrableOn_univ, hcover]
  exact hrayneg.union (hwindow.union hraypos)

/-! ### The closed form of the transform: `Φ_{F_h}(z) = 1/(h−(z−1/2)) + 1/(h+(z−1/2))` -/

/-- The complex exponential is integrable on the right ray when its rate has
positive real part. -/
theorem integrableOn_Ioi_cexp_neg {c : ℂ} (hc : 0 < c.re) :
    MeasureTheory.IntegrableOn (fun x : ℝ => Complex.exp (-(c * x)))
      (Set.Ioi (0:ℝ)) := by
  refine Integrable.mono' (g := fun x : ℝ => Real.exp (-c.re * x))
    (exp_neg_integrableOn_Ioi 0 hc) ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).restrict
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr (le_of_eq ?_)
    simp [Complex.mul_re]

/-- `∫_0^∞ e^{−cx} dx = 1/c` for `Re c > 0`. -/
theorem integral_Ioi_cexp_neg {c : ℂ} (hc : 0 < c.re) :
    ∫ x in Set.Ioi (0:ℝ), Complex.exp (-(c * x)) = 1/c := by
  have hc0 : c ≠ 0 := fun hc0 => by
    rw [hc0] at hc
    simp at hc
  have hderiv : ∀ x ∈ Set.Ioi (0:ℝ),
      HasDerivAt (fun y : ℝ => -Complex.exp (-(c * y))/c)
        (Complex.exp (-(c * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => ((y:ℝ):ℂ)) (((1:ℝ)):ℂ) x :=
      (hasDerivAt_id x).ofReal_comp
    have h2 : HasDerivAt (fun y : ℝ => -(c * ((y:ℝ):ℂ))) (-c) x := by
      have h2a := h1.const_mul (-c)
      have h2b : HasDerivAt (fun y : ℝ => (-c) * ((y:ℝ):ℂ)) (-c) x := by
        simpa using h2a
      exact h2b.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun y => by ring))
    have h3 : HasDerivAt (fun y : ℝ => Complex.exp (-(c * y)))
        (Complex.exp (-(c * x)) * -c) x := h2.cexp
    have h4 := (h3.neg).div_const c
    refine h4.congr_deriv ?_
    field_simp
  have hlim : Filter.Tendsto (fun y : ℝ => -Complex.exp (-(c * y))/c) atTop
      (nhds 0) := by
    refine squeeze_zero_norm (a := fun y : ℝ => Real.exp (-c.re * y) / ‖c‖)
      (fun y => le_of_eq ?_) ?_
    · rw [norm_div, norm_neg, Complex.norm_exp]
      simp [Complex.mul_re]
    · have h5 : Filter.Tendsto (fun y : ℝ => Real.exp (-c.re * y)) atTop
          (nhds 0) :=
        Real.tendsto_exp_atBot.comp
          (Tendsto.const_mul_atTop_of_neg (by linarith : -c.re < 0) tendsto_id)
      have h6 := h5.div_const ‖c‖
      rw [zero_div] at h6
      exact h6
  have hcont : ContinuousWithinAt (fun y : ℝ => -Complex.exp (-(c * y))/c)
      (Set.Ici 0) 0 := by
    refine Continuous.continuousWithinAt ?_
    fun_prop
  have hkey := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    hcont hderiv (integrableOn_Ioi_cexp_neg hc) hlim
  rw [hkey]
  push_cast
  rw [mul_zero, neg_zero, Complex.exp_zero]
  field_simp
  ring

/-- Reflecting a left-ray integral. -/
theorem integral_Iio_comp_neg (G : ℝ → ℂ) :
    ∫ x in Set.Iio (0:ℝ), G x = ∫ x in Set.Ioi (0:ℝ), G (-x) := by
  have A : MeasurableEmbedding fun x : ℝ => -x :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).restrict (Set.Iio (0:ℝ))
      = Measure.map (fun x : ℝ => -x) ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    rw [show Set.Ioi (0:ℝ) = (fun x : ℝ => -x) ⁻¹' (Set.Iio 0) by ext x; simp,
      ← Measure.restrict_map A.measurable measurableSet_Iio,
      Measure.map_neg_eq_self (volume : Measure ℝ)]
  rw [show (∫ x in Set.Iio (0:ℝ), G x)
      = ∫ x, G x ∂((volume : Measure ℝ).restrict (Set.Iio 0)) from rfl,
    hmap, A.integral_map]

/-- The weighted Landau–Stark kernel matches the pure exponential on the right
ray. -/
theorem expTest_kernel_eq_Ici {h : ℝ} (z : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    expTest h x * Complex.exp ((z - 1/2) * x)
      = Complex.exp (-(((h:ℂ) - (z - 1/2)) * x)) := by
  unfold expTest
  rw [abs_of_nonneg hx, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The closed form of the Poitou transform of `F_h`** on the convergence strip
`|Re z − 1/2| < h`:
`Φ_{F_h}(z) = 1/(h − (z−1/2)) + 1/(h + (z−1/2))`. -/
theorem paperPhi_expTest {h : ℝ} {z : ℂ} (hz : |z.re - 1/2| < h) :
    paperPhi (expTest h) z
      = 1/((h:ℂ) - (z - 1/2)) + 1/((h:ℂ) + (z - 1/2)) := by
  have habs := abs_lt.mp hz
  have hre1 : 0 < ((h:ℂ) - (z - 1/2)).re := by
    have he : (h:ℂ) - (z - 1/2) = ((h + 1/2 : ℝ) : ℂ) - z := by push_cast; ring
    rw [he, Complex.sub_re, Complex.ofReal_re]
    linarith [habs.2]
  have hre2 : 0 < ((h:ℂ) + (z - 1/2)).re := by
    have he : (h:ℂ) + (z - 1/2) = ((h - 1/2 : ℝ) : ℂ) + z := by push_cast; ring
    rw [he, Complex.add_re, Complex.ofReal_re]
    linarith [habs.1]
  have hEqIoi : ∀ x ∈ Set.Ioi (0:ℝ),
      expTest h x * Complex.exp ((z - 1/2) * x)
        = Complex.exp (-(((h:ℂ) - (z - 1/2)) * x)) :=
    fun x hx => expTest_kernel_eq_Ici z (le_of_lt hx)
  have hEqIoi' : ∀ x ∈ Set.Ioi (0:ℝ),
      expTest h (-x) * Complex.exp ((z - 1/2) * ((-x : ℝ) : ℂ))
        = Complex.exp (-(((h:ℂ) + (z - 1/2)) * x)) := by
    intro x hx
    rw [expTest_neg]
    unfold expTest
    rw [abs_of_nonneg (le_of_lt hx), Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hIci_int : MeasureTheory.IntegrableOn
      (fun x : ℝ => expTest h x * Complex.exp ((z - 1/2) * x)) (Set.Ici 0) :=
    ((integrableOn_Ioi_cexp_neg hre1).congr_fun
      (fun x hx => (hEqIoi x hx).symm) measurableSet_Ioi).congr_set_ae
      (Ioi_ae_eq_Ici (a := (0:ℝ))).symm
  have hIio_int : MeasureTheory.IntegrableOn
      (fun x : ℝ => expTest h x * Complex.exp ((z - 1/2) * x)) (Set.Iio 0) := by
    rw [integrableOn_Iio_comp_neg_iff]
    exact (integrableOn_Ioi_cexp_neg hre2).congr_fun
      (fun x hx => (hEqIoi' x hx).symm) measurableSet_Ioi
  have hIci_val : (∫ x in Set.Ici (0:ℝ), expTest h x * Complex.exp ((z - 1/2) * x))
      = 1/((h:ℂ) - (z - 1/2)) := by
    rw [← MeasureTheory.setIntegral_congr_set (Ioi_ae_eq_Ici (a := (0:ℝ))),
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEqIoi]
    have h1 := integral_Ioi_cexp_neg hre1
    rw [h1, one_div]
  have hIio_val : (∫ x in Set.Iio (0:ℝ), expTest h x * Complex.exp ((z - 1/2) * x))
      = 1/((h:ℂ) + (z - 1/2)) := by
    rw [integral_Iio_comp_neg,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEqIoi']
    have h1 := integral_Ioi_cexp_neg hre2
    rw [h1, one_div]
  rw [paperPhi, ← MeasureTheory.setIntegral_univ,
    show (Set.univ : Set ℝ) = Set.Iio 0 ∪ Set.Ici 0 from
      (Set.Iio_union_Ici (a := (0:ℝ))).symm,
    MeasureTheory.setIntegral_union (Set.Iio_disjoint_Ici le_rfl)
      measurableSet_Ici hIio_int hIci_int, hIci_val, hIio_val]
  ring

/-- The conjugate-pair combination collapses to the real rational
`2h/(h²+γ²)`. -/
theorem one_div_sub_add_one_div_add_I {h γ : ℝ} (hh : 0 < h) :
    1/((h:ℂ) - (γ:ℂ)*Complex.I) + 1/((h:ℂ) + (γ:ℂ)*Complex.I)
      = ((2*h/(h^2 + γ^2) : ℝ) : ℂ) := by
  have hd1 : ((h:ℂ) - (γ:ℂ)*Complex.I) ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    simp at h1
    linarith
  have hd2 : ((h:ℂ) + (γ:ℂ)*Complex.I) ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    simp at h1
    linarith
  have hprod : ((h:ℂ) - (γ:ℂ)*Complex.I) * ((h:ℂ) + (γ:ℂ)*Complex.I)
      = (((h^2 + γ^2 : ℝ)) : ℂ) := by
    have h2 : ((h:ℂ) - (γ:ℂ)*Complex.I) * ((h:ℂ) + (γ:ℂ)*Complex.I)
        = (h:ℂ)^2 - ((γ:ℂ)*Complex.I)^2 := by ring
    rw [h2, mul_pow, Complex.I_sq]
    push_cast
    ring
  rw [div_add_div _ _ hd1 hd2, hprod, Complex.ofReal_div]
  congr 1
  push_cast
  ring

/-- **The Fourier decay of `F̂_h`**: the transform is the rational
`2h/(h²+γ²) ≤ 2h/γ²`. -/
theorem exists_norm_fourier_expTest_le {h : ℝ} (hh : 0 < h) :
    ∃ C γ₀ : ℝ, 0 < C ∧ 1 ≤ γ₀ ∧ ∀ γ : ℝ, γ₀ ≤ |γ| →
      ‖paperFourierIntegral (expTest h) γ‖ ≤ C / γ^2 := by
  refine ⟨2*h, 1, by linarith [hh], le_refl 1, fun γ hγ => ?_⟩
  have hγ0 : γ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hγ
    linarith
  have h1 : paperFourierIntegral (expTest h) γ
      = paperPhi (expTest h) (1/2 + (γ : ℂ) * Complex.I) :=
    (paperPhi_half_add_mul_I (expTest h) γ).symm
  have hre : ((1:ℂ)/2 + (γ:ℂ)*Complex.I).re = 1/2 := by simp
  have h2 := paperPhi_expTest
    (z := 1/2 + (γ:ℂ)*Complex.I) (h := h) (by rw [hre]; simpa using hh)
  have hzero1 : ((h:ℂ) - ((1/2 + (γ:ℂ)*Complex.I) - 1/2))
      = (h:ℂ) - (γ:ℂ)*Complex.I := by ring
  have hzero2 : ((h:ℂ) + ((1/2 + (γ:ℂ)*Complex.I) - 1/2))
      = (h:ℂ) + (γ:ℂ)*Complex.I := by ring
  rw [h1, h2, hzero1, hzero2, one_div_sub_add_one_div_add_I hh, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (show (0:ℝ) ≤ 2 * h / (h ^ 2 + γ ^ 2) from
      div_nonneg (by linarith) (by positivity))]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg γ, sq_nonneg h]

/-- **`hB` at the Landau–Stark function**: the band bound `M/max(|t|,1)` with
`M = 2/δ + 2`, `δ = h − (1/2+a)`, straight from the closed form. -/
theorem exists_band_bound_paperPhi_expTest {h : ℝ} (hh : 0 < h) {a : ℝ}
    (ha : 0 < a) (hah : 1/2 + a < h) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ t : ℝ, -a ≤ σ → σ ≤ 1+a →
      ‖paperPhi (expTest h) ((σ:ℂ) + (t:ℂ)*Complex.I)‖ ≤ M / max |t| 1 := by
  set δ : ℝ := h - (1/2 + a) with hδ_def
  have hδ0 : 0 < δ := by rw [hδ_def]; linarith
  refine ⟨2/δ + 2, by positivity, fun σ t hσl hσr => ?_⟩
  have hre : ((σ:ℂ) + (t:ℂ)*Complex.I).re = σ := by simp
  have hband : |((σ:ℂ) + (t:ℂ)*Complex.I).re - 1/2| < h := by
    rw [hre, abs_lt]
    constructor <;> linarith
  rw [paperPhi_expTest hband]
  have hkey : ∀ w : ℂ, δ ≤ |w.re| → |t| ≤ |w.im| → w ≠ 0 →
      ‖1/w‖ ≤ (1/δ + 1) / max |t| 1 := by
    intro w hwre hwim hw0
    rw [norm_div, norm_one]
    have h1 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
    have h2 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
    have hw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    rcases le_total |t| 1 with ht | ht
    · rw [max_eq_right ht, div_one]
      rw [div_add' _ _ _ hδ0.ne', div_le_div_iff₀ hw hδ0]
      have h3 : δ ≤ ‖w‖ := le_trans hwre h1
      nlinarith
    · rw [max_eq_left ht]
      rw [div_le_div_iff₀ hw (by linarith : (0:ℝ) < |t|)]
      have h3 : |t| ≤ ‖w‖ := le_trans hwim h2
      have h4 : (0:ℝ) ≤ 1/δ := by positivity
      nlinarith
  have hb1 : ‖1/((h:ℂ) - (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))‖
      ≤ (1/δ + 1) / max |t| 1 := by
    refine hkey _ ?_ ?_ ?_
    · rw [show (((h:ℂ) - (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))).re
          = h - (σ - 1/2) by simp]
      rw [abs_of_pos (by linarith)]
      rw [hδ_def]
      linarith
    · rw [show (((h:ℂ) - (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))).im = -t by simp,
        abs_neg]
    · intro h0
      have h1' := congrArg Complex.re h0
      rw [show (((h:ℂ) - (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))).re
          = h - (σ - 1/2) by simp] at h1'
      simp at h1'
      linarith
  have hb2 : ‖1/((h:ℂ) + (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))‖
      ≤ (1/δ + 1) / max |t| 1 := by
    refine hkey _ ?_ ?_ ?_
    · rw [show (((h:ℂ) + (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))).re
          = h + (σ - 1/2) by simp]
      rw [abs_of_pos (by linarith)]
      rw [hδ_def]
      linarith
    · rw [show (((h:ℂ) + (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))).im = t by simp]
    · intro h0
      have h1' := congrArg Complex.re h0
      rw [show (((h:ℂ) + (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))).re
          = h + (σ - 1/2) by simp] at h1'
      simp at h1'
      linarith
  refine le_trans (norm_add_le _ _) ?_
  have hmax : (0:ℝ) < max |t| 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  calc ‖1/((h:ℂ) - (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))‖
        + ‖1/((h:ℂ) + (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))‖
      ≤ (1/δ + 1) / max |t| 1 + (1/δ + 1) / max |t| 1 := add_le_add hb1 hb2
    _ = (2/δ + 2) / max |t| 1 := by
        field_simp
        ring

/-- **`hΦd` at the Landau–Stark function**: the transform is differentiable on the
closed band (which sits strictly inside the convergence strip). -/
theorem differentiableAt_paperPhi_expTest {h : ℝ} {a : ℝ}
    (_ha : 0 < a) (hah : 1/2 + a < h) :
    ∀ ζ : ℂ, -a ≤ ζ.re → ζ.re ≤ 1+a →
      DifferentiableAt ℂ (paperPhi (expTest h)) ζ := by
  intro ζ hζl hζr
  set U : Set ℂ := {z : ℂ | |z.re - 1/2| < h} with hU_def
  have hUopen : IsOpen U := by
    have h1 : U = (fun z : ℂ => |z.re - 1/2|) ⁻¹' (Set.Iio h) := rfl
    rw [h1]
    exact (Continuous.abs (by fun_prop)).isOpen_preimage _ isOpen_Iio
  have hζU : ζ ∈ U := by
    rw [hU_def, Set.mem_setOf_eq, abs_lt]
    constructor <;> linarith
  have hrat : DifferentiableAt ℂ
      (fun z : ℂ => 1/((h:ℂ) - (z - 1/2)) + 1/((h:ℂ) + (z - 1/2))) ζ := by
    have habs : |ζ.re - 1/2| < h := hζU
    have habs' := abs_lt.mp habs
    have hd1 : ((h:ℂ) - (ζ - 1/2)) ≠ 0 := by
      intro h0
      have h1 := congrArg Complex.re h0
      have h2 : ((h:ℂ) - (ζ - 1/2)) = ((h + 1/2 : ℝ) : ℂ) - ζ := by push_cast; ring
      rw [h2, Complex.sub_re, Complex.ofReal_re] at h1
      simp at h1
      linarith
    have hd2 : ((h:ℂ) + (ζ - 1/2)) ≠ 0 := by
      intro h0
      have h1 := congrArg Complex.re h0
      have h2 : ((h:ℂ) + (ζ - 1/2)) = ((h - 1/2 : ℝ) : ℂ) + ζ := by push_cast; ring
      rw [h2, Complex.add_re, Complex.ofReal_re] at h1
      simp at h1
      linarith
    refine DifferentiableAt.add ?_ ?_
    · exact (differentiableAt_const _).div
        ((differentiableAt_const _).sub
          ((differentiableAt_id).sub (differentiableAt_const _))) hd1
    · exact (differentiableAt_const _).div
        ((differentiableAt_const _).add
          ((differentiableAt_id).sub (differentiableAt_const _))) hd2
  refine hrat.congr_of_eventuallyEq ?_
  filter_upwards [hUopen.mem_nhds hζU] with z hz
  exact paperPhi_expTest hz

/-! ### Boundary decay, the prime side, and the pole windows at `F_h` -/

/-- **`htop2`/`hbot2` at the Landau–Stark function**: `ρ_σ·γ_{F_h} → 0` along any
`|t| → ∞` filter. -/
theorem tendsto_boundary_expTest {h : ℝ} (hh : 0 < h)
    {σ : ℝ} (hσ : 0 < σ) (hσl : -1 ≤ σ) (hσr : σ ≤ 2) (l : Filter ℝ)
    (habs : Filter.Tendsto (fun t : ℝ => |t|) l atTop) :
    Filter.Tendsto (fun t : ℝ => rhoFT (fun x => ((poitouKernel σ x : ℝ) : ℂ)) t
      * gammaFT (expTest h) t) l (nhds 0) := by
  obtain ⟨C, γ₀, hC, hγ₀, hφ⟩ := exists_norm_fourier_expTest_le hh
  refine tendsto_rhoFT_mul_gammaFT_of_decay (C := C) (γ₀ := γ₀) hσ hσl hσr ?_ l habs
  refine norm_gammaFT_le_of_fourier_decay (integrable_expTest hh)
    (integrableOn_expTest_diffQuot_window hh) hγ₀ ?_
  intro γ hγ
  rw [← paperFourierIntegral_eq_muFT]
  exact hφ γ hγ

/-- **`htop4`/`hbot4` at the Landau–Stark function**: the half-scaled boundary
decay. -/
theorem tendsto_boundary_expTest_half {h : ℝ} (hh : 0 < h)
    {σ : ℝ} (hσ : 0 < σ) (hσl : -1 ≤ σ) (hσr : σ ≤ 2) (l : Filter ℝ)
    (habs : Filter.Tendsto (fun t : ℝ => |t|) l atTop) :
    Filter.Tendsto (fun t : ℝ => rhoFT (fun x => ((poitouKernel σ x : ℝ) : ℂ)) t
      * gammaFT (fun x : ℝ => expTest h (x/2) / 2) t) l (nhds 0) := by
  obtain ⟨C, γ₀, hC, hγ₀, hφ⟩ := exists_norm_fourier_expTest_le hh
  refine tendsto_rhoFT_mul_gammaFT_of_decay (C := C) (γ₀ := γ₀) hσ hσl hσr ?_ l habs
  have hFh : Integrable (fun x : ℝ => expTest h (x/2) / 2) :=
    integrable_halfScale (integrable_expTest hh)
  have hFhdiv : MeasureTheory.IntegrableOn (fun x : ℝ =>
      ((fun x : ℝ => expTest h (x/2) / 2) 0 - (fun x : ℝ => expTest h (x/2) / 2) x)/(x:ℂ))
      (Set.Ioc (-1) 1) := by
    refine (integrableOn_halfScale_div (integrableOn_expTest_diffQuot_window hh)).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    show (expTest h 0/2 - expTest h (x/2)/2)/(x:ℂ)
        = (expTest h (0/2) / 2 - expTest h (x/2) / 2)/(x:ℂ)
    norm_num
  refine norm_gammaFT_le_of_fourier_decay hFh hFhdiv hγ₀ ?_
  intro u hu
  have hFour : (∫ x : ℝ, (expTest h (x/2) / 2) * Complex.exp ((u*x : ℝ) * Complex.I))
      = ∫ x : ℝ, expTest h x * Complex.exp (((2*u)*x : ℝ) * Complex.I) := by
    set g : ℝ → ℂ := fun w => expTest h w * Complex.exp (((2*u)*w : ℝ) * Complex.I)
      with hg
    have h1 : (∫ x : ℝ, g ((2:ℝ)⁻¹ * x)) = |(((2:ℝ)⁻¹))⁻¹| • ∫ x : ℝ, g x :=
      MeasureTheory.Measure.integral_comp_mul_left g ((2:ℝ)⁻¹)
    have h2 : (fun x : ℝ => (expTest h (x/2) / 2) * Complex.exp ((u*x : ℝ) * Complex.I))
        = fun x : ℝ => (1/2 : ℂ) * g ((2:ℝ)⁻¹ * x) := by
      funext x
      show (expTest h (x/2) / 2) * Complex.exp ((u*x : ℝ) * Complex.I)
          = (1/2 : ℂ) * g ((2:ℝ)⁻¹ * x)
      rw [hg]
      show (expTest h (x/2) / 2) * Complex.exp ((u*x : ℝ) * Complex.I)
          = (1/2 : ℂ) * (expTest h ((2:ℝ)⁻¹ * x)
            * Complex.exp (((2*u)*((2:ℝ)⁻¹ * x) : ℝ) * Complex.I))
      rw [show (2:ℝ)⁻¹ * x = x/2 by ring]
      rw [show ((2*u)*(x/2) : ℝ) = (u*x : ℝ) by ring]
      ring
    rw [h2, MeasureTheory.integral_const_mul, h1,
      show |(((2:ℝ)⁻¹))⁻¹| = (2:ℝ) by norm_num, Complex.real_smul,
      Complex.ofReal_ofNat]
    ring
  show ‖∫ x : ℝ, (expTest h (x/2) / 2) * Complex.exp ((u*x : ℝ) * Complex.I)‖ ≤ C/u^2
  rw [hFour, ← paperFourierIntegral_eq_muFT]
  have h2u : γ₀ ≤ |2*u| := by
    rw [abs_mul, abs_two]
    have h0 := abs_nonneg u
    linarith
  refine le_trans (hφ (2*u) h2u) ?_
  have hu0 : (0:ℝ) < u^2 := by
    have h0 : u ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hu
      linarith
    positivity
  rw [mul_pow]
  rw [show (2:ℝ)^2 * u^2 = 4 * u^2 by ring]
  refine div_le_div_of_nonneg_left hC.le hu0 ?_
  linarith

/-- The uniform bound on the weighted Landau–Stark symbol
`G = F_h·e^{(1/2+a)x}`. -/
theorem norm_expTest_mul_exp_le {h : ℝ} {a : ℝ} (ha : 0 < a) (hah : 1/2 + a < h)
    (x : ℝ) :
    ‖expTest h x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [norm_mul, norm_expTest, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
    ← Real.exp_add]
  refine Real.exp_le_one_iff.mpr ?_
  have h1 : (1/2+a) * x ≤ (1/2+a) * |x| :=
    mul_le_mul_of_nonneg_left (le_abs_self x) (by linarith)
  nlinarith [abs_nonneg x]

/-- `‖(w : ℂ) * z‖ ≤ w` when `0 ≤ w` and `‖z‖ ≤ 1` — the Weierstrass-`M` step for
the prime-side series. -/
theorem norm_ofReal_mul_le_of_norm_le_one {w : ℝ} (hw : 0 ≤ w) {z : ℂ}
    (hz : ‖z‖ ≤ 1) : ‖(w : ℂ) * z‖ ≤ w := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
  exact mul_le_of_le_one_right hw hz

/-- Pointwise summability of the prime-side series at the Landau–Stark function. -/
theorem summable_primeSideH_term_expTest {h : ℝ} {a : ℝ} (ha : 0 < a)
    (hah : 1/2 + a < h) (u : ℝ) :
    Summable (fun pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ =>
      ((Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
        * (expTest h (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
            * ((Real.exp ((1/2+a)
                * (u + (((pk.2+1 : ℕ)) : ℝ)
                  * Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ))) := by
  refine Summable.of_norm_bounded
    (g := fun pk => Real.log (Ideal.absNorm pk.1.1)
      * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)))
    (summable_primeIdeal_pow_log_rpow K (by linarith : (1:ℝ) < 1+a))
    (fun pk => ?_)
  exact norm_ofReal_mul_le_of_norm_le_one (primeSideH_weight_nonneg K pk)
    (norm_expTest_mul_exp_le ha hah _)

/-- **`hH`-BV at the Landau–Stark function** (complex level). -/
theorem boundedVariationOn_primeSideH_expTest {h : ℝ} {a : ℝ} (ha : 0 < a)
    (hah : 1/2 + a < h) :
    BoundedVariationOn (primeSideH K a (expTest h)) Set.univ := by
  set G : ℝ → ℂ := fun x => expTest h x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ) with hG
  have hGbv : BoundedVariationOn G Set.univ :=
    boundedVariationOn_expTest_mul_exp (by linarith) hah
  have h0 : primeSideH K a (expTest h)
      = fun u : ℝ => ∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
          ((Real.log (Ideal.absNorm pk.1.1)
              * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
            * G (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1)) := by
    funext u
    rw [primeSideH]
  have hwsum : Summable (fun pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ =>
      Real.log (Ideal.absNorm pk.1.1)
        * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a))) :=
    summable_primeIdeal_pow_log_rpow K (by linarith : (1:ℝ) < 1+a)
  have hwsum' : Summable (fun pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ =>
      ‖((Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)‖₊) := by
    rw [← NNReal.summable_coe]
    refine hwsum.congr (fun pk => ?_)
    rw [coe_nnnorm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (primeSideH_weight_nonneg K pk)]
  have hwtop : (∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
      (‖((Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)‖₊
        : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr hwsum'
  unfold BoundedVariationOn
  rw [h0]
  refine ne_top_of_le_ne_top ?_ (eVariationOn_tsum_le _ _ (fun x _ => by
    have h1 := summable_primeSideH_term_expTest K ha hah x
    rw [hG]
    exact h1))
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum (fun pk =>
    eVariationOn_smul_translate_le G _ _))
  rw [ENNReal.tsum_mul_right]
  exact ENNReal.mul_ne_top hwtop hGbv

/-- **`hHre` at the Landau–Stark function.** -/
theorem locallyBoundedVariationOn_primeSideH_expTest_re {h : ℝ} {a : ℝ}
    (ha : 0 < a) (hah : 1/2 + a < h) :
    LocallyBoundedVariationOn
      (fun u : ℝ => (primeSideH K a (expTest h) u).re) Set.univ :=
  (lipschitzWith_complex_re.comp_boundedVariationOn
    (boundedVariationOn_primeSideH_expTest K ha hah)).locallyBoundedVariationOn

/-- **`hHim` at the Landau–Stark function.** -/
theorem locallyBoundedVariationOn_primeSideH_expTest_im {h : ℝ} {a : ℝ}
    (ha : 0 < a) (hah : 1/2 + a < h) :
    LocallyBoundedVariationOn
      (fun u : ℝ => (primeSideH K a (expTest h) u).im) Set.univ :=
  (lipschitzWith_complex_im.comp_boundedVariationOn
    (boundedVariationOn_primeSideH_expTest K ha hah)).locallyBoundedVariationOn

/-- The prime side is continuous at the Landau–Stark function (Weierstrass
M-test). -/
theorem continuous_primeSideH_expTest {h : ℝ} {a : ℝ} (ha : 0 < a)
    (hah : 1/2 + a < h) :
    Continuous (primeSideH K a (expTest h)) := by
  have h0 : primeSideH K a (expTest h)
      = fun u : ℝ => ∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
          ((Real.log (Ideal.absNorm pk.1.1)
              * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
            * (expTest h (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
                * ((Real.exp ((1/2+a)
                    * (u + (((pk.2+1 : ℕ)) : ℝ)
                      * Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ)) := by
    funext u
    rw [primeSideH]
  rw [h0]
  refine continuous_tsum (fun pk => ?_)
    (summable_primeIdeal_pow_log_rpow K (by linarith : (1:ℝ) < 1+a)) (fun pk u => ?_)
  · refine continuous_const.mul ?_
    refine Continuous.mul ?_ ?_
    · exact (continuous_expTest h).comp (continuous_id.add continuous_const)
    · exact Complex.continuous_ofReal.comp (by fun_prop)
  · exact norm_ofReal_mul_le_of_norm_le_one (primeSideH_weight_nonneg K pk)
      (norm_expTest_mul_exp_le ha hah _)

/-- **`hHp` at the Landau–Stark function.** -/
theorem tendsto_primeSideH_expTest_right {h : ℝ} {a : ℝ} (ha : 0 < a)
    (hah : 1/2 + a < h) :
    Filter.Tendsto (primeSideH K a (expTest h)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (primeSideH K a (expTest h) 0)) :=
  ((continuous_primeSideH_expTest K ha hah).continuousAt).tendsto.mono_left
    nhdsWithin_le_nhds

/-- **`hHm` at the Landau–Stark function.** -/
theorem tendsto_primeSideH_expTest_left {h : ℝ} {a : ℝ} (ha : 0 < a)
    (hah : 1/2 + a < h) :
    Filter.Tendsto (primeSideH K a (expTest h)) (nhdsWithin 0 (Set.Iio 0))
      (nhds (primeSideH K a (expTest h) 0)) :=
  ((continuous_primeSideH_expTest K ha hah).continuousAt).tendsto.mono_left
    nhdsWithin_le_nhds

/-- **BV of the pole-window sum** at the Landau–Stark symbol `G = F_h·e^{(1/2+a)x}`. -/
theorem locallyBoundedVariationOn_poleWindow_sum_expTest {h : ℝ} {a : ℝ}
    (ha : 0 < a) (hah : 1/2 + a < h) :
    LocallyBoundedVariationOn (fun u : ℝ =>
      poleWindow a (fun x : ℝ => expTest h x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) u
        + poleWindow (1+a)
            (fun x : ℝ => expTest h x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) u)
      Set.univ := by
  have hG : Integrable (fun x : ℝ => expTest h x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) :=
    integrable_expTest_mul_exp (by rw [abs_of_pos (by linarith)]; linarith)
  have hGc : Continuous (fun x : ℝ => expTest h x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) :=
    (continuous_expTest h).mul (Complex.continuous_ofReal.comp (by fun_prop))
  exact locallyBoundedVariationOn_poleWindow_add ha (by linarith) hG hGc

/-- **`hEre` at the Landau–Stark function.** -/
theorem locallyBoundedVariationOn_poleWindow_expTest_re {h : ℝ} {a : ℝ}
    (ha : 0 < a) (hah : 1/2 + a < h) :
    LocallyBoundedVariationOn (fun u : ℝ =>
      ((poleWindow a (fun x : ℝ => expTest h x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) u
        + poleWindow (1+a)
            (fun x : ℝ => expTest h x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) u)).re)
      Set.univ :=
  lipschitzWith_complex_re.comp_locallyBoundedVariationOn
    (locallyBoundedVariationOn_poleWindow_sum_expTest ha hah)

/-- **`hEim` at the Landau–Stark function.** -/
theorem locallyBoundedVariationOn_poleWindow_expTest_im {h : ℝ} {a : ℝ}
    (ha : 0 < a) (hah : 1/2 + a < h) :
    LocallyBoundedVariationOn (fun u : ℝ =>
      ((poleWindow a (fun x : ℝ => expTest h x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) u
        + poleWindow (1+a)
            (fun x : ℝ => expTest h x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) u)).im)
      Set.univ :=
  lipschitzWith_complex_im.comp_locallyBoundedVariationOn
    (locallyBoundedVariationOn_poleWindow_sum_expTest ha hah)

/-- **The Weil–Poitou explicit formula at the Landau–Stark function**: every
hypothesis of `weil_explicit_formula` holds for `F_h(x) = e^{−h|x|}` when
`0 < a ≤ 1/4` and `1/2 + a < h`. -/
theorem weil_explicit_formula_expTest {h : ℝ} {a : ℝ}
    (ha : 0 < a) (ha' : a ≤ 1/4) (hah : 1/2 + a < h) :
    ∃ T : ℕ → ℝ, Filter.Tendsto T atTop atTop ∧
      Filter.Tendsto (fun n : ℕ =>
          ∑ᶠ ρ, (((MeromorphicOn.divisor (completedDedekindZetaEntire K)
          (Set.Ioo (-a) (1+a) ×ℂ Set.Ioo (-(T n)) (T n))) ρ : ℂ))
            * paperPhi (expTest h) ρ)
        atTop (nhds
          ((paperPhi (expTest h) 0 + paperPhi (expTest h) 1)
            + ((Real.log |NumberField.discr K| : ℝ) : ℂ) * expTest h 0
            + (((-(((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
                + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ))
                  * (Real.eulerMascheroniConstant + Real.log (8*π))
                + (NumberField.InfinitePlace.nrRealPlaces K : ℝ) * (π/2)) : ℝ)) : ℂ)
                * expTest h 0
            + (((NumberField.InfinitePlace.nrRealPlaces K
                + 2*NumberField.InfinitePlace.nrComplexPlaces K : ℕ)) : ℂ)
                * (∫ y in Set.Ioi (0:ℝ),
                  ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (expTest h 0 - expTest h y))
            + ((NumberField.InfinitePlace.nrRealPlaces K : ℕ) : ℂ)
                * (∫ y in Set.Ioi (0:ℝ),
                  ((1/(2 * Real.cosh (y/2)) : ℝ) : ℂ) * (expTest h 0 - expTest h y))
            - (primeSideH K a (expTest h) 0 + primeSideH K a (expTest h) 0))) := by
  have hh0 : (0:ℝ) < h := by linarith
  obtain ⟨M, hM0, hMb⟩ := exists_band_bound_paperPhi_expTest hh0 ha hah
  exact weil_explicit_formula K ha ha'
    (integrable_expTest hh0)
    (locallyBoundedVariationOn_expTest_re hh0)
    (locallyBoundedVariationOn_expTest_im hh0)
    (((continuous_expTest h).continuousAt).tendsto.mono_left nhdsWithin_le_nhds)
    (expTest_neg h)
    (integrableOn_expTest_diffQuot_window hh0)
    (memLp_two_expTest_diffQuot hh0)
    (tendsto_boundary_expTest hh0 (by norm_num) (by norm_num) (by norm_num)
      atTop tendsto_abs_atTop_atTop)
    (tendsto_boundary_expTest hh0 (by norm_num) (by norm_num) (by norm_num)
      atBot tendsto_abs_atBot_atTop)
    (tendsto_boundary_expTest_half hh0 (by norm_num) (by norm_num) (by norm_num)
      atTop tendsto_abs_atTop_atTop)
    (tendsto_boundary_expTest_half hh0 (by norm_num) (by norm_num) (by norm_num)
      atBot tendsto_abs_atBot_atTop)
    (differentiableAt_paperPhi_expTest ha hah)
    (B := fun T : ℝ => M / max T 1)
    (fun σ t h1 h2 => hMb σ t h1 h2)
    (tendsto_div_max_mul_log_sq M)
    (integrable_expTest_mul_exp (by rw [abs_of_pos (by linarith)]; linarith))
    (locallyBoundedVariationOn_expTest_mul_exp_re ha hah)
    (locallyBoundedVariationOn_expTest_mul_exp_im ha hah)
    (locallyBoundedVariationOn_poleWindow_expTest_re ha hah)
    (locallyBoundedVariationOn_poleWindow_expTest_im ha hah)
    (locallyBoundedVariationOn_primeSideH_expTest_re K ha hah)
    (locallyBoundedVariationOn_primeSideH_expTest_im K ha hah)
    (tendsto_primeSideH_expTest_right K ha hah)
    (tendsto_primeSideH_expTest_left K ha hah)

/-! ### Evaluating the three sides: eq:Stark (L5-b) -/

/-- **The transform value at a critical-line zero**: `Φ_{F_h}(1/2+iγ) = 2h/(h²+γ²)`. -/
theorem paperPhi_expTest_at_zero {h : ℝ} (hh : 0 < h) {ρ : ℂ} (hre : ρ.re = 1/2) :
    paperPhi (expTest h) ρ = ((2*h/(h^2 + ρ.im^2) : ℝ) : ℂ) := by
  have hz : |ρ.re - 1/2| < h := by
    rw [hre, sub_self, abs_zero]
    exact hh
  rw [paperPhi_expTest hz]
  have hρ_eq : ρ - 1/2 = (ρ.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [hre]
    · simp
  rw [hρ_eq]
  exact one_div_sub_add_one_div_add_I hh

/-- **Absolute convergence of the zero side at the Landau–Stark function.** -/
theorem summable_zetaZeros_paperPhi_expTest (hGRH : GeneralizedRiemannHypothesis K)
    {h : ℝ} (hh : 1/2 < h) :
    Summable (fun ρ : ZetaZeros K =>
      (zetaZeroDivisor K ρ.1 : ℂ) * paperPhi (expTest h) ρ.1) := by
  have hs : Summable (fun ρ : ZetaZeros K =>
      (zetaZeroDivisor K ρ.1 : ℂ) * ((2*h/(h^2 + ρ.1.im^2) : ℝ) : ℂ)) := by
    refine summable_zetaZeros_mul_of_norm_le K (σ := h + 1/2) (by linarith)
      (f := fun γ => ((2*h/(h^2 + γ^2) : ℝ) : ℂ)) (c := 2*h) (fun γ => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (by linarith) (by positivity)),
      show (h + 1/2 - 1/2) = h by ring]
  refine hs.congr (fun ρ => ?_)
  rw [paperPhi_expTest_at_zero (by linarith) (ZetaZeros_re_eq_half K hGRH ρ)]

/-- **The von Mangoldt Dirichlet sum** `Σ_{𝔭,m} log N𝔭 · N𝔭^{−mσ}`
(= `−ζ'_K/ζ_K(σ)` for `σ > 1`; B–F's `−2ζ'_K/ζ_K(σ)` term is twice this). -/
noncomputable def vonMangoldtSum (K : Type*) [Field K] [NumberField K] (σ : ℝ) : ℝ :=
  ∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
    Real.log (Ideal.absNorm pk.1.1)
      * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * σ)

/-- **The prime side at the Landau–Stark function is the von Mangoldt sum**:
`H(0) = Σ log N𝔭 · N𝔭^{−m/2}·e^{−h·m·log N𝔭} = Σ log N𝔭 · N𝔭^{−mσ}`, `σ = h+1/2`. -/
theorem primeSideH_expTest_zero_eq (a : ℝ) {h : ℝ} (_ : 0 < h) :
    primeSideH K a (expTest h) 0 = ((vonMangoldtSum K (h + 1/2) : ℝ) : ℂ) := by
  rw [primeSideH_auxF_zero_eq, vonMangoldtSum, Complex.ofReal_tsum]
  refine tsum_congr (fun pk => ?_)
  have hN2 : (2:ℝ) ≤ (Ideal.absNorm pk.1.1 : ℝ) := by
    have hne0 : Ideal.absNorm pk.1.1 ≠ 0 :=
      fun h0 => pk.1.2.2 (Ideal.absNorm_eq_zero_iff.mp h0)
    have hne1 : Ideal.absNorm pk.1.1 ≠ 1 :=
      fun h0 => pk.1.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h0)
    have h2 : 2 ≤ Ideal.absNorm pk.1.1 := by omega
    exact_mod_cast h2
  have hN0 : (0:ℝ) < (Ideal.absNorm pk.1.1 : ℝ) := by linarith
  have hlogNn : (0:ℝ) ≤ Real.log (Ideal.absNorm pk.1.1) :=
    Real.log_nonneg (by linarith)
  have hmlogNn : (0:ℝ) ≤ (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) :=
    mul_nonneg (Nat.cast_nonneg _) hlogNn
  unfold expTest
  rw [abs_of_nonneg hmlogNn, ← Complex.ofReal_mul]
  congr 1
  have hkey : (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
      * Real.exp (-h * ((((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1)))
      = (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (h + 1/2)) := by
    rw [Real.rpow_def_of_pos hN0, Real.rpow_def_of_pos hN0, ← Real.exp_add]
    congr 1
    ring
  rw [mul_assoc, hkey]

/-- **The pole terms at the Landau–Stark function**:
`Φ(0) + Φ(1) = 2/(h+1/2) + 2/(h−1/2) = 2/σ + 2/(σ−1)`. -/
theorem paperPhi_expTest_zero_add_one {h : ℝ} (hh : 1/2 < h) :
    paperPhi (expTest h) 0 + paperPhi (expTest h) 1
      = ((2/(h + 1/2) + 2/(h - 1/2) : ℝ) : ℂ) := by
  have hz0 : |(0:ℂ).re - 1/2| < h := by
    simp only [Complex.zero_re, zero_sub, abs_neg]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    linarith [hh]
  have hz1 : |(1:ℂ).re - 1/2| < h := by
    simp only [Complex.one_re]
    rw [show (1:ℝ) - 1/2 = 1/2 by norm_num, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    linarith
  rw [paperPhi_expTest hz0, paperPhi_expTest hz1]
  have h0eq : ((h:ℂ) - ((0:ℂ) - 1/2)) = ((h + 1/2 : ℝ) : ℂ) := by push_cast; ring
  have h0eq' : ((h:ℂ) + ((0:ℂ) - 1/2)) = ((h - 1/2 : ℝ) : ℂ) := by push_cast; ring
  have h1eq : ((h:ℂ) - ((1:ℂ) - 1/2)) = ((h - 1/2 : ℝ) : ℂ) := by push_cast; ring
  have h1eq' : ((h:ℂ) + ((1:ℂ) - 1/2)) = ((h + 1/2 : ℝ) : ℂ) := by push_cast; ring
  rw [h0eq, h0eq', h1eq, h1eq']
  have hne1' : (h + 1/2 : ℝ) ≠ 0 := by linarith
  have hne2' : (h - 1/2 : ℝ) ≠ 0 := by linarith
  push_cast
  field_simp
  ring

/-- Realifying the archimedean integrals at the Landau–Stark function. -/
theorem arch_expTest_integral_eq (h : ℝ) (w : ℝ → ℝ) :
    (∫ y in Set.Ioi (0:ℝ), ((w y : ℝ) : ℂ) * (expTest h 0 - expTest h y))
      = ((∫ y in Set.Ioi (0:ℝ), w y * (1 - Real.exp (-h * y)) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
  rw [expTest_zero]
  unfold expTest
  rw [abs_of_nonneg (le_of_lt hy)]
  push_cast
  ring

/-- **eq:Stark** (B–F lines 554–557, ×2): for `σ > 1`, under GRH,
`2(σ−1/2)·Σ_ρ m_ρ/((σ−1/2)²+γ_ρ²)
  = 2/σ + 2/(σ−1) + log Δ_K − [Γ-constant] + n·I_sinh(σ) + r₁·I_cosh(σ)
    − 2·Σ_{𝔭,m} log N𝔭·N𝔭^{−mσ}`,
the explicit formula evaluated at the Landau–Stark function `F_{σ−1/2}`. -/
theorem stark_identity (hGRH : GeneralizedRiemannHypothesis K) {σ : ℝ} (hσ : 1 < σ) :
    2*(σ - 1/2) * zeroSumSigma K σ
      = 2/σ + 2/(σ - 1) + Real.log |NumberField.discr K|
        + (-(((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
            + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ))
              * (Real.eulerMascheroniConstant + Real.log (8*π))
            + (NumberField.InfinitePlace.nrRealPlaces K : ℝ) * (π/2)))
        + ((NumberField.InfinitePlace.nrRealPlaces K
            + 2*NumberField.InfinitePlace.nrComplexPlaces K : ℕ) : ℝ)
            * (∫ y in Set.Ioi (0:ℝ),
              1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y)))
        + (NumberField.InfinitePlace.nrRealPlaces K : ℝ)
            * (∫ y in Set.Ioi (0:ℝ),
              1/(2 * Real.cosh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y)))
        - 2 * vonMangoldtSum K σ := by
  have hh : 1/2 < σ - 1/2 := by linarith
  have hh0 : (0:ℝ) < σ - 1/2 := by linarith
  set a : ℝ := min (1/4) ((σ - 1)/2) with ha_def
  have ha : 0 < a := lt_min (by norm_num) (by linarith)
  have ha' : a ≤ 1/4 := min_le_left _ _
  have hah : 1/2 + a < σ - 1/2 := by
    have h1 : a ≤ (σ - 1)/2 := min_le_right _ _
    linarith
  obtain ⟨T, hT, hlim⟩ := weil_explicit_formula_expTest K ha ha' hah
  have hsum := summable_zetaZeros_paperPhi_expTest K hGRH hh
  have hbridge := tendsto_finsum_window_zetaZeros K hGRH hsum ha hT
  have hkey := tendsto_nhds_unique hbridge hlim
  -- evaluate the zero side
  have hzeros : (∑' ρ : ZetaZeros K,
      (zetaZeroDivisor K ρ.1 : ℂ) * paperPhi (expTest (σ - 1/2)) ρ.1)
      = ((2*(σ - 1/2) * zeroSumSigma K σ : ℝ) : ℂ) := by
    have h1 : ∀ ρ : ZetaZeros K,
        (zetaZeroDivisor K ρ.1 : ℂ) * paperPhi (expTest (σ - 1/2)) ρ.1
        = (((zetaZeroDivisor K ρ.1 : ℝ)
            * (2*(σ - 1/2)/((σ - 1/2)^2 + ρ.1.im^2)) : ℝ) : ℂ) := by
      intro ρ
      rw [paperPhi_expTest_at_zero hh0 (ZetaZeros_re_eq_half K hGRH ρ)]
      push_cast
      ring
    rw [tsum_congr h1, ← Complex.ofReal_tsum]
    congr 1
    rw [zeroSumSigma, ← tsum_mul_left]
    refine tsum_congr (fun ρ => ?_)
    ring
  -- evaluate the prime side
  have hprime := primeSideH_expTest_zero_eq K a hh0
  rw [show (σ - 1/2) + 1/2 = σ by ring] at hprime
  -- evaluate the pole terms
  have hpoles := paperPhi_expTest_zero_add_one hh
  rw [show (σ - 1/2) + 1/2 = σ by ring, show (σ - 1/2) - 1/2 = σ - 1 by ring] at hpoles
  -- realify the archimedean integrals
  have harch1 := arch_expTest_integral_eq (σ - 1/2) (fun y => 1/(2 * Real.sinh (y/2)))
  have harch2 := arch_expTest_integral_eq (σ - 1/2) (fun y => 1/(2 * Real.cosh (y/2)))
  rw [hzeros, hpoles, hprime, harch1, harch2, expTest_zero] at hkey
  have hkey2 : ((2*(σ - 1/2) * zeroSumSigma K σ : ℝ) : ℂ)
      = ((2/σ + 2/(σ - 1) + Real.log |NumberField.discr K|
        + (-(((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
            + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ))
              * (Real.eulerMascheroniConstant + Real.log (8*π))
            + (NumberField.InfinitePlace.nrRealPlaces K : ℝ) * (π/2)))
        + ((NumberField.InfinitePlace.nrRealPlaces K
            + 2*NumberField.InfinitePlace.nrComplexPlaces K : ℕ) : ℝ)
            * (∫ y in Set.Ioi (0:ℝ),
              1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y)))
        + (NumberField.InfinitePlace.nrRealPlaces K : ℝ)
            * (∫ y in Set.Ioi (0:ℝ),
              1/(2 * Real.cosh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y)))
        - 2 * vonMangoldtSum K σ : ℝ) : ℂ) := by
    rw [hkey]
    push_cast
    ring
  exact_mod_cast hkey2

/-! ### The Landau–Stark estimate (L5-c) -/

/-- **B–F's `d_{K,σ}`** (line 528), with the archimedean side kept in its integral
form (the digamma evaluation is a numeric-phase concern):
`d_{K,σ} = 2Σ log N𝔭·N𝔭^{−mσ} + [Γ-constant] − n·I_sinh(σ) − r₁·I_cosh(σ) − 2/σ`. -/
noncomputable def dSigma (K : Type*) [Field K] [NumberField K] (σ : ℝ) : ℝ :=
  2 * vonMangoldtSum K σ
    - (-(((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
        + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ))
          * (Real.eulerMascheroniConstant + Real.log (8*π))
        + (NumberField.InfinitePlace.nrRealPlaces K : ℝ) * (π/2)))
    - ((NumberField.InfinitePlace.nrRealPlaces K
        + 2*NumberField.InfinitePlace.nrComplexPlaces K : ℕ) : ℝ)
        * (∫ y in Set.Ioi (0:ℝ),
          1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y)))
    - (NumberField.InfinitePlace.nrRealPlaces K : ℝ)
        * (∫ y in Set.Ioi (0:ℝ),
          1/(2 * Real.cosh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y)))
    - 2/σ

/-- eq:Stark in `d_{K,σ}`-form: `2(σ−1/2)·Σ_σ = log Δ_K + 2/(σ−1) − d_{K,σ}`. -/
theorem stark_identity' (hGRH : GeneralizedRiemannHypothesis K) {σ : ℝ} (hσ : 1 < σ) :
    2*(σ - 1/2) * zeroSumSigma K σ
      = Real.log |NumberField.discr K| + 2/(σ - 1) - dSigma K σ := by
  rw [stark_identity K hGRH hσ, dSigma]
  ring

/-- **B–F Lemma 5 (`Estimate`, line 523)**: under GRH, for `σ > 1`,
`Σ_ρ m_ρ/(¼+γ_ρ²) ≤ (2σ−1)·(log Δ_K + 2/(σ−1) − d_{K,σ})`. -/
theorem landau_stark_estimate (hGRH : GeneralizedRiemannHypothesis K) {σ : ℝ}
    (hσ : 1 < σ) :
    zeroSumSigma K 1
      ≤ (2*σ - 1) * (Real.log |NumberField.discr K| + 2/(σ - 1) - dSigma K σ) := by
  have hZ : zeroSumSigma K 1 ≤ (2*σ - 1)^2 * zeroSumSigma K σ := by
    have hZ2 : (2*σ - 1)^2 * zeroSumSigma K σ
        = ∑' ρ : ZetaZeros K, (2*σ - 1)^2
            * ((zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2)) := by
      rw [zeroSumSigma, tsum_mul_left]
    rw [zeroSumSigma, hZ2]
    refine Summable.tsum_le_tsum (fun ρ => ?_)
      (summable_zetaZeros_inv_sq K ((1:ℝ) - 1/2) (by norm_num))
      (((summable_zetaZeros_inv_sq K (σ - 1/2) (by linarith)).mul_left _))
    have hm : (0:ℝ) ≤ (zetaZeroDivisor K ρ.1 : ℝ) := by
      exact_mod_cast zetaZeroDivisor_nonneg K ρ.1
    have hB : (0:ℝ) < ((1:ℝ) - 1/2)^2 + ρ.1.im^2 :=
      add_pos_of_pos_of_nonneg (by norm_num) (sq_nonneg _)
    have hA : (0:ℝ) < (σ - 1/2)^2 + ρ.1.im^2 :=
      add_pos_of_pos_of_nonneg (pow_pos (by linarith) 2) (sq_nonneg _)
    rw [mul_div_assoc', div_le_div_iff₀ hB hA]
    have h41 : (1:ℝ) ≤ (2*σ - 1)^2 := by nlinarith
    nlinarith [mul_nonneg hm (sq_nonneg ρ.1.im), sq_nonneg ρ.1.im,
      mul_nonneg (mul_nonneg hm (sq_nonneg ρ.1.im))
        (by nlinarith : (0:ℝ) ≤ (2*σ - 1)^2 - 1)]
  calc zeroSumSigma K 1 ≤ (2*σ - 1)^2 * zeroSumSigma K σ := hZ
    _ = (2*σ - 1) * (2*(σ - 1/2) * zeroSumSigma K σ) := by ring
    _ = (2*σ - 1) * (Real.log |NumberField.discr K| + 2/(σ - 1) - dSigma K σ) := by
        rw [stark_identity' K hGRH hσ]

end DedekindResidue

end
