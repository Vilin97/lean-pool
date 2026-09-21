/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # One Dim IBP -/

namespace Homogenization

open MeasureTheory intervalIntegral Set

/-!
# One-dimensional integration by parts across a kink

Standalone real-analysis lemma feeding the Fubini assembly of the single-face
even reflection.  A function that is `C¹` on each side of a point `a` and
continuous across it integrates by parts against a `C¹` compactly supported test
with no interface term — the two boundary contributions at `a` cancel because
the function matches there.
-/

noncomputable section

/-- **Integration by parts across a kink.**
If `f₁, f₂ : ℝ → ℝ` are `C¹` (globally, via `HasDerivAt` with continuous
derivatives) and agree at `a`, and `φ` is `C¹` with compact support, then the
piecewise function `t ↦ if t ≤ a then f₁ t else f₂ t` integrates by parts against
`φ'` with derivative the piecewise `t ↦ if t ≤ a then f₁' t else f₂' t` and **no**
boundary term. -/
theorem integral_mul_deriv_piecewise_eq_neg (a : ℝ)
    {f₁ f₂ f₁' f₂' φ φ' : ℝ → ℝ}
    (hf₁ : ∀ x, HasDerivAt f₁ (f₁' x) x) (hf₁' : Continuous f₁')
    (hf₂ : ∀ x, HasDerivAt f₂ (f₂' x) x) (hf₂' : Continuous f₂')
    (hmatch : f₁ a = f₂ a)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ' : Continuous φ')
    (hφ_supp : HasCompactSupport φ) :
    (∫ t, (if t ≤ a then f₁ t else f₂ t) * φ' t)
      = -∫ t, (if t ≤ a then f₁' t else f₂' t) * φ t := by
  have hcf₁ : Continuous f₁ :=
    continuous_iff_continuousAt.2 (fun x => (hf₁ x).continuousAt)
  have hcf₂ : Continuous f₂ :=
    continuous_iff_continuousAt.2 (fun x => (hf₂ x).continuousAt)
  have hcφ : Continuous φ :=
    continuous_iff_continuousAt.2 (fun x => (hφ x).continuousAt)
  -- φ' vanishes off the (compact) support of φ
  have hφ'_zero : ∀ x, x ∉ tsupport φ → φ' x = 0 := by
    intro x hx
    have hev : φ =ᶠ[nhds x] 0 :=
      (isClosed_tsupport φ).isOpen_compl.eventually_mem hx |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    have h0 : HasDerivAt φ 0 x := by
      have : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x := hasDerivAt_const x 0
      exact this.congr_of_eventuallyEq hev
    exact (hφ x).unique h0
  -- choose R with tsupport φ ⊆ Icc (-R₀) R₀ and a, ±R strictly outside support
  obtain ⟨R₀, hR₀⟩ := (hφ_supp.isBounded).subset_closedBall (0 : ℝ)
  set R := |R₀| + |a| + 1 with hRdef
  have hR_pos : 0 < R := by positivity
  have hsub_Icc : tsupport φ ⊆ Icc (-|R₀|) |R₀| := by
    intro x hx
    have := hR₀ hx
    rw [Real.closedBall_eq_Icc] at this
    simp only [zero_sub, zero_add] at this
    exact ⟨le_trans (neg_le_neg (le_abs_self R₀)) this.1,
      le_trans this.2 (le_abs_self R₀)⟩
  have hR₀_lt : |R₀| < R := by rw [hRdef]; have := abs_nonneg a; linarith
  have ha_mem : a ∈ Ioo (-R) R := by
    constructor
    · rw [hRdef]; have := neg_abs_le a; have := abs_nonneg R₀; linarith
    · rw [hRdef]; have := le_abs_self a; have := abs_nonneg R₀; linarith
  -- φ vanishes at ±R (they lie outside the support)
  have hnotin : ∀ y : ℝ, |R₀| < |y| → y ∉ tsupport φ := by
    intro y hy hymem
    have := hsub_Icc hymem
    rw [mem_Icc] at this
    have : |y| ≤ |R₀| := abs_le.2 ⟨this.1, this.2⟩
    linarith
  have hφR : φ R = 0 :=
    image_eq_zero_of_notMem_tsupport (hnotin R (by rw [abs_of_pos hR_pos]; exact hR₀_lt))
  have hφnegR : φ (-R) = 0 :=
    image_eq_zero_of_notMem_tsupport
      (hnotin (-R) (by rw [abs_neg, abs_of_pos hR_pos]; exact hR₀_lt))
  -- support of any function that vanishes off tsupport φ lands in Ioc (-R) R
  have hIoc : ∀ (F : ℝ → ℝ), (∀ x, x ∉ tsupport φ → F x = 0) →
      Function.support F ⊆ Ioc (-R) R := by
    intro F hF x hx
    rw [Function.mem_support] at hx
    have hmem : x ∈ tsupport φ := by
      by_contra hc; exact hx (hF x hc)
    have hxIcc := hsub_Icc hmem
    rw [mem_Icc] at hxIcc
    exact ⟨by linarith [hxIcc.1, hR₀_lt], le_of_lt (lt_of_le_of_lt hxIcc.2 hR₀_lt)⟩
  -- piecewise function and its piecewise derivative
  set pw : ℝ → ℝ := fun t => if t ≤ a then f₁ t else f₂ t with hpw
  set pwd : ℝ → ℝ := fun t => if t ≤ a then f₁' t else f₂' t with hpwd
  have hle : -R ≤ a := le_of_lt ha_mem.1
  have hle' : a ≤ R := le_of_lt ha_mem.2
  have hpw_cont : Continuous pw := by
    refine Continuous.if_le hcf₁ hcf₂ continuous_id continuous_const ?_
    intro x hx; rw [hx]; exact hmatch
  -- integrands vanish off tsupport φ, so ℝ-integrals become interval integrals
  have hFsupp : Function.support (fun t => pw t * φ' t) ⊆ Ioc (-R) R :=
    hIoc _ (fun x hx => by simp [hφ'_zero x hx])
  have hGsupp : Function.support (fun t => pwd t * φ t) ⊆ Ioc (-R) R :=
    hIoc _ (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  -- interval-integrability of the four pieces
  have hFII1 : IntervalIntegrable (fun t => pw t * φ' t) volume (-R) a :=
    (hpw_cont.mul hφ').intervalIntegrable _ _
  have hFII2 : IntervalIntegrable (fun t => pw t * φ' t) volume a R :=
    (hpw_cont.mul hφ').intervalIntegrable _ _
  have hGII1 : IntervalIntegrable (fun t => pwd t * φ t) volume (-R) a := by
    refine (intervalIntegrable_congr (f := fun t => f₁' t * φ t) ?_).mp
      ((hf₁'.mul hcφ).intervalIntegrable _ _)
    intro t ht
    rw [uIoc_of_le hle, mem_Ioc] at ht
    simp [hpwd, if_pos ht.2]
  have hGII2 : IntervalIntegrable (fun t => pwd t * φ t) volume a R := by
    refine (intervalIntegrable_congr (f := fun t => f₂' t * φ t) ?_).mp
      ((hf₂'.mul hcφ).intervalIntegrable _ _)
    intro t ht
    rw [uIoc_of_le hle', mem_Ioc] at ht
    simp [hpwd, if_neg (not_le.mpr ht.1)]
  -- the four interval-integral evaluations
  have hL1 : ∫ t in (-R)..a, pw t * φ' t
      = f₁ a * φ a - ∫ t in (-R)..a, f₁' t * φ t := by
    rw [integral_congr (g := fun t => f₁ t * φ' t) (fun t ht => by
      rw [uIcc_of_le hle, mem_Icc] at ht; simp [hpw, if_pos ht.2])]
    rw [integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hcf₁.continuousOn hcφ.continuousOn
      (fun x _ => hf₁ x) (fun x _ => hφ x)
      (hf₁'.intervalIntegrable _ _) (hφ'.intervalIntegrable _ _)]
    rw [hφnegR, mul_zero, sub_zero]
  have hL2 : ∫ t in a..R, pw t * φ' t
      = -(f₂ a * φ a) - ∫ t in a..R, f₂' t * φ t := by
    rw [integral_congr (g := fun t => f₂ t * φ' t) (fun t ht => by
      rw [uIcc_of_le hle', mem_Icc] at ht
      by_cases h : t ≤ a
      · have hta : t = a := le_antisymm h ht.1
        subst hta; simp [hpw, if_pos h, hmatch]
      · simp [hpw, if_neg h])]
    rw [integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hcf₂.continuousOn hcφ.continuousOn
      (fun x _ => hf₂ x) (fun x _ => hφ x)
      (hf₂'.intervalIntegrable _ _) (hφ'.intervalIntegrable _ _)]
    rw [hφR, mul_zero, zero_sub]
  have hR1 : ∫ t in (-R)..a, pwd t * φ t = ∫ t in (-R)..a, f₁' t * φ t :=
    integral_congr (fun t ht => by
      rw [uIcc_of_le hle, mem_Icc] at ht; simp [hpwd, if_pos ht.2])
  have hR2 : ∫ t in a..R, pwd t * φ t = ∫ t in a..R, f₂' t * φ t :=
    integral_congr_ae (Filter.Eventually.of_forall (fun t ht => by
      rw [uIoc_of_le hle', mem_Ioc] at ht
      simp [hpwd, if_neg (not_le.mpr ht.1)]))
  -- assemble
  rw [← integral_eq_integral_of_support_subset hFsupp,
      ← integral_eq_integral_of_support_subset hGsupp,
      ← integral_add_adjacent_intervals hFII1 hFII2,
      ← integral_add_adjacent_intervals hGII1 hGII2,
      hL1, hL2, hR1, hR2, hmatch]
  ring

/-- **One-dimensional integration by parts** (globally `C¹` special case).
No interface, no boundary term. -/
theorem integral_mul_deriv_eq_neg
    {f f' φ φ' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ' : Continuous φ')
    (hφ_supp : HasCompactSupport φ) :
    (∫ t, f t * φ' t) = -∫ t, f' t * φ t := by
  have h := integral_mul_deriv_piecewise_eq_neg (a := 0)
    hf hf' hf hf' rfl hφ hφ' hφ_supp
  simpa only [ite_self] using h

/-- A dichotomous integrand times a continuous compactly supported test is
integrable (each branch is continuous). -/
private theorem integrable_ite_mul {p : ℝ → Prop} [DecidablePred p]
    (hp : MeasurableSet {t | p t}) {g₁ g₂ φ : ℝ → ℝ}
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun t => (if p t then g₁ t else g₂ t) * φ t) := by
  have hsplit : (fun t => (if p t then g₁ t else g₂ t) * φ t)
      = fun t => (if p t then g₁ t * φ t else 0) + (if p t then 0 else g₂ t * φ t) := by
    funext t; by_cases h : p t <;> simp [h]
  rw [hsplit]
  refine Integrable.add ?_ ?_
  · rw [show (fun t => if p t then g₁ t * φ t else 0)
        = Set.indicator {t | p t} (fun t => g₁ t * φ t) from by
      funext t; by_cases h : p t <;> simp [Set.indicator, h]]
    exact ((hg₁.mul hφ).integrable_of_hasCompactSupport hφc.mul_left).indicator hp
  · rw [show (fun t => if p t then 0 else g₂ t * φ t)
        = Set.indicator {t | p t}ᶜ (fun t => g₂ t * φ t) from by
      funext t; by_cases h : p t <;> simp [Set.indicator, h]]
    exact ((hg₂.mul hφ).integrable_of_hasCompactSupport hφc.mul_left).indicator hp.compl

/-- Almost every real number differs from a fixed point. -/
private theorem ae_ne_pt (b : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by
  rw [MeasureTheory.ae_iff]; simp

/-- Additivity of the integral over a three-term pointwise sum. -/
private theorem integral_add3 {g1 g2 g3 : ℝ → ℝ}
    (h1 : Integrable g1) (h2 : Integrable g2) (h3 : Integrable g3) :
    (∫ t, g1 t + g2 t + g3 t) = (∫ t, g1 t) + (∫ t, g2 t) + (∫ t, g3 t) := by
  rw [show (∫ t, g1 t + g2 t + g3 t)
        = (∫ t, g1 t + g2 t) + ∫ t, g3 t from
      MeasureTheory.integral_add (h1.add h2) h3,
    MeasureTheory.integral_add h1 h2]

/-- **Integration by parts across two kinks.**
If `f₁, f₂, f₃` are globally `C¹` and match at `b₁ ≤ b₂` (`f₁ b₁ = f₂ b₁`,
`f₂ b₂ = f₃ b₂`), the continuous piecewise function
`t ↦ if t < b₁ then f₁ t else if b₂ < t then f₃ t else f₂ t` integrates by parts
against a `C¹` compactly supported test with the piecewise derivative and **no**
boundary term. -/
theorem integral_mul_deriv_two_kink_eq_neg (b₁ b₂ : ℝ) (hb : b₁ ≤ b₂)
    {f₁ f₂ f₃ f₁' f₂' f₃' φ φ' : ℝ → ℝ}
    (hf₁ : ∀ x, HasDerivAt f₁ (f₁' x) x) (hf₁' : Continuous f₁')
    (hf₂ : ∀ x, HasDerivAt f₂ (f₂' x) x) (hf₂' : Continuous f₂')
    (hf₃ : ∀ x, HasDerivAt f₃ (f₃' x) x) (hf₃' : Continuous f₃')
    (hm₁ : f₁ b₁ = f₂ b₁) (hm₂ : f₂ b₂ = f₃ b₂)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ' : Continuous φ') (hφc : HasCompactSupport φ) :
    (∫ t, (if t < b₁ then f₁ t else if b₂ < t then f₃ t else f₂ t) * φ' t)
      = -∫ t, (if t < b₁ then f₁' t else if b₂ < t then f₃' t else f₂' t) * φ t := by
  classical
  have hcφ : Continuous φ :=
    continuous_iff_continuousAt.2 (fun x => (hφ x).continuousAt)
  have hcf₂ : Continuous f₂ :=
    continuous_iff_continuousAt.2 (fun x => (hf₂ x).continuousAt)
  -- `φ'` is compactly supported
  have hφ'_zero : ∀ x, x ∉ tsupport φ → φ' x = 0 := by
    intro x hx
    have hev : φ =ᶠ[nhds x] 0 :=
      (isClosed_tsupport φ).isOpen_compl.eventually_mem hx |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    exact (hφ x).unique ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev)
  have hφ'c : HasCompactSupport φ' :=
    HasCompactSupport.intro (K := tsupport φ) hφc hφ'_zero
  have hcf₁ : Continuous f₁ :=
    continuous_iff_continuousAt.2 (fun x => (hf₁ x).continuousAt)
  have hcf₃ : Continuous f₃ :=
    continuous_iff_continuousAt.2 (fun x => (hf₃ x).continuousAt)
  -- three integration-by-parts identities
  have hE0 : (∫ t, f₂ t * φ' t) = -∫ t, f₂' t * φ t :=
    integral_mul_deriv_eq_neg hf₂ hf₂' hφ hφ' hφc
  have hE1 : (∫ t, (if t ≤ b₁ then f₁ t - f₂ t else 0) * φ' t)
      = -∫ t, (if t ≤ b₁ then f₁' t - f₂' t else 0) * φ t := by
    have h := integral_mul_deriv_piecewise_eq_neg b₁
      (f₁ := fun t => f₁ t - f₂ t) (f₂ := fun _ => (0 : ℝ))
      (f₁' := fun t => f₁' t - f₂' t) (f₂' := fun _ => (0 : ℝ))
      (fun x => (hf₁ x).sub (hf₂ x)) (hf₁'.sub hf₂')
      (fun x => hasDerivAt_const x 0) continuous_const
      (sub_eq_zero.mpr hm₁) hφ hφ' hφc
    simpa using h
  have hE2 : (∫ t, (if t ≤ b₂ then (0 : ℝ) else f₃ t - f₂ t) * φ' t)
      = -∫ t, (if t ≤ b₂ then (0 : ℝ) else f₃' t - f₂' t) * φ t := by
    have h := integral_mul_deriv_piecewise_eq_neg b₂
      (f₁ := fun _ => (0 : ℝ)) (f₂ := fun t => f₃ t - f₂ t)
      (f₁' := fun _ => (0 : ℝ)) (f₂' := fun t => f₃' t - f₂' t)
      (fun x => hasDerivAt_const x 0) continuous_const
      (fun x => (hf₃ x).sub (hf₂ x)) (hf₃'.sub hf₂')
      (by simpa using (sub_eq_zero.mpr hm₂.symm).symm) hφ hφ' hφc
    simpa using h
  -- integrabilities
  have hI0 : Integrable (fun t => f₂ t * φ' t) :=
    (hcf₂.mul hφ').integrable_of_hasCompactSupport hφ'c.mul_left
  have hIc1 : Integrable (fun t => (if t ≤ b₁ then f₁ t - f₂ t else 0) * φ' t) :=
    integrable_ite_mul measurableSet_Iic (hcf₁.sub hcf₂) continuous_const hφ' hφ'c
  have hIc2 : Integrable (fun t => (if t ≤ b₂ then (0 : ℝ) else f₃ t - f₂ t) * φ' t) :=
    integrable_ite_mul measurableSet_Iic continuous_const (hcf₃.sub hcf₂) hφ' hφ'c
  have hJ0 : Integrable (fun t => f₂' t * φ t) :=
    (hf₂'.mul hcφ).integrable_of_hasCompactSupport hφc.mul_left
  have hJc1 : Integrable (fun t => (if t ≤ b₁ then f₁' t - f₂' t else 0) * φ t) :=
    integrable_ite_mul measurableSet_Iic (hf₁'.sub hf₂') continuous_const hcφ hφc
  have hJc2 : Integrable (fun t => (if t ≤ b₂ then (0 : ℝ) else f₃' t - f₂' t) * φ t) :=
    integrable_ite_mul measurableSet_Iic continuous_const (hf₃'.sub hf₂') hcφ hφc
  -- pointwise decompositions
  have hFsum : ∀ t, (if t < b₁ then f₁ t else if b₂ < t then f₃ t else f₂ t)
      = f₂ t + (if t ≤ b₁ then f₁ t - f₂ t else 0)
        + (if t ≤ b₂ then (0 : ℝ) else f₃ t - f₂ t) := by
    intro t
    rcases lt_trichotomy t b₁ with h | h | h
    · rw [if_pos h, if_pos (le_of_lt h), if_pos (le_of_lt (lt_of_lt_of_le h hb))]; ring
    · subst h
      rw [if_neg (lt_irrefl _), if_neg (by linarith : ¬ b₂ < t),
        if_pos (le_refl t), if_pos (by linarith : t ≤ b₂), hm₁]; ring
    · rw [if_neg (not_lt.mpr (le_of_lt h)), if_neg (by linarith : ¬ t ≤ b₁)]
      rcases lt_trichotomy t b₂ with h2 | h2 | h2
      · rw [if_neg (not_lt.mpr (le_of_lt h2)), if_pos (le_of_lt h2)]; ring
      · subst h2
        rw [if_neg (lt_irrefl _), if_pos (le_refl t)]; ring
      · rw [if_pos h2, if_neg (by linarith : ¬ t ≤ b₂)]; ring
  have hPWD : ∀ t, t ≠ b₁ → t ≠ b₂ →
      f₂' t + (if t ≤ b₁ then f₁' t - f₂' t else 0)
        + (if t ≤ b₂ then (0 : ℝ) else f₃' t - f₂' t)
      = (if t < b₁ then f₁' t else if b₂ < t then f₃' t else f₂' t) := by
    intro t ht1 ht2
    rcases lt_trichotomy t b₁ with h | h | h
    · rw [if_pos (le_of_lt h), if_pos (le_of_lt (lt_of_lt_of_le h hb)), if_pos h]; ring
    · exact absurd h ht1
    · rw [if_neg (by linarith : ¬ t ≤ b₁), if_neg (not_lt.mpr (le_of_lt h))]
      rcases lt_trichotomy t b₂ with h2 | h2 | h2
      · rw [if_pos (le_of_lt h2), if_neg (not_lt.mpr (le_of_lt h2))]; ring
      · exact absurd h2 ht2
      · rw [if_neg (by linarith : ¬ t ≤ b₂), if_pos h2]; ring
  -- assemble
  calc (∫ t, (if t < b₁ then f₁ t else if b₂ < t then f₃ t else f₂ t) * φ' t)
      = ∫ t, (f₂ t * φ' t + (if t ≤ b₁ then f₁ t - f₂ t else 0) * φ' t
                + (if t ≤ b₂ then (0 : ℝ) else f₃ t - f₂ t) * φ' t) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => by
          simp only [hFsum t]; ring)
    _ = (∫ t, f₂ t * φ' t) + (∫ t, (if t ≤ b₁ then f₁ t - f₂ t else 0) * φ' t)
          + (∫ t, (if t ≤ b₂ then (0 : ℝ) else f₃ t - f₂ t) * φ' t) :=
        integral_add3 hI0 hIc1 hIc2
    _ = -((∫ t, f₂' t * φ t) + (∫ t, (if t ≤ b₁ then f₁' t - f₂' t else 0) * φ t)
          + (∫ t, (if t ≤ b₂ then (0 : ℝ) else f₃' t - f₂' t) * φ t)) := by
        rw [hE0, hE1, hE2]; ring
    _ = -(∫ t, (f₂' t * φ t + (if t ≤ b₁ then f₁' t - f₂' t else 0) * φ t
                + (if t ≤ b₂ then (0 : ℝ) else f₃' t - f₂' t) * φ t)) := by
        rw [integral_add3 hJ0 hJc1 hJc2]
    _ = -∫ t, (if t < b₁ then f₁' t else if b₂ < t then f₃' t else f₂' t) * φ t := by
        congr 1
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [ae_ne_pt b₁, ae_ne_pt b₂] with t ht1 ht2
        simp only [← hPWD t ht1 ht2]; ring

end

end Homogenization
