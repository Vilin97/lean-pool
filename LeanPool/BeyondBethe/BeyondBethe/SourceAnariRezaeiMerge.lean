/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.SourceAnariRezaei

/-! # Source Anari Rezaei Merge -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# The Anari--Rezaei merge argument

This file formalizes the dimension-reduction lemma in the source proof.  We
use the rational cutoff `14/25`; it is smaller than the source cutoff and its
complement is exactly the `11/25` used by the analytic three-variable proof.
-/

/-- Loss in `phi` before two adjacent masses `r,s` are merged. -/
noncomputable def anariRezaeiMergeGap (q r s t : ℝ) : ℝ :=
  r * Real.log ((q+r)/(q+r+s)) +
    s * Real.log ((s+t)/(r+s+t)) -
    2*(1-r)*Real.log (1-r) -
    2*(1-s)*Real.log (1-s) +
    2*(1-r-s)*Real.log (1-r-s)

/-- The value of the merge gap at its stationary choice of the exterior
masses. -/
noncomputable def anariRezaeiMergePsi (r s : ℝ) : ℝ :=
  -(r+s)*Real.log (1+r+s) +
    (s-r)*Real.log ((1+s)/(1+r)) -
    2*(1-r)*Real.log (1-r) -
    2*(1-s)*Real.log (1-s) +
    2*(1-r-s)*Real.log (1-r-s)

noncomputable def anariRezaeiMergePsiAlong (C x : ℝ) : ℝ :=
  anariRezaeiMergePsi x (C-x)

noncomputable def anariRezaeiMergePsiDerivative (r s : ℝ) : ℝ :=
  -2*Real.log ((1+s)/(1+r)) -
    (s-r)*(1/(1+r)+1/(1+s)) +
    2*Real.log ((1-r)/(1-s))

theorem anariRezaeiMergePsi_zero (C : ℝ) :
    anariRezaeiMergePsi 0 C = 0 := by
  rw [anariRezaeiMergePsi]
  norm_num

theorem hasDerivAt_anariRezaeiMergePsiAlong
    {C x : ℝ} (hx0 : 0 ≤ x) (hxC : x ≤ C)
    (hC : C < 1) :
    HasDerivAt (anariRezaeiMergePsiAlong C)
      (anariRezaeiMergePsiDerivative x (C-x)) x := by
  have h1px : 1+x ≠ 0 := by linarith
  have h1ps : 1+(C-x) ≠ 0 := by linarith
  have h1mx : 1-x ≠ 0 := by linarith
  have h1ms : 1-(C-x) ≠ 0 := by linarith
  have hconst : HasDerivAt (fun _y : ℝ ↦ C) 0 x := hasDerivAt_const x C
  have hid := hasDerivAt_id x
  have hs := hconst.sub hid
  have h1px' := (hasDerivAt_const x 1).add hid
  have h1ps' := (hasDerivAt_const x 1).add hs
  have hratioPlus := h1ps'.div h1px' h1px
  have hlogPlus := (Real.hasDerivAt_log (div_ne_zero h1ps h1px)).comp x hratioPlus
  have hdiff := hs.sub hid
  have hmiddle := hdiff.mul hlogPlus
  have h1mx' := (hasDerivAt_const x 1).sub hid
  have h1ms' := (hasDerivAt_const x 1).sub hs
  have hlogmx := (Real.hasDerivAt_log h1mx).comp x h1mx'
  have hlogms := (Real.hasDerivAt_log h1ms).comp x h1ms'
  have hxm := (h1mx'.mul hlogmx).const_mul (-2)
  have hsm := (h1ms'.mul hlogms).const_mul (-2)
  have hlast : HasDerivAt
      (fun _y : ℝ ↦ 2*(1-C)*Real.log (1-C)) 0 x :=
    hasDerivAt_const x _
  have hfirst : HasDerivAt
      (fun _y : ℝ ↦ -C*Real.log (1+C)) 0 x :=
    hasDerivAt_const x _
  have hd := (((hfirst.add hmiddle).add hxm).add hsm).add hlast
  convert! hd using 1
  · funext y
    simp only [anariRezaeiMergePsiAlong, anariRezaeiMergePsi,
      Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.div_apply, id_eq]
    ring
  · dsimp [anariRezaeiMergePsiDerivative]
    rw [Real.log_div h1mx h1ms]
    try simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply,
      Pi.mul_apply, Pi.div_apply, id_eq]
    field_simp [h1px, h1ps, h1mx, h1ms]
    ring

/-- The derivative of `psi(x,C-x)` is nonpositive on its first half.  The
proof uses the elementary hyperbolic logarithm bound and exact polynomial
arithmetic; it replaces the integral estimate in the source. -/
theorem anariRezaeiMergePsiDerivative_nonpos
    {r s : ℝ} (hr0 : 0 ≤ r) (hrs : r ≤ s)
    (hC : r+s ≤ 14/25) :
    anariRezaeiMergePsiDerivative r s ≤ 0 := by
  have hs0 : 0 ≤ s := hr0.trans hrs
  have hs1 : s < 1 := (le_add_of_nonneg_left hr0).trans hC |>.trans_lt (by norm_num)
  have hr1 : r < 1 := hrs.trans_lt hs1
  have h1mr : 0 < 1-r := sub_pos.mpr hr1
  have h1ms : 0 < 1-s := sub_pos.mpr hs1
  have h1pr : 0 < 1+r := by linarith
  have h1ps : 0 < 1+s := by linarith
  let z : ℝ := (1-r^2)/(1-s^2)
  have hden : 0 < 1-s^2 := by nlinarith
  have hnum : 0 < 1-r^2 := by nlinarith
  have hzpos : 0 < z := div_pos hnum hden
  have hz1 : 1 ≤ z := by
    apply (one_le_div hden).mpr
    nlinarith [mul_self_le_mul_self (by linarith : 0 ≤ r) hrs]
  have hlog := two_mul_log_le_sub_inv hz1
  have hcut : 0 ≤ 2-3*(r+s)-(r+s)^2 := by
    have hfac : 0 ≤ (14/25-(r+s))*(3+14/25+(r+s)) :=
      mul_nonneg (sub_nonneg.mpr hC) (by positivity)
    nlinarith
  have hrat : z-1/z ≤
      (s-r)*(1/(1+r)+1/(1+s)) := by
    dsimp [z]
    have hA : 1-r^2 ≠ 0 := hnum.ne'
    have hB : 1-s^2 ≠ 0 := hden.ne'
    field_simp [hA, hB, h1pr.ne', h1ps.ne']
    have hrs0 : 0 ≤ r*s := mul_nonneg hr0 hs0
    have h2C : 0 ≤ 2-(r+s) := by linarith
    have hextra : 0 ≤ (r+s)^3 + (2-(r+s))*(r*s) :=
      add_nonneg (pow_nonneg (add_nonneg hr0 hs0) 3)
        (mul_nonneg h2C hrs0)
    have hD : 0 ≤ 2-3*(r+s)-(r+s)^2 +
        ((r+s)^3 + (2-(r+s))*(r*s)) := add_nonneg hcut hextra
    have hfactor : 0 ≤ (s-r)*(1+r)*(1+s)*
        (2-3*(r+s)-(r+s)^2 +
          ((r+s)^3 + (2-(r+s))*(r*s))) := by positivity
    nlinarith
  have hlogRewrite : Real.log z =
      Real.log ((1-r)/(1-s)) - Real.log ((1+s)/(1+r)) := by
    have hzEq : z = ((1-r)/(1-s))/((1+s)/(1+r)) := by
      dsimp [z]
      field_simp [h1mr.ne', h1ms.ne', h1pr.ne', h1ps.ne']
      ring
    rw [hzEq, Real.log_div (div_ne_zero h1mr.ne' h1ms.ne')
      (div_ne_zero h1ps.ne' h1pr.ne')]
  rw [hlogRewrite] at hlog
  rw [anariRezaeiMergePsiDerivative]
  linarith

theorem anariRezaeiMergePsi_nonpos_ordered
    {r s : ℝ} (hr0 : 0 ≤ r) (hrs : r ≤ s)
    (hC : r+s ≤ 14/25) :
    anariRezaeiMergePsi r s ≤ 0 := by
  let C := r+s
  have hC0 : 0 ≤ C := add_nonneg hr0 (hr0.trans hrs)
  have hrC : r ≤ C := le_add_of_nonneg_right (hr0.trans hrs)
  have hClt : C < 1 := hC.trans_lt (by norm_num)
  have hcont : ContinuousOn (anariRezaeiMergePsiAlong C) (Set.Icc 0 r) := by
    intro x hx
    exact (hasDerivAt_anariRezaeiMergePsiAlong hx.1 (hx.2.trans hrC) hClt).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (anariRezaeiMergePsiAlong C)
      (interior (Set.Icc 0 r)) := by
    intro x hx
    have hx' : 0 < x ∧ x < r := by simpa using hx
    exact (hasDerivAt_anariRezaeiMergePsiAlong hx'.1.le
      (hx'.2.le.trans hrC) hClt).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn (anariRezaeiMergePsiAlong C) (Set.Icc 0 r) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 r) hcont hdiff fun x hx ↦ by
      have hx' : 0 < x ∧ x < r := by simpa using hx
      rw [(hasDerivAt_anariRezaeiMergePsiAlong hx'.1.le
        (hx'.2.le.trans hrC) hClt).deriv]
      apply anariRezaeiMergePsiDerivative_nonpos hx'.1.le
      · dsimp [C]
        linarith
      · dsimp [C]
        ring_nf
        exact hC
  have hle := hanti ⟨le_rfl, hr0⟩ ⟨hr0, le_rfl⟩ hr0
  dsimp [anariRezaeiMergePsiAlong, C] at hle
  rw [show r+s-r=s by ring, anariRezaeiMergePsi_zero] at hle
  exact hle

theorem anariRezaeiMergePsi_comm
    {r s : ℝ} (hr0 : 0 ≤ r) (hs0 : 0 ≤ s) :
    anariRezaeiMergePsi r s = anariRezaeiMergePsi s r := by
  have h1pr : 1+r ≠ 0 := by linarith
  have h1ps : 1+s ≠ 0 := by linarith
  rw [anariRezaeiMergePsi, anariRezaeiMergePsi]
  rw [Real.log_div h1ps h1pr, Real.log_div h1pr h1ps]
  ring

theorem anariRezaeiMergePsi_nonpos
    {r s : ℝ} (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hC : r+s ≤ 14/25) :
    anariRezaeiMergePsi r s ≤ 0 := by
  rcases le_total r s with hrs | hsr
  · exact anariRezaeiMergePsi_nonpos_ordered hr0 hrs hC
  · rw [anariRezaeiMergePsi_comm hr0 hs0]
    exact anariRezaeiMergePsi_nonpos_ordered hs0 hsr (by linarith)

noncomputable def anariRezaeiMergeQStar (r s : ℝ) : ℝ :=
  (1-r*(1+r+s))/(2+r+s)

noncomputable def anariRezaeiMergeTStar (r s : ℝ) : ℝ :=
  (1-s*(1+r+s))/(2+r+s)

private theorem anariRezaeiCutoff_product
    {C : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ 14/25) :
    C*(1+C) < 1 := by
  have hfac : 0 ≤ (14/25-C)*(1+14/25+C) :=
    mul_nonneg (sub_nonneg.mpr hC) (by positivity)
  nlinarith

theorem anariRezaeiMergeStars_nonnegative
    {r s : ℝ} (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hC : r+s ≤ 14/25) :
    0 ≤ anariRezaeiMergeQStar r s ∧
      0 ≤ anariRezaeiMergeTStar r s := by
  have hC0 : 0 ≤ r+s := add_nonneg hr0 hs0
  have hprod := anariRezaeiCutoff_product hC0 hC
  have hrC : r ≤ r+s := le_add_of_nonneg_right hs0
  have hsC : s ≤ r+s := le_add_of_nonneg_left hr0
  have hden : 0 < 2+r+s := by linarith
  constructor
  · rw [anariRezaeiMergeQStar]
    exact div_nonneg (by nlinarith) hden.le
  · rw [anariRezaeiMergeTStar]
    exact div_nonneg (by nlinarith) hden.le

theorem anariRezaeiMergeStars_sum (r s : ℝ) (hden : 2+r+s ≠ 0) :
    anariRezaeiMergeQStar r s + anariRezaeiMergeTStar r s =
      1-r-s := by
  rw [anariRezaeiMergeQStar, anariRezaeiMergeTStar]
  field_simp [hden]
  ring

noncomputable def anariRezaeiMergeGapAlong (r s x : ℝ) : ℝ :=
  anariRezaeiMergeGap x r s (1-r-s-x)

noncomputable def anariRezaeiMergeGapDerivative (r s x : ℝ) : ℝ :=
  r*s*(1/((x+r)*(x+r+s)) -
    1/((1-r-x)*(1-x)))

theorem hasDerivAt_anariRezaeiMergeGapAlong
    {r s x : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hx0 : 0 ≤ x) (ht0 : 0 ≤ 1-r-s-x) :
    HasDerivAt (anariRezaeiMergeGapAlong r s)
      (anariRezaeiMergeGapDerivative r s x) x := by
  have hxr : 0 < x+r := add_pos_of_nonneg_of_pos hx0 hr
  have hxC : 0 < x+r+s := add_pos hxr hs
  have hst : 0 < s+(1-r-s-x) := add_pos_of_pos_of_nonneg hs ht0
  have hCt : 0 < r+s+(1-r-s-x) := add_pos_of_pos_of_nonneg (add_pos hr hs) ht0
  have hid := hasDerivAt_id x
  have hxR := hid.add_const r
  have hxC' := (hid.add_const r).add_const s
  have hratio1 := hxR.div hxC' hxC.ne'
  have hlog1 := (Real.hasDerivAt_log (div_ne_zero hxr.ne' hxC.ne')).comp x hratio1
  have hst2 : 0 < 1-r-x := by linarith
  have hCt2 : 0 < 1-x := by linarith
  have hsT' := (hasDerivAt_const x (1-r)).sub hid
  have hCT' := (hasDerivAt_const x 1).sub hid
  have hratio2 := hsT'.div hCT' hCt2.ne'
  have hlog2 := (Real.hasDerivAt_log
    (div_ne_zero hst2.ne' hCt2.ne')).comp x hratio2
  have hvar := (hlog1.const_mul r).add (hlog2.const_mul s)
  have hconst : HasDerivAt (fun _y : ℝ ↦
      -2*(1-r)*Real.log (1-r) -
      2*(1-s)*Real.log (1-s) +
      2*(1-r-s)*Real.log (1-r-s)) 0 x := hasDerivAt_const x _
  have hd := hvar.add hconst
  convert! hd using 1
  · funext y
    simp only [anariRezaeiMergeGapAlong, anariRezaeiMergeGap,
      Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, id_eq]
    ring
  · dsimp [anariRezaeiMergeGapDerivative]
    try simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply,
      Pi.div_apply, id_eq]
    field_simp [hxr.ne', hxC.ne', hst2.ne', hCt2.ne']
    ring

theorem anariRezaeiMergeGapDerivative_sign
    {r s x : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hx0 : 0 ≤ x) (ht0 : 0 ≤ 1-r-s-x) :
    (0 ≤ anariRezaeiMergeGapDerivative r s x ↔
      x ≤ anariRezaeiMergeQStar r s) ∧
    (anariRezaeiMergeGapDerivative r s x ≤ 0 ↔
      anariRezaeiMergeQStar r s ≤ x) := by
  have hxr : 0 < x+r := add_pos_of_nonneg_of_pos hx0 hr
  have hxC : 0 < x+r+s := add_pos hxr hs
  have hst : 0 < 1-r-x := by linarith
  have hCt : 0 < 1-x := by linarith
  have hden : 0 < (x+r)*(x+r+s)*(1-r-x)*(1-x) := by positivity
  have hstar : 0 < 2+r+s := by positivity
  have hid : anariRezaeiMergeGapDerivative r s x =
      r*s*(1-r*(1+r+s)-(2+r+s)*x) /
        ((x+r)*(x+r+s)*(1-r-x)*(1-x)) := by
    rw [anariRezaeiMergeGapDerivative]
    field_simp [hxr.ne', hxC.ne', hst.ne', hCt.ne']
    ring
  rw [hid]
  have hrs : 0 < r*s := mul_pos hr hs
  constructor
  · constructor
    · intro h
      have hmul := mul_nonneg h hden.le
      rw [div_mul_cancel₀ _ hden.ne'] at hmul
      have hlin : 0 ≤ 1-r*(1+r+s)-(2+r+s)*x :=
        nonneg_of_mul_nonneg_right hmul hrs
      rw [anariRezaeiMergeQStar, (le_div_iff₀ hstar)]
      linarith
    · intro h
      rw [anariRezaeiMergeQStar, (le_div_iff₀ hstar)] at h
      exact div_nonneg (mul_nonneg hrs.le (by linarith)) hden.le
  · constructor
    · intro h
      have hmul := mul_nonpos_of_nonpos_of_nonneg h hden.le
      rw [div_mul_cancel₀ _ hden.ne'] at hmul
      have hlin : 1-r*(1+r+s)-(2+r+s)*x ≤ 0 :=
        nonpos_of_mul_nonpos_right hmul hrs
      rw [anariRezaeiMergeQStar, (div_le_iff₀ hstar)]
      linarith
    · intro h
      rw [anariRezaeiMergeQStar, (div_le_iff₀ hstar)] at h
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hrs.le (by linarith)) hden.le

theorem anariRezaeiMergeGap_le_stationary
    {q r s t : ℝ} (hq0 : 0 ≤ q) (hr : 0 < r) (hs : 0 < s)
    (ht0 : 0 ≤ t) (hsum : q+r+s+t = 1)
    (hC : r+s ≤ 14/25) :
    anariRezaeiMergeGap q r s t ≤
      anariRezaeiMergeGap (anariRezaeiMergeQStar r s) r s
        (anariRezaeiMergeTStar r s) := by
  have hstars := anariRezaeiMergeStars_nonnegative hr.le hs.le hC
  have hqstar0 := hstars.1
  have htstar0 := hstars.2
  have htEq : t = 1-r-s-q := by linarith
  have hden : 2+r+s ≠ 0 := by positivity
  have hstarEq : anariRezaeiMergeTStar r s =
      1-r-s-anariRezaeiMergeQStar r s := by
    linarith [anariRezaeiMergeStars_sum r s hden]
  have hcapStar : 0 ≤ 1-r-s-anariRezaeiMergeQStar r s := by
    rw [← hstarEq]
    exact htstar0
  subst t
  rw [hstarEq]
  change anariRezaeiMergeGapAlong r s q ≤
    anariRezaeiMergeGapAlong r s (anariRezaeiMergeQStar r s)
  rcases le_total q (anariRezaeiMergeQStar r s) with hq | hq
  · have hcont : ContinuousOn (anariRezaeiMergeGapAlong r s)
        (Set.Icc q (anariRezaeiMergeQStar r s)) := by
      intro x hx
      exact (hasDerivAt_anariRezaeiMergeGapAlong hr hs
        (hq0.trans hx.1) (by linarith [hcapStar, hx.2])).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (anariRezaeiMergeGapAlong r s)
        (interior (Set.Icc q (anariRezaeiMergeQStar r s))) := by
      intro x hx
      have hx' : q < x ∧ x < anariRezaeiMergeQStar r s := by simpa using hx
      exact (hasDerivAt_anariRezaeiMergeGapAlong hr hs
        (hq0.trans hx'.1.le) (by linarith [hcapStar, hx'.2.le])).differentiableAt.differentiableWithinAt
    have hmono := monotoneOn_of_deriv_nonneg
      (convex_Icc q (anariRezaeiMergeQStar r s)) hcont hdiff fun x hx ↦ by
        have hx' : q < x ∧ x < anariRezaeiMergeQStar r s := by simpa using hx
        rw [(hasDerivAt_anariRezaeiMergeGapAlong hr hs
          (hq0.trans hx'.1.le) (by linarith [hcapStar, hx'.2.le])).deriv]
        exact (anariRezaeiMergeGapDerivative_sign hr hs
          (hq0.trans hx'.1.le) (by linarith [hcapStar, hx'.2.le])).1.mpr hx'.2.le
    exact hmono ⟨le_rfl, hq⟩ ⟨hq, le_rfl⟩ hq
  · have hcont : ContinuousOn (anariRezaeiMergeGapAlong r s)
        (Set.Icc (anariRezaeiMergeQStar r s) q) := by
      intro x hx
      exact (hasDerivAt_anariRezaeiMergeGapAlong hr hs
        (hqstar0.trans hx.1) (by linarith [ht0, hx.2])).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (anariRezaeiMergeGapAlong r s)
        (interior (Set.Icc (anariRezaeiMergeQStar r s) q)) := by
      intro x hx
      have hx' : anariRezaeiMergeQStar r s < x ∧ x < q := by simpa using hx
      exact (hasDerivAt_anariRezaeiMergeGapAlong hr hs
        (hqstar0.trans hx'.1.le) (by linarith [ht0, hx'.2.le])).differentiableAt.differentiableWithinAt
    have hanti := antitoneOn_of_deriv_nonpos
      (convex_Icc (anariRezaeiMergeQStar r s) q) hcont hdiff fun x hx ↦ by
        have hx' : anariRezaeiMergeQStar r s < x ∧ x < q := by simpa using hx
        rw [(hasDerivAt_anariRezaeiMergeGapAlong hr hs
          (hqstar0.trans hx'.1.le) (by linarith [ht0, hx'.2.le])).deriv]
        exact (anariRezaeiMergeGapDerivative_sign hr hs
          (hqstar0.trans hx'.1.le) (by linarith [ht0, hx'.2.le])).2.mpr hx'.1.le
    exact hanti ⟨le_rfl, hq⟩ ⟨hq, le_rfl⟩ hq

theorem anariRezaeiMergeGap_stationary_eq
    {r s : ℝ} (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hC : r+s ≤ 14/25) :
    anariRezaeiMergeGap (anariRezaeiMergeQStar r s) r s
        (anariRezaeiMergeTStar r s) = anariRezaeiMergePsi r s := by
  have h1pr : 1+r ≠ 0 := by linarith
  have h1ps : 1+s ≠ 0 := by linarith
  have h1pC : 1+r+s ≠ 0 := by linarith
  have hden : 2+r+s ≠ 0 := by linarith
  have hqNum : anariRezaeiMergeQStar r s+r =
      (1+r)/(2+r+s) := by
    rw [anariRezaeiMergeQStar]
    field_simp [hden]
    ring
  have hqDen : anariRezaeiMergeQStar r s+r+s =
      ((1+r+s)*(1+s))/(2+r+s) := by
    rw [anariRezaeiMergeQStar]
    field_simp [hden]
    ring
  have hqratio :
      (anariRezaeiMergeQStar r s+r)/
          (anariRezaeiMergeQStar r s+r+s) =
        (1+r)/((1+r+s)*(1+s)) := by
    rw [hqDen, hqNum]
    field_simp [hden, h1pr, h1ps, h1pC]
  have htNum : s+anariRezaeiMergeTStar r s =
      (1+s)/(2+r+s) := by
    rw [anariRezaeiMergeTStar]
    field_simp [hden]
    ring
  have htDen : r+s+anariRezaeiMergeTStar r s =
      ((1+r+s)*(1+r))/(2+r+s) := by
    rw [anariRezaeiMergeTStar]
    field_simp [hden]
    ring
  have htratio :
      (s+anariRezaeiMergeTStar r s)/
          (r+s+anariRezaeiMergeTStar r s) =
        (1+s)/((1+r+s)*(1+r)) := by
    rw [htDen, htNum]
    field_simp [hden, h1pr, h1ps, h1pC]
  rw [anariRezaeiMergeGap, anariRezaeiMergePsi, hqratio, htratio]
  rw [Real.log_div h1pr (mul_ne_zero h1pC h1ps),
    Real.log_div h1ps (mul_ne_zero h1pC h1pr),
    Real.log_div h1ps h1pr,
    Real.log_mul h1pC h1ps, Real.log_mul h1pC h1pr]
  ring

/-- Four-mass merge lemma with the rational cutoff used by the formal proof. -/
theorem anariRezaeiMergeGap_nonpos
    {q r s t : ℝ} (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hsum : q+r+s+t = 1) (hC : r+s ≤ 14/25) :
    anariRezaeiMergeGap q r s t ≤ 0 := by
  by_cases hrz : r = 0
  · subst r
    rw [anariRezaeiMergeGap]
    by_cases hst : s+t = 0
    · have hs : s = 0 := by linarith
      subst s
      norm_num
    · have hratio : (s+t)/(s+t) = (1 : ℝ) := div_self hst
      have hratio' : (s+t)/(0+s+t) = (1 : ℝ) := by
        convert hratio using 1 <;> ring
      rw [hratio']
      norm_num
  · by_cases hsz : s = 0
    · subst s
      rw [anariRezaeiMergeGap]
      by_cases hqr : q+r = 0
      · have hrzero : r = 0 := by linarith
        exact (hrz hrzero).elim
      · have hratio : (q+r)/(q+r) = (1 : ℝ) := div_self hqr
        have hratio' : (q+r)/(q+r+0) = (1 : ℝ) := by
          convert hratio using 1 <;> ring
        rw [hratio']
        norm_num
    · calc
        anariRezaeiMergeGap q r s t ≤
            anariRezaeiMergeGap (anariRezaeiMergeQStar r s) r s
              (anariRezaeiMergeTStar r s) :=
          anariRezaeiMergeGap_le_stationary hq0
            (lt_of_le_of_ne hr0 (Ne.symm hrz))
            (lt_of_le_of_ne hs0 (Ne.symm hsz)) ht0 hsum hC
        _ = anariRezaeiMergePsi r s :=
          anariRezaeiMergeGap_stationary_eq hr0 hs0 hC
        _ ≤ 0 := anariRezaeiMergePsi_nonpos hr0 hs0 hC

end BeyondBethe
