/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.Boundary.Basic
import LeanPool.LeanModularForms.ValenceFormula.Definitions
import LeanPool.LeanModularForms.ValenceFormula.ModularInvariance
import LeanPool.LeanModularForms.ValenceFormula.OnCurvePV.Main
import LeanPool.LeanModularForms.ValenceFormula.OrbitSum
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue

/-!
# PV Chain Helpers

Definitions for `pvIntegralLogDeriv`, the singular sets `sArcOfS` and
`sVertOfS`, and the two core analytical stubs
(`cpv_modular_side_of_SarcSvert` and `cpv_residue_side_of_SarcSvert`)
that are needed to prove `pv_modular_side` and `pv_residue_side`.

## Main Results

* `cpv_modular_side_of_SarcSvert` — the CPV integral of `f'/f` around
    `fdBoundaryH H` equals `-(2πi · (k/12 - ord_∞(f)))`.
* `cpv_residue_side_of_SarcSvert` — the CPV integral of `f'/f` around
    `fdBoundaryH H` equals `2πi · Σ gWN · ord`.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-- The ε-truncated integrand for the PV integral of `f'/f` along `γ`,
with singular set `S₀`. Zero when `γ(t)` is within `ε` of any `s ∈ S₀`,
otherwise `logDeriv f (γ t) * γ'(t)`. -/
noncomputable def pvIntegrand {k : ℤ} (f : ModularForm (Gamma 1) k) (γ : ℝ → ℂ)
    (S₀ : Finset ℂ) (ε : ℝ) (t : ℝ) : ℂ :=
  cauchyPrincipalValueIntegrandOn S₀ (logDeriv (modularFormCompOfComplex f)) γ ε t

/-- Arc singular set: unit-circle zeros (and S-transforms) plus ρ, ρ+1. -/
noncomputable def sArcOfS (S : Finset UpperHalfPlane) : Finset ℂ :=
  (S.filter (fun (p : ℍ) => ‖(↑p : ℂ)‖ = 1)).image (↑· : ℍ → ℂ) ∪
  (S.filter (fun (p : ℍ) => ‖(↑p : ℂ)‖ = 1)).image (fun (p : ℍ) => -(1 : ℂ) / (↑p : ℂ)) ∪
  {ellipticPointRho, ellipticPointRhoPlusOne}

/-- Vertical singular set: re = ±1/2, ‖z‖ > 1 zeros, plus T-shifts. -/
noncomputable def sVertOfS (S : Finset UpperHalfPlane) : Finset ℂ :=
  (S.filter (fun p : ℍ => (↑p : ℂ).re = 1/2 ∧ ‖(↑p : ℂ)‖ > 1)).image
    (↑· : ℍ → ℂ) ∪
  (S.filter (fun p : ℍ => (↑p : ℂ).re = 1/2 ∧ ‖(↑p : ℂ)‖ > 1)).image
    (fun p : ℍ => (↑p : ℂ) - 1) ∪
  (S.filter (fun p : ℍ => (↑p : ℂ).re = -1/2 ∧ ‖(↑p : ℂ)‖ > 1)).image
    (↑· : ℍ → ℂ) ∪
  (S.filter (fun p : ℍ => (↑p : ℂ).re = -1/2 ∧ ‖(↑p : ℂ)‖ > 1)).image
    (fun p : ℍ => (↑p : ℂ) + 1)

/-- CPV existence at all on-curve singular points of `fdBoundaryH H`. -/
def onCurvePVProvider (S : Finset UpperHalfPlane) : Prop :=
  ∀ (H : ℝ), Real.sqrt 3 / 2 < H →
    ∀ s ∈ sArcOfS S ∪ sVertOfS S, (∃ t ∈ Icc (0 : ℝ) 5, fdBoundaryH H t = s) →
      CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundaryH H) 0 5 s

omit f hf in
/-- CPV exists at every on-curve singular point. -/
theorem fdBoundary_H_onCurvePVProvider (S : Finset UpperHalfPlane) :
    onCurvePVProvider S := by
  intro H hH s _ h_on
  exact fdBoundary_H_cpv_exists_of_onCurve H hH s h_on

omit f hf in
lemma sArcOfS_rho_in (S : Finset UpperHalfPlane) :
    ellipticPointRho ∈ sArcOfS S := by
  simp [sArcOfS]

omit f hf in
lemma sArcOfS_rho_plus_one_in (S : Finset UpperHalfPlane) :
    ellipticPointRhoPlusOne ∈ sArcOfS S := by
  simp [sArcOfS]

omit f hf in
lemma sArcOfS_unit (S : Finset UpperHalfPlane) :
    ∀ s ∈ sArcOfS S, ‖s‖ = 1 := by
  intro s hs
  simp only [sArcOfS, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with ⟨⟨p, ⟨_, hp_norm⟩, rfl⟩ | ⟨p, ⟨_, hp_norm⟩, rfl⟩⟩ | hs
  · exact hp_norm
  · rw [norm_div, norm_neg, norm_one, hp_norm, div_one]
  · rcases hs with rfl | rfl
    · exact ellipticPointRho_norm
    · exact ellipticPointRhoPlusOne_norm

omit f hf in
private lemma neg_inv_rho_eq_rho_plus_one :
    -(1 : ℂ) / ellipticPointRho = ellipticPointRhoPlusOne := by
  have hre : (ellipticPointRho : ℂ).re = -1/2 := by
    simp [ellipticPointRho, ellipticPointRho']
  have him : (ellipticPointRho : ℂ).im = Real.sqrt 3 / 2 := by
    simp [ellipticPointRho, ellipticPointRho']
  have hre2 : (ellipticPointRhoPlusOne : ℂ).re = 1/2 := by
    simp [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']
  have him2 : (ellipticPointRhoPlusOne : ℂ).im = Real.sqrt 3 / 2 := by
    simp [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']
  have hnormSq :
      -(1/2 : ℝ) * -(1/2) + Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  apply Complex.ext
  · simp only [neg_div, Complex.neg_re, Complex.div_re,
      Complex.one_re, Complex.one_im, Complex.normSq_apply,
      hre, him, hre2, hnormSq]; ring
  · simp only [neg_div, Complex.neg_im, Complex.div_im,
      Complex.one_re, Complex.one_im, Complex.normSq_apply,
      hre, him, him2, hnormSq]; ring

omit f hf in
private lemma neg_inv_rho_plus_one_eq_rho :
    -(1 : ℂ) / ellipticPointRhoPlusOne = ellipticPointRho := by
  have hre : (ellipticPointRhoPlusOne : ℂ).re = 1/2 := by
    simp [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']
  have him : (ellipticPointRhoPlusOne : ℂ).im = Real.sqrt 3 / 2 := by
    simp [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']
  have hre2 : (ellipticPointRho : ℂ).re = -1/2 := by
    simp [ellipticPointRho, ellipticPointRho']
  have him2 : (ellipticPointRho : ℂ).im = Real.sqrt 3 / 2 := by
    simp [ellipticPointRho, ellipticPointRho']
  have hnormSq : (1/2 : ℝ) * (1/2) + Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  apply Complex.ext
  · simp only [neg_div, Complex.neg_re, Complex.div_re,
      Complex.one_re, Complex.one_im, Complex.normSq_apply,
      hre, him, hre2, hnormSq]; ring
  · simp only [neg_div, Complex.neg_im, Complex.div_im,
      Complex.one_re, Complex.one_im, Complex.normSq_apply,
      hre, him, him2, hnormSq]; ring

omit f hf in
lemma sArcOfS_closed (S : Finset UpperHalfPlane) :
    ∀ s ∈ sArcOfS S, -(1 : ℂ) / s ∈ sArcOfS S := by
  intro s hs
  simp only [sArcOfS, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hs ⊢
  rcases hs with ⟨⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩⟩ | hs
  · left; right; exact ⟨p, hp, rfl⟩
  · have hp_ne : (↑p : ℂ) ≠ 0 := by
      intro h; have := hp.2; rw [h, norm_zero] at this; norm_num at this
    left; left; exact ⟨p, hp, by field_simp⟩
  · rcases hs with rfl | rfl
    · right; right; exact neg_inv_rho_eq_rho_plus_one
    · right; left; exact neg_inv_rho_plus_one_eq_rho

omit f hf in
lemma sVertOfS_re (S : Finset UpperHalfPlane) :
    ∀ s ∈ sVertOfS S, s.re = 1/2 ∨ s.re = -1/2 := by
  intro s hs
  unfold sVertOfS at hs
  rcases Finset.mem_union.mp hs with h | hD
  · rcases Finset.mem_union.mp h with h | hC
    · rcases Finset.mem_union.mp h with hA | hB
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hA
        left; exact (Finset.mem_filter.mp hp).2.1
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hB
        right; simp only [Complex.sub_re, (Finset.mem_filter.mp hp).2.1]
        norm_num
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
      right; exact (Finset.mem_filter.mp hp).2.1
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hD
    left; simp only [Complex.add_re, (Finset.mem_filter.mp hp).2.1]
    norm_num

omit f hf in
lemma sVertOfS_pair_left (S : Finset UpperHalfPlane) :
    ∀ s ∈ sVertOfS S, s.re = 1/2 → s - 1 ∈ sVertOfS S := by
  intro s hs hre
  unfold sVertOfS at hs ⊢
  rcases Finset.mem_union.mp hs with h | hD
  · rcases Finset.mem_union.mp h with h | hC
    · rcases Finset.mem_union.mp h with hA | hB
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hA
        apply Finset.mem_union.mpr; left
        apply Finset.mem_union.mpr; left
        apply Finset.mem_union.mpr; right
        exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hB
        exfalso; obtain ⟨_, hp_re, _⟩ := Finset.mem_filter.mp hp
        simp only [Complex.sub_re] at hre
        rw [hp_re] at hre; norm_num at hre
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
      exfalso; obtain ⟨_, hp_re, _⟩ := Finset.mem_filter.mp hp
      linarith
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hD
    rw [show (↑p : ℂ) + 1 - 1 = (↑p : ℂ) from by ring]
    apply Finset.mem_union.mpr; left
    apply Finset.mem_union.mpr; right
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

omit f hf in
lemma sVertOfS_pair_right (S : Finset UpperHalfPlane) :
    ∀ s ∈ sVertOfS S, s.re = -1/2 → s + 1 ∈ sVertOfS S := by
  intro s hs hre
  unfold sVertOfS at hs ⊢
  rcases Finset.mem_union.mp hs with h | hD
  · rcases Finset.mem_union.mp h with h | hC
    · rcases Finset.mem_union.mp h with hA | hB
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hA
        exfalso; obtain ⟨_, hp_re, _⟩ := Finset.mem_filter.mp hp
        linarith
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hB
        rw [show (↑p : ℂ) - 1 + 1 = (↑p : ℂ) from by ring]
        apply Finset.mem_union.mpr; left
        apply Finset.mem_union.mpr; left
        apply Finset.mem_union.mpr; left
        exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
      apply Finset.mem_union.mpr; right
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hD
    exfalso; obtain ⟨_, hp_re, _⟩ := Finset.mem_filter.mp hp
    simp only [Complex.add_re] at hre
    rw [hp_re] at hre; norm_num at hre

omit hf in
/-- `modularFormCompOfComplex f` is periodic with period 1. -/
private theorem modularFormCompOfComplex_periodic :
    Function.Periodic (modularFormCompOfComplex f) (1 : ℂ) := by
  exact SlashInvariantFormClass.periodic_comp_ofComplex f
    (by simp)

omit f hf in
/-- There exists a height above √3/2 exceeding all points in `S`. -/
theorem exists_height_bound_S (S : Finset UpperHalfPlane) :
    ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧ 1 < H₁ ∧ ∀ s ∈ S, (s : ℂ).im < H₁ := by
  rcases S.eq_empty_or_nonempty with h_empty | h_ne
  · exact ⟨2, by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)],
      by norm_num, by simp [h_empty]⟩
  · set M := S.sup' h_ne (fun s : ℍ => (s : ℂ).im) with hM_def
    have hM_pos : 0 < M := by
      obtain ⟨s, hs⟩ := h_ne
      calc (0 : ℝ) < (s : ℂ).im := s.2
        _ ≤ M := Finset.le_sup' (fun s : ℍ => (↑s : ℂ).im) hs
    refine ⟨max 2 (M + 1), lt_of_lt_of_le ?_ (le_max_left _ _),
        lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _), ?_⟩
    · nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    · intro s hs
      calc (s : ℂ).im ≤ M := Finset.le_sup' (fun s : ℍ => (↑s : ℂ).im) hs
        _ < M + 1 := by linarith
        _ ≤ max 2 (M + 1) := le_max_right _ _

omit f hf in
/-- All elements of `sVertOfS S` have im < H₁ when all elements of `S` have im < H₁. -/
lemma sVertOfS_im_lt_height_bound (S : Finset UpperHalfPlane) (s : ℂ)
    (hs : s ∈ sVertOfS S) (h_bound : ∀ p ∈ S, (p : ℂ).im < H₁) :
    s.im < H₁ := by
  unfold sVertOfS at hs
  rcases Finset.mem_union.mp hs with h | hD
  · rcases Finset.mem_union.mp h with h | hC
    · rcases Finset.mem_union.mp h with hA | hB
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hA
        exact h_bound p (Finset.mem_of_mem_filter p hp)
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hB
        simp only [Complex.sub_im, Complex.one_im, sub_zero]
        exact h_bound p (Finset.mem_of_mem_filter p hp)
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
      exact h_bound p (Finset.mem_of_mem_filter p hp)
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hD
    simp only [Complex.add_im, Complex.one_im, add_zero]
    exact h_bound p (Finset.mem_of_mem_filter p hp)

include hf in
/-- Zeros in `S` are complete: every zero of `f` in `𝒟` is in `S.filter zeros`. -/
private theorem zeros_complete_of_hS_complete (S : Finset UpperHalfPlane)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∀ s, s ∈ 𝒟 → f s = 0 → s ∈ S.filter (fun p => f p = 0) := by
  intro s hs_fd hs_zero
  exact Finset.mem_filter.mpr
    ⟨hS_complete s hs_fd (orderOfVanishingAt'_ne_zero_of_eq_zero f hf s hs_zero), hs_zero⟩

omit hf in
/-- Summing `gWN · ord` over all of `S` equals summing over just zeros. -/
theorem sum_gWN_ord_eq_filter_zeros (S : Finset UpperHalfPlane) (g : ℂ → ℂ) :
    ∑ s ∈ S, g (↑s : ℂ) * (orderOfVanishingAt' (⇑f) s : ℂ) =
    ∑ s ∈ S.filter (fun p => f p = 0),
      g (↑s : ℂ) * (orderOfVanishingAt' (⇑f) s : ℂ) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl; intro p _
  split_ifs with h
  · rfl
  · simp only [orderOfVanishingAt'_eq_zero_of_ne_zero' f p h, Int.cast_zero, mul_zero]

omit f hf in
/-- All elements of `sArcOfS S` have positive imaginary part. -/
lemma sArcOfS_im_pos (S : Finset UpperHalfPlane) (s : ℂ) (hs : s ∈ sArcOfS S) : 0 < s.im := by
  simp only [sArcOfS, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with ⟨⟨p, ⟨_, _⟩, rfl⟩ | ⟨p, ⟨_, hp_norm⟩, rfl⟩⟩ | hs
  · exact p.2
  · have hz_ne : (↑p : ℂ) ≠ 0 := by intro h; simp [h] at hp_norm
    rw [show -(1 : ℂ) / (↑p : ℂ) = (-(↑p : ℂ))⁻¹ from by field_simp, Complex.inv_im]
    simp only [neg_im, neg_neg]
    exact div_pos p.2 (Complex.normSq_pos.mpr (neg_ne_zero.mpr hz_ne))
  · rcases hs with rfl | rfl
    · change (0 : ℝ) < (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).im
      simp only [add_im, neg_im, one_im, div_im, mul_im, I_re, I_im]; norm_num
    · change (0 : ℝ) < (1/2 + (Real.sqrt 3 / 2) * I : ℂ).im
      simp only [add_im, one_im, div_im, mul_im, I_re, I_im]; norm_num

omit f hf in
/-- All elements of `sVertOfS S` have positive imaginary part. -/
lemma sVertOfS_im_pos (S : Finset UpperHalfPlane) (s : ℂ) (hs : s ∈ sVertOfS S) : 0 < s.im := by
  unfold sVertOfS at hs
  rcases Finset.mem_union.mp hs with h | hD
  · rcases Finset.mem_union.mp h with h | hC
    · rcases Finset.mem_union.mp h with hA | hB
      · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hA; exact p.2
      · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hB
        simp only [Complex.sub_im, Complex.one_im, sub_zero]; exact p.2
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hC; exact p.2
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hD
    simp only [Complex.add_im, Complex.one_im, add_zero]; exact p.2

omit f hf in
private lemma sVertOfS_re_bound (S : Finset UpperHalfPlane) (s : ℂ)
    (hs : s ∈ sVertOfS S) : |s.re| ≤ 1/2 := by
  unfold sVertOfS at hs
  rcases Finset.mem_union.mp hs with h | hD
  · rcases Finset.mem_union.mp h with h | hC
    · rcases Finset.mem_union.mp h with hA | hB
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hA
        rw [(Finset.mem_filter.mp hp).2.1]; norm_num
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hB
        simp only [Complex.sub_re, Complex.one_re]
        rw [(Finset.mem_filter.mp hp).2.1]; norm_num
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
      rw [(Finset.mem_filter.mp hp).2.1]; norm_num
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hD
    simp only [Complex.add_re, Complex.one_re]
    rw [(Finset.mem_filter.mp hp).2.1]; norm_num

omit f hf in
private lemma im_gt_sqrt3_half_of_re_half_and_norm_gt_one (p : ℍ)
    (hre : (↑p : ℂ).re = 1 / 2 ∨ (↑p : ℂ).re = -1 / 2)
    (hnorm : ‖(↑p : ℂ)‖ > 1) : (↑p : ℂ).im > Real.sqrt 3 / 2 := by
  have h_nsq : (↑p : ℂ).re ^ 2 + (↑p : ℂ).im ^ 2 > 1 := by
    have h_norm_sq : ‖(↑p : ℂ)‖ ^ 2 > 1 := by nlinarith [sq_nonneg (‖(↑p : ℂ)‖ - 1)]
    have : ‖(↑p : ℂ)‖ ^ 2 = (↑p : ℂ).re ^ 2 + (↑p : ℂ).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    linarith
  have h_re_sq : (↑p : ℂ).re ^ 2 = 1/4 := by rcases hre with h | h <;> (rw [h]; ring)
  have h_im_sq' : (Real.sqrt 3 / 2) ^ 2 < (↑p : ℂ).im ^ 2 := by
    rw [div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]; linarith
  have h_sqrt_ineq := Real.sqrt_lt_sqrt (sq_nonneg (Real.sqrt 3 / 2)) h_im_sq'
  have : Real.sqrt ((↑p : ℂ).im ^ 2) = (↑p : ℂ).im := Real.sqrt_sq p.2.le
  rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt 3 / 2), this] at h_sqrt_ineq
  exact h_sqrt_ineq

omit f hf in
private lemma sVertOfS_im_gt_sqrt3_half (S : Finset UpperHalfPlane) (s : ℂ)
    (hs : s ∈ sVertOfS S) : s.im > Real.sqrt 3 / 2 := by
  unfold sVertOfS at hs
  rcases Finset.mem_union.mp hs with h | hD
  · rcases Finset.mem_union.mp h with h | hC
    · rcases Finset.mem_union.mp h with hA | hB
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hA
        exact im_gt_sqrt3_half_of_re_half_and_norm_gt_one p
          (Or.inl (Finset.mem_filter.mp hp).2.1) (Finset.mem_filter.mp hp).2.2
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hB
        simp only [Complex.sub_im, Complex.one_im, sub_zero]
        exact im_gt_sqrt3_half_of_re_half_and_norm_gt_one p
          (Or.inl (Finset.mem_filter.mp hp).2.1) (Finset.mem_filter.mp hp).2.2
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
      exact im_gt_sqrt3_half_of_re_half_and_norm_gt_one p
        (Or.inr (Finset.mem_filter.mp hp).2.1) (Finset.mem_filter.mp hp).2.2
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hD
    simp only [Complex.add_im, Complex.one_im, add_zero]
    exact im_gt_sqrt3_half_of_re_half_and_norm_gt_one p
      (Or.inr (Finset.mem_filter.mp hp).2.1) (Finset.mem_filter.mp hp).2.2

omit f hf in
private lemma im_ge_sqrt3_half_of_re_half_and_norm_eq_one (p : ℍ)
    (hre : |(↑p : ℂ).re| ≤ 1 / 2) (hnorm : ‖(↑p : ℂ)‖ = 1) : (↑p : ℂ).im ≥ Real.sqrt 3 / 2 := by
  have h_nsq : (↑p : ℂ).re ^ 2 + (↑p : ℂ).im ^ 2 = 1 := by
    have h_norm_sq : ‖(↑p : ℂ)‖ ^ 2 = 1 := by rw [hnorm]; norm_num
    have : ‖(↑p : ℂ)‖ ^ 2 = (↑p : ℂ).re ^ 2 + (↑p : ℂ).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    linarith
  have h_im_sq : (↑p : ℂ).im ^ 2 ≥ 3/4 := by
    have h_re2 : (↑p : ℂ).re ^ 2 ≤ 1 / 4 := by
      have ⟨h1, h2⟩ := abs_le.mp hre; nlinarith [h1, h2]
    nlinarith [h_nsq, h_re2]
  have h_im_sq' : (Real.sqrt 3 / 2) ^ 2 ≤ (↑p : ℂ).im ^ 2 := by
    rw [div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]; linarith
  rcases eq_or_lt_of_le h_im_sq' with h_eq | h_lt
  · have h_sqrt_eq := congr_arg Real.sqrt h_eq
    have : Real.sqrt ((↑p : ℂ).im ^ 2) = (↑p : ℂ).im := Real.sqrt_sq p.2.le
    rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt 3 / 2), this] at h_sqrt_eq
    exact h_sqrt_eq ▸ le_refl _
  · have h_sqrt_ineq := Real.sqrt_lt_sqrt (sq_nonneg (Real.sqrt 3 / 2)) h_lt
    have : Real.sqrt ((↑p : ℂ).im ^ 2) = (↑p : ℂ).im := Real.sqrt_sq p.2.le
    rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt 3 / 2), this] at h_sqrt_ineq
    exact le_of_lt h_sqrt_ineq

omit f hf in
/-- On-curve singular points lie inside `fdBox M` when `H < M`. -/
lemma fdBox_of_on_curve (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    {H M : ℝ} (_hH_sqrt3 : Real.sqrt 3 / 2 < H) (hH_lt_M : H < M) (hH_ge1 : 1 ≤ H)
    (hH_bound : ∀ s ∈ S, (s : ℂ).im < H)
    (s : ℂ) (hs : s ∈ sArcOfS S ∪ sVertOfS S) : s ∈ fdBox M := by
  rcases Finset.mem_union.mp hs with h_arc | h_vert
  · have h_unit := sArcOfS_unit S s h_arc
    have h_im_pos := sArcOfS_im_pos S s h_arc
    have h_nsq : s.re ^ 2 + s.im ^ 2 = 1 := by
      have h_sq : ‖s‖ ^ 2 = (s.re ^ 2 + s.im ^ 2) := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      nlinarith [h_unit, h_sq]
    have h_re_sq_lt : s.re ^ 2 < 1 := by nlinarith
    have h_im_le : s.im ≤ 1 := by nlinarith
    have h_im_ge : s.im ≥ Real.sqrt 3 / 2 := by
      simp only [sArcOfS, Finset.mem_union, Finset.mem_image,
        Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at h_arc
      rcases h_arc with ⟨⟨p, ⟨hp_mem, hp_norm⟩, rfl⟩ | ⟨p, ⟨hp_mem, hp_norm⟩, rfl⟩⟩ | h_ell
      · exact im_ge_sqrt3_half_of_re_half_and_norm_eq_one p (hS p hp_mem).2 hp_norm
      · have hz_ne : (↑p : ℂ) ≠ 0 := by intro h; simp [h] at hp_norm
        have h_eq : (-(1 : ℂ) / (↑p : ℂ)).im = (↑p : ℂ).im := by
          rw [show -(1 : ℂ) / (↑p : ℂ) = (-(↑p : ℂ))⁻¹ from by field_simp, Complex.inv_im]
          simp only [neg_im, neg_neg]
          have h_nsq_val : Complex.normSq (-(↑p : ℂ)) = 1 := by
            rw [Complex.normSq_neg]
            have h_norm_sq : ‖(↑p : ℂ)‖ ^ 2 = 1 := by
              rw [hp_norm]; norm_num
            have : ‖(↑p : ℂ)‖ ^ 2 = (↑p : ℂ).re ^ 2 + (↑p : ℂ).im ^ 2 := by
              rw [Complex.sq_norm, Complex.normSq_apply]
              ring
            have h_nsq : (↑p : ℂ).re ^ 2 + (↑p : ℂ).im ^ 2 = 1 := by linarith
            simp only [Complex.normSq_apply]
            nlinarith [h_nsq]
          rw [h_nsq_val, div_one]
        rw [h_eq]
        exact im_ge_sqrt3_half_of_re_half_and_norm_eq_one p (hS p hp_mem).2 hp_norm
      · rcases h_ell with rfl | rfl
        · change (Real.sqrt 3 / 2 : ℝ) ≤ (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).im
          simp only [add_im, neg_im, one_im, div_im, mul_im, I_re, I_im]; norm_num
        · change (Real.sqrt 3 / 2 : ℝ) ≤ (1/2 + (Real.sqrt 3 / 2) * I : ℂ).im
          simp only [add_im, one_im, div_im, mul_im, I_re, I_im]; norm_num
    have h_re_bound : -1 < s.re ∧ s.re < 1 := by
      constructor
      · nlinarith [sq_abs s.re]
      · nlinarith [sq_abs s.re]
    have sqrt3_gt_one : (1 : ℝ) < Real.sqrt 3 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    exact ⟨h_re_bound.1, h_re_bound.2, by linarith [h_im_ge], by linarith [h_im_le, hH_ge1]⟩
  · have h_re := sVertOfS_re_bound S s h_vert
    have h_im_gt := sVertOfS_im_gt_sqrt3_half S s h_vert
    have h_im_lt := sVertOfS_im_lt_height_bound S s h_vert hH_bound
    have sqrt3_gt_one : (1 : ℝ) < Real.sqrt 3 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    exact ⟨by linarith [abs_le.mp h_re], by linarith [abs_le.mp h_re],
      by linarith, by linarith⟩

end
