/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.Boundary.Winding.LeftEdge
import LeanPool.LeanModularForms.ValenceFormula.Boundary.Winding.RightEdge
import LeanPool.LeanModularForms.ValenceFormula.Boundary.Winding.UnitArc
import LeanPool.LeanModularForms.ValenceFormula.InteriorWinding
import LeanPool.LeanModularForms.ValenceFormula.OrbitSum
import LeanPool.LeanModularForms.ValenceFormula.PVChain
import LeanPool.LeanModularForms.ValenceFormula.WindingWeights

/-!
# Core Identity for the Valence Formula

The orbit-sum valence formula applied to the canonical zero set `s₀`.

## Main Results

* `valence_formula_orbit_sum` — orbit-sum with boundary weight hypothesis
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

omit f hf in
private lemma ellipticPointRho_re_neg : (ellipticPointRho' : ℂ).re < 0 := by
  change (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).re < 0
  simp only [add_re, mul_re, I_re, I_im, mul_zero, mul_one]; norm_num

omit f hf in
private lemma ellipticPointRhoPlusOne_re_pos :
    (ellipticPointRhoPlusOne' : ℂ).re > 0 := by
  change (1/2 + (Real.sqrt 3 / 2) * I : ℂ).re > 0
  simp only [add_re, mul_re, I_re, I_im, mul_zero, mul_one]; norm_num

omit f hf in
private lemma ellipticPoint_ne_iρ1 : ellipticPointI' ≠ ellipticPointRhoPlusOne' := by
  intro h; have := congr_arg (fun z : UpperHalfPlane => (z : ℂ).re) h
  simp [ellipticPointI', ellipticPointRhoPlusOne'] at this

omit f hf in
private lemma ellipticPoint_ne_ρρ1 : ellipticPointRho' ≠ ellipticPointRhoPlusOne' := by
  intro h; have := congr_arg (fun z : UpperHalfPlane => (z : ℂ).re) h
  simp [ellipticPointRho', ellipticPointRhoPlusOne'] at this; norm_num at this

omit f hf in
private lemma elliptic_finset_sum_eq_three (S : Finset UpperHalfPlane)
    (g : UpperHalfPlane → ℂ) (_hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete_zero : ∀ p, p ∈ 𝒟 → p ∉ S → g p = 0) :
    let P := fun (p : UpperHalfPlane) =>
      p = ellipticPointI' ∨ p = ellipticPointRho' ∨ p = ellipticPointRhoPlusOne'
    ∑ s ∈ S.filter P, g s =
      g ellipticPointI' + g ellipticPointRho' + g ellipticPointRhoPlusOne' := by
  intro P
  have h_ell_sub : S.filter P ⊆
      ({ellipticPointI', ellipticPointRho',
        ellipticPointRhoPlusOne'} : Finset UpperHalfPlane) := by
    intro x hx; have := (Finset.mem_filter.mp hx).2
    simp only [Finset.mem_insert, Finset.mem_singleton]; exact this
  have h_zero_outside : ∀ x ∈
      ({ellipticPointI', ellipticPointRho',
        ellipticPointRhoPlusOne'} : Finset UpperHalfPlane),
      x ∉ S.filter P → g x = 0 := by
    intro x hx hx_not
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hx_not_S : x ∉ S :=
      fun hx_S => hx_not (Finset.mem_filter.mpr ⟨hx_S, hx⟩)
    have hx_fd : x ∈ 𝒟 := by
      rcases hx with rfl | rfl | rfl
      · exact ellipticPointI_mem_fd
      · exact ellipticPointRho_mem_fd
      · exact ellipticPointRhoPlusOne_mem_fd
    exact hS_complete_zero x hx_fd hx_not_S
  rw [Finset.sum_subset h_ell_sub h_zero_outside,
    Finset.sum_insert (by simp [ellipticPointI_ne_rho, ellipticPoint_ne_iρ1]),
    Finset.sum_insert (by simp [ellipticPoint_ne_ρρ1]), Finset.sum_singleton]
  ring

include hf in
private theorem explicit_coefficients (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∃ H₀ : ℝ, 1 < H₀ ∧ ∀ {H : ℝ}, H₀ ≤ H →
      (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
      (1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
      (1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRhoPlusOne') +
      ∑ s ∈ S.filter (fun p =>
          p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧
          p ≠ ellipticPointRhoPlusOne'),
        (-generalizedWindingNumber' (fdBoundaryH H) 0 5 (↑s : ℂ)) *
          ↑(orderOfVanishingAt' (⇑f) s) =
      (k : ℂ) / 12 := by
  obtain ⟨H₀, hH₀_gt, h_identity⟩ := pv_chain_identity f hf S hS hS_complete
  refine ⟨max H₀ 2, by linarith [le_max_right H₀ 2], fun {H} hH => ?_⟩
  have hH_gt_1 : 1 < H := by linarith [le_max_right H₀ 2]
  have hH_gt_sqrt3 : Real.sqrt 3 / 2 < H := by
    nlinarith [Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), sq_nonneg (Real.sqrt 3 - 2)]
  have h_sum := h_identity (le_trans (le_max_left H₀ 2) hH)
  set g := fun (s : UpperHalfPlane) =>
    generalizedWindingNumber' (fdBoundaryH H) 0 5 (↑s : ℂ) *
      (orderOfVanishingAt' (⇑f) s : ℂ) with hg_def
  have h_ord_zero : ∀ p, p ∈ 𝒟 → p ∉ S → orderOfVanishingAt' (⇑f) p = 0 :=
    fun p hp hp_not => by_contra fun h_ne => hp_not (hS_complete _ hp h_ne)
  set P := fun (p : UpperHalfPlane) =>
    p = ellipticPointI' ∨ p = ellipticPointRho' ∨ p = ellipticPointRhoPlusOne'
  have h_split := (Finset.sum_filter_add_sum_filter_not S P g).symm
  have h_ell_sum : ∑ s ∈ S.filter P, g s =
      g ellipticPointI' + g ellipticPointRho' + g ellipticPointRhoPlusOne' :=
    elliptic_finset_sum_eq_three S g hS (fun p hp hp_not => by
      simp [hg_def, h_ord_zero p hp hp_not, Int.cast_zero, mul_zero])
  have hg_i : g ellipticPointI' =
      (-1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') := by
    change generalizedWindingNumber' (fdBoundaryH H) 0 5 I *
      ↑(orderOfVanishingAt' (⇑f) ellipticPointI') = _
    rw [gWN_fdBoundary_H_at_i H hH_gt_1]
  have hg_ρ : g ellipticPointRho' =
      (-1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') := by
    change generalizedWindingNumber' (fdBoundaryH H) 0 5 ellipticPointRho *
      ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') = _
    rw [gWN_fdBoundary_H_at_rho H hH_gt_sqrt3]
  have hg_ρ1 : g ellipticPointRhoPlusOne' =
      (-1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRhoPlusOne') := by
    change generalizedWindingNumber' (fdBoundaryH H) 0 5 ellipticPointRhoPlusOne *
      ↑(orderOfVanishingAt' (⇑f) ellipticPointRhoPlusOne') = _
    rw [gWN_fdBoundary_H_at_rho_plus_one H hH_gt_sqrt3]
  have h_filter_eq : S.filter (fun p => ¬P p) = S.filter (fun p =>
      p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne') := by
    ext x; simp only [Finset.mem_filter, P, not_or]
  set R := ∑ s ∈ S.filter (fun p => ¬P p), g s with hR_def
  have h_neg_R :
      ∑ s ∈ S.filter (fun p =>
          p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne'),
        (-generalizedWindingNumber' (fdBoundaryH H) 0 5 (↑s : ℂ)) *
          ↑(orderOfVanishingAt' (⇑f) s) = -R := by
    rw [hR_def, h_filter_eq]; simp only [neg_mul, Finset.sum_neg_distrib, hg_def]
  rw [h_neg_R]
  rw [h_split, h_ell_sum, hg_i, hg_ρ, hg_ρ1] at h_sum
  linear_combination -h_sum

private lemma unit_circle_re_neg_half_eq_rho (s : ℍ)
    (hs_norm : ‖(s : ℂ)‖ = 1) (hs_re : (s : ℂ).re = -1 / 2) : s = ellipticPointRho' := by
  have h_nsq : Complex.normSq (s : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hs_norm, one_pow]
  rw [Complex.normSq_apply, hs_re] at h_nsq
  have h_im : (s : ℂ).im = Real.sqrt 3 / 2 := by
    have h_prod : ((s : ℂ).im - Real.sqrt 3 / 2) *
        ((s : ℂ).im + Real.sqrt 3 / 2) = 0 := by
      nlinarith [Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
    rcases mul_eq_zero.mp h_prod with h | h
    · linarith
    · exact absurd h (ne_of_gt (add_pos s.2 (by positivity)))
  apply UpperHalfPlane.ext; apply Complex.ext <;>
    simp only [ellipticPointRho', UpperHalfPlane.coe_mk, add_re, add_im, neg_re, neg_im, one_re,
      one_im, div_ofNat_re, div_ofNat_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, mul_one, sub_zero, add_zero, zero_add, zero_div, neg_zero] <;>
    linarith

private lemma unit_circle_re_pos_half_eq_rho_plus_one (s : ℍ)
    (hs_norm : ‖(s : ℂ)‖ = 1) (hs_re : (s : ℂ).re = 1 / 2) :
    s = ellipticPointRhoPlusOne' := by
  have h_nsq : Complex.normSq (s : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hs_norm, one_pow]
  rw [Complex.normSq_apply, hs_re] at h_nsq
  have h_im : (s : ℂ).im = Real.sqrt 3 / 2 := by
    have h_prod : ((s : ℂ).im - Real.sqrt 3 / 2) *
        ((s : ℂ).im + Real.sqrt 3 / 2) = 0 := by
      nlinarith [Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
    rcases mul_eq_zero.mp h_prod with h | h
    · linarith
    · exact absurd h (ne_of_gt (add_pos s.2 (by positivity)))
  apply UpperHalfPlane.ext; apply Complex.ext <;>
    simp only [ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk, add_re, add_im, one_re, one_im,
      div_ofNat_re, div_ofNat_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
      mul_one, sub_zero, add_zero, zero_add, zero_div] <;>
    linarith

private lemma vert_edge_im_gt_sqrt3_half (s : ℍ) (hs_norm : ‖(s : ℂ)‖ > 1)
    (hs_abs_re : |(s : ℂ).re| = 1 / 2) : Real.sqrt 3 / 2 < (s : ℂ).im := by
  by_contra h_le; push Not at h_le
  have h_nsq_gt : Complex.normSq (s : ℂ) > 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [hs_norm, sq_nonneg (‖(s : ℂ)‖ - 1)]
  have h_re_sq : (s : ℂ).re * (s : ℂ).re ≤ 1/4 := by
    rcases (abs_eq (by norm_num : (1 : ℝ)/2 ≥ 0)).mp hs_abs_re with h | h <;> rw [h] <;> norm_num
  have h_im_sq : (s : ℂ).im * (s : ℂ).im ≤ 3/4 := by
    have h3 := Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num)
    nlinarith [mul_self_le_mul_self s.2.le h_le]
  linarith [Complex.normSq_apply (s : ℂ)]

private lemma unit_circle_re_zero_eq_i (s : ℍ)
    (hs_norm : ‖(s : ℂ)‖ = 1) (hs_re : (s : ℂ).re = 0) : s = ellipticPointI' := by
  apply UpperHalfPlane.ext
  have h_nsq : Complex.normSq (s : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hs_norm, one_pow]
  rw [Complex.normSq_apply, hs_re, mul_zero, zero_add] at h_nsq
  have h_le : (s : ℂ).im ≤ 1 := by nlinarith [mul_self_nonneg ((s : ℂ).im - 1), h_nsq]
  have h_ge : 1 ≤ (s : ℂ).im := by
    nlinarith [mul_le_of_le_one_right s.2.le h_le, h_nsq]
  apply Complex.ext
  · exact hs_re.trans Complex.I_re.symm
  · exact (le_antisymm h_le h_ge).trans Complex.I_im.symm

private theorem boundary_weight_auto
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) :
    ∃ H₁ : ℝ, 1 < H₁ ∧ ∀ {H : ℝ}, H₁ ≤ H → ∀ s ∈ S,
      s ≠ ellipticPointI' → s ≠ ellipticPointRho' →
      s ≠ ellipticPointRhoPlusOne' →
      ¬(‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2) →
      generalizedWindingNumber' (fdBoundaryH H) 0 5 (↑s : ℂ) = -1/2 := by
  set M := S.sum (fun s : UpperHalfPlane => (s : ℂ).im) with hM_def
  refine ⟨max 2 (M + 1), by linarith [le_max_left (2 : ℝ) (M + 1)], ?_⟩
  intro H hH s hs hsi hsρ hsρ1 h_not_int
  have hs_fd := hS s hs
  have habs_re := hs_fd.2
  have hnorm_ge : 1 ≤ ‖(s : ℂ)‖ := by
    rw [Complex.norm_def]; exact Real.sqrt_one ▸ Real.sqrt_le_sqrt hs_fd.1
  have hH_ge2 : (2 : ℝ) ≤ H := le_trans (le_max_left 2 (M + 1)) hH
  have h_im_lt_H : (s : ℂ).im < H := by
    have h1 : (s : ℂ).im ≤ M := Finset.single_le_sum (fun x _ => le_of_lt x.2) hs
    linarith [le_max_right (2 : ℝ) (M + 1)]
  have hH_sqrt : Real.sqrt 3 / 2 < H := by
    nlinarith [Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), sq_nonneg (Real.sqrt 3 - 2)]
  rcases eq_or_lt_of_le hnorm_ge with h_eq | h_gt
  · have h_re_lt : |(s : ℂ).re| < 1/2 := by
      by_contra h_ge; push Not at h_ge
      have h_abs_eq : |(s : ℂ).re| = 1/2 := le_antisymm habs_re h_ge
      rcases abs_cases (s : ℂ).re with ⟨h_eq_abs, _⟩ | ⟨h_eq_abs, _⟩
      · exact hsρ1 (unit_circle_re_pos_half_eq_rho_plus_one s h_eq.symm (by linarith))
      · exact hsρ (unit_circle_re_neg_half_eq_rho s h_eq.symm (by linarith))
    exact gWN_fdBoundary_H_eq_neg_half_of_unitArc
      H (by linarith) (↑s) h_eq.symm h_re_lt s.2
  · have h_abs_eq : |(s : ℂ).re| = 1/2 := by
      by_contra h_ne; exact h_not_int ⟨h_gt, lt_of_le_of_ne habs_re h_ne⟩
    rcases abs_cases (s : ℂ).re with ⟨h_eq_abs, _⟩ | ⟨h_eq_abs, _⟩
    · exact gWN_fdBoundary_H_eq_neg_half_of_rightEdge
        H hH_sqrt (↑s) (by linarith) h_gt
        (vert_edge_im_gt_sqrt3_half s h_gt h_abs_eq) h_im_lt_H
    · exact gWN_fdBoundary_H_eq_neg_half_of_leftEdge
        H hH_sqrt (↑s) (by linarith) h_gt
        (vert_edge_im_gt_sqrt3_half s h_gt h_abs_eq) h_im_lt_H

private lemma rho_singleton_sum_eq (S : Finset UpperHalfPlane)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_ord : orderOfVanishingAt' (⇑f) ellipticPointRho' ≠ 0) :
    ∑ s ∈ (if ellipticPointRhoPlusOne' ∈ sRightArc S
        then {ellipticPointRhoPlusOne'} else ∅),
      (orderOfVanishingAt' (⇑f) s : ℂ) =
    ∑ s ∈ (if ellipticPointRho' ∈ sLeftArc S
        then {ellipticPointRho'} else ∅),
      (orderOfVanishingAt' (⇑f) s : ℂ) := by
  have hρ_in_LA : ellipticPointRho' ∈ sLeftArc S := by
    simp only [sLeftArc, Finset.mem_filter]
    exact ⟨hS_complete _ ellipticPointRho_mem_fd h_ord,
      ellipticPointRho_norm, ellipticPointRho_re_neg⟩
  have hρ1_in_RA : ellipticPointRhoPlusOne' ∈ sRightArc S := by
    simp only [sRightArc, Finset.mem_filter]
    exact ⟨hS_complete _ ellipticPointRhoPlusOne_mem_fd
      (by rwa [ord_rho_plus_one_eq_ord_rho_via_vAdd]),
      ellipticPointRhoPlusOne_norm, ellipticPointRhoPlusOne_re_pos⟩
  rw [if_pos hρ1_in_RA, if_pos hρ_in_LA, Finset.sum_singleton, Finset.sum_singleton]
  exact_mod_cast congr_arg (Int.cast (R := ℂ)) (ord_rho_plus_one_eq_ord_rho_via_vAdd f)

/-- Non-elliptic right-arc ord sum equals non-elliptic left-arc ord sum. -/
private theorem sum_nonEllArc_right_eq_left
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    let RA_ne := S.filter (fun p =>
      p ≠ ellipticPointRhoPlusOne' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re > 0)
    let LA_ne := S.filter (fun p =>
      p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)
    ∑ p ∈ RA_ne, (orderOfVanishingAt' (⇑f) p : ℂ) =
    ∑ p ∈ LA_ne, (orderOfVanishingAt' (⇑f) p : ℂ) := by
  intro RA_ne LA_ne
  have h_ra_ne : RA_ne =
      (sRightArc S).filter (· ≠ ellipticPointRhoPlusOne') := by
    ext s; simp only [RA_ne, sRightArc, Finset.mem_filter]; tauto
  have h_la_ne : LA_ne =
      (sLeftArc S).filter (· ≠ ellipticPointRho') := by
    ext s; simp only [LA_ne, sLeftArc, Finset.mem_filter]; tauto
  rw [h_ra_ne, h_la_ne]
  set f_ord := fun s : ℍ => (orderOfVanishingAt' (⇑f) s : ℂ) with hf_ord_def
  have h_ra_split := Finset.sum_filter_add_sum_filter_not (sRightArc S)
    (· ≠ ellipticPointRhoPlusOne') f_ord
  have h_la_split := Finset.sum_filter_add_sum_filter_not (sLeftArc S)
    (· ≠ ellipticPointRho') f_ord
  suffices h_sing :
      ∑ p ∈ (sRightArc S).filter
          (fun x => ¬(x ≠ ellipticPointRhoPlusOne')), f_ord p =
      ∑ p ∈ (sLeftArc S).filter
          (fun x => ¬(x ≠ ellipticPointRho')), f_ord p by
    linear_combination
      sum_ord_rightArc_eq_sum_ord_leftArc f S hS hS_complete +
        h_ra_split - h_la_split - h_sing
  simp_rw [not_not]
  conv_lhs => rw [Finset.filter_eq' (sRightArc S) ellipticPointRhoPlusOne']
  conv_rhs => rw [Finset.filter_eq' (sLeftArc S) ellipticPointRho']
  by_cases h_ord : orderOfVanishingAt' (⇑f) ellipticPointRho' = 0
  · have hf1 : f_ord ellipticPointRho' = 0 := by simp [hf_ord_def, h_ord]
    have hf2 : f_ord ellipticPointRhoPlusOne' = 0 := by
      simp [hf_ord_def, ord_rho_plus_one_eq_ord_rho_via_vAdd f ▸ h_ord]
    split_ifs <;> simp [Finset.sum_singleton, Finset.sum_empty, hf1, hf2]
  · simp only [hf_ord_def]; exact rho_singleton_sum_eq f S hS_complete h_ord

/-- Forward: a non-elliptic, non-interior boundary point of 𝒟 lies in one of
the four boundary subsets (right vert, left vert, right arc, left arc). -/
private theorem bdry_ne_mem_union (S : Finset UpperHalfPlane) (s : UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟) (hs_S : s ∈ S) (hsi : s ≠ ellipticPointI')
    (hsρ : s ≠ ellipticPointRho') (hsρ1 : s ≠ ellipticPointRhoPlusOne')
    (h_not_int : ¬(‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2)) :
    s ∈ sRightVert S ∨ s ∈ sLeftVert S ∨
    (s ∈ S ∧ s ≠ ellipticPointRhoPlusOne' ∧ ‖(s : ℂ)‖ = 1 ∧ (s : ℂ).re > 0) ∨
    (s ∈ S ∧ s ≠ ellipticPointRho' ∧ ‖(s : ℂ)‖ = 1 ∧ (s : ℂ).re < 0) := by
  have hs_fd := hS s hs_S
  have hnorm_ge : 1 ≤ ‖(s : ℂ)‖ := by
    rw [Complex.norm_def]; exact Real.sqrt_one ▸ Real.sqrt_le_sqrt hs_fd.1
  rcases eq_or_lt_of_le hnorm_ge with h_eq | h_gt
  · rcases lt_trichotomy (s : ℂ).re 0 with hre_neg | hre_zero | hre_pos
    · exact Or.inr (Or.inr (Or.inr ⟨hs_S, hsρ, h_eq.symm, hre_neg⟩))
    · exact absurd (unit_circle_re_zero_eq_i s h_eq.symm hre_zero) hsi
    · exact Or.inr (Or.inr (Or.inl ⟨hs_S, hsρ1, h_eq.symm, hre_pos⟩))
  · have h_abs_eq : |(s : ℂ).re| = 1/2 := by
      by_contra h_ne; exact h_not_int ⟨h_gt, lt_of_le_of_ne hs_fd.2 h_ne⟩
    rcases abs_cases (s : ℂ).re with ⟨_, h_sign⟩ | ⟨_, h_sign⟩
    · exact Or.inl (Finset.mem_filter.mpr ⟨hs_S, by linarith, h_gt⟩)
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hs_S, by linarith, h_gt⟩))

/-- Non-elliptic non-interior boundary points decompose into four disjoint sets. -/
private theorem bdry_ne_eq_union (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) :
    let S_NE := S.filter (fun p =>
      p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne')
    S_NE.filter (fun (p : ℍ) => ¬(‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2)) =
    (sRightVert S) ∪ (sLeftVert S) ∪
    S.filter (fun p =>
      p ≠ ellipticPointRhoPlusOne' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re > 0) ∪
    S.filter (fun p =>
      p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0) := by
  intro S_NE
  have h_rho_norm := ellipticPointRho_norm
  have h_rho1_norm := ellipticPointRhoPlusOne_norm
  ext s; simp only [S_NE, sRightVert, sLeftVert, Finset.mem_union, Finset.mem_filter]
  constructor
  · intro ⟨⟨hs_S, hsi, hsρ, hsρ1⟩, h_not_int⟩
    have := bdry_ne_mem_union S s hS hs_S hsi hsρ hsρ1 h_not_int
    simp only [sRightVert, sLeftVert, Finset.mem_filter] at this
    tauto
  · intro h
    rcases h with
      ((⟨hs, hre, hn⟩ | ⟨hs, hre, hn⟩) |
        ⟨hs, hne, hn_eq, hre⟩) |
        ⟨hs, hne, hn_eq, hre⟩
    · exact ⟨⟨hs,
        fun h => by rw [h] at hre; norm_num [ellipticPointI'] at hre,
        fun h => by rw [h] at hn; linarith [h_rho_norm],
        fun h => by rw [h] at hn; linarith [h_rho1_norm]⟩,
        fun ⟨_, h⟩ => by have := (abs_lt.mp h).2; linarith⟩
    · exact ⟨⟨hs,
        fun h => by rw [h] at hre; norm_num [ellipticPointI'] at hre,
        fun h => by rw [h] at hn; linarith [h_rho_norm],
        fun h => by rw [h] at hn; linarith [h_rho1_norm]⟩,
        fun ⟨_, h⟩ => by have := (abs_lt.mp h).1; linarith⟩
    · exact ⟨⟨hs,
        fun h => by rw [h] at hre; simp [ellipticPointI'] at hre,
        fun h => by rw [h] at hre; linarith [ellipticPointRho_re_neg],
        hne⟩,
        fun ⟨h, _⟩ => by linarith⟩
    · exact ⟨⟨hs,
        fun h => by rw [h] at hre; simp [ellipticPointI'] at hre,
        hne,
        fun h => by rw [h] at hre; linarith [ellipticPointRhoPlusOne_re_pos]⟩,
        fun ⟨h, _⟩ => by linarith⟩

omit f hf in
private lemma bdry_four_disjoint (S : Finset UpperHalfPlane) (RA_ne LA_ne : Finset UpperHalfPlane)
    (hRA : RA_ne = S.filter (fun p =>
      p ≠ ellipticPointRhoPlusOne' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re > 0))
    (hLA : LA_ne = S.filter (fun p =>
      p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)) :
    Disjoint (sRightVert S ∪ sLeftVert S ∪ RA_ne) LA_ne := by
  subst hRA; subst hLA
  apply Finset.disjoint_union_left.mpr
  exact ⟨Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_filter.mpr
        fun s _ ⟨hre, _⟩ ⟨_, _, hre2⟩ => by linarith,
      Finset.disjoint_filter.mpr
        fun s _ ⟨_, hn⟩ ⟨_, hn_eq, _⟩ => by linarith⟩,
    Finset.disjoint_filter.mpr
      fun s _ ⟨_, _, hre1⟩ ⟨_, _, hre2⟩ => by linarith⟩

/-- Half the boundary-sum equals the left-vert sum plus the left-arc sum. -/
private theorem half_bdry_sum_eq_leftVert_plus_leftArc (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    let S_NE := S.filter (fun p =>
      p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne')
    let BDRY := S_NE.filter
      (fun (p : ℍ) => ¬(‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2))
    let LA_ne := S.filter (fun p =>
      p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)
    (1/2 : ℂ) * ∑ s ∈ BDRY, (orderOfVanishingAt' (⇑f) s : ℂ) =
    ∑ s ∈ sLeftVert S, (orderOfVanishingAt' (⇑f) s : ℂ) +
    ∑ s ∈ LA_ne, (orderOfVanishingAt' (⇑f) s : ℂ) := by
  intro S_NE BDRY LA_ne
  set RA_ne := S.filter (fun p =>
    p ≠ ellipticPointRhoPlusOne' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re > 0) with hRA_ne_def
  have h_disj_RV_LV : Disjoint (sRightVert S) (sLeftVert S) :=
    Finset.disjoint_filter.mpr fun s _ ⟨hre1, _⟩ ⟨hre2, _⟩ => by linarith
  have h12 : Disjoint (sRightVert S ∪ sLeftVert S) RA_ne :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_filter.mpr fun s _ ⟨_, hn⟩ ⟨_, hn_eq, _⟩ => by linarith,
        Finset.disjoint_filter.mpr fun s _ ⟨hre, _⟩ ⟨_, _, hre2⟩ => by linarith⟩
  have h_sum_decomp :
      ∑ s ∈ BDRY, (orderOfVanishingAt' (⇑f) s : ℂ) =
      ∑ s ∈ sRightVert S, (orderOfVanishingAt' (⇑f) s : ℂ) +
      ∑ s ∈ sLeftVert S, (orderOfVanishingAt' (⇑f) s : ℂ) +
      ∑ s ∈ RA_ne, (orderOfVanishingAt' (⇑f) s : ℂ) +
      ∑ s ∈ LA_ne, (orderOfVanishingAt' (⇑f) s : ℂ) := by
    have h_bdry_decomp : BDRY =
        sRightVert S ∪ sLeftVert S ∪ RA_ne ∪ LA_ne := bdry_ne_eq_union S hS
    rw [h_bdry_decomp,
      Finset.sum_union (bdry_four_disjoint S RA_ne LA_ne hRA_ne_def rfl),
      Finset.sum_union h12, Finset.sum_union h_disj_RV_LV]
  rw [h_sum_decomp, sum_ord_rightVert_eq_sum_ord_leftVert f S hS hS_complete,
    sum_nonEllArc_right_eq_left f S hS hS_complete]; ring

include hf in
/-- Orbit-sum valence formula with boundary weight hypothesis. -/
theorem valence_formula_orbit_sum (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' ∧
        ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
      ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ sLeftVert S, ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
      ↑(orderOfVanishingAt' (⇑f) s) =
    (k : ℂ) / 12 := by
  obtain ⟨H₀, hH₀, h_explicit⟩ := explicit_coefficients f hf S hS hS_complete
  obtain ⟨H₁, hH₁, h_bdry⟩ := boundary_weight_auto S hS
  set M := S.sum (fun s : UpperHalfPlane => (s : ℂ).im)
  set H := max (max H₀ H₁) (max heightCutoff M + 1)
  have hH_height : heightCutoff ≤ H := by
    linarith [le_max_left heightCutoff M,
      le_max_right (max H₀ H₁) (max heightCutoff M + 1)]
  have hH_above : ∀ s ∈ S, (s : ℂ).im < H := fun s hs => by
    have h1 : (s : ℂ).im ≤ M := Finset.single_le_sum (fun x _ => le_of_lt x.2) hs
    linarith [le_max_right heightCutoff M,
      le_max_right (max H₀ H₁) (max heightCutoff M + 1)]
  have hH0_le : H₀ ≤ H := le_trans (le_max_left _ _) (le_max_left _ _)
  have h_explicit' := h_explicit hH0_le
  rw [ord_rho_plus_one_eq_ord_rho_via_vAdd f] at h_explicit'
  have h_formula : (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
      (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
      ∑ s ∈ S.filter (fun p =>
          p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne'),
        (-generalizedWindingNumber' (fdBoundaryH H) 0 5 (↑s : ℂ)) *
          ↑(orderOfVanishingAt' (⇑f) s) =
      (k : ℂ) / 12 := by linear_combination h_explicit'
  set S_NE := S.filter (fun p =>
    p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧
    p ≠ ellipticPointRhoPlusOne') with hS_NE_def
  set INT := S.filter (fun p =>
    p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' ∧
    ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2)
  suffices h_eq :
      ∑ s ∈ S_NE,
        (-generalizedWindingNumber' (fdBoundaryH H) 0 5 (↑s : ℂ)) *
          ↑(orderOfVanishingAt' (⇑f) s) =
      ∑ s ∈ INT, ↑(orderOfVanishingAt' (⇑f) s) +
      ∑ s ∈ sLeftVert S, ↑(orderOfVanishingAt' (⇑f) s) +
      ∑ s ∈ S.filter (fun p =>
          p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
        ↑(orderOfVanishingAt' (⇑f) s) by
    rw [h_eq] at h_formula; linear_combination h_formula
  have h_gWN_val : ∀ s ∈ S_NE,
      (-generalizedWindingNumber' (fdBoundaryH H) 0 5 (↑s : ℂ)) *
        ↑(orderOfVanishingAt' (⇑f) s) =
      (if ‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2 then (1 : ℂ) else 1/2) *
        ↑(orderOfVanishingAt' (⇑f) s) := by
    intro s hs
    simp only [hS_NE_def, Finset.mem_filter] at hs
    obtain ⟨hs_S, hsi, hsρ, hsρ1⟩ := hs
    split_ifs with h_int
    · obtain ⟨hnorm, hre⟩ := h_int
      rw [gWN_fdBoundary_H_eq_neg_one_of_strictInterior _
        hnorm hre s.2 hH_height (hH_above s hs_S)]; ring
    · rw [h_bdry (le_trans (le_max_right _ _) (le_max_left _ _)) s hs_S hsi hsρ hsρ1 h_int]; ring
  rw [Finset.sum_congr rfl h_gWN_val]
  set LA_ne := S.filter (fun p =>
    p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)
  set BDRY := S_NE.filter
    (fun (p : ℍ) => ¬(‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2))
  have h_ne_int : S_NE.filter
      (fun (p : ℍ) => ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2) = INT := by
    ext s; simp only [hS_NE_def, INT, Finset.mem_filter]; tauto
  have h_bdry_identity := half_bdry_sum_eq_leftVert_plus_leftArc f S hS hS_complete
  have h_split := Finset.sum_filter_add_sum_filter_not S_NE
    (fun (p : ℍ) => ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2) (fun s =>
      (if ‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2 then (1 : ℂ) else 1/2) *
        ↑(orderOfVanishingAt' (⇑f) s))
  have h_int_sum :
      ∑ x ∈ S_NE.filter (fun (p : ℍ) => ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
        (if ‖(x : ℂ)‖ > 1 ∧ |(x : ℂ).re| < 1/2 then (1 : ℂ) else 1/2) *
          ↑(orderOfVanishingAt' (⇑f) x) =
      ∑ x ∈ INT, ↑(orderOfVanishingAt' (⇑f) x) := by
    rw [h_ne_int]; apply Finset.sum_congr rfl
    intro s hs
    simp only [INT, Finset.mem_filter] at hs
    rw [if_pos ⟨hs.2.2.2.2.1, hs.2.2.2.2.2⟩, one_mul]
  have h_bdry_sum :
      ∑ x ∈ BDRY,
        (if ‖(x : ℂ)‖ > 1 ∧ |(x : ℂ).re| < 1/2 then (1 : ℂ) else 1/2) *
          ↑(orderOfVanishingAt' (⇑f) x) =
      (1/2 : ℂ) * ∑ x ∈ BDRY, (orderOfVanishingAt' (⇑f) x : ℂ) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s hs
    rw [if_neg (show ¬(‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2) from
      (Finset.mem_filter.mp hs).2)]
  linear_combination h_int_sum + h_bdry_sum + h_bdry_identity - h_split

end
