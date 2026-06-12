/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.OrbitSum

/-!
# Canonical Representatives for Non-Elliptic Orbits

Every non-elliptic orbit with nonzero order of vanishing has a representative in the canonical
finsets used by `valence_formula_orbit_sum_s₀`.

## Main Results

* `exists_repCanon_of_nonEllOrbit` — For any non-elliptic orbit `q` with `ordOrbit f q ≠ 0`,
  there exists `p ∈ repCanon f hf` with `orb p = q`.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-- Strict interior representatives: points in s₀ with ‖p‖ > 1, |re| < 1/2, not elliptic. -/
noncomputable def repStrict : Finset ℍ :=
  (s₀ f hf).filter (fun p => p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧
    p ≠ ellipticPointRhoPlusOne' ∧ ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2)

/-- Left vertical edge representatives: points in s₀ with re = -1/2, ‖p‖ > 1. -/
noncomputable def repLeftVert : Finset ℍ := sLeftVert (s₀ f hf)

/-- Left arc representatives: points in s₀ with ‖p‖ = 1, re < 0, not ρ. -/
noncomputable def repLeftArc : Finset ℍ :=
  (s₀ f hf).filter (fun p => p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)

/-- The canonical representative finset: union of strict interior, left vertical, and left arc. -/
noncomputable def repCanon : Finset ℍ :=
  repStrict f hf ∪ repLeftVert f hf ∪ repLeftArc f hf

lemma repStrict_mem_s₀ {p : ℍ} (hp : p ∈ repStrict f hf) : p ∈ s₀ f hf :=
  (Finset.mem_filter.mp hp).1

lemma repLeftVert_mem_s₀ {p : ℍ} (hp : p ∈ repLeftVert f hf) : p ∈ s₀ f hf :=
  (Finset.mem_filter.mp hp).1

lemma repLeftArc_mem_s₀ {p : ℍ} (hp : p ∈ repLeftArc f hf) : p ∈ s₀ f hf :=
  (Finset.mem_filter.mp hp).1

lemma repCanon_mem_s₀ {p : ℍ} (hp : p ∈ repCanon f hf) :
    p ∈ s₀ f hf := by
  simp only [repCanon, Finset.mem_union] at hp
  obtain (h | h) | h := hp
  · exact repStrict_mem_s₀ f hf h
  · exact repLeftVert_mem_s₀ f hf h
  · exact repLeftArc_mem_s₀ f hf h

lemma repCanon_mem_fd {p : ℍ} (hp : p ∈ repCanon f hf) : p ∈ 𝒟 :=
  s₀_mem_fd f hf p (repCanon_mem_s₀ f hf hp)

/-- T⁻¹-translation preserves orbits: `orb((-1)+ᵥp) = orb(p)`. -/
lemma orb_vAdd_neg_one_eq (p : ℍ) :
    orb ((-1 : ℝ) +ᵥ p) = orb p := by
  have h_eq : ModularGroup.T⁻¹ • p = (-1 : ℝ) +ᵥ p := by
    have h1 : ModularGroup.T • (ModularGroup.T⁻¹ • p) = p :=
      smul_inv_smul _ p
    rw [UpperHalfPlane.modular_T_smul] at h1
    have h2 : ModularGroup.T⁻¹ • p = (-1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ (ModularGroup.T⁻¹ • p)) := by
      rw [← add_vadd, show (-1 : ℝ) + 1 = 0 from by ring,
        zero_vadd]
    rwa [h1] at h2
  change Quotient.mk'' ((-1 : ℝ) +ᵥ p) = Quotient.mk'' p
  rw [Quotient.eq'', MulAction.orbitRel_apply,
    MulAction.mem_orbit_iff]
  exact ⟨ModularGroup.T⁻¹, h_eq⟩

/-- S-action preserves orbits: `orb(S • p) = orb(p)`. -/
lemma orb_S_smul_eq (p : ℍ) :
    orb (ModularGroup.S • p) = orb p := by
  change Quotient.mk'' (ModularGroup.S • p) = Quotient.mk'' p
  rw [Quotient.eq'', MulAction.orbitRel_apply,
    MulAction.mem_orbit_iff]
  exact ⟨ModularGroup.S, rfl⟩

private lemma uhp_norm_one_re_zero_eq_i (p : ℍ) (hn : ‖(p : ℂ)‖ = 1) (hr : (p : ℂ).re = 0) :
    p = ellipticPointI' := by
  apply UpperHalfPlane.ext; change (p : ℂ) = I
  have h_nsq : Complex.normSq (p : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hn, one_pow]
  rw [Complex.normSq_apply, hr] at h_nsq
  have h_im : (p : ℂ).im = 1 := by
    have h_prod : ((p : ℂ).im - 1) * ((p : ℂ).im + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp h_prod with h | h
    · linarith
    · exact absurd h (ne_of_gt (add_pos p.2 one_pos))
  exact Complex.ext (hr.trans Complex.I_re.symm) (h_im.trans Complex.I_im.symm)

private lemma uhp_norm_one_re_neg_half_eq_rho (p : ℍ)
    (hn : ‖(p : ℂ)‖ = 1) (hr : (p : ℂ).re = -1 / 2) :
    p = ellipticPointRho' := by
  apply UpperHalfPlane.ext
  show (p : ℂ) = (ellipticPointRho' : ℂ)
  have h_nsq : Complex.normSq (p : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hn, one_pow]
  rw [Complex.normSq_apply, hr] at h_nsq
  have h_im : (p : ℂ).im = Real.sqrt 3 / 2 := by
    have h_sq : (p : ℂ).im ^ 2 = 3 / 4 := by nlinarith
    have h_im_sq : (p : ℂ).im ^ 2 = (Real.sqrt 3 / 2) ^ 2 := by
      rw [h_sq, div_pow, Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]; norm_num
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h_im_sq with h | h
    · exact h
    · exact absurd h (by
        have : (↑p : ℂ).im > 0 := p.2
        linarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)])
  apply Complex.ext
  · simp [ellipticPointRho']; have : p.re = (↑p : ℂ).re := rfl; linarith
  · simp [ellipticPointRho']; have : p.im = (↑p : ℂ).im := rfl; linarith

private lemma uhp_norm_one_re_half_eq_rho_plus_one (p : ℍ)
    (hn : ‖(p : ℂ)‖ = 1) (hr : (p : ℂ).re = 1 / 2) :
    p = ellipticPointRhoPlusOne' := by
  apply UpperHalfPlane.ext
  show (p : ℂ) = (ellipticPointRhoPlusOne' : ℂ)
  have h_nsq : Complex.normSq (p : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hn, one_pow]
  rw [Complex.normSq_apply, hr] at h_nsq
  have h_im : (p : ℂ).im = Real.sqrt 3 / 2 := by
    have h_sq : (p : ℂ).im ^ 2 = 3 / 4 := by nlinarith
    have h_im_sq : (p : ℂ).im ^ 2 = (Real.sqrt 3 / 2) ^ 2 := by
      rw [h_sq, div_pow, Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]; norm_num
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h_im_sq with h | h
    · exact h
    · exact absurd h (by
        have : (↑p : ℂ).im > 0 := p.2
        linarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)])
  apply Complex.ext
  · simp [ellipticPointRhoPlusOne']; have : p.re = (↑p : ℂ).re := rfl; linarith
  · simp [ellipticPointRhoPlusOne']; have : p.im = (↑p : ℂ).im := rfl; linarith

private lemma case_right_vertical_via_tInv (q : NonEllOrbit) (p0 : ℍ)
    (hp0_fd : p0 ∈ 𝒟) (hp0_ord : orderOfVanishingAt' (⇑f) p0 ≠ 0)
    (h_half : (↑p0 : ℂ).re = 1 / 2) (h_gt : ‖(↑p0 : ℂ)‖ > 1)
    (hp0_orb : orb p0 = q.val) :
    ∃ p1 ∈ repCanon f hf, orb p1 = q.val := by
  set p1 := (-1 : ℝ) +ᵥ p0
  have hp1_ord : orderOfVanishingAt' (⇑f) p1 ≠ 0 := (ord_vAdd_neg_one_eq f p0).symm ▸ hp0_ord
  have hp1_s₀ : p1 ∈ s₀ f hf :=
    s₀_complete f hf p1 (vAdd_neg_one_mem_fd_of_right_vert p0 hp0_fd h_half) hp1_ord
  have hp1_re : (↑p1 : ℂ).re = -1/2 := by
    change (↑((-1 : ℝ) +ᵥ p0 : ℍ) : ℂ).re = -1/2
    rw [vAdd_neg_one_coe, sub_re, one_re]; linarith
  have hp1_norm : ‖(↑p1 : ℂ)‖ > 1 := by
    change ‖(↑((-1 : ℝ) +ᵥ p0 : ℍ) : ℂ)‖ > 1
    rw [vAdd_neg_one_norm_eq_of_re_half p0 h_half]; exact h_gt
  refine ⟨p1, ?_, orb_vAdd_neg_one_eq p0 ▸ hp0_orb⟩
  simp only [repCanon, Finset.mem_union]; left; right
  exact Finset.mem_filter.mpr ⟨hp1_s₀, hp1_re, hp1_norm⟩

private lemma case_right_arc_via_S (q : NonEllOrbit) (p0 : ℍ)
    (hp0_fd : p0 ∈ 𝒟) (hp0_ord : orderOfVanishingAt' (⇑f) p0 ≠ 0)
    (h_norm_eq : ‖(↑p0 : ℂ)‖ = 1) (h_pos : (↑p0 : ℂ).re > 0)
    (hp0_orb : orb p0 = q.val) (hq_ne_rho : orb (ellipticPointRho' : ℍ) ≠ q.val) :
    ∃ p1 ∈ repCanon f hf, orb p1 = q.val := by
  set p1 := ModularGroup.S • p0
  have hp1_ord : orderOfVanishingAt' (⇑f) p1 ≠ 0 := (ord_S_eq f p0).symm ▸ hp0_ord
  have hp1_s₀ : p1 ∈ s₀ f hf :=
    s₀_complete f hf p1 (S_smul_mem_fd_of_unit p0 hp0_fd h_norm_eq) hp1_ord
  have h_re_S : (ModularGroup.S • p0 : ℍ).re = -p0.re :=
    S_smul_re_neg_of_unit p0 h_norm_eq
  have hp1_re_neg : (↑p1 : ℂ).re < 0 := by
    change (ModularGroup.S • p0 : ℍ).re < 0; rw [h_re_S]
    have : p0.re = (↑p0 : ℂ).re := rfl; linarith
  have hp1_ne_rho : p1 ≠ ellipticPointRho' := by
    intro h
    have : orb ellipticPointRho' = q.val := by
      rw [← h, show orb (ModularGroup.S • p0) = orb p0 from orb_S_smul_eq p0, hp0_orb]
    exact hq_ne_rho this
  refine ⟨p1, ?_, orb_S_smul_eq p0 ▸ hp0_orb⟩
  simp only [repCanon, Finset.mem_union]; right
  exact Finset.mem_filter.mpr ⟨hp1_s₀, hp1_ne_rho,
    S_smul_norm_of_unit p0 h_norm_eq, hp1_re_neg⟩

/-- Every non-elliptic orbit with nonzero order has a representative in `repCanon`. -/
theorem exists_repCanon_of_nonEllOrbit :
    ∀ q : NonEllOrbit,
      ordOrbit f q.val ≠ 0 →
      ∃ p ∈ repCanon f hf, orb p = q.val := by
  intro q hord
  obtain ⟨hq_ne_i, hq_ne_rho⟩ := q.2
  obtain ⟨p0, hp0_orb, hp0_fd⟩ := orbit_has_fd_rep q.val
  have hp0_ord : orderOfVanishingAt' (⇑f) p0 ≠ 0 := by
    rw [← ordOrbit_mk f p0, hp0_orb]; exact hord
  have hp0_s₀ : p0 ∈ s₀ f hf := s₀_complete f hf p0 hp0_fd hp0_ord
  have hp0_ne_i : p0 ≠ ellipticPointI' :=
    fun h ↦ by rw [h] at hp0_orb; exact hq_ne_i hp0_orb.symm
  have hp0_ne_rho : p0 ≠ ellipticPointRho' :=
    fun h ↦ by rw [h] at hp0_orb; exact hq_ne_rho hp0_orb.symm
  have hp0_ne_rho1 : p0 ≠ ellipticPointRhoPlusOne' := fun h ↦ by
    rw [h] at hp0_orb; exact hq_ne_rho (hp0_orb.symm.trans orb_rho_plus_one_eq_orb_rho)
  rcases (by nlinarith [Complex.normSq_eq_norm_sq (p0 : ℂ),
      norm_nonneg (p0 : ℂ), sq_nonneg (‖(p0 : ℂ)‖ - 1),
      hp0_fd.1] : ‖(p0 : ℂ)‖ ≥ 1).lt_or_eq with h_gt | h_eq
  · rcases hp0_fd.2.lt_or_eq with h_re_lt | h_re_eq
    · refine ⟨p0, ?_, hp0_orb⟩
      simp only [repCanon, Finset.mem_union]; left; left
      exact Finset.mem_filter.mpr ⟨hp0_s₀, hp0_ne_i, hp0_ne_rho, hp0_ne_rho1, h_gt, h_re_lt⟩
    · rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1/2)).mp h_re_eq with h_half | h_neg_half
      · exact case_right_vertical_via_tInv f hf q p0 hp0_fd hp0_ord h_half h_gt hp0_orb
      · refine ⟨p0, ?_, hp0_orb⟩
        simp only [repCanon, Finset.mem_union]; left; right
        exact Finset.mem_filter.mpr ⟨hp0_s₀, by change p0.re = -1/2; linarith, h_gt⟩
  · have h_norm_eq : ‖(↑p0 : ℂ)‖ = 1 := h_eq.symm
    have h_re_ne_zero : (↑p0 : ℂ).re ≠ 0 :=
      fun h => hp0_ne_i (uhp_norm_one_re_zero_eq_i p0 h_norm_eq h)
    rcases lt_or_gt_of_ne h_re_ne_zero with h_neg | h_pos
    · refine ⟨p0, ?_, hp0_orb⟩
      simp only [repCanon, Finset.mem_union]; right
      exact Finset.mem_filter.mpr ⟨hp0_s₀, hp0_ne_rho, h_norm_eq, h_neg⟩
    · exact case_right_arc_via_S f hf q p0 hp0_fd hp0_ord h_norm_eq h_pos hp0_orb hq_ne_rho.symm

end
