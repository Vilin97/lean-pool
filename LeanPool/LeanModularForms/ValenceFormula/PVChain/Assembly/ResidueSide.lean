/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.PVChain.OnCurveCapture
import LeanPool.LeanModularForms.ValenceFormula.PVChain.ResidueSideInfra
import LeanPool.LeanModularForms.ValenceFormula.ModularInvariance

/-!
# PV Chain Assembly: Residue Side

The residue side of the PV chain assembly, showing that the ε-truncated
integral of `f'/f` around `fdBoundaryH H` tends to `2πi · Σ gWN · ord`.

## Main Results

* `cpv_residue_side_tendsto` — the ε-truncated integral tends to
  `2πi · Σ gWN · ord`
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-! ### Residue side -/

include hf in
private lemma fd_point_mem_fdBox
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    {H M : ℝ} (hM_half : (1 : ℝ) / 2 < M) (hH_lt_M : H < M)
    (hH_bound : ∀ s ∈ S, (s : ℂ).im < H)
    (p : UpperHalfPlane) (hp_S : p ∈ S) (hp_zero : f p = 0) :
    (↑p : ℂ) ∈ allZerosInFdBox f hf hM_half := by
  rw [mem_allZerosInFdBox_iff]
  have h_fd := hS p hp_S
  refine ⟨⟨?_, ?_, ?_, by linarith [hH_bound p hp_S]⟩, ?_⟩
  · rw [UpperHalfPlane.coe_re]; linarith [(abs_le.mp h_fd.2).1]
  · rw [UpperHalfPlane.coe_re]; linarith [(abs_le.mp h_fd.2).2]
  · by_contra h_le
    have h_le' : (↑p : ℂ).im ≤ 1/2 := le_of_not_gt h_le
    rw [UpperHalfPlane.coe_im] at h_le'
    have h_nsq :
        1 ≤ p.re * p.re + p.im * p.im := by
      have := Complex.normSq_apply (↑p : ℂ)
      rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at this
      linarith [h_fd.1]
    nlinarith [(abs_le.mp h_fd.2).1, (abs_le.mp h_fd.2).2, p.im_pos]
  · have h_mfcc_eq : modularFormCompOfComplex f (↑p : ℂ) = f p := by
      simp only [modularFormCompOfComplex, Function.comp_apply]
      congr 1; exact UpperHalfPlane.ofComplex_apply_of_im_pos p.im_pos
    rw [h_mfcc_eq]; exact hp_zero

omit f hf in
private lemma exists_height_above_sqrt3_and_S
    (S : Finset UpperHalfPlane) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧ 1 ≤ H₀ ∧
      ∀ s ∈ S, (s : ℂ).im < H₀ := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)],
      le_refl _, fun s hs => absurd hs (Finset.notMem_empty s)⟩
  · refine ⟨max 1 (S.sup' hne (fun s => (s : ℂ).im) + 1), ?_, ?_, ?_⟩
    · calc Real.sqrt 3 / 2 < 1 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
          _ ≤ _ := le_max_left _ _
    · exact le_max_left _ _
    · intro s hs
      exact lt_of_le_of_lt (Finset.le_sup' (fun p : ℍ => (p : ℂ).im) hs)
        (lt_of_lt_of_le (lt_add_one _) (le_max_right _ _))

include hf in
private lemma cpv_residue_side_simplePoles
    (S : Finset UpperHalfPlane)
    {H : ℝ} (_hH_sqrt3 : Real.sqrt 3 / 2 < H)
    {M : ℝ} (hM_half : (1 : ℝ) / 2 < M)
    (Sbox : Finset ℂ) (hSbox : Sbox = allZerosInFdBox f hf hM_half)
    (S_on : Finset ℂ) (hS_on : S_on = sArcOfS S ∪ sVertOfS S) :
    ∀ s ∈ Sbox ∪ S_on,
      HasSimplePoleAt (logDeriv (modularFormCompOfComplex f)) s := by
  intro s hs; rw [Finset.mem_union] at hs
  rcases hs with h_box | h_on
  · exact hasSimplePoleAt_logDeriv_at_point f hf s
      (fdBox_im_pos ((mem_allZerosInFdBox_iff f hf hM_half).mp (hSbox ▸ h_box)).1)
  · exact hasSimplePoleAt_logDeriv_at_point f hf s (by
      rw [hS_on] at h_on
      rcases Finset.mem_union.mp h_on with h | h
      · exact sArcOfS_im_pos S s h
      · exact sVertOfS_im_pos S s h)

include hf in
private lemma cpv_residue_side_Fp_diffOn
    (_S : Finset UpperHalfPlane)
    {M : ℝ} (hM_half : (1 : ℝ) / 2 < M)
    (Sbox : Finset ℂ) (hSbox : Sbox = allZerosInFdBox f hf hM_half)
    (S_on : Finset ℂ)
    (S0 : Finset ℂ) (hS0 : S0 = Sbox ∪ S_on)
    (hSimplePoles : ∀ s ∈ S0,
      HasSimplePoleAt (logDeriv (modularFormCompOfComplex f)) s) :
    let F := logDeriv (modularFormCompOfComplex f)
    let Fp := logDerivPatched F S0 hSimplePoles
    DifferentiableOn ℂ Fp (fdBox M \ ↑S0) := by
  intro F Fp z hz
  have hz_not_S0 : z ∉ (S0 : Finset ℂ) :=
    fun h => hz.2 (Finset.mem_coe.mpr h)
  have h_ev : Fp =ᶠ[𝓝 z] F := by
    filter_upwards [S0.finite_toSet.isClosed.isOpen_compl.mem_nhds hz_not_S0]
      with w hw
    exact logDerivPatched_eq_raw_off F S0 hSimplePoles hw
  exact (h_ev.differentiableAt_iff.mpr
    (analyticAt_logDeriv_off_zeros' f z (fdBox_im_pos hz.1) (fun h_zero =>
      hz_not_S0 (hS0 ▸ Finset.mem_union_left S_on
        (hSbox ▸ (mem_allZerosInFdBox_iff f hf hM_half).mpr ⟨hz.1, h_zero⟩)))
      ).differentiableAt).differentiableWithinAt

private lemma cpv_residue_side_cpvExists
    (_S : Finset UpperHalfPlane)
    {H : ℝ} (hH_sqrt3 : Real.sqrt 3 / 2 < H)
    (S0 : Finset ℂ)
    (hSimplePoles : ∀ s ∈ S0,
      HasSimplePoleAt (logDeriv (modularFormCompOfComplex f)) s) :
    let F := logDeriv (modularFormCompOfComplex f)
    let _γ := fdBoundaryH H
    let Fp := logDerivPatched F S0 hSimplePoles
    let γ_imm := fdBoundaryHImmersion H hH_sqrt3
    ∀ s ∈ S0, CauchyPrincipalValueExists'
      (fun z => residueSimplePole Fp s / (z - s))
      γ_imm.toFun γ_imm.a γ_imm.b s := by
  intro F γ Fp γ_imm s hs
  have h_res_eq : residueSimplePole Fp s = residueSimplePole F s :=
    residue_logDerivPatched_eq_raw F S0 hSimplePoles s hs
  rw [show γ_imm.toFun = γ from rfl,
      show γ_imm.a = (0 : ℝ) from rfl,
      show γ_imm.b = (5 : ℝ) from rfl, h_res_eq]
  by_cases h_on_curve : ∃ t ∈ Icc (0 : ℝ) 5, γ t = s
  · exact cpvExists_scale γ 0 5 s _ (fdBoundary_H_cpv_exists_of_onCurve H hH_sqrt3 s h_on_curve)
  · push Not at h_on_curve
    exact cpvExists_of_off_curve γ (fdBoundary_H_continuous H) 0 5 s _
      (by norm_num) h_on_curve

include hf in
private lemma cpv_residue_side_off_curve_min_dist
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete :
      ∀ p, p ∈ 𝒟 →
        orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H : ℝ} (hH_sqrt3 : Real.sqrt 3 / 2 < H)
    (hH_ge1 : 1 ≤ H)
    (hH_bound : ∀ s ∈ S, (s : ℂ).im < H)
    {M : ℝ} (hM_half : (1 : ℝ) / 2 < M) (_hHM : H < M)
    (Sbox : Finset ℂ) (hSbox : Sbox = allZerosInFdBox f hf hM_half)
    (S_on : Finset ℂ) (hS_on : S_on = sArcOfS S ∪ sVertOfS S) :
    ∀ s ∈ Sbox \ S_on,
      ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 5, δ ≤ ‖fdBoundaryH H t - s‖ := by
  intro s hs
  set γ := fdBoundaryH H
  have h_capture_S_on : ∀ t ∈ Icc (0 : ℝ) 5,
      modularFormCompOfComplex f (γ t) = 0 →
      γ t ∈ (↑(sArcOfS S ∪ sVertOfS S) : Set ℂ) :=
    oncurve_full_capture f hf S hS hS_complete hH_ge1 hH_sqrt3 hH_bound
  have h_off : ∀ t ∈ Icc (0 : ℝ) 5, γ t ≠ s := by
    intro t ht heq
    obtain ⟨h_box, h_narc⟩ := Finset.mem_sdiff.mp hs
    rw [hS_on] at h_narc
    exact h_narc (Finset.mem_coe.mp (heq ▸ h_capture_S_on t ht
      (heq ▸ ((mem_allZerosInFdBox_iff f hf hM_half).mp (hSbox ▸ h_box)).2)))
  have h_cont : ContinuousOn (fun t => ‖γ t - s‖) (Icc 0 5) :=
    ((fdBoundary_H_continuous H).continuousOn.sub continuousOn_const).norm
  obtain ⟨t₀, ht₀, ht₀_min⟩ := isCompact_Icc.exists_isMinOn
    ⟨0, left_mem_Icc.mpr (by norm_num)⟩ h_cont
  exact ⟨‖γ t₀ - s‖, norm_pos_iff.mpr (sub_ne_zero.mpr (h_off t₀ ht₀)),
    fun t ht => ht₀_min ht⟩

include hf in
private lemma cpv_residue_side_eventually_eq
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete :
      ∀ p, p ∈ 𝒟 →
        orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H : ℝ} (hH_sqrt3 : Real.sqrt 3 / 2 < H)
    (hH_ge1 : 1 ≤ H)
    (hH_bound : ∀ s ∈ S, (s : ℂ).im < H)
    {M : ℝ} (hM_half : (1 : ℝ) / 2 < M) (hHM : H < M)
    (Sbox : Finset ℂ) (hSbox : Sbox = allZerosInFdBox f hf hM_half)
    (S_on : Finset ℂ) (hS_on : S_on = sArcOfS S ∪ sVertOfS S)
    (S0 : Finset ℂ) (hS0 : S0 = Sbox ∪ S_on) :
    let F := logDeriv (modularFormCompOfComplex f)
    let γ := fdBoundaryH H
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t ∈ Set.uIcc (0 : ℝ) 5,
        cauchyPrincipalValueIntegrandOn S0 F γ ε t =
        cauchyPrincipalValueIntegrandOn S_on F γ ε t := by
  intro F γ
  have h_finite_family : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ s ∈ Sbox \ S_on, ∀ t ∈ Icc (0 : ℝ) 5, ε < ‖γ t - s‖ := by
    have : ∀ s ∈ Sbox \ S_on, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∀ t ∈ Icc (0 : ℝ) 5, ε < ‖γ t - s‖ := by
      intro s hs
      obtain ⟨δ, hδ_pos, hδ_bound⟩ := cpv_residue_side_off_curve_min_dist
        f hf S hS hS_complete hH_sqrt3 hH_ge1 hH_bound hM_half hHM
        Sbox hSbox S_on hS_on s hs
      filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
      intro t ht; exact lt_of_lt_of_le hε.2 (hδ_bound t ht)
    have h_all : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∀ (s : ((Sbox \ S_on : Finset ℂ) : Set ℂ)),
          ∀ t ∈ Icc (0 : ℝ) 5, ε < ‖γ t - (s : ℂ)‖ := by
      rw [Filter.eventually_all]; intro ⟨s, hs⟩; exact this s hs
    exact h_all.mono (fun ε hε s hs => hε ⟨s, hs⟩)
  filter_upwards [h_finite_family] with ε hε t ht
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at ht
  simp only [cauchyPrincipalValueIntegrandOn]
  have h_iff :
      (∃ s ∈ S0, ‖γ t - s‖ ≤ ε) ↔ (∃ s ∈ S_on, ‖γ t - s‖ ≤ ε) := by
    constructor
    · rintro ⟨s, hs, h_norm⟩
      rw [hS0, Finset.mem_union] at hs
      rcases hs with h_box | h_on
      · by_cases h_on2 : s ∈ S_on
        · exact ⟨s, h_on2, h_norm⟩
        · exact absurd h_norm (not_le.mpr
            (hε s (Finset.mem_sdiff.mpr ⟨h_box, h_on2⟩) t ht))
      · exact ⟨s, h_on, h_norm⟩
    · rintro ⟨s, hs, h_norm⟩
      exact ⟨s, hS0 ▸ Finset.mem_union.mpr (Or.inr hs), h_norm⟩
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (h_iff.mp h1) h2
  · exact absurd (h_iff.mpr h2) h1
  · rfl

include hf in
/-- The on-curve singular points that are not box-zeros contribute zero to the
    residue sum (the curve avoids non-zeros, so the residue vanishes there).
    Shared between `cpv_residue_side_sum_convert` and `cpv_residue_side_tendsto`. -/
private lemma residue_sum_over_S_on_sdiff_Sbox_zero
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    {H : ℝ} (hH_sqrt3 : Real.sqrt 3 / 2 < H)
    (hH_ge1 : 1 ≤ H)
    (hH_bound : ∀ s ∈ S, (s : ℂ).im < H)
    {M : ℝ} (hM_half : (1 : ℝ) / 2 < M) (hHM : H < M)
    (Sbox : Finset ℂ) (hSbox : Sbox = allZerosInFdBox f hf hM_half)
    (S_on : Finset ℂ) (hS_on : S_on = sArcOfS S ∪ sVertOfS S) :
    ∑ s ∈ S_on \ Sbox,
      generalizedWindingNumber' (fdBoundaryH H) 0 5 s *
        residueSimplePole (logDeriv (modularFormCompOfComplex f)) s = 0 := by
  apply Finset.sum_eq_zero; intro s hs
  have hs_on := (Finset.mem_sdiff.mp hs).1
  have h_nz : modularFormCompOfComplex f s ≠ 0 := by
    intro h_zero
    exact (Finset.mem_sdiff.mp hs).2 (hSbox ▸
      (mem_allZerosInFdBox_iff f hf hM_half).mpr
        ⟨fdBox_of_on_curve S hS hH_sqrt3 hHM hH_ge1 hH_bound s
          (hS_on ▸ hs_on), h_zero⟩)
  rw [residueSimplePole_logDeriv_eq_zero_at_nonzero f s (by
    rw [hS_on] at hs_on
    rcases Finset.mem_union.mp hs_on with h | h
    · exact sArcOfS_im_pos S s h
    · exact sVertOfS_im_pos S s h) h_nz, mul_zero]

include hf in
private lemma cpv_residue_side_sum_convert
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete :
      ∀ p, p ∈ 𝒟 →
        orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H : ℝ} (hH_sqrt3 : Real.sqrt 3 / 2 < H)
    (hH_ge1 : 1 ≤ H)
    (hH_bound : ∀ s ∈ S, (s : ℂ).im < H)
    (S_on : Finset ℂ) (hS_on : S_on = sArcOfS S ∪ sVertOfS S) :
    let hM_half : (1 : ℝ)/2 < H + 1 := by linarith
    let Sbox := allZerosInFdBox f hf hM_half
    let F := logDeriv (modularFormCompOfComplex f)
    let γ := fdBoundaryH H
    ∑ s ∈ Sbox,
      generalizedWindingNumber' γ 0 5 s *
        residueSimplePole F s =
    ∑ s ∈ S, generalizedWindingNumber' γ 0 5 (↑s : ℂ) *
      (orderOfVanishingAt' (⇑f) s : ℂ) := by
  intro hM_half Sbox F γ
  have hHM : H < H + 1 := lt_add_one H
  have h_sarc_zero : ∑ s ∈ S_on \ Sbox,
      generalizedWindingNumber' γ 0 5 s *
        residueSimplePole F s = 0 :=
    residue_sum_over_S_on_sdiff_Sbox_zero f hf S hS hH_sqrt3 hH_ge1 hH_bound
      hM_half hHM Sbox rfl S_on hS_on
  set S_zeros := S.filter (fun p => f p = 0) with hS_zeros_def
  have h_image_sub : S_zeros.image (↑· : ℍ → ℂ) ⊆ Sbox :=
    Finset.image_subset_iff.mpr (fun p hp => by
      rw [Finset.mem_filter] at hp
      exact fd_point_mem_fdBox f hf S hS hM_half hHM hH_bound p hp.1 hp.2)
  have h_complement_zero : ∀ s ∈ Sbox,
      s ∉ S_zeros.image (↑· : ℍ → ℂ) →
      generalizedWindingNumber' γ 0 5 s *
        residueSimplePole F s = 0 := by
    intro s hs hs_ni
    have h_not_S : ∀ p ∈ S, (↑p : ℂ) ≠ s := by
      intro p hp h_eq
      have h_mfcc_eq : modularFormCompOfComplex f (↑p : ℂ) = f p := by
        simp only [modularFormCompOfComplex, Function.comp_apply]
        congr 1; exact UpperHalfPlane.ofComplex_apply_of_im_pos p.im_pos
      exact hs_ni (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, by
        rw [← h_mfcc_eq, h_eq]
        exact ((mem_allZerosInFdBox_iff f hf hM_half).mp hs).2⟩, h_eq⟩)
    rw [winding_zero_for_non_fd_point_H_geo f hf S hS_complete hH_ge1 s
      hs h_not_S, zero_mul]
  calc ∑ s ∈ Sbox, generalizedWindingNumber' γ 0 5 s *
        residueSimplePole F s
      = ∑ s ∈ S_zeros.image (↑· : ℍ → ℂ),
          generalizedWindingNumber' γ 0 5 s *
            residueSimplePole F s :=
        (Finset.sum_subset h_image_sub h_complement_zero).symm
    _ = ∑ p ∈ S_zeros,
          generalizedWindingNumber' γ 0 5 (↑p : ℂ) *
            residueSimplePole F (↑p : ℂ) :=
        Finset.sum_image (fun _ _ _ _ h => UpperHalfPlane.ext h)
    _ = ∑ p ∈ S_zeros,
          generalizedWindingNumber' γ 0 5 (↑p : ℂ) *
            (orderOfVanishingAt' (⇑f) p : ℂ) := by
        apply Finset.sum_congr rfl; intro p hp
        congr 1; exact residueSimplePole_logDeriv_eq_order f hf p
          (Finset.mem_filter.mp hp).2
    _ = ∑ p ∈ S,
          generalizedWindingNumber' γ 0 5 (↑p : ℂ) *
            (orderOfVanishingAt' (⇑f) p : ℂ) :=
        (sum_gWN_ord_eq_filter_zeros f S _).symm

include hf in
/-- Residue side: ε-truncated integral of `f'/f` tends to `2πi · Σ gWN · ord`. -/
theorem cpv_residue_side_tendsto
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete :
      ∀ p, p ∈ 𝒟 →
        orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        Tendsto (fun ε =>
          ∫ t in (0 : ℝ)..5,
            pvIntegrand f (fdBoundaryH H)
              (sArcOfS S ∪ sVertOfS S) ε t)
          (𝓝[>] 0)
          (𝓝 (2 * ↑Real.pi * I *
            ∑ s ∈ S,
              generalizedWindingNumber'
                (fdBoundaryH H) 0 5 (↑s : ℂ) *
                (orderOfVanishingAt' (⇑f) s : ℂ))) := by
  obtain ⟨H₀, hH₀_sqrt3, hH₀_ge1, hH₀_bound⟩ := exists_height_above_sqrt3_and_S S
  refine ⟨H₀, hH₀_sqrt3, fun {H} hH_ge => ?_⟩
  have hH_sqrt3 : Real.sqrt 3 / 2 < H := lt_of_lt_of_le hH₀_sqrt3 hH_ge
  have hH_ge1 : 1 ≤ H := le_trans hH₀_ge1 hH_ge
  have hH_bound : ∀ s ∈ S, (s : ℂ).im < H :=
    fun s hs => lt_of_lt_of_le (hH₀_bound s hs) hH_ge
  set F := logDeriv (modularFormCompOfComplex f) with hF_def
  set γ := fdBoundaryH H with hγ_def
  set S_on := sArcOfS S ∪ sVertOfS S with hS_on_def
  set M := H + 1 with hM_def
  have hM_half : (1 : ℝ)/2 < M := by linarith
  have hHM : H < M := by linarith
  set Sbox := allZerosInFdBox f hf hM_half with hSbox_def
  set S0 := Sbox ∪ S_on with hS0_def
  have hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt F s :=
    cpv_residue_side_simplePoles f hf S hH_sqrt3
      hM_half Sbox hSbox_def S_on hS_on_def
  set Fp := logDerivPatched F S0 hSimplePoles with hFp_def
  have h_capture : ∀ t ∈ Icc (0 : ℝ) 5,
      modularFormCompOfComplex f (γ t) = 0 → γ t ∈ (↑S0 : Set ℂ) := by
    intro t ht h_zero
    rw [Finset.mem_coe, hS0_def, Finset.mem_union]
    left; rw [hSbox_def, mem_allZerosInFdBox_iff]
    exact ⟨fdBoundary_H_mem_fdBox' hH_ge1 hHM t ht, h_zero⟩
  set γ_imm := fdBoundaryHImmersion H hH_sqrt3 with hγ_imm_def
  have hFp_diff : DifferentiableOn ℂ Fp (fdBox M \ ↑S0) :=
    cpv_residue_side_Fp_diffOn f hf S hM_half Sbox hSbox_def S_on S0
      hS0_def hSimplePoles
  have hS0_in_U : ∀ s ∈ (↑S0 : Set ℂ), s ∈ fdBox M := by
    intro s hs; rw [Finset.mem_coe, hS0_def, Finset.mem_union] at hs
    rcases hs with h | h
    · exact ((mem_allZerosInFdBox_iff f hf hM_half).mp (hSbox_def ▸ h)).1
    · exact fdBox_of_on_curve S hS hH_sqrt3 hHM hH_ge1 hH_bound s
        (hS_on_def ▸ h)
  have h_grt := generalizedResidueTheorem' (fdBox M) (fdBox_isOpen M)
    (fdBox_convex M) (↑S0) hS0_in_U (finset_discrete S0)
    S0.finite_toSet.isClosed S0 (fun s hs => Finset.mem_coe.mpr hs)
    Fp hFp_diff γ_imm (fdBoundary_HCurve_closed H)
    (fun t ht => fdBoundary_H_mem_fdBox' hH_ge1 hHM t ht)
    (fun _ _ h => Finset.mem_coe.mp h)
    (fun s hs => hasSimplePoleAt_logDerivPatched F S0 hSimplePoles s hs)
    (logDerivPatched_hf_ext F S0 hSimplePoles)
    (cpv_residue_side_cpvExists f S hH_sqrt3 S0 hSimplePoles)
  obtain ⟨⟨L, hL_tendsto⟩, h_val⟩ := h_grt
  rw [show γ_imm.toFun = γ from rfl,
      show γ_imm.a = (0 : ℝ) from rfl,
      show γ_imm.b = (5 : ℝ) from rfl] at hL_tendsto h_val
  have hL_tendsto_F : Tendsto (fun ε =>
      ∫ t in (0 : ℝ)..5, cauchyPrincipalValueIntegrandOn S0 F γ ε t)
      (𝓝[>] 0) (𝓝 L) := by
    apply hL_tendsto.congr'; filter_upwards [self_mem_nhdsWithin]
    intro ε hε; apply intervalIntegral.integral_congr; intro t _
    simp only [cauchyPrincipalValueIntegrandOn]
    split_ifs with h
    · rfl
    · push Not at h
      have h_not : γ t ∉ S0 := by
        intro habs
        have := h (γ t) habs
        simp [sub_self] at this
        linarith [mem_Ioi.mp hε]
      change Fp (γ t) * _ = F (γ t) * _
      congr 1; exact logDerivPatched_eq_raw_off F S0 hSimplePoles h_not
  have hL_tendsto_S_on : Tendsto (fun ε =>
      ∫ t in (0 : ℝ)..5, cauchyPrincipalValueIntegrandOn S_on F γ ε t)
      (𝓝[>] 0) (𝓝 L) :=
    hL_tendsto_F.congr' ((cpv_residue_side_eventually_eq f hf S hS
      hS_complete hH_sqrt3 hH_ge1 hH_bound hM_half hHM
      Sbox hSbox_def S_on hS_on_def S0 hS0_def).mono fun ε hε =>
      intervalIntegral.integral_congr (fun t ht => hε t ht))
  have h_sum_convert : L = 2 * ↑Real.pi * I *
      ∑ s ∈ S, generalizedWindingNumber' γ 0 5 (↑s : ℂ) *
        (orderOfVanishingAt' (⇑f) s : ℂ) := by
    rw [show L = cauchyPrincipalValueOn S0 Fp γ 0 5 from
      (Filter.Tendsto.limUnder_eq hL_tendsto).symm, h_val]; congr 1
    have h_res_congr : ∀ s ∈ S0,
        generalizedWindingNumber' γ 0 5 s * residueSimplePole Fp s =
        generalizedWindingNumber' γ 0 5 s * residueSimplePole F s := by
      intro s hs; congr 1; exact residue_logDerivPatched_eq_raw F S0 hSimplePoles s hs
    rw [Finset.sum_congr rfl h_res_congr,
      show S0 = Sbox ∪ (S_on \ Sbox) from by
      rw [hS0_def]; exact Finset.union_sdiff_self_eq_union.symm]
    rw [Finset.sum_union Finset.disjoint_sdiff]
    have h_sarc_zero : ∑ s ∈ S_on \ Sbox,
        generalizedWindingNumber' γ 0 5 s *
          residueSimplePole F s = 0 :=
      residue_sum_over_S_on_sdiff_Sbox_zero f hf S hS hH_sqrt3 hH_ge1 hH_bound
        hM_half hHM Sbox hSbox_def S_on hS_on_def
    rw [h_sarc_zero, add_zero]
    exact cpv_residue_side_sum_convert f hf S hS hS_complete
      hH_sqrt3 hH_ge1 hH_bound S_on hS_on_def
  rw [h_sum_convert] at hL_tendsto_S_on
  exact hL_tendsto_S_on.congr (fun ε => by apply intervalIntegral.integral_congr; intro t _; rfl)

end
