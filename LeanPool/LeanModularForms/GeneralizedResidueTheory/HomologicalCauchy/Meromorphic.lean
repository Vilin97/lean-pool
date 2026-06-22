/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.HomologicalCauchy.DixonProof
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.FlatnessTransfer.CPVExistence
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.GeneralizedTheoremBase

/-!
# Meromorphic Contour Integral Vanishing (Null-Homologous)

Extensions of the null-homologous Cauchy theorem to meromorphic functions.
The key results show that contour integrals of meromorphic functions with
zero residues vanish along null-homologous curves.

## Main results

* `contourIntegral_eq_zero_of_meromorphic_residue_zero_nh` --
  single-pole meromorphic vanishing
* `contourIntegral_eq_zero_of_meromorphic_residue_zero_finset_nh` --
  multi-pole meromorphic vanishing (by induction on |S|)
* `conditionsAB_imply_higherOrderCancel_nh` --
  null-homologous higher-order cancellation
* `pv_res_tendsto_of_immersion_nullHomologous` --
  PV residue sum convergence for null-homologous curves
-/

open Complex Set Filter Topology MeasureTheory intervalIntegral

private lemma regularPart_update_differentiableOn (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) (U : Set ℂ) (hU : IsOpen U)
    (hf_diff : DifferentiableOn ℂ f (U \ {s})) (hs_in_U : s ∈ U)
    (g_an : ℂ → ℂ) (hg_an_at : AnalyticAt ℂ g_an s)
    (hg_eq : ∀ᶠ z in 𝓝[≠] s,
      f z - GeneralizedResidueTheory.meromorphicPrincipalPart f s z = g_an z) :
    DifferentiableOn ℂ
      (Function.update (fun z => f z - GeneralizedResidueTheory.meromorphicPrincipalPart f s z)
        s (g_an s)) U := by
  set pp := GeneralizedResidueTheory.meromorphicPrincipalPart f s
  set rp := fun z => f z - pp z
  set rp_nf := Function.update rp s (g_an s)
  intro z hz
  by_cases h : z = s
  · subst h
    have h_an : AnalyticAt ℂ rp_nf z := by
      apply hg_an_at.congr
      rw [Filter.eventuallyEq_iff_exists_mem]
      rw [Filter.Eventually, mem_nhdsWithin] at hg_eq
      obtain ⟨V, hV_open, hz_V, hV_eq⟩ := hg_eq
      exact ⟨V, hV_open.mem_nhds hz_V, fun w hw => by
        by_cases hwz : w = z
        · simp only [hwz, Function.update_self, rp_nf]
        · simp only [rp_nf]
          rw [Function.update_of_ne hwz]
          exact (hV_eq ⟨hw, hwz⟩).symm⟩
    exact h_an.differentiableAt.differentiableWithinAt
  · have h_rp_diff : DifferentiableAt ℂ rp z :=
      ((hf_diff z ⟨hz, Set.mem_compl_singleton_iff.mpr h⟩).differentiableAt
        ((hU.sdiff isClosed_singleton).mem_nhds ⟨hz, Set.mem_compl_singleton_iff.mpr h⟩)).sub
      ((GeneralizedResidueTheory.meromorphicPrincipalPart_differentiableOn f s hf z
        (Set.mem_compl_singleton_iff.mpr h)).differentiableAt
        (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr h)))
    have h_ev : rp =ᶠ[𝓝 z] rp_nf := by
      apply Filter.Eventually.mono (isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr h))
      intro w hw
      exact (Function.update_of_ne (Set.mem_compl_singleton_iff.mp hw) (g_an s) rp).symm
    exact (h_ev.differentiableAt_iff.mp h_rp_diff).differentiableWithinAt

private lemma contourIntegral_eq_of_agree_on_curve (f g : ℂ → ℂ)
    (γ : PiecewiseC1Immersion)
    (h_agree : ∀ t ∈ Icc γ.a γ.b, f (γ.toFun t) = g (γ.toFun t)) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t =
    ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (le_of_lt γ.hab)] at ht
  dsimp only
  rw [h_agree t ht]

private lemma contourIntegral_add_principalPart_regularPart (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) (U : Set ℂ) (hf_diff : DifferentiableOn ℂ f (U \ {s}))
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hγ_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t =
    (∫ t in γ.a..γ.b,
      GeneralizedResidueTheory.meromorphicPrincipalPart f s (γ.toFun t) *
        deriv γ.toFun t) +
    ∫ t in γ.a..γ.b,
      (f (γ.toFun t) - GeneralizedResidueTheory.meromorphicPrincipalPart f s (γ.toFun t)) *
        deriv γ.toFun t := by
  set pp := GeneralizedResidueTheory.meromorphicPrincipalPart f s
  have hab := le_of_lt γ.hab
  have hγ_bdd := piecewiseC1Immersion_deriv_bounded γ
  have h_decomp : ∀ t ∈ Set.uIcc γ.a γ.b,
      f (γ.toFun t) * deriv γ.toFun t =
      pp (γ.toFun t) * deriv γ.toFun t +
        (f (γ.toFun t) - pp (γ.toFun t)) * deriv γ.toFun t := by
    intro t _; ring
  rw [intervalIntegral.integral_congr h_decomp]
  have h_pp_int : IntervalIntegrable
      (fun t => pp (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b :=
    (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve hγ_bdd).continuousOn_mul
      (Set.uIcc_of_le hab ▸
        (GeneralizedResidueTheory.meromorphicPrincipalPart_differentiableOn
          f s hf).continuousOn.comp γ.toPiecewiseC1Curve.continuous_toFun
          (fun t ht => Set.mem_compl_singleton_iff.mpr (hγ_avoids t ht)))
  have h_rp_int : IntervalIntegrable
      (fun t => (f (γ.toFun t) - pp (γ.toFun t)) * deriv γ.toFun t) volume γ.a γ.b :=
    (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve hγ_bdd).continuousOn_mul
      (Set.uIcc_of_le hab ▸
        (hf_diff.sub
          ((GeneralizedResidueTheory.meromorphicPrincipalPart_differentiableOn
            f s hf).mono
            (fun z hz => (Set.mem_sdiff_singleton.mp hz).2))).continuousOn.comp
          γ.toPiecewiseC1Curve.continuous_toFun
          (fun t ht =>
            ⟨h_null.image_subset t ht,
             Set.mem_compl_singleton_iff.mpr (hγ_avoids t ht)⟩))
  convert intervalIntegral.integral_add h_pp_int h_rp_int using 1

/-- Null-homologous version: contour integral of meromorphic function with zero residue
vanishes when the curve is null-homologous and avoids the singularity. -/
theorem contourIntegral_eq_zero_of_meromorphic_residue_zero_nh (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) (hres : residueAt f s = 0) (U : Set ℂ) (hU : IsOpen U)
    (hf_diff : DifferentiableOn ℂ f (U \ {s})) (hs_in_U : s ∈ U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hγ_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t = 0 := by
  obtain ⟨g_an, hg_an_at, hg_eq⟩ :=
    GeneralizedResidueTheory.meromorphicAt_sub_principalPart_eventually f s hf
  set rp : ℂ → ℂ := fun z => f z - GeneralizedResidueTheory.meromorphicPrincipalPart f s z
  have h_pp_zero := GeneralizedResidueTheory.contourIntegral_principalPart_eq_zero_of_residue_zero
    f s hf hres γ h_null.closed hγ_avoids
  have h_rp_nf_zero := contourIntegral_eq_zero_of_nullHomologous hU
    (regularPart_update_differentiableOn f s hf U hU hf_diff hs_in_U g_an hg_an_at hg_eq) γ h_null
  have h_rp_zero := (contourIntegral_eq_of_agree_on_curve rp (Function.update rp s (g_an s)) γ
    (fun t ht => (Function.update_of_ne (hγ_avoids t ht) (g_an s) rp).symm)).trans h_rp_nf_zero
  rw [contourIntegral_add_principalPart_regularPart f s hf U hf_diff γ h_null hγ_avoids,
    h_pp_zero, h_rp_zero, add_zero]

private theorem contourIntegral_sum_principalParts_eq_zero (S : Finset ℂ) (f : ℂ → ℂ)
    (hf_mero : ∀ s ∈ S, MeromorphicAt f s) (hres : ∀ s ∈ S, residueAt f s = 0)
    (γ : PiecewiseC1Immersion) (h_closed : γ.toFun γ.a = γ.toFun γ.b)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, (∑ s ∈ S,
      GeneralizedResidueTheory.meromorphicPrincipalPart f s (γ.toFun t)) *
      deriv γ.toFun t = 0 := by
  have hab := le_of_lt γ.hab
  have hγ_bdd := piecewiseC1Immersion_deriv_bounded γ
  simp only [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun s hs =>
    (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve hγ_bdd).continuousOn_mul
      (Set.uIcc_of_le hab ▸
        (GeneralizedResidueTheory.meromorphicPrincipalPart_differentiableOn
          f s (hf_mero s hs)).continuousOn.comp γ.toPiecewiseC1Curve.continuous_toFun
          (fun t ht => Set.mem_compl_singleton_iff.mpr (hγ_avoids s hs t ht))))]
  exact Finset.sum_eq_zero fun s hs =>
    GeneralizedResidueTheory.contourIntegral_principalPart_eq_zero_of_residue_zero
      f s (hf_mero s hs) (hres s hs) γ h_closed (fun t ht => hγ_avoids s hs t ht)

private theorem diff_sub_principalParts_differentiableOn (S : Finset ℂ) (f : ℂ → ℂ)
    (U : Set ℂ) (hf_mero : ∀ s ∈ S, MeromorphicAt f s)
    (hf_diff : DifferentiableOn ℂ f (U \ ↑S)) :
    DifferentiableOn ℂ (fun z => f z -
      ∑ s ∈ S, GeneralizedResidueTheory.meromorphicPrincipalPart f s z) (U \ ↑S) := by
  intro z hz
  exact (hf_diff z hz).sub (DifferentiableWithinAt.fun_sum fun s hs =>
    ((GeneralizedResidueTheory.meromorphicPrincipalPart_differentiableOn f s
      (hf_mero s hs)).mono (fun w hw =>
        Set.mem_compl_singleton_iff.mpr (fun h =>
          hw.2 (h ▸ Finset.mem_coe.mpr hs)))) z hz)

private theorem analytic_correction_at_pole (S : Finset ℂ) (f : ℂ → ℂ)
    (hf_mero : ∀ s ∈ S, MeromorphicAt f s) (g : ℂ → ℂ) (hg_def : g = fun z => f z -
      ∑ s ∈ S, GeneralizedResidueTheory.meromorphicPrincipalPart f s z)
    (z : ℂ) (hzS : z ∈ (S : Set ℂ)) :
    ∃ g_ext : ℂ → ℂ, DifferentiableAt ℂ g_ext z ∧
      (g =ᶠ[𝓝[≠] z] g_ext) ∧
      Tendsto g (𝓝[≠] z) (𝓝 (g_ext z)) := by
  have hzS' := Finset.mem_coe.mp hzS
  obtain ⟨g_an, hg_an_at, hg_an_eq⟩ :=
    GeneralizedResidueTheory.meromorphicAt_sub_principalPart_eventually
      f z (hf_mero z hzS')
  have h_each_diff : ∀ s' ∈ S.erase z,
      DifferentiableAt ℂ (fun w =>
        GeneralizedResidueTheory.meromorphicPrincipalPart f s' w) z := by
    intro s' hs'
    have hne : z ≠ s' := (Finset.ne_of_mem_erase hs').symm
    exact (GeneralizedResidueTheory.meromorphicPrincipalPart_differentiableOn f s'
      (hf_mero s' (Finset.mem_of_mem_erase hs')) z
      (Set.mem_compl_singleton_iff.mpr hne)).differentiableAt
      (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hne))
  set g_ext : ℂ → ℂ := fun w => g_an w - ∑ s' ∈ S.erase z,
      GeneralizedResidueTheory.meromorphicPrincipalPart f s' w with g_ext_def
  have hg_ext_diff : DifferentiableAt ℂ g_ext z := by
    apply DifferentiableAt.sub hg_an_at.differentiableAt
    convert DifferentiableAt.sum h_each_diff using 1
    ext w; exact (Finset.sum_apply w _ _).symm
  have hg_eq_ext : g =ᶠ[𝓝[≠] z] g_ext := by
    rw [hg_def]
    apply hg_an_eq.mono; intro w hw
    simp only [g_ext_def]
    rw [show ∑ s ∈ S,
          GeneralizedResidueTheory.meromorphicPrincipalPart f s w =
        GeneralizedResidueTheory.meromorphicPrincipalPart f z w +
          ∑ s' ∈ S.erase z,
            GeneralizedResidueTheory.meromorphicPrincipalPart f s' w from
        (Finset.add_sum_erase S (fun s =>
          GeneralizedResidueTheory.meromorphicPrincipalPart f s w) hzS').symm,
      ← sub_sub, hw]
  exact ⟨g_ext, hg_ext_diff, hg_eq_ext,
    (hg_ext_diff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      hg_eq_ext.symm⟩

private theorem analytic_correction_differentiableOn (S : Finset ℂ) (f : ℂ → ℂ)
    (U : Set ℂ) (hU : IsOpen U) (hf_mero : ∀ s ∈ S, MeromorphicAt f s) (g : ℂ → ℂ)
    (hg_def : g = fun z => f z -
      ∑ s ∈ S, GeneralizedResidueTheory.meromorphicPrincipalPart f s z)
    (h_g_diff_off : DifferentiableOn ℂ g (U \ ↑S)) :
    ∃ g_corr : ℂ → ℂ,
      DifferentiableOn ℂ g_corr U ∧ ∀ z ∈ U \ (S : Set ℂ), g_corr z = g z := by
  refine ⟨fun z => if z ∈ (S : Set ℂ) then limUnder (𝓝[≠] z) g else g z, ?_, ?_⟩
  · intro z hz
    by_cases hzS : z ∈ (S : Set ℂ)
    · obtain ⟨g_ext, hg_ext_diff, hg_eq_ext, h_tendsto⟩ :=
        analytic_correction_at_pole S f hf_mero g hg_def z hzS
      have h_no_S_near : ∀ᶠ w in 𝓝[≠] z, w ∉ (S : Set ℂ) := by
        rw [eventually_nhdsWithin_iff]
        exact Filter.Eventually.mono ((S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds
          (mt Finset.mem_coe.mp (Finset.notMem_erase z S)))
          fun w hw hwne hwS =>
            hw (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hwne, Finset.mem_coe.mp hwS⟩))
      have h_punc : ∀ᶠ w in 𝓝[≠] z,
          (if w ∈ (S : Set ℂ) then limUnder (𝓝[≠] w) g else g w) = g_ext w :=
        (h_no_S_near.and hg_eq_ext).mono fun w ⟨hw1, hw2⟩ => by simp only [hw1, ↓reduceIte, hw2]
      have h_at_z :
          (if z ∈ (S : Set ℂ) then limUnder (𝓝[≠] z) g else g z) = g_ext z := by
        simp only [hzS, ↓reduceIte, h_tendsto.limUnder_eq]
      rw [eventually_nhdsWithin_iff] at h_punc
      have h_ev : (fun w => if w ∈ (S : Set ℂ) then
          limUnder (𝓝[≠] w) g else g w) =ᶠ[𝓝 z] g_ext :=
        h_punc.mono fun w hw => by
          by_cases hwz : w = z
          · subst hwz; exact h_at_z
          · exact hw hwz
      exact (h_ev.differentiableAt_iff.mpr hg_ext_diff).differentiableWithinAt
    · have h_ev : (fun w => if w ∈ (S : Set ℂ) then
          limUnder (𝓝[≠] w) g else g w) =ᶠ[𝓝 z] g := by
        apply Filter.Eventually.mono (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hzS)
        intro w hw
        have : w ∉ (S : Set ℂ) := hw
        simp only [this, if_false]
      exact (h_ev.differentiableAt_iff.mpr
        ((h_g_diff_off z ⟨hz, hzS⟩).differentiableAt
          ((hU.sdiff S.finite_toSet.isClosed).mem_nhds ⟨hz, hzS⟩))).differentiableWithinAt
  · intro z ⟨_, hzS⟩; simp only [if_neg hzS]

private theorem image_subset_diff_of_avoids (S : Finset ℂ) (U : Set ℂ)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    γ.toFun '' Icc γ.a γ.b ⊆ U \ ↑S :=
  fun _ ⟨t, ht, htz⟩ => ⟨htz ▸ h_null.image_subset t ht,
    fun hs => hγ_avoids _ (Finset.mem_coe.mp hs) t ht (htz ▸ rfl)⟩

private theorem remainder_integrable (S : Finset ℂ) (f : ℂ → ℂ) (U : Set ℂ)
    (hf_mero : ∀ s ∈ S, MeromorphicAt f s) (hf_diff : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    IntervalIntegrable (fun t => (f (γ.toFun t) -
      ∑ s ∈ S, GeneralizedResidueTheory.meromorphicPrincipalPart f s (γ.toFun t)) *
      deriv γ.toFun t) volume γ.a γ.b := by
  have hab := le_of_lt γ.hab
  have hγ_bdd := piecewiseC1Immersion_deriv_bounded γ
  have h_g_diff_off := diff_sub_principalParts_differentiableOn S f U hf_mero hf_diff
  have h_image_off := image_subset_diff_of_avoids S U γ h_null hγ_avoids
  exact (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve hγ_bdd).continuousOn_mul
    (Set.uIcc_of_le hab ▸ h_g_diff_off.continuousOn.comp
      γ.toPiecewiseC1Curve.continuous_toFun (fun t ht => h_image_off ⟨t, ht, rfl⟩))

private theorem principalParts_integrable (S : Finset ℂ) (f : ℂ → ℂ)
    (hf_mero : ∀ s ∈ S, MeromorphicAt f s) (γ : PiecewiseC1Immersion)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    IntervalIntegrable (fun t => (∑ s ∈ S,
      GeneralizedResidueTheory.meromorphicPrincipalPart f s (γ.toFun t)) *
      deriv γ.toFun t) volume γ.a γ.b := by
  have hab := le_of_lt γ.hab
  have hγ_bdd := piecewiseC1Immersion_deriv_bounded γ
  exact (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve hγ_bdd).continuousOn_mul
    (Set.uIcc_of_le hab ▸ by
      apply continuousOn_finsetSum; intro s hs
      exact (GeneralizedResidueTheory.meromorphicPrincipalPart_differentiableOn f s
        (hf_mero s hs)).continuousOn.comp γ.toPiecewiseC1Curve.continuous_toFun
        (fun t ht => Set.mem_compl_singleton_iff.mpr (hγ_avoids s hs t ht)))

private theorem contourIntegral_correction_eq (S : Finset ℂ) (g g_corr : ℂ → ℂ)
    (U : Set ℂ) (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s)
    (h_agree : ∀ z ∈ U \ (S : Set ℂ), g_corr z = g z) :
    ∀ t ∈ Set.uIcc γ.a γ.b,
      g (γ.toFun t) * deriv γ.toFun t =
      g_corr (γ.toFun t) * deriv γ.toFun t := by
  intro t ht
  rw [Set.uIcc_of_le (le_of_lt γ.hab)] at ht
  rw [h_agree _ (image_subset_diff_of_avoids S U γ h_null hγ_avoids
    ⟨t, ht, rfl⟩)]

/-- Finset version: induction on |S| using the single-pole version. -/
theorem contourIntegral_eq_zero_of_meromorphic_residue_zero_finset_nh (S : Finset ℂ)
    (f : ℂ → ℂ) (hf_mero : ∀ s ∈ S, MeromorphicAt f s)
    (hres : ∀ s ∈ S, residueAt f s = 0) (U : Set ℂ) (hU : IsOpen U)
    (hf_diff : DifferentiableOn ℂ f (U \ ↑S)) (γ : PiecewiseC1Immersion)
    (h_null : IsNullHomologous γ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t = 0 := by
  set pp := fun z => ∑ s ∈ S, GeneralizedResidueTheory.meromorphicPrincipalPart f s z
  set g := fun z => f z - pp z
  obtain ⟨gc, hd, ha⟩ := analytic_correction_differentiableOn S f U hU hf_mero g rfl
    (diff_sub_principalParts_differentiableOn S f U hf_mero hf_diff)
  rw [intervalIntegral.integral_congr (show ∀ t ∈ Set.uIcc γ.a γ.b, f (γ.toFun t) *
      deriv γ.toFun t = g (γ.toFun t) * deriv γ.toFun t + pp (γ.toFun t) *
      deriv γ.toFun t from fun t _ => by simp only [g]; ring),
    intervalIntegral.integral_add (remainder_integrable S f U hf_mero hf_diff γ h_null hγ_avoids)
      (principalParts_integrable S f hf_mero γ hγ_avoids),
    show ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0 from by
      rw [intervalIntegral.integral_congr
        (contourIntegral_correction_eq S g gc U γ h_null hγ_avoids ha)]
      exact contourIntegral_eq_zero_of_nullHomologous hU hd γ h_null,
    contourIntegral_sum_principalParts_eq_zero S f hf_mero hres γ h_null.closed hγ_avoids,
    add_zero]

open GeneralizedResidueTheory in
private theorem higherOrderCancel_assembly_nh (U : Set ℂ) (hU : IsOpen U)
    (S0 : Finset ℂ) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0) (_hγ_meas : Measurable γ.toFun)
    (h_no_endpt : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (hS0_in_U : ∀ s ∈ S0, s ∈ U) :
    let h : ℂ → ℂ := fun z => f z - ∑ s ∈ S0, residueAt f s / (z - s)
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) :=
  GeneralizedResidueTheory.higherOrderCancel_assembly_abstract U hU S0 f hf γ
    h_null.closed h_null.image_subset hMero hCondA hCondB _hγ_meas h_no_endpt
    h_unique_cross hS0_in_U
    (fun _ hg => contourIntegral_eq_zero_of_nullHomologous hU hg γ h_null)
    (fun T g hg_mero hg_res hg_diff _hT_in_U hg_avoids =>
      contourIntegral_eq_zero_of_meromorphic_residue_zero_finset_nh T g
        hg_mero hg_res U hU hg_diff γ h_null hg_avoids)

/-! ## L5: Assembly — conditions (A')+(B) imply higher-order cancellation

The main result: combine per-term vanishing over all Laurent terms and all
crossing points to show the global PV difference tends to 0.

Note: This uses `SatisfiesConditionA'` (variable-order flatness matching the
pole order) rather than `SatisfiesConditionA` (order 1 only). The paper's
Theorem 3.3 requires flatness of the pole order, which is stronger than
flatness of order 1 for higher-order poles. -/

open GeneralizedResidueTheory in
/-- Null-homologous version of conditionsAB_imply_higherOrderCancel. -/
theorem conditionsAB_imply_higherOrderCancel_nh (U : Set ℂ) (hU : IsOpen U)
    (S0 : Finset ℂ) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0) (hγ_meas : Measurable γ.toFun)
    (h_no_endpt : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (hS0_in_U : ∀ s ∈ S0, s ∈ U) :
    Tendsto
      (fun ε =>
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) -
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0
          (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t))
      (𝓝[>] 0) (𝓝 0) := by
  set h : ℂ → ℂ := fun z => f z - ∑ s ∈ S0, residueAt f s / (z - s) with hh_def
  have h_integrand_eq : ∀ ε t,
      cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t -
      cauchyPrincipalValueIntegrandOn S0
        (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t =
      cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t := by
    intro ε t
    exact cpvIntegrandOn_sub S0 f (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t
  suffices h_main : Tendsto
      (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) by
    apply h_main.congr'
    filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
    symm
    have h_int_f : IntervalIntegrable
        (cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε) volume γ.a γ.b :=
      intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff
        U S0 f hf.continuousOn γ h_null.image_subset ε hε
    have h_int_fres : IntervalIntegrable
        (cauchyPrincipalValueIntegrandOn S0
          (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε)
        volume γ.a γ.b := by
      have hfres_cont : ContinuousOn (fun z => ∑ s ∈ S0, residueAt f s / (z - s))
          (U \ ↑S0) := by
        apply continuousOn_finsetSum; intro s _
        apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
        intro z ⟨_, hz_not_S0⟩
        exact sub_ne_zero.mpr
          (fun heq => by subst heq; exact hz_not_S0 (Finset.mem_coe.mpr ‹_›))
      exact intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff
        U S0 _ hfres_cont γ h_null.image_subset ε hε
    rw [← intervalIntegral.integral_sub h_int_f h_int_fres]
    congr 1; ext t
    exact h_integrand_eq ε t
  exact higherOrderCancel_assembly_nh U hU S0 f hf γ h_null
    hMero hCondA hCondB hγ_meas h_no_endpt h_unique_cross hS0_in_U

open GeneralizedResidueTheory in
lemma pv_res_tendsto_of_immersion_nullHomologous (U : Set ℂ) (S : Set ℂ)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S) (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (_hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0
          (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t)
      (𝓝[>] 0) (𝓝 (2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s)) := by
  set f_res := fun z => ∑ s ∈ S0, residueAt f s / (z - s) with hf_res_def
  have hf_res_diff := differentiableOn_sum_div_sub S0 (residueAt f) U
  have hf_ext_res : ∀ s ∈ S0, ContinuousAt
      (fun z => f_res z - residueSimplePole f_res s / (z - s)) s := fun s hs =>
    continuousAt_sum_remainder S0 (residueAt f) s hs
  have h_res_eq : ∀ s ∈ S0, residueSimplePole f_res s = residueAt f s := fun s hs =>
    residueSimplePole_sum_div_sub S0 (residueAt f) s hs
  have hPV_singular : ∀ s ∈ S0, CauchyPrincipalValueExists'
      (fun z => residueSimplePole f_res s / (z - s)) γ.toFun γ.a γ.b s := by
    intro s hs
    have h_eq : (fun z => residueSimplePole f_res s / (z - s)) =
        (fun z => residueSimplePole f_res s * (fun z => (z - s)⁻¹) z) := by
      ext z; simp only [div_eq_mul_inv]
    rw [h_eq]
    apply CauchyPrincipalValueExists'.const_mul
    apply cauchyPrincipalValueExists_of_singular_inv γ s
    intro ⟨t₀, ht₀, hcross⟩
    have ht₀_Ioo : t₀ ∈ Ioo γ.a γ.b := by
      refine ⟨lt_of_le_of_ne ht₀.1 (fun h => ?_), lt_of_le_of_ne ht₀.2 (fun h => ?_)⟩
      · exact (h_no_endpt_cross s hs).1 (h ▸ hcross)
      · exact (h_no_endpt_cross s hs).2 (h ▸ hcross)
    obtain ⟨a', b', ha't₀, ht₀b', ha'b'_sub, honly', _⟩ :=
      exists_isolated_crossing_interval γ s t₀ ht₀_Ioo hcross
    suffices ∃ M, Tendsto (fun ε => ∫ (t : ℝ) in γ.a..γ.b,
        if ε < ‖γ.toFun t - s‖ then (γ.toFun t - s)⁻¹ * deriv γ.toFun t else 0)
        (𝓝[>] 0) (𝓝 M) from this.choose_spec.cauchy_map
    exact cpv_exists_inv_sub_of_closed_unique γ s h_null.closed
      (h_no_endpt_cross s hs) t₀ ht₀_Ioo hcross
      (fun t ht hgt => h_unique_cross s hs t ht t₀ ht₀ hgt hcross)
  have hSimple_res : ∀ s ∈ S0, HasSimplePoleAt f_res s :=
    fun s hs => hasSimplePoleAt_sum_div_sub S0 (residueAt f) s hs
  have hf_res_diff_univ : DifferentiableOn ℂ f_res (Set.univ \ ↑S0) :=
    differentiableOn_sum_div_sub S0 (residueAt f) Set.univ
  have h_thm := generalizedResidueTheorem' Set.univ isOpen_univ convex_univ
    S (fun s _ => Set.mem_univ s) hS_discrete hS_closed S0 hS0_subset
    f_res hf_res_diff_univ γ h_null.closed (fun t _ => Set.mem_univ _)
    (fun t ht h_mem => hS_on_curve t ht h_mem)
    hSimple_res hf_ext_res hPV_singular
  obtain ⟨h_exists, h_value⟩ := h_thm
  obtain ⟨L, hL⟩ := h_exists
  have h_limit_eq : L = 2 * Real.pi * I * ∑ s ∈ S0,
      generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s := by
    have hL_eq : L = cauchyPrincipalValueOn S0 f_res γ.toFun γ.a γ.b :=
      hL.limUnder_eq.symm
    rw [hL_eq, h_value]; congr 1; apply Finset.sum_congr rfl
    intro s hs; rw [h_res_eq s hs]
  rw [← h_limit_eq]
  exact hL

