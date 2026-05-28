/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/

import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import LeanPool.SardMoreira.LebesgueDensity
import LeanPool.SardMoreira.ContDiff
import LeanPool.SardMoreira.ToMathlib.PR32186

open scoped Topology NNReal ENNReal unitInterval
open Asymptotics Filter MeasureTheory AffineMap Set Metric

theorem UniformSpace.Completion.hasFDerivAt_coe {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {a : E} :
    HasFDerivAt ((↑) : E → Completion E) (toComplL : E →L[𝕜] Completion E) a := by
  simpa using (toComplL (𝕜 := 𝕜) (E := E)).hasFDerivAt

section NormedField

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem openSegment_subset_ball_left {x y : E} (h : x ≠ y) :
    openSegment ℝ x y ⊆ ball x ‖y - x‖ := by
  rw [openSegment_eq_image_lineMap, ← mapsTo_iff_image_subset]
  intro t ht
  rw [mem_ball, dist_lineMap_left, dist_eq_norm_sub', Real.norm_of_nonneg ht.1.le]
  exact mul_lt_of_lt_one_left (by simpa [sub_eq_zero, eq_comm] using h) ht.2

lemma dist_le_mul_volume_of_norm_lineDeriv_le {f : E → F} {a b : E} {C : ℝ}
    (hfc : ContinuousOn f (segment ℝ a b))
    (hfd : ∀ t ∈ Ioo (0 : ℝ) 1, LineDifferentiableAt ℝ f (lineMap a b t) (b - a))
    (hf' : ∀ᵐ t : ℝ, t ∈ Ioo (0 : ℝ) 1 → ‖lineDeriv ℝ f (lineMap a b t) (b - a)‖ ≤ C) :
    ‖f b - f a‖ ≤
      C * volume.real {t ∈ Ioo (0 : ℝ) 1 | lineDeriv ℝ f (lineMap a b t) (b - a) ≠ 0} := by
  set g : ℝ → F := fun t ↦ f (lineMap a b t)
  have hgc : ContinuousOn g (Icc 0 1) := by
    refine hfc.comp ?_ ?_
    · exact AffineMap.lineMap_continuous.continuousOn
    · simp [segment_eq_image_lineMap, mapsTo_image]
  have hdg (t : ℝ) (ht : t ∈ Ioo 0 1) : HasDerivAt g (lineDeriv ℝ f (lineMap a b t) (b - a)) t := by
    have := (hfd t ht).hasLineDerivAt.scomp_of_eq (𝕜 := ℝ) t ((hasDerivAt_id t).sub_const t)
    simpa [g, lineMap_apply_module', Function.comp_def, sub_smul, add_comm _ a] using this
  suffices dist (g 0) (g 1) ≤ C * volume.real {t ∈ Ioo 0 1 | deriv g t ≠ 0} by
    convert this using 1
    · simp [g, dist_eq_norm_sub']
    · congr 2 with t
      simp +contextual [(hdg _ _).deriv]
  apply dist_le_mul_volume_of_norm_deriv_le_of_le zero_le_one hgc
  · exact fun t ht ↦ (hdg t ht).differentiableAt.differentiableWithinAt
  · exact hf'.mono fun t ht ht_mem ↦ by simpa only [(hdg t ht_mem).deriv] using ht ht_mem

lemma dist_le_mul_volume_of_norm_fderiv_le {f : E → F} {a b : E} {C : ℝ} {s : Set E}
    (hs : IsOpen s) (hf : DiffContOnCl ℝ f s) (hab : openSegment ℝ a b ⊆ s)
    (hC : ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ C) :
    ‖f b - f a‖ ≤
      C * ‖b - a‖ * volume.real {t ∈ Ioo (0 : ℝ) 1 | fderiv ℝ f (lineMap a b t) ≠ 0} := by
  have hmem_s : ∀ t ∈ Ioo (0 : ℝ) 1, lineMap a b t ∈ s := fun t ht ↦
    hab <| lineMap_mem_openSegment _ a b ht
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans <| hC _ <| hmem_s (1 / 2) (by norm_num)
  have hfc : ContinuousOn f (segment ℝ a b) :=
    hf.continuousOn.mono <| segment_subset_closure_openSegment.trans <| closure_mono hab
  have hfd : ∀ t ∈ Ioo (0 : ℝ) 1, LineDifferentiableAt ℝ f (lineMap a b t) (b - a) := fun t ht ↦
    (hf.differentiableAt hs <| hmem_s t ht).lineDifferentiableAt
  have hfC : ∀ t ∈ Ioo (0 : ℝ) 1, ‖lineDeriv ℝ f (lineMap a b t) (b - a)‖ ≤ C * ‖b - a‖ := by
    intro t ht
    rw [DifferentiableAt.lineDeriv_eq_fderiv]
    · exact ContinuousLinearMap.le_of_opNorm_le _ (hC _ <| hmem_s t ht) _
    · exact hf.differentiableAt hs <| hmem_s t ht
  refine dist_le_mul_volume_of_norm_lineDeriv_le hfc hfd (.of_forall hfC) |>.trans ?_
  gcongr
  · refine ne_top_of_le_ne_top ?_ (measure_mono inter_subset_left)
    simp
  · simp +contextual [(hf.differentiableAt hs <| hmem_s _ ‹_›).lineDeriv_eq_fderiv]

theorem sub_isBigO_norm_rpow_add_one_of_fderiv {f : E → F} {a : E} {r : ℝ} (hr : 0 ≤ r)
    (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x) (hderiv : fderiv ℝ f =O[𝓝 a] (‖· - a‖ ^ r)) :
    (f · - f a) =O[𝓝 a] (‖· - a‖ ^ (r + 1)) := by
  rcases hderiv.exists_pos with ⟨C, hC₀, hC⟩
  rw [Asymptotics.IsBigOWith_def] at hC
  rcases eventually_nhds_iff_ball.mp (hdf.and hC) with ⟨ε, hε₀, hε⟩
  refine .of_bound C ?_
  rw [eventually_nhds_iff_ball]
  refine ⟨ε, hε₀, fun y hy ↦ ?_⟩
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_add_one' (by positivity) (by positivity),
    ← mul_assoc]
  have hsub : closedBall a ‖y - a‖ ⊆ ball a ε :=
    closedBall_subset_ball (mem_ball_iff_norm.mp hy)
  apply (convex_closedBall a ‖y - a‖).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
  · exact fun z hz ↦ (hε z <| hsub hz).1
  · intro z hz
    grw [(hε z <| hsub hz).2, Real.norm_of_nonneg (by positivity), mem_closedBall_iff_norm.mp hz]
  · simp
  · simp [dist_eq_norm_sub]

theorem isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero {f : E → F} {a : E} {r : ℝ} (hr : 0 ≤ r)
    (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x) (hderiv : fderiv ℝ f =O[𝓝 a] (‖· - a‖ ^ r))
    (hf₀ : f a = 0) : f =O[𝓝 a] (‖· - a‖ ^ (r + 1)) := by
  simpa [hf₀] using sub_isBigO_norm_rpow_add_one_of_fderiv hr hdf hderiv

open UniformSpace (Completion) in
theorem sub_isLittleO_norm_rpow_add_one_of_fderiv_of_density_point [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {f : E → F} {a : E} {r : ℝ}
    {μ : Measure E} [μ.IsAddHaarMeasure] {s : Set E}
    (hr : 0 ≤ r) (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x)
    (hderiv : fderiv ℝ f =O[𝓝 a] (‖· - a‖ ^ r))
    (hs : fderiv ℝ f =ᶠ[𝓝[s] a] 0)
    (hmeas : Tendsto (fun r ↦ μ (s ∩ closedBall a r) / μ (closedBall a r)) (𝓝[>] 0) (𝓝 1)) :
    (f · - f a) =o[𝓝 a] (‖· - a‖ ^ (r + 1)) := by
  wlog hF : CompleteSpace F generalizing F
  · set e : F →L[ℝ] Completion F := Completion.toComplL
    set g := e ∘ f
    have hdg_eq : fderiv ℝ g =ᶠ[𝓝 a] (e ∘L fderiv ℝ f ·) :=
      hdf.mono fun x hx ↦ (e.hasFDerivAt.comp _ hx.hasFDerivAt).fderiv
    have hdg : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ g x :=
      hdf.mono fun x hx ↦ e.differentiableAt.comp _ hx
    have hg_deriv : fderiv ℝ g =O[𝓝 a] fun x ↦ ‖x - a‖ ^ r := by
      calc
        fderiv ℝ g =ᶠ[𝓝 a] (e ∘L fderiv ℝ f ·) := hdg_eq
        _ =O[𝓝 a] (‖e‖ * ‖fderiv ℝ f ·‖) :=
          .of_norm_le fun _ ↦ ContinuousLinearMap.opNorm_comp_le _ _
        _ =O[𝓝 a] fderiv ℝ f := by
          refine .of_norm_right <| .const_mul_left (isBigO_refl _ _) _
        _ =O[𝓝 a] (‖· - a‖ ^ r) := by
          exact hderiv
    have hg₀ : fderiv ℝ g =ᶠ[𝓝[s] a] 0 := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hdg_eq, hs] with x hx₁ hx₂
      simp [hx₁, hx₂]
    refine IsBigO.trans_isLittleO (.of_norm_right ?_) (this hdg hg_deriv hg₀ inferInstance)
    simp_rw [g, Function.comp_apply, ← map_sub, e, Completion.coe_toComplL, Completion.norm_coe]
    exact (isBigO_refl _ _).norm_right
  wlog hsm : MeasurableSet s generalizing s
  · -- TODO: I'm getting a timeout without this line. Test with the latest Mathlib
    have aux : MeasurableSingletonClass (E →L[ℝ] F) :=
      OpensMeasurableSpace.toMeasurableSingletonClass
    apply @this (toMeasurable μ s ∩ {x | fderiv ℝ f x = 0})
    · refine hmeas.congr' ?_
      rw [EventuallyEq, eventually_nhdsWithin_iff] at hs
      rcases Metric.eventually_nhds_iff_ball.mp hs with ⟨r, hr₀, hr⟩
      filter_upwards [Ioo_mem_nhdsGT hr₀] with δ ⟨hδ₀, hδr⟩
      rw [inter_assoc, Measure.measure_toMeasurable_inter_of_sFinite, ← inter_assoc,
        inter_right_comm, inter_eq_self_of_subset_left (_ : s ∩ _ ⊆ _)]
      · refine fun y hy ↦ hr _ (closedBall_subset_ball hδr hy.2) hy.1
      · exact (measurableSet_eq.preimage (measurable_fderiv _ _)).inter measurableSet_closedBall
    · exact eventually_mem_nhdsWithin.mono fun x hx ↦ hx.2
    · refine measurableSet_toMeasurable _ _ |>.inter ?_
      refine measurableSet_eq.preimage (measurable_fderiv _ _)
  rw [isLittleO_iff]
  intro c hc
  lift c to ℝ≥0 using hc.le
  rcases hderiv.exists_pos with ⟨C, hC₀, hC⟩
  rw [isBigOWith_iff] at hC
  lift C to ℝ≥0 using hC₀.le
  norm_cast at hc hC₀
  rcases exists_pos_forall_measure_le_exists_mem_sphere_dist_lt_volume_lineMap_mem_lt (E := E)
    (show c / C / 2 ≠ 0 by positivity) with ⟨δ, hδ₀, hδ⟩
  specialize hδ μ
  replace hmeas : ∀ᶠ r in 𝓝[>] 0, μ (sᶜ ∩ closedBall a r) ≤ δ * μ (closedBall a r) := by
    refine hmeas.eventually_const_lt (show 1 - δ < (1 : ℝ≥0∞) by simpa [ENNReal.sub_lt_self_iff])
      |>.mono fun r hr ↦ ?_
    replace hr := ENNReal.mul_lt_of_lt_div hr
    have : μ (closedBall a r ∩ s) ≠ ∞ :=
      measure_ne_top_of_subset inter_subset_left measure_closedBall_lt_top.ne
    rw [inter_comm, ← diff_eq, ← ENNReal.add_le_add_iff_left this, measure_inter_add_diff _ hsm,
      ← tsub_le_iff_right, inter_comm]
    rw [ENNReal.sub_mul, one_mul] at hr
    exacts [hr.le, fun _ _ ↦ measure_closedBall_lt_top.ne]
  rw [eventually_nhds_iff_ball]
  rw [EventuallyEq, eventually_nhdsWithin_iff] at hs
  rcases eventually_nhds_iff_ball.mp (hdf.and <| hs.and hC) with ⟨ε, hε₀, hε⟩
  choose hdf hdfs hdfr using hε
  rw [(nhdsGT_basis (0 : ℝ)).eventually_iff] at hmeas
  rcases hmeas with ⟨ε', hε₀', hε'⟩
  use min ε ε', by positivity
  intro y hy
  rcases eq_or_ne y a with rfl | hya
  · simp only [sub_self, norm_zero, Real.norm_eq_abs]
    positivity
  obtain ⟨z, hz_mem, hzy, hz_vol⟩ : ∃ z ∈ sphere a ‖y - a‖, dist z y < ↑(c / C / 2) * ‖y - a‖ ∧
      volume {t : ℝ | 0 ≤ t ∧ lineMap a z t ∈ sᶜ ∩ ball a ‖y - a‖} < ↑(c / C / 2) := by
    refine hδ ‖y - a‖ (by simpa [sub_eq_zero]) a (sᶜ ∩ ball a ‖y - a‖) ?_ y (by simp)
    have : Nontrivial E := ⟨⟨_, _, hya⟩⟩
    grw [← Measure.addHaar_closedBall_eq_addHaar_ball, ← hε', ball_subset_closedBall]
    grw [min_le_right] at hy
    simpa [sub_eq_zero, hya, dist_eq_norm_sub] using hy
  have hsub : closedBall a ‖y - a‖ ⊆ ball a ε := by
    apply closedBall_subset_ball
    grw [mem_ball_iff_norm, min_le_left] at hy
    exact hy
  have hz_norm : ‖z - a‖ = ‖y - a‖ := by simpa using hz_mem
  have hyz : ‖f y - f z‖ ≤ (c / 2) * ‖y - a‖ ^ (r + 1) := calc
    ‖f y - f z‖ ≤ C * ‖y - a‖ ^ r * ‖y - z‖ := by
      apply (convex_closedBall a ‖y - a‖).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      · exact fun w hw ↦ hdf w <| hsub hw
      · intro w hw
        grw [hdfr _ (hsub hw), Real.norm_of_nonneg (by positivity), mem_closedBall_iff_norm.mp hw]
      · exact sphere_subset_closedBall hz_mem
      · simp [dist_eq_norm_sub]
    _ ≤ (c / 2) * ‖y - a‖ ^ (r + 1) := by
      grw [← dist_eq_norm_sub' z y, hzy, Real.rpow_add_one' (by positivity) (by positivity)]
      apply le_of_eq
      push_cast
      field_simp
  have hza : ‖f z - f a‖ ≤ (c / 2) * ‖y - a‖ ^ (r + 1) := by
    grw [dist_le_mul_volume_of_norm_fderiv_le (C := C * ‖y - a‖ ^ r) _ _
      (openSegment_subset_ball_left _)]
    · have H :
          volume.real {t : ℝ | t ∈ Ioo 0 1 ∧ fderiv ℝ f ((lineMap a z) t) ≠ 0} < (c / C / 2) := by
        rw [Measure.real]
        apply ENNReal.toReal_lt_of_lt_ofReal
        norm_cast
        rw [ENNReal.ofReal_coe_nnreal]
        refine lt_of_le_of_lt ?_ hz_vol
        gcongr 2 with t
        rintro ⟨⟨ht₀, ht₁⟩, ht⟩
        have : (lineMap a z) t ∈ ball a ‖y - a‖ := by
          -- TODO: Part of the proof of `openSegment_subset_ball_left`. Move to a lemma?
          rw [mem_ball, dist_lineMap_left, Real.norm_of_nonneg ht₀.le, dist_comm, hz_mem]
          exact mul_lt_of_lt_one_left (by simpa [sub_eq_zero]) ht₁
        refine ⟨ht₀.le, ?_, this⟩
        contrapose! ht
        apply hdfs
        · grw [← hsub, ← ball_subset_closedBall]
          exact this
        · simpa using ht
      grw [H, hz_norm, Real.rpow_add_one' (by positivity) (by positivity)]
      apply le_of_eq
      field_simp
    · intro w hw
      grw [hdfr, Real.norm_of_nonneg (by positivity), mem_ball_iff_norm.mp hw, hz_norm]
      grw [← hsub, ← ball_subset_closedBall, ← hz_norm]
      exact hw
    · exact isOpen_ball
    · apply DifferentiableOn.diffContOnCl_ball (U := ball a ε)
      · exact fun w hw ↦ (hdf w hw).differentiableWithinAt
      · grw [hz_norm, hsub]
    · rintro rfl
      simpa [sub_eq_zero, hya] using hz_norm.symm
  grw [norm_sub_le_norm_sub_add_norm_sub _ (f z), hyz, hza, Real.norm_of_nonneg (by positivity)]
  apply le_of_eq
  field_simp
  ring

theorem isLittleO_norm_rpow_add_one_of_fderiv_of_density_point_of_apply_eq_zero
   [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {f : E → F} {a : E} {r : ℝ}
    {μ : Measure E} [μ.IsAddHaarMeasure] {s : Set E}
    (hr : 0 ≤ r) (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x)
    (hderiv : fderiv ℝ f =O[𝓝 a] (‖· - a‖ ^ r)) (hs : ∀ᶠ x in 𝓝[s] a, fderiv ℝ f x = 0)
    (hmeas : Tendsto (fun r ↦ μ (s ∩ closedBall a r) / μ (closedBall a r)) (𝓝[>] 0) (𝓝 1))
    (hf₀ : f a = 0) :
    f =o[𝓝 a] (‖· - a‖ ^ (r + 1)) := by
  simpa [hf₀]
    using sub_isLittleO_norm_rpow_add_one_of_fderiv_of_density_point hr hdf hderiv hs hmeas

end NormedField
