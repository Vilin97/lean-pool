/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.ChartL2Pullback
public import LeanPool.PoincareGeometry.AlmostSchur.ChartDerivativeBound
public import LeanPool.PoincareGeometry.AlmostSchur.GradientL2
public import LeanPool.PoincareGeometry.AlmostSchur.OpenDomainIntegration
public import LeanPool.PoincareGeometry.AlmostSchur.L2WeakLimit

/-! # Vanishing-energy limits in coordinates

All measures are the constructed Riemannian volume or Euclidean volume.
No weak regularity of the limit is assumed.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M]

local instance : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E
    (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)

local instance : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

omit [T2Space M] [CompactSpace M] in
/-- Global almost-everywhere equality pulls back on compact chart subsets. -/
theorem ae_eq_comp_chart_symm {f g : M → ℝ}
    (hfg : f =ᵐ[riemannianVolume (I := I)] g)
    (c : M) {K : Set E} (hK : IsCompact K)
    (hsub : K ⊆ (extChartAt I c).target) :
    f ∘ (extChartAt I c).symm =ᵐ[(volume : Measure E).restrict K]
      g ∘ (extChartAt I c).symm := by
  classical
  let e := extChartAt I c
  let ν : Measure M := riemannianVolume (I := I)
  let μ := (volume : Measure E).restrict K
  let q : E → M := e.target.piecewise e.symm (fun _ => c)
  have hq : Measurable q :=
    (continuousOn_extChartAt_symm c).measurable_piecewise
      continuous_const.continuousOn (isOpen_extChartAt_target c).measurableSet
  have he : AEMeasurable e (ν.restrict e.source) :=
    aemeasurable_restrict_of_measurable_subtype
      (isOpen_extChartAt_source c).measurableSet
      (continuousOn_extChartAt c).domRestrict.measurable
  have hback : Measure.map q (Measure.map e (ν.restrict e.source)) =
      ν.restrict e.source := by
    rw [AEMeasurable.map_map_of_aemeasurable hq.aemeasurable he]
    calc
      Measure.map (q ∘ e) (ν.restrict e.source) =
          Measure.map id (ν.restrict e.source) := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem (isOpen_extChartAt_source c).measurableSet]
          with x hx
        simp [q, e.map_source hx, e.left_inv hx]
      _ = _ := Measure.map_id
  obtain ⟨A, B, _, _, hdom, _⟩ := chartPushforward_measure_comparison c hK hsub
  have hμ : Measure.map q μ ≤ A • ν := by
    calc
      Measure.map q μ ≤ Measure.map q
          (A • (Measure.map e (ν.restrict e.source)).restrict K) :=
        Measure.map_mono hdom hq
      _ = A • Measure.map q ((Measure.map e (ν.restrict e.source)).restrict K) :=
        Measure.map_smul A hq.aemeasurable
      _ ≤ A • Measure.map q (Measure.map e (ν.restrict e.source)) :=
        smul_le_smul_left A (Measure.map_mono Measure.restrict_le_self hq)
      _ = A • ν.restrict e.source := by rw [hback]
      _ ≤ A • ν := smul_le_smul_left A Measure.restrict_le_self
  have ha := ae_of_ae_map hq.aemeasurable
    (ae_mono hμ (Measure.ae_smul_measure hfg A))
  filter_upwards [ha, ae_restrict_mem hK.measurableSet] with z hz hzK
  have hzT : z ∈ e.target := hsub hzK
  change f (e.symm z) = g (e.symm z)
  simpa only [q, Set.piecewise_eq_of_mem _ _ _ hzT] using hz

/-- The coordinate directional derivative belongs to local L², with a uniform
bound by the actual intrinsic Dirichlet energy. -/
theorem exists_chart_derivative_L2_bound (c : M) {K : Set E}
    (hK : IsCompact K) (hsub : K ⊆ (extChartAt I c).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : M → ℝ) (_hf : CMDiff 1 f) (v : E),
      ∃ hd : MemLp (fun z => fderiv ℝ (f ∘ (extChartAt I c).symm) z v) 2
          ((volume : Measure E).restrict K),
        ‖hd.toLp _‖ ≤ C * ‖v‖ * Real.sqrt (dirichletForm (I := I) f f) := by
  obtain ⟨A, _, T, hT, hTa⟩ := exists_chartL2Pullback c hK hsub
  obtain ⟨B, hB, hb⟩ := exists_abs_fderiv_chart_comp_apply_le c hK hsub
  let a : ℝ := (A ^ (1 / (2 : ℝ≥0∞)).toReal).toReal
  refine ⟨B * a, mul_nonneg hB ENNReal.toReal_nonneg, ?_⟩
  intro f hf v
  let G := (memLp_norm_gradient hf).toLp (fun x => ‖gradient (I := I) f x‖)
  have hG : (T G : E → ℝ) =ᵐ[(volume : Measure E).restrict K]
      fun z => ‖gradient (I := I) f ((extChartAt I c).symm z)‖ :=
    (hTa G).trans (ae_eq_comp_chart_symm (memLp_norm_gradient hf).coeFn_toLp c hK hsub)
  have hdc := ((contDiffOn_chart_comp c f hf.contMDiffOn).continuousOn_fderiv_of_isOpen
    (isOpen_extChartAt_target c) (by norm_num)).clm_apply (continuousOn_const (c := v))
  have hm := (hdc.mono hsub).aestronglyMeasurable (μ := volume) hK.measurableSet
  have hbound : ∀ᵐ z ∂(volume : Measure E).restrict K,
      ‖fderiv ℝ (f ∘ (extChartAt I c).symm) z v‖ ≤ (B * ‖v‖) * (T G) z := by
    filter_upwards [hG, ae_restrict_mem hK.measurableSet] with z hz hzK
    rw [hz, Real.norm_eq_abs]
    exact hb f hf z hzK v
  have hd := ((Lp.memLp (T G)).const_mul (B * ‖v‖)).mono' hm hbound
  refine ⟨hd, ?_⟩
  calc
    ‖hd.toLp _‖ ≤ ‖(B * ‖v‖) • T G‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hd.coeFn_toLp, Lp.coeFn_smul (B * ‖v‖) (T G), hbound]
        with z hz hs hbz
      rw [hz, hs]
      exact hbz.trans (le_abs_self _)
    _ = (B * ‖v‖) * ‖T G‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hB (norm_nonneg v))]
    _ ≤ (B * ‖v‖) * (a * ‖G‖) :=
      mul_le_mul_of_nonneg_left (hT G) (mul_nonneg hB (norm_nonneg v))
    _ = (B * a) * ‖v‖ * Real.sqrt (dirichletForm (I := I) f f) := by
      rw [show ‖G‖ = _ from norm_toLp_gradient hf]
      ring

/-- The scalar square-integrability proofs used in the limit theorem are
automatic for C¹ functions on the compact manifold. -/
theorem memLp_c1_riemannianVolume {f : M → ℝ} (hf : CMDiff 1 f) :
    MemLp f 2 (riemannianVolume (I := I)) := by
  let : IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
    ⟨(riemannianVolume_finite_positive (I := I)).2⟩
  exact hf.continuous.memLp_of_hasCompactSupport isClosed_closure.isCompact

/-- A strong actual-volume L² limit of C¹ functions with vanishing intrinsic
energy has zero coordinate weak directional derivatives. Tests may be C¹,
not just smooth. Square integrability here only records the representatives
used in the convergence hypothesis; no regularity of `u` is assumed. -/
theorem integral_chart_limit_mul_fderiv_eq_zero
    (f : ℕ → M → ℝ) (hf : ∀ n, CMDiff 1 (f n))
    (hfLp : ∀ n, MemLp (f n) 2 (riemannianVolume (I := I)))
    (u : Lp ℝ 2 (riemannianVolume (I := I)))
    (hlim : Tendsto (fun n => (hfLp n).toLp (f n)) atTop (𝓝 u))
    (henergy : Tendsto (fun n => Real.sqrt (dirichletForm (I := I) (f n) (f n)))
      atTop (𝓝 0))
    (c : M) (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (extChartAt I c).target) (v : E) :
    (∫ z, u ((extChartAt I c).symm z) * fderiv ℝ φ z v) = 0 := by
  let K := tsupport φ
  let μ := (volume : Measure E).restrict K
  obtain ⟨A, _, T, _, hTa⟩ := exists_chartL2Pullback c hc hs
  obtain ⟨C, _, hC⟩ := exists_chart_derivative_L2_bound c hc hs
  choose hd hdBound using fun n => hC (f n) (hf n) v
  let w : ℕ → Lp ℝ 2 μ := fun n => (hd n).toLp _
  have hw : Tendsto (fun n => ‖w n‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg (w n)) hdBound
    simpa only [mul_zero] using henergy.const_mul (C * ‖v‖)
  have ht : Tendsto (fun n => T ((hfLp n).toLp (f n))) atTop (𝓝 (T u)) :=
    (T.continuous.tendsto u).comp hlim
  have hφLp : MemLp φ 2 μ :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).mono_measure Measure.restrict_le_self
  have hdφLp : MemLp (fun z => fderiv ℝ φ z v) 2 μ :=
    (((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ v)).mono_measure Measure.restrict_le_self
  have hfn (n : ℕ) : (T ((hfLp n).toLp (f n)) : E → ℝ) =ᵐ[μ]
      (f n) ∘ (extChartAt I c).symm :=
    (hTa _).trans (ae_eq_comp_chart_symm (hfLp n).coeFn_toLp c hc hs)
  have hl (F : E → ℝ) :
      (∫ z in K, F z * fderiv ℝ φ z v) = ∫ z, F z * fderiv ℝ φ z v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hz' : z ∉ tsupport (fun z => fderiv ℝ φ z v) :=
      fun hh => hz (tsupport_fderiv_apply_subset ℝ v hh)
    rw [image_eq_zero_of_notMem_tsupport hz', mul_zero]
  have hr (F : E → ℝ) : (∫ z in K, F z * φ z) = ∫ z, F z * φ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  have hibp (n : ℕ) :
      (∫ z, T ((hfLp n).toLp (f n)) z * (hdφLp.toLp _) z ∂μ) =
        -(∫ z, w n z * (hφLp.toLp φ) z ∂μ) := by
    have hleft : (∫ z, T ((hfLp n).toLp (f n)) z * (hdφLp.toLp _) z ∂μ) =
        ∫ z, ((f n) ∘ (extChartAt I c).symm) z * fderiv ℝ φ z v ∂μ := by
      apply integral_congr_ae
      filter_upwards [hfn n, hdφLp.coeFn_toLp] with z hz hz'
      rw [hz, hz']
    have hright : (∫ z, w n z * (hφLp.toLp φ) z ∂μ) =
        ∫ z, fderiv ℝ ((f n) ∘ (extChartAt I c).symm) z v * φ z ∂μ := by
      apply integral_congr_ae
      filter_upwards [(hd n).coeFn_toLp, hφLp.coeFn_toLp] with z hz hz'
      change (hd n).toLp _ z * _ = _
      rw [hz, hz']
    rw [hleft, hright]
    change (∫ z in K, _) = -(∫ z in K, _)
    rw [hl, hr]
    exact integral_mul_fderiv_openDomain (isOpen_extChartAt_target c)
      _ φ (contDiffOn_chart_comp c (f n) (hf n).contMDiffOn) hφ hc hs v
  have hz := integral_mul_L2_eq_zero_of_limit ht hw (hφLp.toLp φ) (hdφLp.toLp _) hibp
  have heq : (∫ z, (T u) z * (hdφLp.toLp _) z ∂μ) =
      ∫ z, u ((extChartAt I c).symm z) * fderiv ℝ φ z v ∂μ := by
    apply integral_congr_ae
    filter_upwards [hTa u, hdφLp.coeFn_toLp] with z hz hz'
    rw [hz, hz']
    rfl
  rw [heq] at hz
  exact (hl (fun z => u ((extChartAt I c).symm z))).symm.trans hz

end AlmostSchur
