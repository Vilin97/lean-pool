/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Core.Defs
import LeanPool.PLAcceleratedNesterovLean.MorseBott.NormalHessianBound
import LeanPool.PLAcceleratedNesterovLean.MorseBott.Submanifold
import LeanPool.PLAcceleratedNesterovLean.MorseBott.TubularProjection

/-!
# Embedded Manifold Geometry

Proves that C² smooth embeddings of manifolds have local graph
representations (via the inverse function theorem), and that general
tubular neighborhoods yield the `IsTubularNeighborhoodOfSubmanifold`
structure.

## Main results

* `exists_general_tubular_subneighborhood` — For C² embedded submanifolds
  contained in an open set, construct a smaller general tubular neighborhood.
* `general_tubular_of_smooth_embedding` — For C² embedded submanifolds,
  a general tubular neighborhood directly
  gives the `IsTubularNeighborhoodOfSubmanifold` structure.
* `general_to_metric_tubular` — For *compact* C² embedded submanifolds,
  a general tubular neighborhood can be refined to a metric tubular
  sub-neighborhood.
-/

noncomputable section

namespace PLAcceleratedNesterovLean


open scoped Topology NNReal
open Manifold

variable {d : ℕ}

/-! ## Auxiliary lemmas -/

private abbrev isCompact_range_of_smoothEmbedding {d n : ℕ}
    (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ManifoldModel n) M]
    [IsManifold (modelI n) 2 M] [CompactSpace M]
    (ι : M → E d)
    (hι : IsSmoothEmbedding (modelI n) (𝓘(ℝ, E d)) 2 ι) :
    IsCompact (Set.range ι) :=
  isCompact_range hι.isEmbedding.continuous

private abbrev exists_metric_tube_subset {d : ℕ}
    {K U : Set (E d)}
    (hK : IsCompact K) (hKne : K.Nonempty)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ r : ℝ, 0 < r ∧
      {x : E d | Metric.infDist x K < r} ⊆ U := by
  obtain ⟨ε, hε_pos, hε⟩ :=
    IsCompact.exists_thickening_subset_open hK hU hKU
  exact ⟨ε, hε_pos, fun x hx =>
    hε ((Metric.mem_thickening_iff_infDist_lt hKne).mpr hx)⟩

/-- π_{V⊥} ∘ L = 0 when range(L) = V. -/
private abbrev orthogonalProjection_perp_comp_range_eq_zero
    {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
    (L : E₁ →L[ℝ] E₂)
    (V : Submodule ℝ E₂) [Vᗮ.HasOrthogonalProjection]
    (hV : V = LinearMap.range L.toLinearMap) :
    (Vᗮ.orthogonalProjectionOnto).comp L = 0 := by
  ext u
  simp only [ContinuousLinearMap.comp_apply, zero_apply]
  have hmem : L u ∈ Vᗮᗮ := Submodule.le_orthogonal_orthogonal V
    (hV ▸ LinearMap.mem_range_self L.toLinearMap u)
  have := Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hmem
  exact_mod_cast this

/-- If L : E₁ →L[ℝ] E₂ is injective and V = range(L), then π_V ∘ L is bijective. -/
private abbrev orthogonalProjection_comp_injective_bijective
    {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (L : E₁ →L[ℝ] E₂) (hL : Function.Injective L)
    (V : Submodule ℝ E₂) (hV : V = LinearMap.range L.toLinearMap)
    [V.HasOrthogonalProjection] :
    Function.Bijective ((V.orthogonalProjectionOnto).comp L) := by
  constructor
  · intro x y hxy
    apply hL
    have hLx : L x ∈ V := hV ▸ LinearMap.mem_range_self L.toLinearMap x
    have hLy : L y ∈ V := hV ▸ LinearMap.mem_range_self L.toLinearMap y
    have := congr_arg Subtype.val hxy
    simp only [ContinuousLinearMap.comp_apply] at this
    rwa [Subtype.coe_injective.eq_iff.mpr
           (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨L x, hLx⟩ : V)),
         Subtype.coe_injective.eq_iff.mpr
           (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨L y, hLy⟩ : V))] at this
  · rintro ⟨v, hv⟩
    obtain ⟨x, rfl⟩ := (hV ▸ hv : v ∈ LinearMap.range L.toLinearMap)
    exact ⟨x, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      ⟨L x, hV ▸ LinearMap.mem_range_self L.toLinearMap x⟩⟩

private abbrev isInvertible_of_bijective_finiteDimensional
    {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (L : A →L[ℝ] B) (hL : Function.Bijective L) :
    L.IsInvertible := by
  refine ⟨(LinearEquiv.ofBijective L.toLinearMap ?_).toContinuousLinearEquiv, ?_⟩
  · exact hL
  · ext x
    rfl

-- IFT + chart argument: large because of manifold API elaboration
/-- At each point of a C² smooth embedding, the image is locally a C² graph
    over an n-dimensional subspace, with φ(0) = 0, Dφ(0) = 0.
    (IFT applied to the embedding.) -/
private abbrev smooth_embedding_local_graph {d n : ℕ}
    (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ManifoldModel n) M]
    [IsManifold (modelI n) 2 M]
    (ι : M → E d)
    (hι : IsSmoothEmbedding (modelI n) (𝓘(ℝ, E d)) 2 ι)
    (m : E d) (hm : m ∈ Set.range ι) :
    ∃ (V : Submodule ℝ (E d)) (φ : V → V.orthogonal) (δ : ℝ),
      0 < δ ∧ ContDiff ℝ 2 φ ∧ φ 0 = 0 ∧
      fderiv ℝ φ 0 = 0 ∧
      ∀ x ∈ Metric.ball m δ,
        x ∈ Set.range ι ↔
          ∃ v : V, x = m + (v : E d) + (φ v : E d) := by
  -- Step 1: Obtain a preimage p of m under ι
  obtain ⟨p, hp⟩ := hm
  -- Step 2: Set up chart composition
  let c := extChartAt (modelI n) p
  let a := c p
  let g : ManifoldModel n → E d := ι ∘ c.symm
  have hp_source : p ∈ c.source := mem_extChartAt_source p
  -- Step 3: Key analytic properties of g
  have hg_smooth : ContDiffAt ℝ 2 g a := by
    obtain ⟨F, _, _, hF⟩ := hι.isImmersion
    have hFp := hF p
    have hp_ext_source : p ∈ (hFp.domChart.extend (modelI n)).source := by
      rw [hFp.domChart.extend_source]; exact hFp.mem_domChart_source
    have hp_inTarget := (hFp.domChart.extend (modelI n)).map_source hp_ext_source
    haveI : (modelI n).Boundaryless := by unfold modelI; infer_instance
    have htarget_open : IsOpen (hFp.domChart.extend (modelI n)).target :=
      hFp.domChart.isOpen_extend_target
    have heq : (hFp.codChart.extend (𝓘(ℝ, E d)) ∘ ι ∘ (hFp.domChart.extend (modelI n)).symm)
        =ᶠ[𝓝 (hFp.domChart.extend (modelI n) p)]
        (↑hFp.equiv ∘ fun v => (v, (0 : F))) :=
      hFp.writtenInCharts.eventuallyEq_of_mem (htarget_open.mem_nhds hp_inTarget)
    have hsmooth : ContDiffAt ℝ 2 (↑hFp.equiv ∘ fun v => (v, (0 : F)))
        (hFp.domChart.extend (modelI n) p) :=
      (hFp.equiv.contDiff.comp (contDiff_prodMk_left 0)).contDiffAt
    have hcoord_cda := hsmooth.congr_of_eventuallyEq heq
    have hι_cont : ContinuousAt ι p := hι.isEmbedding.continuous.continuousAt
    have hι_cmd : ContMDiffAt (modelI n) (𝓘(ℝ, E d)) 2 ι p := by
      change ContMDiffWithinAt (modelI n) (𝓘(ℝ, E d)) 2 ι Set.univ p
      rw [contMDiffWithinAt_iff_of_mem_maximalAtlas
        hFp.domChart_mem_maximalAtlas hFp.codChart_mem_maximalAtlas
        hFp.mem_domChart_source hFp.mem_codChart_source]
      exact ⟨hι_cont.continuousWithinAt, hcoord_cda.contDiffWithinAt⟩
    rw [contMDiffAt_iff] at hι_cmd
    simp only [modelI, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ] at hι_cmd
    exact hι_cmd.2
  have hg_a : g a = m := by
    change ι (c.symm (c p)) = m
    rw [PartialEquiv.left_inv c hp_source, hp]
  have hg_inj : Function.Injective (fderiv ℝ g a) := by
    obtain ⟨F, _, _, hF⟩ := hι.isImmersion
    have hFp := hF p
    haveI : (modelI n).Boundaryless := by unfold modelI; infer_instance
    have hg_diff' : DifferentiableAt ℝ g a := hg_smooth.differentiableAt (by norm_num)
    have hp_ext_source : p ∈ (hFp.domChart.extend (modelI n)).source := by
      rw [hFp.domChart.extend_source]; exact hFp.mem_domChart_source
    set transition : ManifoldModel n → ManifoldModel n :=
      hFp.domChart.extend (modelI n) ∘ ↑c.symm with htrans_def
    have hcsymm_mem : ∀ᶠ y in 𝓝 a, c.symm y ∈ hFp.domChart.source := by
      have hcont := continuousAt_extChartAt_symm (I := modelI n) p
      have h_mem : hFp.domChart.source ∈ 𝓝 (c.symm a) := by
        rw [c.left_inv hp_source]
        exact hFp.domChart.open_source.mem_nhds hFp.mem_domChart_source
      exact hcont h_mem
    have ha_target : a ∈ c.target := c.map_source hp_source
    have htarget_mem := (isOpen_extChartAt_target (I := modelI n) p).mem_nhds ha_target
    have htarget_open : IsOpen (hFp.domChart.extend (modelI n)).target :=
      hFp.domChart.isOpen_extend_target
    have heq_comp : (↑(hFp.codChart.extend (𝓘(ℝ, E d))) ∘ g)
        =ᶠ[𝓝 a] (↑hFp.equiv ∘ fun v => (v, (0 : F))) ∘ transition := by
      filter_upwards [hcsymm_mem] with y hy
      simp only [Function.comp]
      have hy' : c.symm y ∈ (hFp.domChart.extend (modelI n)).source := by
        rwa [OpenPartialHomeomorph.extend_source]
      have hz := hFp.writtenInCharts ((hFp.domChart.extend (modelI n)).map_source hy')
      simp only [Function.comp] at hz
      rwa [(hFp.domChart.extend (modelI n)).left_inv hy'] at hz
    have hfderiv_eq := heq_comp.fderiv_eq (𝕜 := ℝ)
    have htrans_diff : DifferentiableAt ℝ transition a := by
      have h := ModelWithCorners.contDiffWithinAt_extendCoordChange' (I := modelI n)
        (IsManifold.chart_mem_maximalAtlas (I := modelI n) p)
        hFp.domChart_mem_maximalAtlas
        (mem_chart_source (ManifoldModel n) p) hFp.mem_domChart_source
      simp only [modelI, modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ] at h
      simpa [transition, htrans_def, a, c, extChartAt, modelI] using
        h.differentiableAt (by norm_num)
    have hinv_comp_eq : (↑c ∘ ↑(hFp.domChart.extend (modelI n)).symm) ∘ transition
        =ᶠ[𝓝 a] id := by
      filter_upwards [hcsymm_mem, htarget_mem] with y hy1 hy2
      simp only [Function.comp, id, htrans_def]
      have hy1' : c.symm y ∈ (hFp.domChart.extend (modelI n)).source := by
        rwa [OpenPartialHomeomorph.extend_source]
      rw [(hFp.domChart.extend (modelI n)).left_inv hy1', c.right_inv hy2]
    have htrans_a : transition a = hFp.domChart.extend (modelI n) p := by
      change (hFp.domChart.extend (modelI n)) (c.symm (c p)) = _
      rw [c.left_inv hp_source]
    have hinv_diff : DifferentiableAt ℝ (↑c ∘ ↑(hFp.domChart.extend (modelI n)).symm)
        (transition a) := by
      have h := ModelWithCorners.contDiffWithinAt_extendCoordChange' (I := modelI n)
        hFp.domChart_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas (I := modelI n) p)
        hFp.mem_domChart_source (mem_chart_source (ManifoldModel n) p)
      simp only [modelI, modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ] at h
      simpa [htrans_a, c, extChartAt, modelI] using h.differentiableAt (by norm_num)
    have hcomp_id : fderiv ℝ ((↑c ∘ ↑(hFp.domChart.extend (modelI n)).symm) ∘ transition) a =
        ContinuousLinearMap.id ℝ _ := by
      rw [hinv_comp_eq.fderiv_eq (𝕜 := ℝ), fderiv_id]
    have hchain := fderiv_comp (x := a) hinv_diff htrans_diff
    rw [hchain] at hcomp_id
    have htrans_inj : Function.Injective (fderiv ℝ transition a) :=
      Function.HasLeftInverse.injective ⟨fderiv ℝ (↑c ∘ ↑(hFp.domChart.extend (modelI n)).symm)
        (transition a), fun x => by
        have := congr_fun (congr_arg DFunLike.coe hcomp_id) x
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
        exact this⟩
    set equiv_inl : ManifoldModel n →L[ℝ] E d :=
      hFp.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ F) with hequiv_inl_def
    have hequiv_inl_eq : ↑hFp.equiv ∘ (fun v => (v, (0 : F))) = ⇑equiv_inl := by
      ext v; simp [equiv_inl, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    have hequiv_inl_inj : Function.Injective equiv_inl :=
      hFp.equiv.injective.comp (fun x y h => (Prod.mk.inj h).1)
    have hrhs_inj : Function.Injective
        (fderiv ℝ ((↑hFp.equiv ∘ fun v => (v, (0 : F))) ∘ transition) a) := by
      rw [hequiv_inl_eq]
      rw [fderiv_comp (x := a) equiv_inl.differentiableAt htrans_diff,
          ContinuousLinearMap.fderiv]
      exact hequiv_inl_inj.comp htrans_inj
    rw [← hfderiv_eq] at hrhs_inj
    have hcodchart_diff : DifferentiableAt ℝ (↑(hFp.codChart.extend (𝓘(ℝ, E d)))) (g a) := by
      have hga : g a = ι p := by change ι (c.symm (c p)) = ι p; rw [c.left_inv hp_source]
      rw [hga]
      have h := ModelWithCorners.contDiffWithinAt_extendCoordChange' (I := 𝓘(ℝ, E d))
        (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E d)) (ι p))
        hFp.codChart_mem_maximalAtlas
        (mem_chart_source (E d) (ι p)) hFp.mem_codChart_source
      simp only [modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ] at h
      simpa [extChartAt_model_space_eq_id, PartialEquiv.refl_coe] using
        h.differentiableAt (by norm_num)
    rw [fderiv_comp (x := a) hcodchart_diff hg_diff'] at hrhs_inj
    intro x y hxy
    apply hrhs_inj
    simp only [ContinuousLinearMap.comp_apply, hxy]
  have hg_diff : DifferentiableAt ℝ g a := hg_smooth.differentiableAt (by norm_num)
  -- Step 4: Define the tangent subspace V = range(Dg(a))
  set L : ManifoldModel n →L[ℝ] E d := fderiv ℝ g a with hL_def
  set V : Submodule ℝ (E d) := LinearMap.range L.toLinearMap with hV_def
  haveI : FiniteDimensional ℝ ↥V := LinearMap.finiteDimensional_range L.toLinearMap
  haveI hV_OP : V.HasOrthogonalProjection := inferInstance
  haveI hVperp_OP : Vᗮ.HasOrthogonalProjection := inferInstance
  -- Step 5: Define tangent projection h(t) = π_V(g(t) − m) and its properties
  let h : ManifoldModel n → ↥V := fun t => V.orthogonalProjectionOnto (g t - m)
  have hh_a : h a = 0 := by
    change V.orthogonalProjectionOnto (g a - m) = 0; rw [hg_a, sub_self, map_zero]
  have hh_smooth : ContDiffAt ℝ 2 h a :=
    (V.orthogonalProjectionOnto).contDiff.contDiffAt.comp a (hg_smooth.sub contDiffAt_const)
  have hh_fderiv : HasFDerivAt h (V.orthogonalProjectionOnto.comp L) a := by
    have h2 : HasFDerivAt (fun t => g t - m) L a := by
      have := hg_diff.hasFDerivAt.sub (hasFDerivAt_const m a); rwa [sub_zero] at this
    exact V.orthogonalProjectionOnto.hasFDerivAt.comp a h2
  have hDh_bij : Function.Bijective (V.orthogonalProjectionOnto.comp L) :=
    orthogonalProjection_comp_injective_bijective L hg_inj V rfl
  -- Step 6: Package bijective derivative as ContinuousLinearEquiv
  have hDh_ker : (V.orthogonalProjectionOnto.comp L).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hDh_bij.1
  have hDh_range : (V.orthogonalProjectionOnto.comp L).range = ⊤ :=
    LinearMap.range_eq_top.mpr hDh_bij.2
  let Dh_equiv : ManifoldModel n ≃L[ℝ] ↥V :=
    ContinuousLinearEquiv.ofBijective (V.orthogonalProjectionOnto.comp L) hDh_ker hDh_range
  have hDh_equiv_coe :
      (Dh_equiv : ManifoldModel n →L[ℝ] ↥V) = V.orthogonalProjectionOnto.comp L :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hh_fderiv_equiv : HasFDerivAt h (Dh_equiv : ManifoldModel n →L[ℝ] ↥V) a := by
    rw [hDh_equiv_coe]; exact hh_fderiv
  -- Step 7: Apply C² inverse function theorem to h
  have h_two_ne_zero : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hh_strict : HasStrictFDerivAt h (Dh_equiv : ManifoldModel n →L[ℝ] ↥V) a :=
    hh_smooth.hasStrictFDerivAt' hh_fderiv_equiv h_two_ne_zero
  set ψ : ↥V → ManifoldModel n := hh_strict.localInverse h Dh_equiv a with hψ_def
  have hψ_zero : ψ 0 = a := by
    have := hh_strict.localInverse_apply_image; rwa [hh_a] at this
  have hψ_right : ∀ᶠ v in 𝓝 (0 : ↥V), h (ψ v) = v := by
    have := hh_strict.eventually_right_inverse; rwa [hh_a] at this
  have _hψ_left : ∀ᶠ t in 𝓝 a, ψ (h t) = t := hh_strict.eventually_left_inverse
  have hψ_smooth : ContDiffAt ℝ 2 ψ (0 : ↥V) := by
    have := hh_smooth.to_localInverse hh_fderiv_equiv h_two_ne_zero; rwa [hh_a] at this
  -- Step 8: Construct φ_raw(v) = π_{V⊥}(g(ψ(v)) − m) and extend globally via bump function
  let φ_raw : ↥V → ↥(Vᗮ) := fun v => Vᗮ.orthogonalProjectionOnto (g (ψ v) - m)
  have hφ_raw_zero : φ_raw 0 = 0 := by
    change Vᗮ.orthogonalProjectionOnto (g (ψ 0) - m) = 0
    rw [hψ_zero, hg_a, sub_self, map_zero]
  have hφ_raw_smooth_at : ContDiffAt ℝ 2 φ_raw 0 := by
    have hgψ : ContDiffAt ℝ 2 (g ∘ ψ) 0 := (hψ_zero ▸ hg_smooth).comp 0 hψ_smooth
    exact Vᗮ.orthogonalProjectionOnto.contDiff.contDiffAt.comp 0 (hgψ.sub contDiffAt_const)
  have hDφ_raw_zero : fderiv ℝ φ_raw 0 = 0 := by
    have hψ_diff : DifferentiableAt ℝ ψ 0 :=
      hψ_smooth.differentiableAt (by norm_num)
    have hg_fda : HasFDerivAt g L (ψ 0) := by rw [hψ_zero]; exact hg_diff.hasFDerivAt
    have hgψ_fda : HasFDerivAt (g ∘ ψ) (L.comp (fderiv ℝ ψ 0)) 0 :=
      hg_fda.comp 0 hψ_diff.hasFDerivAt
    have hsub_fda : HasFDerivAt (fun v => g (ψ v) - m) (L.comp (fderiv ℝ ψ 0)) 0 := by
      have h := hgψ_fda.sub (hasFDerivAt_const m (0 : ↥V)); rwa [sub_zero] at h
    have hφ_raw_fda :
        HasFDerivAt φ_raw (Vᗮ.orthogonalProjectionOnto.comp (L.comp (fderiv ℝ ψ 0))) 0 :=
      Vᗮ.orthogonalProjectionOnto.hasFDerivAt.comp 0 hsub_fda
    rw [hφ_raw_fda.fderiv]
    have hperp := orthogonalProjection_perp_comp_range_eq_zero L V rfl
    suffices hassoc : Vᗮ.orthogonalProjectionOnto.comp (L.comp (fderiv ℝ ψ 0)) =
        (Vᗮ.orthogonalProjectionOnto.comp L).comp (fderiv ℝ ψ 0) by
      rw [hassoc, hperp, ContinuousLinearMap.zero_comp]
    ext1 v; simp only [ContinuousLinearMap.comp_apply]
  -- Extract ball around 0 where φ_raw is C²
  have hφ_raw_ev : ∀ᶠ v in 𝓝 (0 : ↥V), ContDiffAt ℝ 2 φ_raw v :=
    hφ_raw_smooth_at.eventually (by norm_num)
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.eventually_nhds_iff.mp hφ_raw_ev
  -- Construct smooth bump χ equal to 1 near 0 with support inside ball 0 ε
  let bump : ContDiffBump (0 : ↥V) :=
    { rIn := ε / 3
      rOut := ε / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  -- Define bump-extended φ := bump • φ_raw, which is globally C²
  set φ : ↥V → ↥(Vᗮ) := fun v => bump v • φ_raw v with hφ_def
  -- Near 0, bump = 1 so φ = φ_raw
  have hφ_eq_raw_near : φ =ᶠ[𝓝 0] φ_raw := by
    filter_upwards [bump.eventuallyEq_one] with v hv
    change bump v • φ_raw v = φ_raw v
    have hbv : (↑bump : ↥V → ℝ) v = 1 := by simpa using hv
    rw [hbv, one_smul]
  have hφ_zero : φ 0 = 0 := by
    change bump 0 • φ_raw 0 = 0
    rw [hφ_raw_zero, smul_zero]
  have hφ_smooth : ContDiff ℝ 2 φ := by
    rw [contDiff_iff_contDiffAt]
    intro v
    by_cases hv : v ∈ tsupport (↑bump : ↥V → ℝ)
    · have hv_dist : dist v 0 < ε := by
        have hmem : v ∈ Metric.closedBall (0 : ↥V) (ε / 2) := bump.tsupport_eq ▸ hv
        exact lt_of_le_of_lt (Metric.mem_closedBall.mp hmem) (by linarith)
      exact (bump.contDiff (n := 2)).contDiffAt.smul (hε_ball hv_dist)
    · have hφ_eq_zero : φ =ᶠ[𝓝 v] (fun _ : ↥V => (0 : ↥(Vᗮ))) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hv] with w hw
        change bump w • φ_raw w = (0 : ↥(Vᗮ))
        have hbw : (↑bump : ↥V → ℝ) w = 0 := by simpa using hw
        rw [hbw, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hφ_eq_zero
  have hDφ_zero : fderiv ℝ φ 0 = 0 := by
    rw [hφ_eq_raw_near.fderiv_eq]
    exact hDφ_raw_zero
  -- Step 9: Extract δ and prove the iff characterization
  suffices ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ Metric.ball m δ,
        x ∈ Set.range ι ↔ ∃ v : ↥V, x = m + (v : E d) + (φ v : E d) by
    obtain ⟨δ, hδ_pos, hδ_iff⟩ := this
    exact ⟨V, φ, δ, hδ_pos, hφ_smooth, hφ_zero, hDφ_zero, hδ_iff⟩
  -- Extract metric balls from filter-level eventually statements
  obtain ⟨r₁, hr₁_pos, hr₁⟩ := Metric.eventually_nhds_iff.mp hψ_right
  obtain ⟨r₂, hr₂_pos, hr₂⟩ := Metric.eventually_nhds_iff.mp _hψ_left
  obtain ⟨r₃, hr₃_pos, hr₃_eq⟩ := Metric.eventually_nhds_iff.mp hφ_eq_raw_near
  set ρ := min r₁ r₃ with hρ_def
  have hρ_pos : 0 < ρ := lt_min hr₁_pos hr₃_pos
  -- Key identity: g(ψ v) = m + ↑v + ↑(φ v) for v ∈ ball(0, ρ)
  have key : ∀ v : ↥V, dist v 0 < ρ →
      g (ψ v) = m + (v : E d) + (φ v : E d) := by
    intro v hv
    have hright : h (ψ v) = v := hr₁ (lt_of_lt_of_le hv (min_le_left _ _))
    have hφ_eq' : φ v = φ_raw v := hr₃_eq (lt_of_lt_of_le hv (min_le_right _ _))
    suffices hsuff : g (ψ v) - m = (v : E d) + (φ v : E d) by
      rw [sub_eq_iff_eq_add'] at hsuff; rw [hsuff, add_assoc]
    rw [hφ_eq']
    have decomp := V.starProjection_add_starProjection_orthogonal (g (ψ v) - m)
    have h1 : V.starProjection (g (ψ v) - m) = (v : E d) := congrArg Subtype.val hright
    have h2 : Vᗮ.starProjection (g (ψ v) - m) = (φ_raw v : E d) := rfl
    rw [h1, h2] at decomp; exact decomp.symm
  -- Projection bound: dist v 0 ≤ dist x m when x = m + v + φ(v)
  have proj_bound : ∀ (v : ↥V) (x : E d),
      x = m + (v : E d) + (φ v : E d) → dist v 0 ≤ dist x m := by
    intro v x hx
    rw [dist_eq_norm, sub_zero, dist_eq_norm]
    have hxm : x - m = (v : E d) + (φ v : E d) := by rw [hx, add_assoc, add_sub_cancel_left]
    have hproj : V.orthogonalProjectionOnto (x - m) = v := by
      have hφ_proj : V.orthogonalProjectionOnto (φ v : E d) = 0 :=
        Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr (Submodule.coe_mem (φ v))
      rw [hxm, map_add,
          Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v,
          hφ_proj, add_zero]
    calc ‖v‖ = ‖V.orthogonalProjectionOnto (x - m)‖ := by rw [hproj]
      _ ≤ ‖x - m‖ := Submodule.norm_orthogonalProjectionOnto_apply_le V (x - m)
  -- Forward direction: embedding provides local preimage in chart domain
  have forward : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ x ∈ Metric.ball m δ₀,
      x ∈ Set.range ι → ∃ v : ↥V, x = m + (v : E d) + (φ v : E d) := by
    have hι_nhds : 𝓝 p = Filter.comap ι (𝓝 m) := by
      rw [hι.isEmbedding.isInducing.nhds_eq_comap, hp]
    have hc_cont : ContinuousAt c p := continuousAt_extChartAt (I := modelI n) p
    have hhc_cont : ContinuousAt (fun q => h (c q)) p :=
      hh_smooth.continuousAt.comp hc_cont
    have hS_nhds : c.source ∩ c ⁻¹' Metric.ball a r₂ ∩
        (fun q => h (c q)) ⁻¹' Metric.ball 0 ρ ∈ 𝓝 p := by
      apply Filter.inter_mem (Filter.inter_mem _ _) _
      · exact extChartAt_source_mem_nhds (I := modelI n) p
      · exact hc_cont.preimage_mem_nhds (Metric.ball_mem_nhds a hr₂_pos)
      · apply hhc_cont.preimage_mem_nhds
        change Metric.ball 0 ρ ∈ 𝓝 (h a)
        rw [hh_a]
        exact Metric.ball_mem_nhds 0 hρ_pos
    rw [hι_nhds] at hS_nhds
    obtain ⟨U, hU_mem, hU_sub⟩ := Filter.mem_comap.mp hS_nhds
    obtain ⟨δ₀, hδ₀_pos, hδ₀_ball⟩ := Metric.mem_nhds_iff.mp hU_mem
    refine ⟨δ₀, hδ₀_pos, ?_⟩
    intro x hx ⟨q, hq⟩
    have hq_U : q ∈ ι ⁻¹' U :=
      Set.mem_preimage.mpr (hq ▸ hδ₀_ball (Metric.mem_ball.mp hx))
    obtain ⟨⟨hq_source, hq_ball_a⟩, hq_ball_0⟩ := hU_sub hq_U
    set v := h (c q) with hv_def
    have hg_cq : g (c q) = x := by
      change ι (c.symm (c q)) = x; rw [PartialEquiv.left_inv c hq_source, hq]
    have hleft : ψ (h (c q)) = c q := hr₂ (Metric.mem_ball.mp hq_ball_a)
    have hv_near : dist v 0 < ρ := Metric.mem_ball.mp hq_ball_0
    exact ⟨v, by rw [← hg_cq, show c q = ψ v from hleft.symm, key v hv_near]⟩
  -- Combine forward and backward into the iff
  obtain ⟨δ₀, hδ₀_pos, hfwd⟩ := forward
  refine ⟨min ρ δ₀, lt_min hρ_pos hδ₀_pos, ?_⟩
  intro x hx
  have hx_lt : dist x m < min ρ δ₀ := Metric.mem_ball.mp hx
  constructor
  · exact hfwd x (Metric.mem_ball.mpr (lt_of_lt_of_le hx_lt (min_le_right _ _)))
  · intro ⟨v, hv⟩
    have hv_dist : dist v 0 < ρ :=
      lt_of_le_of_lt (proj_bound v x hv) (lt_of_lt_of_le hx_lt (min_le_left _ _))
    rw [hv, ← key v hv_dist]
    exact ⟨c.symm (ψ v), rfl⟩

/-- If `p` is a nearest point to `x` on `S` and lies on the C² graph chart at
    `m`, then the graph coordinate of `p` is a local minimizer of the squared
    distance-to-`x` function on the graph. -/
private lemma nearest_isLocalMin_on_graph {d : ℕ}
    {S : Set (E d)} {V : Submodule ℝ (E d)}
    {φ : V → V.orthogonal} {u_p : V}
    (hφ_cont : ContinuousAt φ u_p)
    {m : E d} {δ : ℝ}
    (hchart : ∀ y ∈ Metric.ball m δ,
      y ∈ S ↔ ∃ v : V, y = m + (v : E d) + (φ v : E d))
    {x p : E d}
    (hp_dist : dist x p = Metric.infDist x S)
    (hp_graph : p = m + (u_p : E d) + (φ u_p : E d))
    (hp_ball : p ∈ Metric.ball m δ) :
    IsLocalMin (fun v : V => ‖(x - m) - (v : E d) - (φ v : E d)‖ ^ 2) u_p := by
  have hcont : ContinuousAt (fun v : V => m + (v : E d) + (φ v : E d)) u_p :=
    (continuousAt_const.add V.subtypeL.continuous.continuousAt).add
      (V.orthogonal.subtypeL.continuous.continuousAt.comp hφ_cont)
  have h_pre :
      (fun v : V => m + (v : E d) + (φ v : E d)) ⁻¹' Metric.ball m δ ∈ 𝓝 u_p := by
    apply hcont.preimage_mem_nhds
    rw [show m + (u_p : E d) + (φ u_p : E d) = p from hp_graph.symm]
    exact Metric.isOpen_ball.mem_nhds hp_ball
  rw [IsLocalMin]
  filter_upwards [h_pre] with v hv
  have hv_S : m + (v : E d) + (φ v : E d) ∈ S := (hchart _ hv).mpr ⟨v, rfl⟩
  have h_opt : dist x p ≤ dist x (m + (v : E d) + (φ v : E d)) :=
    hp_dist ▸ Metric.infDist_le_dist_of_mem hv_S
  have h1 : ‖(x - m) - (u_p : E d) - (φ u_p : E d)‖ = dist x p := by
    rw [dist_eq_norm, hp_graph]
    congr 1
    abel
  have h2 : ‖(x - m) - (v : E d) - (φ v : E d)‖ =
      dist x (m + (v : E d) + (φ v : E d)) := by
    rw [dist_eq_norm]
    congr 1
    abel
  calc ‖(x - m) - (u_p : E d) - (φ u_p : E d)‖ ^ 2
      = dist x p ^ 2 := by rw [h1]
    _ ≤ dist x (m + (v : E d) + (φ v : E d)) ^ 2 :=
        pow_le_pow_left₀ dist_nonneg h_opt 2
    _ = ‖(x - m) - (v : E d) - (φ v : E d)‖ ^ 2 := by rw [h2]

/-- For orthogonal components `u ∈ V` and `w ∈ Vᗮ`, `‖u‖ ≤ ‖u + w‖`. -/
private lemma norm_submodule_le_norm_add_orthogonal
    {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
    {V : Submodule ℝ E₁} (u : V) (w : V.orthogonal) :
    ‖(u : E₁)‖ ≤ ‖(u : E₁) + (w : E₁)‖ := by
  have h_sq : ‖(u : E₁)‖ ^ 2 ≤ ‖(u : E₁) + (w : E₁)‖ ^ 2 := by
    have := norm_add_sq_real (u : E₁) (w : E₁)
    rw [V.inner_right_of_mem_orthogonal (Submodule.coe_mem u)
      (Submodule.coe_mem w), mul_zero, add_zero] at this
    linarith [sq_nonneg ‖(w : E₁)‖]
  nlinarith [norm_nonneg (u : E₁), norm_nonneg ((u : E₁) + (w : E₁))]

/-- A graph coordinate cannot be farther from `0` than the graph point is from
    the base point. -/
private lemma graph_param_dist_le {d : ℕ}
    {V : Submodule ℝ (E d)} {φ : V → V.orthogonal}
    (m q : E d) (u : V)
    (hq : q = m + (u : E d) + (φ u : E d)) :
    dist u 0 ≤ dist q m := by
  rw [dist_zero_right, dist_eq_norm]
  have hqm : q - m = (u : E d) + (φ u : E d) := by
    rw [hq]
    abel
  rw [hqm]
  exact norm_submodule_le_norm_add_orthogonal u (φ u)

/-- When a nearest point `q` lies in the graph chart near `m`, its chart
    coordinate is determined by the implicit-function solution for the
    first-order nearest-point equation. -/
private lemma nearest_ift_coord {d : ℕ}
    {V : Submodule ℝ (E d)} {φ : V → V.orthogonal}
    {S : Set (E d)} {m x q : E d}
    {v_impl : E d → V}
    {ε_ift ε_cont r δ : ℝ}
    (hφC2 : ContDiff ℝ 2 φ)
    (hF_zero : optimalityEqn φ m (0, (0 : V)) = 0)
    (hε_ift : ∀ p : E d × V, dist p (0, (0 : V)) < ε_ift →
      (optimalityEqn φ m p = optimalityEqn φ m (0, (0 : V)) ↔
        v_impl p.1 = p.2))
    (hε_cont : ∀ v : V, dist v 0 < ε_cont → ContinuousAt φ v)
    (hchart : ∀ y ∈ Metric.ball m δ,
      y ∈ S ↔ ∃ v : V, y = m + (v : E d) + (φ v : E d))
    (_h3r_lt_δ : 3 * r < δ) (h3r_lt_εi : 3 * r < ε_ift)
    (h3r_lt_εc : 3 * r < ε_cont)
    (hxm : dist x m < r)
    (hq_S : q ∈ S) (hq_near_m : dist q m < 2 * r)
    (hq_dist : dist x q = Metric.infDist x S)
    (hq_in_chart : q ∈ Metric.ball m δ) :
    ∃ u_q : V, q = m + (u_q : E d) + (φ u_q : E d) ∧
      v_impl (x - m) = u_q := by
  obtain ⟨u_q, huq_graph⟩ := (hchart q hq_in_chart).mp hq_S
  have huq_dist : dist u_q (0 : V) < 3 * r := by
    have h1 := graph_param_dist_le m q u_q huq_graph
    have h2 : (0 : ℝ) ≤ dist x m := dist_nonneg
    linarith only [h1, h2, hq_near_m, hxm]
  have hφ_cont_uq : ContinuousAt φ u_q := hε_cont _ (lt_trans huq_dist h3r_lt_εc)
  have huq_localMin : IsLocalMin
      (fun v : V => ‖(x - m) - (v : E d) - (φ v : E d)‖ ^ 2) u_q :=
    nearest_isLocalMin_on_graph hφ_cont_uq hchart hq_dist huq_graph hq_in_chart
  have hF_uq : optimalityEqn φ m (x - m, u_q) = 0 :=
    localMin_sq_dist_implies_optimalityEqn hφC2 m huq_localMin
  have h_ift_dist_q : dist (x - m, u_q) (0, (0 : V)) < ε_ift := by
    rw [Prod.dist_eq]
    exact max_lt
      (by
        rw [dist_zero_right]
        linarith [dist_eq_norm x m, @dist_nonneg (E d) _ x m])
      (lt_trans huq_dist h3r_lt_εi)
  have huniq := hε_ift (x - m, u_q) h_ift_dist_q
  exact ⟨u_q, huq_graph, huniq.mp (by rw [hF_uq, hF_zero])⟩

/-- Compact-graph existence of a nearest point in `S` inside a local graph
    chart. The minimizing point for the compact local graph is also globally
    nearest among points of `S`, because any closer global competitor must lie
    inside the same chart. -/
private lemma compact_graph_nearest {d : ℕ}
    {V : Submodule ℝ (E d)} {φ : V → V.orthogonal}
    {S : Set (E d)} {m x : E d}
    {δ η ε_cont r : ℝ}
    (hφ0 : φ 0 = 0)
    (hη_bound : ∀ v : V, dist v 0 < η → dist (φ v) (φ 0) < δ / 2)
    (hε_cont : ∀ v : V, dist v 0 < ε_cont → ContinuousAt φ v)
    (hchart : ∀ y ∈ Metric.ball m δ,
      y ∈ S ↔ ∃ v : V, y = m + (v : E d) + (φ v : E d))
    (hr_pos : 0 < r)
    (h3r_lt_δ2 : 3 * r < δ / 2) (h3r_lt_η : 3 * r < η)
    (h3r_lt_εc : 3 * r < ε_cont)
    (hxm : dist x m < r)
    (hm : m ∈ S) :
    ∃ p₀ ∈ S, dist x p₀ < r ∧ dist p₀ m < 2 * r ∧
      p₀ ∈ Metric.ball m δ ∧ dist x p₀ = Metric.infDist x S := by
  have h3r_lt_δ : 3 * r < δ := by linarith only [h3r_lt_δ2, hr_pos]
  set graphMap : V → E d := fun u => m + (u : E d) + (φ u : E d)
  have hgraphMap_cont : ContinuousOn graphMap (Metric.closedBall (0 : V) (3 * r)) := by
    intro u hu
    have hu_dist : dist u 0 < ε_cont :=
      lt_of_le_of_lt (Metric.mem_closedBall.mp hu) h3r_lt_εc
    exact ((continuousAt_const.add V.subtypeL.continuous.continuousAt).add
      (V.orthogonal.subtypeL.continuous.continuousAt.comp
        (hε_cont _ hu_dist))).continuousWithinAt
  have hball_compact : IsCompact (Metric.closedBall (0 : V) (3 * r)) :=
    isCompact_closedBall (0 : V) (3 * r)
  set K := graphMap '' Metric.closedBall (0 : V) (3 * r)
  have hK_compact : IsCompact K := hball_compact.image_of_continuousOn hgraphMap_cont
  have hK_sub_S : K ⊆ S := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := hq
    have hu_norm : dist u 0 ≤ 3 * r := Metric.mem_closedBall.mp hu
    have hφ_bound : dist (φ u) 0 < δ / 2 := by
      have := hη_bound _ (lt_of_le_of_lt hu_norm h3r_lt_η)
      rwa [hφ0] at this
    have h_in_ball : graphMap u ∈ Metric.ball m δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hgm : graphMap u - m = (u : E d) + (φ u : E d) := by
        simp only [graphMap]
        abel
      rw [hgm]
      calc ‖(u : E d) + (φ u : E d)‖
          ≤ ‖(u : E d)‖ + ‖(φ u : E d)‖ := norm_add_le _ _
        _ < 3 * r + δ / 2 := by
            have h1 : ‖(u : E d)‖ = dist u 0 := (dist_zero_right _).symm
            have h2 : ‖(φ u : E d)‖ = dist (φ u) 0 := (dist_zero_right _).symm
            rw [h1, h2]
            exact add_lt_add_of_le_of_lt hu_norm hφ_bound
        _ < δ := by linarith only [h3r_lt_δ2, hφ_bound, hu_norm]
    exact (hchart (graphMap u) h_in_ball).mpr ⟨u, rfl⟩
  have hm_in_K : m ∈ K := by
    refine ⟨0, Metric.mem_closedBall.mpr ?_, ?_⟩
    · simp only [dist_self]
      linarith only [hr_pos]
    · simp only [ZeroMemClass.coe_zero, add_zero, hφ0, graphMap]
  obtain ⟨p₀, hp₀_K, hp₀_infK⟩ := hK_compact.exists_infDist_eq_dist ⟨m, hm_in_K⟩ x
  have hp₀_dist_bound : dist x p₀ < r := by
    calc dist x p₀ ≤ Metric.infDist x K := ge_iff_le.mp (hp₀_infK ▸ le_refl _)
      _ ≤ dist x m := Metric.infDist_le_dist_of_mem hm_in_K
      _ < r := hxm
  have hp₀_S : p₀ ∈ S := hK_sub_S hp₀_K
  have hp₀_eq_infS : dist x p₀ = Metric.infDist x S := by
    apply le_antisymm
    · rw [Metric.le_infDist ⟨m, hm⟩]
      intro q hqS
      by_cases hq : dist x q < r
      · have hq_near : dist q m < 2 * r :=
          lt_of_le_of_lt (dist_triangle q x m) (by
            rw [dist_comm q x]
            linarith only [hq, hxm])
        have hq_ball : q ∈ Metric.ball m δ :=
          Metric.mem_ball.mpr (lt_trans hq_near (by linarith only [h3r_lt_δ, hr_pos]))
        obtain ⟨u_q', huq'_graph⟩ := (hchart q hq_ball).mp hqS
        have huq'_dist : dist u_q' 0 ≤ 3 * r := by
          have h1 := graph_param_dist_le m q u_q' huq'_graph
          linarith only [h1, hq_near, hr_pos]
        have hq_K : q ∈ K :=
          ⟨u_q', Metric.mem_closedBall.mpr huq'_dist, huq'_graph.symm⟩
        rw [← hp₀_infK]
        exact Metric.infDist_le_dist_of_mem hq_K
      · push Not at hq
        linarith only [hq, hp₀_dist_bound]
    · exact Metric.infDist_le_dist_of_mem hp₀_S
  have hp₀_near_m : dist p₀ m < 2 * r := by
    calc dist p₀ m ≤ dist p₀ x + dist x m := dist_triangle _ _ _
      _ = dist x p₀ + dist x m := by rw [dist_comm p₀ x]
      _ < r + r := add_lt_add hp₀_dist_bound hxm
      _ = 2 * r := by ring
  have hp₀_in_chart : p₀ ∈ Metric.ball m δ :=
    Metric.mem_ball.mpr (lt_trans hp₀_near_m (by linarith only [h3r_lt_δ, hr_pos]))
  exact ⟨p₀, hp₀_S, hp₀_dist_bound, hp₀_near_m, hp₀_in_chart, hp₀_eq_infS⟩

/-- A global C² graph chart for `S` gives local unique nearest-point balls. -/
private theorem local_tubular_of_graph_chart
    {d : ℕ} {S U : Set (E d)}
    (hU_open : IsOpen U) (hS_sub : S ⊆ U)
    {m : E d} (hm : m ∈ S)
    {V : Submodule ℝ (E d)} {φ : V → V.orthogonal} {δ : ℝ}
    (hδ_pos : 0 < δ) (hφC2 : ContDiff ℝ 2 φ)
    (hφ0 : φ 0 = 0) (hDφ0 : fderiv ℝ φ 0 = 0)
    (hchart : ∀ y ∈ Metric.ball m δ,
      y ∈ S ↔ ∃ v : V, y = m + (v : E d) + (φ v : E d)) :
    ∃ r > 0, Metric.ball m r ⊆ U ∧
      ∀ x ∈ Metric.ball m r,
        ∃! p, p ∈ S ∧ dist x p = Metric.infDist x S := by
  have hφ_cont_0 : ContinuousAt φ 0 :=
    hφC2.continuous.continuousAt
  obtain ⟨η, hη_pos, hη_bound⟩ :=
    Metric.continuousAt_iff.mp hφ_cont_0 (δ / 2) (by positivity)
  have hφ_cont_nhd : ∀ᶠ v in 𝓝 (0 : V), ContinuousAt φ v :=
    Filter.Eventually.of_forall fun v => hφC2.continuous.continuousAt
  obtain ⟨ε_cont, hε_cont_pos, hε_cont⟩ := Metric.eventually_nhds_iff.mp hφ_cont_nhd
  have hF_C1 : ContDiff ℝ 1 (optimalityEqn φ m) := optimalityEqn_contDiff hφC2 m
  have hF_zero : optimalityEqn φ m (0, (0 : V)) = 0 := by
    simp only [optimalityEqn, hφ0, ZeroMemClass.coe_zero, sub_zero, map_zero, add_zero]
  set F'_0 := fderiv ℝ (optimalityEqn φ m) (0, (0 : V))
  have hF_fda : HasFDerivAt (optimalityEqn φ m) F'_0 (0, (0 : V)) :=
    (hF_C1.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hF_bij : Function.Bijective (F'_0.comp (ContinuousLinearMap.inr ℝ (E d) V)) :=
    optimalityEqn_partial_v_bijective hφC2 hφ0 hDφ0 m
  have hF_cda : ContDiffAt ℝ 1 (optimalityEqn φ m) (0, (0 : V)) := hF_C1.contDiffAt
  have hF_right_inv : (F'_0.comp (ContinuousLinearMap.inr ℝ (E d) V)).IsInvertible :=
    isInvertible_of_bijective_finiteDimensional
      (F'_0.comp (ContinuousLinearMap.inr ℝ (E d) V)) hF_bij
  have hF_partial_inv :
      (fderiv ℝ (optimalityEqn φ m) (0, (0 : V)) ∘L
        ContinuousLinearMap.inr ℝ (E d) V).IsInvertible := by
    rw [hF_fda.fderiv]
    exact hF_right_inv
  set v_impl := hF_cda.implicitFunction one_ne_zero hF_partial_inv with hv_impl_def
  have h_ift_uniq :
      ∀ᶠ p in 𝓝 (0, (0 : V)),
        optimalityEqn φ m p = optimalityEqn φ m (0, (0 : V)) ↔ v_impl p.1 = p.2 := by
    rw [hv_impl_def]
    exact hF_cda.eventually_apply_eq_iff_implicitFunction one_ne_zero hF_partial_inv
  obtain ⟨ε_ift, hε_ift_pos, hε_ift⟩ :=
    Metric.eventually_nhds_iff.mp h_ift_uniq
  have hε_ift_explicit :
      ∀ p : E d × V, dist p (0, (0 : V)) < ε_ift →
        (optimalityEqn φ m p = optimalityEqn φ m (0, (0 : V)) ↔
          v_impl p.1 = p.2) := by
    intro p hp
    exact @hε_ift p hp
  obtain ⟨r_U, hr_U_pos, hr_U_sub⟩ := Metric.isOpen_iff.mp hU_open m (hS_sub hm)
  set r := min (min (δ / 8) (η / 4)) (min (ε_ift / 4) (min (ε_cont / 4) r_U))
    with hr_def
  have hr_pos : 0 < r := by positivity
  have hr_le_δ8 : r ≤ δ / 8 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hr_le_η4 : r ≤ η / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hr_le_εi4 : r ≤ ε_ift / 4 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hr_le_εc4 : r ≤ ε_cont / 4 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hr_le_rU : r ≤ r_U :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have h3r_lt_δ : 3 * r < δ := by linarith only [hr_le_δ8, hδ_pos]
  have h3r_lt_η : 3 * r < η := by linarith only [hr_le_η4, hη_pos]
  have h3r_lt_εi : 3 * r < ε_ift := by linarith only [hr_le_εi4, hε_ift_pos]
  have h3r_lt_εc : 3 * r < ε_cont := by linarith only [hr_le_εc4, hε_cont_pos]
  refine ⟨r, hr_pos, ?_, ?_⟩
  · intro y hy
    exact hr_U_sub (lt_of_lt_of_le (Metric.mem_ball.mp hy) hr_le_rU)
  · intro x hx
    have hxm : dist x m < r := Metric.mem_ball.mp hx
    obtain ⟨p₀, hp₀_S, hp₀_dist_bound, hp₀_near_m, hp₀_in_chart_ball, hp₀_eq_infS⟩ :=
      compact_graph_nearest hφ0 hη_bound hε_cont hchart hr_pos
        (by linarith only [hr_le_δ8, hδ_pos]) h3r_lt_η h3r_lt_εc hxm hm
    obtain ⟨u₀, hu₀_graph, h_impl_u₀⟩ :=
      nearest_ift_coord (v_impl := v_impl) (ε_ift := ε_ift)
        (ε_cont := ε_cont) (r := r) (δ := δ) hφC2 hF_zero
        hε_ift_explicit hε_cont hchart
        h3r_lt_δ h3r_lt_εi h3r_lt_εc hxm hp₀_S hp₀_near_m hp₀_eq_infS
        hp₀_in_chart_ball
    refine ⟨p₀, ⟨hp₀_S, hp₀_eq_infS⟩, ?_⟩
    intro q ⟨hq_S, hq_dist⟩
    have hq_near_m : dist q m < 2 * r := by
      have hxq : dist x q < r := by
        calc dist x q ≤ dist x m := by
                rw [hq_dist]
                exact Metric.infDist_le_dist_of_mem hm
          _ < r := hxm
      calc dist q m ≤ dist q x + dist x m := dist_triangle _ _ _
        _ = dist x q + dist x m := by rw [dist_comm]
        _ < r + r := add_lt_add hxq hxm
        _ = 2 * r := by ring
    have hq_in_chart : q ∈ Metric.ball m δ :=
      Metric.mem_ball.mpr (lt_trans hq_near_m (by linarith only [hr_le_δ8, hδ_pos]))
    obtain ⟨u_q, huq_graph, h_impl_uq⟩ :=
      nearest_ift_coord (v_impl := v_impl) (ε_ift := ε_ift)
        (ε_cont := ε_cont) (r := r) (δ := δ) hφC2 hF_zero
        hε_ift_explicit hε_cont hchart
        h3r_lt_δ h3r_lt_εi h3r_lt_εc hxm hq_S hq_near_m hq_dist hq_in_chart
    rw [hu₀_graph, h_impl_u₀.symm.trans h_impl_uq]
    exact huq_graph

/-- A C² smooth embedded submanifold has local balls on which the nearest point
    in the embedded range exists and is unique. -/
private theorem local_tubular_of_smooth_embedding
    {d n : ℕ}
    (M : Type*) [TopologicalSpace M] [ChartedSpace (ManifoldModel n) M]
    [IsManifold (modelI n) 2 M]
    (ι : M → E d)
    (hι : IsSmoothEmbedding (modelI n) (modelWithCornersSelf ℝ (E d)) 2 ι)
    {U : Set (E d)} (hU_open : IsOpen U) (hS_sub : Set.range ι ⊆ U)
    (m : E d) (hm : m ∈ Set.range ι) :
    ∃ r > 0, Metric.ball m r ⊆ U ∧
      ∀ x ∈ Metric.ball m r,
        ∃! p, p ∈ Set.range ι ∧ dist x p = Metric.infDist x (Set.range ι) := by
  set S := Set.range ι with hS_def
  obtain ⟨V, φ, δ, hδ_pos, hφC2, hφ0, hDφ0, hchart⟩ :=
    smooth_embedding_local_graph M ι hι m hm
  have hφ_cont_0 : ContinuousAt φ 0 :=
    hφC2.continuous.continuousAt
  obtain ⟨η, hη_pos, hη_bound⟩ :=
    Metric.continuousAt_iff.mp hφ_cont_0 (δ / 2) (by positivity)
  have hφ_cont_nhd : ∀ᶠ v in 𝓝 (0 : V), ContinuousAt φ v :=
    Filter.Eventually.of_forall fun v => hφC2.continuous.continuousAt
  obtain ⟨ε_cont, hε_cont_pos, hε_cont⟩ := Metric.eventually_nhds_iff.mp hφ_cont_nhd
  have hF_C1 : ContDiff ℝ 1 (optimalityEqn φ m) := optimalityEqn_contDiff hφC2 m
  have hF_zero : optimalityEqn φ m (0, (0 : V)) = 0 := by
    simp only [optimalityEqn, hφ0, ZeroMemClass.coe_zero, sub_zero, map_zero, add_zero]
  set F'_0 := fderiv ℝ (optimalityEqn φ m) (0, (0 : V))
  have hF_fda : HasFDerivAt (optimalityEqn φ m) F'_0 (0, (0 : V)) :=
    (hF_C1.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hF_bij : Function.Bijective (F'_0.comp (ContinuousLinearMap.inr ℝ (E d) V)) :=
    optimalityEqn_partial_v_bijective hφC2 hφ0 hDφ0 m
  have hF_cda : ContDiffAt ℝ 1 (optimalityEqn φ m) (0, (0 : V)) := hF_C1.contDiffAt
  have hF_right_inv : (F'_0.comp (ContinuousLinearMap.inr ℝ (E d) V)).IsInvertible :=
    isInvertible_of_bijective_finiteDimensional
      (F'_0.comp (ContinuousLinearMap.inr ℝ (E d) V)) hF_bij
  have hF_partial_inv :
      (fderiv ℝ (optimalityEqn φ m) (0, (0 : V)) ∘L
        ContinuousLinearMap.inr ℝ (E d) V).IsInvertible := by
    rw [hF_fda.fderiv]
    exact hF_right_inv
  set v_impl := hF_cda.implicitFunction one_ne_zero hF_partial_inv with hv_impl_def
  have h_ift_uniq :
      ∀ᶠ p in 𝓝 (0, (0 : V)),
        optimalityEqn φ m p = optimalityEqn φ m (0, (0 : V)) ↔ v_impl p.1 = p.2 := by
    rw [hv_impl_def]
    exact hF_cda.eventually_apply_eq_iff_implicitFunction one_ne_zero hF_partial_inv
  obtain ⟨ε_ift, hε_ift_pos, hε_ift⟩ :=
    Metric.eventually_nhds_iff.mp h_ift_uniq
  have hε_ift_explicit :
      ∀ p : E d × V, dist p (0, (0 : V)) < ε_ift →
        (optimalityEqn φ m p = optimalityEqn φ m (0, (0 : V)) ↔
          v_impl p.1 = p.2) := by
    intro p hp
    exact @hε_ift p hp
  obtain ⟨r_U, hr_U_pos, hr_U_sub⟩ := Metric.isOpen_iff.mp hU_open m (hS_sub hm)
  set r := min (min (δ / 8) (η / 4)) (min (ε_ift / 4) (min (ε_cont / 4) r_U))
    with hr_def
  have hr_pos : 0 < r := by positivity
  have hr_le_δ8 : r ≤ δ / 8 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hr_le_η4 : r ≤ η / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hr_le_εi4 : r ≤ ε_ift / 4 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hr_le_εc4 : r ≤ ε_cont / 4 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hr_le_rU : r ≤ r_U :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have h3r_lt_δ : 3 * r < δ := by linarith only [hr_le_δ8, hδ_pos]
  have h3r_lt_η : 3 * r < η := by linarith only [hr_le_η4, hη_pos]
  have h3r_lt_εi : 3 * r < ε_ift := by linarith only [hr_le_εi4, hε_ift_pos]
  have h3r_lt_εc : 3 * r < ε_cont := by linarith only [hr_le_εc4, hε_cont_pos]
  refine ⟨r, hr_pos, ?_, ?_⟩
  · intro y hy
    exact hr_U_sub (lt_of_lt_of_le (Metric.mem_ball.mp hy) hr_le_rU)
  · intro x hx
    have hxm : dist x m < r := Metric.mem_ball.mp hx
    obtain ⟨p₀, hp₀_S, hp₀_dist_bound, hp₀_near_m, hp₀_in_chart_ball, hp₀_eq_infS⟩ :=
      compact_graph_nearest hφ0 hη_bound hε_cont hchart hr_pos
        (by linarith only [hr_le_δ8, hδ_pos]) h3r_lt_η h3r_lt_εc hxm hm
    obtain ⟨u₀, hu₀_graph, h_impl_u₀⟩ :=
      nearest_ift_coord (v_impl := v_impl) (ε_ift := ε_ift)
        (ε_cont := ε_cont) (r := r) (δ := δ) hφC2 hF_zero
        hε_ift_explicit hε_cont hchart
        h3r_lt_δ h3r_lt_εi h3r_lt_εc hxm hp₀_S hp₀_near_m hp₀_eq_infS
        hp₀_in_chart_ball
    refine ⟨p₀, ⟨hp₀_S, hp₀_eq_infS⟩, ?_⟩
    intro q ⟨hq_S, hq_dist⟩
    have hq_near_m : dist q m < 2 * r := by
      have hxq : dist x q < r := by
        calc dist x q ≤ dist x m := by
                rw [hq_dist]
                exact Metric.infDist_le_dist_of_mem hm
          _ < r := hxm
      calc dist q m ≤ dist q x + dist x m := dist_triangle _ _ _
        _ = dist x q + dist x m := by rw [dist_comm]
        _ < r + r := add_lt_add hxq hxm
        _ = 2 * r := by ring
    have hq_in_chart : q ∈ Metric.ball m δ :=
      Metric.mem_ball.mpr (lt_trans hq_near_m (by linarith only [hr_le_δ8, hδ_pos]))
    obtain ⟨u_q, huq_graph, h_impl_uq⟩ :=
      nearest_ift_coord (v_impl := v_impl) (ε_ift := ε_ift)
        (ε_cont := ε_cont) (r := r) (δ := δ) hφC2 hF_zero
        hε_ift_explicit hε_cont hchart
        h3r_lt_δ h3r_lt_εi h3r_lt_εc hxm hq_S hq_near_m hq_dist hq_in_chart
    rw [hu₀_graph, h_impl_u₀.symm.trans h_impl_uq]
    exact huq_graph

/-- Given local unique-projection balls around every point of `S`, construct a
    general tubular sub-neighborhood. -/
private theorem local_tubular_to_general
    {d : ℕ} {S U : Set (E d)}
    (hLocalTub : ∀ m ∈ S, ∃ r > 0, Metric.ball m r ⊆ U ∧
        ∀ x ∈ Metric.ball m r, ∃! p, p ∈ S ∧ dist x p = Metric.infDist x S) :
    ∃ U' : Set (E d), IsOpen U' ∧ S ⊆ U' ∧ U' ⊆ U ∧
        IsGeneralTubularNeighborhood S U' := by
  refine ⟨⋃ (m : {m // m ∈ S}), Metric.ball m.1 (hLocalTub m.1 m.2).choose,
    ?_, ?_, ?_, ?_⟩
  · exact isOpen_iUnion fun _ => Metric.isOpen_ball
  · intro m hm
    exact Set.mem_iUnion.mpr
      ⟨⟨m, hm⟩, Metric.mem_ball_self (hLocalTub m hm).choose_spec.1⟩
  · intro x hx
    obtain ⟨⟨m, hm⟩, hxm⟩ := Set.mem_iUnion.mp hx
    exact (hLocalTub m hm).choose_spec.2.1 hxm
  · exact ⟨isOpen_iUnion fun _ => Metric.isOpen_ball,
      fun m hm => Set.mem_iUnion.mpr
        ⟨⟨m, hm⟩, Metric.mem_ball_self (hLocalTub m hm).choose_spec.1⟩,
      fun x hx => by
        obtain ⟨⟨m, hm⟩, hxm⟩ := Set.mem_iUnion.mp hx
        exact (hLocalTub m hm).choose_spec.2.2 x hxm⟩

private lemma argminSet_eq_localMinSet {d : ℕ} {f : E d → ℝ} {m : E d}
    (hm : m ∈ argminSet f) :
    ∀ x, x ∈ argminSet f ↔ x ∈ localMinSet f m := by
  intro x
  constructor
  · intro hx
    exact ⟨Filter.univ_mem' (fun y => hx y), le_antisymm (hx m) (hm x)⟩
  · intro ⟨_, hfx⟩ y
    rw [hfx]
    exact hm y

private lemma projection_iff_graph {d : ℕ} {V : Submodule ℝ (E d)}
    (φ : V → V.orthogonal) (m x : E d) :
    (V.orthogonal.orthogonalProjectionOnto (x - m) : E d) =
      ((φ (V.orthogonalProjectionOnto (x - m))) : E d) ↔
    ∃ v : V, x = m + (v : E d) + ((φ v) : E d) := by
  constructor
  · intro h
    refine ⟨V.orthogonalProjectionOnto (x - m), ?_⟩
    have decomp := V.starProjection_add_starProjection_orthogonal (x - m)
    simp only [Submodule.starProjection_apply] at decomp
    rw [h] at decomp
    have hsub : x - m = ↑(V.orthogonalProjectionOnto (x - m)) +
        ↑(φ (V.orthogonalProjectionOnto (x - m))) := decomp.symm
    rw [sub_eq_iff_eq_add'] at hsub
    rw [add_assoc]
    exact hsub
  · intro ⟨v, hv⟩
    have hxm : x - m = (v : E d) + ((φ v) : E d) := by
      rw [hv, add_assoc, add_sub_cancel_left]
    have hproj_v : V.orthogonalProjectionOnto (x - m) = v := by
      have hφ_proj : V.orthogonalProjectionOnto (φ v : E d) = 0 :=
        Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr (Submodule.coe_mem (φ v))
      rw [hxm, map_add,
        Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v,
        hφ_proj, add_zero]
    have decomp := V.starProjection_add_starProjection_orthogonal (x - m)
    simp only [Submodule.starProjection_apply] at decomp
    rw [congrArg Subtype.val hproj_v] at decomp
    have key : (↑(V.orthogonal.orthogonalProjectionOnto (x - m)) : E d) =
        ((φ v) : E d) := add_left_cancel (decomp.trans hxm)
    rw [hproj_v]
    exact key

/-- C³+PL gives a global C² graph chart for the global minimizer set near each
    minimizer. -/
private theorem c3_pl_argmin_global_graph
    {d : ℕ} (_hd : 0 < d)
    {f : E d → ℝ} {μ : ℝ}
    {U : Set (E d)} (hU_open : IsOpen U) (hS_sub : argminSet f ⊆ U)
    (hPL : PolyakLojasiewicz f μ U) (hf_C3 : ContDiffOn ℝ 3 f U)
    (m : E d) (hm : m ∈ argminSet f) :
    ∃ (V : Submodule ℝ (E d)) (φ : V → V.orthogonal) (δ : ℝ),
      0 < δ ∧ ContDiff ℝ 2 φ ∧ φ 0 = 0 ∧ fderiv ℝ φ 0 = 0 ∧
      ∀ x ∈ Metric.ball m δ,
        x ∈ argminSet f ↔ ∃ v : V, x = m + (v : E d) + (φ v : E d) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, _hd⟩⟩
  set V := hessianKer f m
  have hm_U : m ∈ U := hS_sub hm
  have hf3_at : ContDiffAt ℝ 3 f m := hf_C3.contDiffAt (hU_open.mem_nhds hm_U)
  have hmin : IsLocalMin f m := Filter.univ_mem' (fun y => hm y)
  have hPL_ext : ExternalThm3.PolyakLojasiewicz f μ U :=
    ⟨hPL.1, fun x hxU => by
      have h := hPL.2.2 x hxU
      have hnorm : ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
        (InnerProductSpace.toDual ℝ (E d)).symm.norm_map (fderiv ℝ f x)
      rwa [hnorm] at h⟩
  have hmuPL : MuPL f μ m :=
    ExternalThm3.pl_to_muPL f μ U m hm (hU_open.mem_nhds hm_U) hPL_ext
  obtain ⟨_, Uloc, hUloc, φ_raw, hφ_raw_C2, hφ_raw0, hDφ_raw0, hGraph⟩ :=
    MuPL.implies_submanifold_C2_chart f μ m hPL.1 hf3_at hmin hmuPL
  have hφ_raw_ev : ∀ᶠ v in 𝓝 (0 : V), ContDiffAt ℝ 2 φ_raw v :=
    hφ_raw_C2.eventually (by norm_num)
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.eventually_nhds_iff.mp hφ_raw_ev
  let bump : ContDiffBump (0 : V) :=
    { rIn := ε / 3
      rOut := ε / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  set φ : V → V.orthogonal := fun v => bump v • φ_raw v with hφ_def
  have hφ_eq_raw_near : φ =ᶠ[𝓝 0] φ_raw := by
    filter_upwards [bump.eventuallyEq_one] with v hv
    change bump v • φ_raw v = φ_raw v
    have hbv : (↑bump : V → ℝ) v = 1 := by simpa using hv
    rw [hbv, one_smul]
  obtain ⟨r_eq, hr_eq_pos, hr_eq⟩ := Metric.eventually_nhds_iff.mp hφ_eq_raw_near
  have hφ0 : φ 0 = 0 := by
    change bump 0 • φ_raw 0 = 0
    rw [hφ_raw0, smul_zero]
  have hφ_smooth : ContDiff ℝ 2 φ := by
    rw [contDiff_iff_contDiffAt]
    intro v
    by_cases hv : v ∈ tsupport (↑bump : V → ℝ)
    · have hv_dist : dist v 0 < ε := by
        have hmem : v ∈ Metric.closedBall (0 : V) (ε / 2) := bump.tsupport_eq ▸ hv
        exact lt_of_le_of_lt (Metric.mem_closedBall.mp hmem) (by linarith)
      exact (bump.contDiff (n := 2)).contDiffAt.smul (hε_ball hv_dist)
    · have hφ_eq_zero : φ =ᶠ[𝓝 v] (fun _ : V => (0 : V.orthogonal)) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hv] with w hw
        change bump w • φ_raw w = (0 : V.orthogonal)
        have hbw : (↑bump : V → ℝ) w = 0 := by simpa using hw
        rw [hbw, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hφ_eq_zero
  have hDφ0 : fderiv ℝ φ 0 = 0 := by
    rw [hφ_eq_raw_near.fderiv_eq]
    exact hDφ_raw0
  obtain ⟨δ_loc, hδ_loc_pos, hδ_loc_sub⟩ := Metric.mem_nhds_iff.mp hUloc
  set δ := min δ_loc r_eq with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ_loc_pos hr_eq_pos
  refine ⟨V, φ, δ, hδ_pos, hφ_smooth, hφ0, hDφ0, ?_⟩
  intro x hx
  have hx_dist : dist x m < δ := Metric.mem_ball.mp hx
  have hx_Uloc : x ∈ Uloc :=
    hδ_loc_sub (lt_of_lt_of_le hx_dist (min_le_left _ _))
  have hproj_near :
      dist (V.orthogonalProjectionOnto (x - m)) (0 : V) < r_eq := by
    calc dist (V.orthogonalProjectionOnto (x - m)) (0 : V)
        = ‖V.orthogonalProjectionOnto (x - m)‖ := dist_zero_right _
      _ ≤ ‖x - m‖ := Submodule.norm_orthogonalProjectionOnto_apply_le V (x - m)
      _ = dist x m := by rw [dist_eq_norm]
      _ < r_eq := lt_of_lt_of_le hx_dist (min_le_right _ _)
  have hφ_proj : φ (V.orthogonalProjectionOnto (x - m)) =
      φ_raw (V.orthogonalProjectionOnto (x - m)) := hr_eq hproj_near
  constructor
  · intro hxS
    have hxLocal : x ∈ localMinSet f m := (argminSet_eq_localMinSet hm x).mp hxS
    have hproj_raw := (hGraph x hx_Uloc).mp hxLocal
    have hproj : (V.orthogonal.orthogonalProjectionOnto (x - m) : E d) =
        (φ (V.orthogonalProjectionOnto (x - m)) : E d) := by
      simpa only [V, hφ_proj] using hproj_raw
    exact (projection_iff_graph φ m x).mp hproj
  · intro ⟨v, hv⟩
    have hv_near : dist v 0 < r_eq :=
      lt_of_le_of_lt (graph_param_dist_le m x v hv)
        (lt_of_lt_of_le hx_dist (min_le_right _ _))
    have hφ_v : φ v = φ_raw v := hr_eq hv_near
    have hv_raw : x = m + (v : E d) + (φ_raw v : E d) := by
      rwa [hφ_v] at hv
    have hproj_raw := (projection_iff_graph φ_raw m x).mpr ⟨v, hv_raw⟩
    exact (argminSet_eq_localMinSet hm x).mpr ((hGraph x hx_Uloc).mpr hproj_raw)

private theorem local_tubular_of_c3_pl
    {d : ℕ} (hd : 0 < d)
    {f : E d → ℝ} {μ : ℝ}
    {U : Set (E d)} (hU_open : IsOpen U) (hS_sub : argminSet f ⊆ U)
    (hPL : PolyakLojasiewicz f μ U) (hf_C3 : ContDiffOn ℝ 3 f U)
    (m : E d) (hm : m ∈ argminSet f) :
    ∃ r > 0, Metric.ball m r ⊆ U ∧
      ∀ x ∈ Metric.ball m r,
        ∃! p, p ∈ argminSet f ∧ dist x p = Metric.infDist x (argminSet f) := by
  obtain ⟨V, φ, δ, hδ, hφC2, hφ0, hDφ0, hchart⟩ :=
    c3_pl_argmin_global_graph hd hU_open hS_sub hPL hf_C3 m hm
  exact local_tubular_of_graph_chart hU_open hS_sub hm hδ hφC2 hφ0 hDφ0 hchart

/-- C³+PL on an open neighborhood of the minimizer set gives a smaller tubular
    sub-neighborhood of the minimizer set. -/
theorem exists_tubular_subneighborhood_of_c3_pl
    {d : ℕ} (hd : 0 < d)
    {f : E d → ℝ} {μ : ℝ}
    {U : Set (E d)} (hU_open : IsOpen U) (hS_sub : argminSet f ⊆ U)
    (hPL : PolyakLojasiewicz f μ U) (hf_C3 : ContDiffOn ℝ 3 f U) :
    ∃ U' : Set (E d),
      IsOpen U' ∧ argminSet f ⊆ U' ∧ U' ⊆ U ∧
      IsGeneralTubularNeighborhood (argminSet f) U' ∧
      IsTubularNeighborhoodOfSubmanifold (argminSet f) U' := by
  obtain ⟨U', hU'_open, hS_sub_U', hU'_sub, hGenTub⟩ :=
    local_tubular_to_general
      (fun m hm => local_tubular_of_c3_pl hd hU_open hS_sub hPL hf_C3 m hm)
  refine ⟨U', hU'_open, hS_sub_U', hU'_sub, hGenTub, ?_⟩
  exact {
    isOpen := hU'_open
    subset := hS_sub_U'
    uniqueProj := hGenTub.uniqueProj
    submanifold_chart := by
      intro m hm
      exact c3_pl_argmin_global_graph hd hU_open hS_sub hPL hf_C3 m hm
  }

/-- A C² smooth embedded submanifold contained in an open set admits a smaller
    general tubular neighborhood contained in that open set. -/
theorem exists_general_tubular_subneighborhood
    {d n : ℕ}
    (M : Type*) [TopologicalSpace M] [ChartedSpace (ManifoldModel n) M]
    [IsManifold (modelI n) 2 M]
    (ι : M → E d)
    (hι : IsSmoothEmbedding (modelI n) (modelWithCornersSelf ℝ (E d)) 2 ι)
    (U : Set (E d)) (hU_open : IsOpen U) (hS_sub : Set.range ι ⊆ U) :
    ∃ (U' : Set (E d)),
      IsOpen U' ∧ Set.range ι ⊆ U' ∧ U' ⊆ U ∧
      IsGeneralTubularNeighborhood (Set.range ι) U' :=
  local_tubular_to_general
    (fun m hm => local_tubular_of_smooth_embedding M ι hι hU_open hS_sub m hm)

/-- For compact C² embedded submanifolds, a general tubular neighborhood
    can be refined to a metric tubular neighborhood with C² chart structure. -/
theorem general_to_metric_tubular
    {d n : ℕ}
    (M : Type*) [TopologicalSpace M] [ChartedSpace (ManifoldModel n) M]
    [IsManifold (modelI n) 2 M] [CompactSpace M] [Nonempty M]
    (ι : M → E d)
    (hι : IsSmoothEmbedding (modelI n) (modelWithCornersSelf ℝ (E d)) 2 ι)
    (U : Set (E d))
    (hU : IsGeneralTubularNeighborhood (Set.range ι) U) :
    ∃ (U' : Set (E d)),
      IsOpen U' ∧ Set.range ι ⊆ U' ∧ U' ⊆ U ∧
      IsTubularNeighborhoodOfSubmanifold (Set.range ι) U' := by
  set S := Set.range ι
  have hK : IsCompact S := isCompact_range_of_smoothEmbedding M ι hι
  have hKne : S.Nonempty := Set.range_nonempty ι
  obtain ⟨r_U, hr_U_pos, hr_U_sub⟩ :=
    exists_metric_tube_subset hK hKne hU.isOpen hU.subset
  set U' := {x : E d | Metric.infDist x S < r_U}
  refine ⟨U', ?_, ?_, ?_, ?_⟩
  · exact isOpen_lt (Metric.continuous_infDist_pt _) continuous_const
  · intro x hx
    change Metric.infDist x S < r_U
    rw [Metric.infDist_zero_of_mem hx]; exact hr_U_pos
  · exact hr_U_sub
  · exact {
      isOpen := isOpen_lt (Metric.continuous_infDist_pt _) continuous_const
      subset := fun x hx => by
        change Metric.infDist x S < r_U
        rw [Metric.infDist_zero_of_mem hx]; exact hr_U_pos
      uniqueProj := fun x (hx : Metric.infDist x S < r_U) =>
        hU.uniqueProj x (hr_U_sub hx)
      submanifold_chart := by
        intro m hm
        obtain ⟨p, rfl⟩ := hm
        exact smooth_embedding_local_graph M ι hι (ι p) ⟨p, rfl⟩
    }

/-- For C² embedded submanifolds, a general tubular neighborhood yields
    `IsTubularNeighborhoodOfSubmanifold` — the submanifold charts come
    from the pointwise IFT. -/
theorem general_tubular_of_smooth_embedding
    {d n : ℕ}
    (M : Type*) [TopologicalSpace M] [ChartedSpace (ManifoldModel n) M]
    [IsManifold (modelI n) 2 M]
    (ι : M → E d)
    (hι : IsSmoothEmbedding (modelI n) (modelWithCornersSelf ℝ (E d)) 2 ι)
    (U : Set (E d))
    (hU : IsGeneralTubularNeighborhood (Set.range ι) U) :
    IsTubularNeighborhoodOfSubmanifold (Set.range ι) U where
  isOpen := hU.isOpen
  subset := hU.subset
  uniqueProj := hU.uniqueProj
  submanifold_chart := by
    intro m hm; obtain ⟨p, rfl⟩ := hm
    exact smooth_embedding_local_graph M ι hι (ι p) ⟨p, rfl⟩

end PLAcceleratedNesterovLean
