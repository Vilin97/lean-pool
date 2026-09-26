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

public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Section smoothing for vector bundles

This file adds a proof-bearing section-smoothing layer under the repo namespace:

* local-to-global gluing of smooth vector-bundle sections valued in fiberwise
  convex sets;
* smooth approximation of continuous sections of the trivial bundle, including a
  version fixed on a closed smooth locus;
* smooth approximation on open subsets and, from that, local smoothing inside a
  chosen bundle trivialization;
* a global smoothing theorem for continuous bundle sections whose values are
  constrained to an open fiberwise convex subset of the total space;
* an intrinsic fiberwise-`ε` approximation theorem for continuous sections of
  smooth Riemannian vector bundles.
-/

@[expose] public noncomputable section

open Bundle Set Function
open scoped Topology ContDiff Manifold

namespace PoincareCurvature

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, Module ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- Repo-local name for mathlib's partition-of-unity gluing theorem for smooth
sections valued in fiberwise convex sets. -/
theorem exists_contMDiffSection_mem_of_local
    {t : ∀ x, Set (V x)} {n : ℕ∞}
    (ht_conv : ∀ x, Convex ℝ (t x))
    (hlocal :
      ∀ x : M, ∃ U ∈ 𝓝 x, ∃ s_loc : (y : M) → V y,
        CMDiff[U] n (T% s_loc) ∧ ∀ y ∈ U, s_loc y ∈ t y) :
    ∃ g : Cₛ^n⟮I; F, V⟯, ∀ x, g x ∈ t x :=
  exists_contMDiffSection_forall_mem_convex_of_local (I := I) V t ht_conv hlocal

theorem Continuous.exists_contMDiffSection_approx_trivialBundle
    {f : M → F} {ε : M → ℝ} (n : ℕ∞)
    (hf : Continuous f) (hε : Continuous ε) (hε_pos : ∀ x, 0 < ε x) :
    ∃ g : Cₛ^n⟮I; F, Bundle.Trivial M F⟯, ∀ x, dist (g x) (f x) < ε x := by
  obtain ⟨g, hg, _⟩ := hf.exists_contMDiff_approx (I := I) (n := n) hε hε_pos
  refine ⟨⟨g, ?_⟩, hg⟩
  intro x
  exact (Bundle.contMDiffAt_section (IB := I) (n := n) (F := F) (E := Bundle.Trivial M F) x).mpr
    (g.contMDiff x)

theorem Continuous.exists_contMDiffSection_approx_and_eqOn_trivialBundle
    {f : M → F} {ε : M → ℝ} (n : ℕ∞)
    (hf : Continuous f) (hε : Continuous ε) (hε_pos : ∀ x, 0 < ε x)
    {S U : Set M} (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S) (hfU : CMDiff[U] n f) :
    ∃ g : Cₛ^n⟮I; F, Bundle.Trivial M F⟯,
      (∀ x, dist (g x) (f x) < ε x) ∧ EqOn g f S ∧ support g ⊆ support f := by
  obtain ⟨g, hg, hgS, hgsupp⟩ := hf.exists_contMDiff_approx_and_eqOn (I := I) (n := n) hε
    hε_pos hS hU hfU
  refine ⟨⟨g, ?_⟩, hg, hgS, hgsupp⟩
  intro x
  exact (Bundle.contMDiffAt_section (IB := I) (n := n) (F := F) (E := Bundle.Trivial M F) x).mpr
    (g.contMDiff x)

theorem ContinuousOn.exists_contMDiffOn_approx
    {s : Set M} (hs : IsOpen s) {f : M → F} {ε : M → ℝ} (n : ℕ∞)
    [SecondCountableTopology H]
    (hf : ContinuousOn f s) (hε : ContinuousOn ε s) (hε_pos : ∀ x ∈ s, 0 < ε x) :
    ∃ g : M → F, ContMDiffOn I 𝓘(ℝ, F) n g s ∧ ∀ x ∈ s, dist (g x) (f x) < ε x := by
  classical
  let U : TopologicalSpace.Opens M := ⟨s, hs⟩
  haveI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  haveI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (I := I)
  haveI : SecondCountableTopology U := inferInstance
  haveI : LocallyCompactSpace U := U.isOpenEmbedding'.locallyCompactSpace
  haveI : SigmaCompactSpace U := inferInstance
  let fU : U → F := (U : Set M).domRestrict f
  let εU : U → ℝ := (U : Set M).domRestrict ε
  have hfU : Continuous fU := by
    dsimp [fU]
    exact (continuousOn_iff_continuous_domRestrict (f := f) (s := (U : Set M))).mp
      (by simpa [U] using hf)
  have hεU : Continuous εU := by
    dsimp [εU]
    exact (continuousOn_iff_continuous_domRestrict (f := ε) (s := (U : Set M))).mp
      (by simpa [U] using hε)
  have hεU_pos : ∀ x : U, 0 < εU x := fun x ↦ hε_pos x x.2
  obtain ⟨gU, hgU, _⟩ := hfU.exists_contMDiff_approx (I := I) (n := n) hεU hεU_pos
  let g : M → F := fun x ↦ if hx : x ∈ s then gU ⟨x, hx⟩ else 0
  refine ⟨g, ?_, ?_⟩
  · intro x hx
    have hg_restr : ContMDiffAt I 𝓘(ℝ, F) n (fun y : U ↦ g y) ⟨x, hx⟩ := by
      convert gU.contMDiff ⟨x, hx⟩ using 1
      ext y
      simp [g, U]
    exact ((contMDiffAt_subtype_iff (U := U) (f := g) (x := ⟨x, hx⟩)).mp hg_restr).contMDiffWithinAt
  · intro x hx
    simpa [g, hx, U, fU, εU] using hgU ⟨x, hx⟩

theorem Bundle.Trivialization.exists_contMDiffSectionOn_approx
    {n : ℕ∞} (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {U : Set M} (hU : IsOpen U) (hUe : U ⊆ e.baseSet)
    {s : ∀ x, V x} {ε : M → ℝ} [SecondCountableTopology H] [ContMDiffVectorBundle n F V I]
    (hs : ContinuousOn (fun x ↦ (e ⟨x, s x⟩).2) U)
    (hε : ContinuousOn ε U) (hε_pos : ∀ x ∈ U, 0 < ε x) :
    ∃ g : ∀ x, V x, CMDiff[U] n (T% g) ∧
      ∀ x ∈ U, dist ((e ⟨x, g x⟩).2) ((e ⟨x, s x⟩).2) < ε x := by
  classical
  obtain ⟨gcoord, hgcoord_smooth, hgcoord_approx⟩ :=
    ContinuousOn.exists_contMDiffOn_approx
      (I := I) (s := U) (f := fun x ↦ (e ⟨x, s x⟩).2) (ε := ε) hU (n := n) hs hε hε_pos
  let g : ∀ x, V x := fun x ↦ if hx : x ∈ U then e.symm x (gcoord x) else 0
  refine ⟨g, ?_, ?_⟩
  · rw [e.contMDiffOn_section_iff (IB := I) (n := n) hU hUe]
    refine hgcoord_smooth.congr ?_
    intro x hx
    simp [g, hx, hUe hx]
  · intro x hx
    simpa [g, hx, hUe hx] using hgcoord_approx x hx

/-- A continuous section whose graph lies in an open fiberwise convex subset of the total space can
be smoothed while staying inside that subset. -/
theorem exists_contMDiffSection_mem_open_of_convex
    {n : ℕ∞} [SecondCountableTopology H] [ContMDiffVectorBundle n F V I]
    {s : ∀ x, V x} (hs : Continuous (T% s))
    {W : Set (TotalSpace F V)} (hW_open : IsOpen W)
    (hW_conv : ∀ x, Convex ℝ {v : V x | TotalSpace.mk' F x v ∈ W})
    (hsW : ∀ x, TotalSpace.mk' F x (s x) ∈ W) :
    ∃ g : Cₛ^n⟮I; F, V⟯, ∀ x, TotalSpace.mk' F x (g x) ∈ W := by
  let t : ∀ x, Set (V x) := fun x ↦ {v | TotalSpace.mk' F x v ∈ W}
  have hlocal :
      ∀ x : M, ∃ U ∈ 𝓝 x, ∃ s_loc : (y : M) → V y,
        CMDiff[U] n (T% s_loc) ∧ ∀ y ∈ U, s_loc y ∈ t y := by
    intro x
    let e : Trivialization F (π F V) := trivializationAt F V x
    have hxbase : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
    let c : M → F := fun y ↦ (e ⟨y, s y⟩).2
    have hc : ContinuousOn c e.baseSet := by
      have hsec : ContinuousOn (T% s) e.baseSet := hs.continuousOn
      have hcoord : ContinuousOn (fun y ↦ e ⟨y, s y⟩) e.baseSet := by
        refine e.continuousOn.comp hsec ?_
        intro y hy
        simpa [e.mem_source] using hy
      exact continuous_snd.comp_continuousOn hcoord
    have hW_nhds :
        W ∈ 𝓝 (TotalSpace.mk' F x (e.symm x (c x))) := by
      simpa [c, e.symm_apply_apply_mk hxbase (s x)] using hW_open.mem_nhds (hsW x)
    have hpre :
        {p : M × F | TotalSpace.mk' F p.1 (e.symm p.1 p.2) ∈ W} ∈ 𝓝 (x, c x) := by
      have htarget_nhds : e.baseSet ×ˢ (univ : Set F) ∈ 𝓝 (x, c x) := by
        exact prod_mem_nhds_iff.2 ⟨e.open_baseSet.mem_nhds hxbase, by simp⟩
      exact (e.continuousOn_symm.continuousAt htarget_nhds).preimage_mem_nhds hW_nhds
    rcases mem_nhds_prod_iff'.mp hpre with ⟨u, v, hu_open, hxu, hv_open, hcxv, huv⟩
    rcases Metric.mem_nhds_iff.mp (hv_open.mem_nhds hcxv) with ⟨δ, hδpos, hδsub⟩
    let r : ℝ := δ / 2
    have hrpos : 0 < r := by
      dsimp [r]
      linarith
    have hcx : ContinuousAt c x := (hc x hxbase).continuousAt (e.open_baseSet.mem_nhds hxbase)
    have hball : c ⁻¹' Metric.ball (c x) r ∈ 𝓝 x := hcx (Metric.ball_mem_nhds _ hrpos)
    have hnhds : u ∩ e.baseSet ∩ c ⁻¹' Metric.ball (c x) r ∈ 𝓝 x := by
      have hu_nhds : u ∈ 𝓝 x := hu_open.mem_nhds hxu
      have hbase_nhds : e.baseSet ∈ 𝓝 x := e.open_baseSet.mem_nhds hxbase
      have hu_base : u ∩ e.baseSet ∈ 𝓝 x := Filter.inter_mem (f := 𝓝 x) hu_nhds hbase_nhds
      exact Filter.inter_mem (f := 𝓝 x) hu_base hball
    rcases mem_nhds_iff.mp hnhds with ⟨U, hUsub, hUopen, hxU⟩
    have hUu : U ⊆ u := fun y hy ↦ (hUsub hy).1.1
    have hUbase : U ⊆ e.baseSet := fun y hy ↦ (hUsub hy).1.2
    have hUball : U ⊆ c ⁻¹' Metric.ball (c x) r := fun y hy ↦ (hUsub hy).2
    obtain ⟨s_loc, hs_loc_smooth, hs_loc_approx⟩ :=
      Bundle.Trivialization.exists_contMDiffSectionOn_approx
        (I := I) (e := e) (n := n) hUopen hUbase (s := s)
        (ε := fun _ ↦ r) (hc.mono hUbase) continuousOn_const (fun _ _ ↦ hrpos)
    refine ⟨U, IsOpen.mem_nhds hUopen hxU, s_loc, hs_loc_smooth, ?_⟩
    intro y hy
    have hyu : y ∈ u := hUu hy
    have hyball : dist (c y) (c x) < r := by
      simpa [Metric.mem_ball] using hUball hy
    have happrox : dist ((e ⟨y, s_loc y⟩).2) (c y) < r := by
      simpa [r] using hs_loc_approx y hy
    have hcoord : dist ((e ⟨y, s_loc y⟩).2) (c x) < δ := by
      have hsum : dist ((e ⟨y, s_loc y⟩).2) (c x) < r + r := by
        exact lt_of_le_of_lt (dist_triangle _ _ _) (add_lt_add happrox hyball)
      have hrδ : r + r = δ := by
        dsimp [r]
        ring
      simpa [hrδ] using hsum
    have hyv : (e ⟨y, s_loc y⟩).2 ∈ v := hδsub (by simpa [Metric.mem_ball] using hcoord)
    have hpair :
        (y, (e ⟨y, s_loc y⟩).2) ∈ {p : M × F | TotalSpace.mk' F p.1 (e.symm p.1 p.2) ∈ W} :=
      huv ⟨hyu, hyv⟩
    simpa [t, e.symm_apply_apply_mk (hUbase hy) (s_loc y)] using hpair
  simpa [t] using exists_contMDiffSection_mem_of_local (I := I) (V := V) (t := t) hW_conv hlocal

end

section NormedApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- In a smooth normed vector bundle, a continuous section can be approximated by a smooth section
within any positive continuous fiberwise error bound, provided inverse trivializations are locally
bounded in operator norm.  The Riemannian approximation theorem below is the special case where this
local bound is supplied by continuity of the fiber inner products. -/
theorem Continuous.exists_contMDiffSection_approx_of_eventually_norm_symmL_lt
    {n : ℕ∞} [SecondCountableTopology H] [ContMDiffVectorBundle n F V I]
    (hbound : ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt F V x).symmL ℝ y‖ < C)
    {s : ∀ x, V x} {ε : M → ℝ}
    (hs : Continuous (T% s)) (hε : Continuous ε) (hε_pos : ∀ x, 0 < ε x) :
    ∃ g : Cₛ^n⟮I; F, V⟯, ∀ x, dist (g x) (s x) < ε x := by
  classical
  let t : ∀ x, Set (V x) := fun x ↦ Metric.ball (s x) (ε x)
  have ht_conv : ∀ x, Convex ℝ (t x) := fun x ↦ convex_ball (s x) (ε x)
  have hlocal :
      ∀ x : M, ∃ U ∈ 𝓝 x, ∃ s_loc : (y : M) → V y,
        CMDiff[U] n (T% s_loc) ∧ ∀ y ∈ U, s_loc y ∈ t y := by
    intro x
    let e : Trivialization F (π F V) := trivializationAt F V x
    have hxbase : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
    let c : M → F := fun y ↦ (e ⟨y, s y⟩).2
    have hc : ContinuousOn c e.baseSet := by
      have hsec : ContinuousOn (T% s) e.baseSet := hs.continuousOn
      have hcoord : ContinuousOn (fun y ↦ e ⟨y, s y⟩) e.baseSet := by
        refine e.continuousOn.comp hsec ?_
        intro y hy
        simpa [e.mem_source] using hy
      exact continuous_snd.comp_continuousOn hcoord
    obtain ⟨C, hCpos, hCevent⟩ := hbound x
    have hnhds : e.baseSet ∩ {y : M | ‖e.symmL ℝ y‖ < C} ∈ 𝓝 x := by
      exact Filter.inter_mem (f := 𝓝 x) (e.open_baseSet.mem_nhds hxbase) hCevent
    rcases mem_nhds_iff.mp hnhds with ⟨U, hUsub, hUopen, hxU⟩
    have hUbase : U ⊆ e.baseSet := fun y hy ↦ (hUsub hy).1
    have hUC : ∀ y ∈ U, ‖e.symmL ℝ y‖ < C := fun y hy ↦ (hUsub hy).2
    let η : M → ℝ := fun y ↦ C⁻¹ * ε y
    have hη : ContinuousOn η U := continuousOn_const.mul hε.continuousOn
    have hη_pos : ∀ y ∈ U, 0 < η y := by
      intro y hy
      dsimp [η]
      exact mul_pos (inv_pos.mpr hCpos) (hε_pos y)
    obtain ⟨s_loc, hs_loc_smooth, hs_loc_approx⟩ :=
      Bundle.Trivialization.exists_contMDiffSectionOn_approx
        (I := I) (e := e) (n := n) hUopen hUbase (s := s) (ε := η)
        (hc.mono hUbase) hη hη_pos
    refine ⟨U, IsOpen.mem_nhds hUopen hxU, s_loc, hs_loc_smooth, ?_⟩
    intro y hy
    have hybase : y ∈ e.baseSet := hUbase hy
    have hyC : ‖e.symmL ℝ y‖ < C := hUC y hy
    have hcoord : dist ((e ⟨y, s_loc y⟩).2) (c y) < η y := by
      simpa [η, c] using hs_loc_approx y hy
    have hcoord' : ‖(e ⟨y, s_loc y⟩).2 - c y‖ < C⁻¹ * ε y := by
      simpa [η, c, dist_eq_norm] using hcoord
    have hsub :
        s_loc y - s y = e.symmL ℝ y ((e ⟨y, s_loc y⟩).2 - c y) := by
      calc
        s_loc y - s y = e.symmL ℝ y (e.continuousLinearMapAt ℝ y (s_loc y - s y)) := by
          symm
          exact e.symmL_continuousLinearMapAt (R := ℝ) hybase (s_loc y - s y)
        _ = e.symmL ℝ y ((e ⟨y, s_loc y⟩).2 - c y) := by
          congr 1
          rw [map_sub]
          simp [c, Trivialization.linearMapAt_apply, hybase]
    have hdist_le :
        dist (s_loc y) (s y) ≤ ‖e.symmL ℝ y‖ * ‖(e ⟨y, s_loc y⟩).2 - c y‖ := by
      rw [dist_eq_norm]
      calc
        ‖s_loc y - s y‖ = ‖e.symmL ℝ y ((e ⟨y, s_loc y⟩).2 - c y)‖ := by
          rw [hsub]
        _ ≤ ‖e.symmL ℝ y‖ * ‖(e ⟨y, s_loc y⟩).2 - c y‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
    have hmul :
        ‖e.symmL ℝ y‖ * ‖(e ⟨y, s_loc y⟩).2 - c y‖ < C * (C⁻¹ * ε y) := by
      exact mul_lt_mul'' hyC hcoord' (norm_nonneg _) (norm_nonneg _)
    have hcancel : C * (C⁻¹ * ε y) = ε y := by
      calc
        C * (C⁻¹ * ε y) = (C * C⁻¹) * ε y := by ring
        _ = ε y := by rw [mul_inv_cancel₀ hCpos.ne', one_mul]
    have hdist : dist (s_loc y) (s y) < ε y := lt_of_le_of_lt hdist_le (hcancel ▸ hmul)
    simpa [t, Metric.mem_ball] using hdist
  obtain ⟨g, hg⟩ := exists_contMDiffSection_mem_of_local (I := I) (V := V) (t := t) ht_conv hlocal
  exact ⟨g, fun x ↦ by simpa [t, Metric.mem_ball] using hg x⟩

end NormedApprox

section RiemannianApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- In a smooth Riemannian vector bundle, a continuous section can be approximated by a smooth
section within any positive continuous fiberwise error bound. -/
theorem Continuous.exists_contMDiffSection_approx
    {n : ℕ∞} [SecondCountableTopology H] [InnerProductSpace ℝ F]
    [ContMDiffVectorBundle n F V I]
    [IsContMDiffRiemannianBundle I n F V]
    {s : ∀ x, V x} {ε : M → ℝ}
    (hs : Continuous (T% s)) (hε : Continuous ε) (hε_pos : ∀ x, 0 < ε x) :
    ∃ g : Cₛ^n⟮I; F, V⟯, ∀ x, dist (g x) (s x) < ε x := by
  classical
  haveI : IsContinuousRiemannianBundle F V := by
    rcases (inferInstance : IsContMDiffRiemannianBundle I n F V).exists_contMDiff with
      ⟨g, hg, hg_inner⟩
    exact ⟨g, hg.continuous, hg_inner⟩
  let t : ∀ x, Set (V x) := fun x ↦ Metric.ball (s x) (ε x)
  have ht_conv : ∀ x, Convex ℝ (t x) := fun x ↦ convex_ball (s x) (ε x)
  have hlocal :
      ∀ x : M, ∃ U ∈ 𝓝 x, ∃ s_loc : (y : M) → V y,
        CMDiff[U] n (T% s_loc) ∧ ∀ y ∈ U, s_loc y ∈ t y := by
    intro x
    let e : Trivialization F (π F V) := trivializationAt F V x
    have hxbase : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
    let c : M → F := fun y ↦ (e ⟨y, s y⟩).2
    have hc : ContinuousOn c e.baseSet := by
      have hsec : ContinuousOn (T% s) e.baseSet := hs.continuousOn
      have hcoord : ContinuousOn (fun y ↦ e ⟨y, s y⟩) e.baseSet := by
        refine e.continuousOn.comp hsec ?_
        intro y hy
        simpa [e.mem_source] using hy
      exact continuous_snd.comp_continuousOn hcoord
    obtain ⟨C, hCpos, hCevent⟩ := eventually_norm_symmL_trivializationAt_lt (F := F) (E := V) x
    have hnhds : e.baseSet ∩ {y : M | ‖e.symmL ℝ y‖ < C} ∈ 𝓝 x := by
      exact Filter.inter_mem (f := 𝓝 x) (e.open_baseSet.mem_nhds hxbase) hCevent
    rcases mem_nhds_iff.mp hnhds with ⟨U, hUsub, hUopen, hxU⟩
    have hUbase : U ⊆ e.baseSet := fun y hy ↦ (hUsub hy).1
    have hUC : ∀ y ∈ U, ‖e.symmL ℝ y‖ < C := fun y hy ↦ (hUsub hy).2
    let η : M → ℝ := fun y ↦ C⁻¹ * ε y
    have hη : ContinuousOn η U := continuousOn_const.mul hε.continuousOn
    have hη_pos : ∀ y ∈ U, 0 < η y := by
      intro y hy
      dsimp [η]
      exact mul_pos (inv_pos.mpr hCpos) (hε_pos y)
    obtain ⟨s_loc, hs_loc_smooth, hs_loc_approx⟩ :=
      Bundle.Trivialization.exists_contMDiffSectionOn_approx
        (I := I) (e := e) (n := n) hUopen hUbase (s := s) (ε := η)
        (hc.mono hUbase) hη hη_pos
    refine ⟨U, IsOpen.mem_nhds hUopen hxU, s_loc, hs_loc_smooth, ?_⟩
    intro y hy
    have hybase : y ∈ e.baseSet := hUbase hy
    have hyC : ‖e.symmL ℝ y‖ < C := hUC y hy
    have hcoord : dist ((e ⟨y, s_loc y⟩).2) (c y) < η y := by
      simpa [η, c] using hs_loc_approx y hy
    have hcoord' : ‖(e ⟨y, s_loc y⟩).2 - c y‖ < C⁻¹ * ε y := by
      simpa [η, c, dist_eq_norm] using hcoord
    have hsub :
        s_loc y - s y = e.symmL ℝ y ((e ⟨y, s_loc y⟩).2 - c y) := by
      calc
        s_loc y - s y = e.symmL ℝ y (e.continuousLinearMapAt ℝ y (s_loc y - s y)) := by
          symm
          exact e.symmL_continuousLinearMapAt (R := ℝ) hybase (s_loc y - s y)
        _ = e.symmL ℝ y ((e ⟨y, s_loc y⟩).2 - c y) := by
          congr 1
          rw [map_sub]
          simp [c, Trivialization.linearMapAt_apply, hybase]
    have hdist_le :
        dist (s_loc y) (s y) ≤ ‖e.symmL ℝ y‖ * ‖(e ⟨y, s_loc y⟩).2 - c y‖ := by
      rw [dist_eq_norm]
      calc
        ‖s_loc y - s y‖ = ‖e.symmL ℝ y ((e ⟨y, s_loc y⟩).2 - c y)‖ := by
          rw [hsub]
        _ ≤ ‖e.symmL ℝ y‖ * ‖(e ⟨y, s_loc y⟩).2 - c y‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
    have hmul :
        ‖e.symmL ℝ y‖ * ‖(e ⟨y, s_loc y⟩).2 - c y‖ < C * (C⁻¹ * ε y) := by
      exact mul_lt_mul'' hyC hcoord' (norm_nonneg _) (norm_nonneg _)
    have hcancel : C * (C⁻¹ * ε y) = ε y := by
      calc
        C * (C⁻¹ * ε y) = (C * C⁻¹) * ε y := by ring
        _ = ε y := by rw [mul_inv_cancel₀ hCpos.ne', one_mul]
    have hdist : dist (s_loc y) (s y) < ε y := lt_of_le_of_lt hdist_le (hcancel ▸ hmul)
    simpa [t, Metric.mem_ball] using hdist
  obtain ⟨g, hg⟩ := exists_contMDiffSection_mem_of_local (I := I) (V := V) (t := t) ht_conv hlocal
  exact ⟨g, fun x ↦ by simpa [t, Metric.mem_ball] using hg x⟩

end RiemannianApprox

end PoincareCurvature
