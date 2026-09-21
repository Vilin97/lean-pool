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

public import LeanPool.PoincareGeometry.LichnerowiczObata.DenseRegionConnected
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Connected complements of finite sets in manifolds -/

@[expose] public noncomputable section
open Set Manifold Topology
open scoped Topology ContDiff

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]

include I in
/-- A boundaryless chart can be shrunk and parameterized by the entire
model vector space using the open-ball homeomorphism. -/
theorem exists_openEmbedding_model_neighborhood (x : M) :
    ∃ g : E → M, IsOpenEmbedding g ∧ x ∈ range g := by
  let φ := extChartAt I x
  let e : OpenPartialHomeomorph M E :=
    { toPartialEquiv := φ
      continuousOn_toFun := continuousOn_extChartAt (I := I) x
      continuousOn_invFun := (contMDiffOn_extChartAt_symm (I := I) (n := 1) x).continuousOn
      open_source := isOpen_extChartAt_source (I := I) x
      open_target := isOpen_extChartAt_target (I := I) x }
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (e.open_target.mem_nhds (e.map_source (mem_extChartAt_source x)))
  let b := OpenPartialHomeomorph.univBall (φ x) r
  let g := b.trans e.symm
  have hsource : g.source = univ := by
    ext z
    simp only [mem_univ, iff_true]
    change z ∈ b.source ∧ b z ∈ e.target
    have hz : z ∈ b.source := by simp only [b, OpenPartialHomeomorph.univBall_source, mem_univ]
    refine ⟨hz, hball ?_⟩
    change b z ∈ Metric.ball (φ x) r
    simpa only [b, OpenPartialHomeomorph.univBall_target _ hr] using b.map_source hz
  refine ⟨g, g.isOpenEmbedding hsource, 0, ?_⟩
  change e.symm (b 0) = x
  rw [OpenPartialHomeomorph.univBall_apply_zero]
  exact φ.left_inv (mem_extChartAt_source x)

omit [ChartedSpace H M] [IsManifold I 1 M] [I.Boundaryless] in
/-- Local open embeddings from a model of dimension greater than one
make the complement of a finite set dense and locally preconnected. -/
theorem finite_compl_local_traces (hdim : 1 < Module.rank ℝ E)
    (hl : ∀ x : M, ∃ g : E → M, IsOpenEmbedding g ∧ x ∈ range g)
    {S : Set M} (hS : S.Finite) :
    Dense Sᶜ ∧ ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ IsPreconnected (U ∩ Sᶜ) := by
  have : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).mp (zero_lt_one.trans hdim)
  constructor
  · intro x
    apply mem_closure_iff.mpr
    intro U hU hxU
    obtain ⟨g, hg, z, hgz⟩ := hl x
    have hc : (g ⁻¹' S).Countable := hS.countable.preimage hg.injective
    have hd : Dense (g ⁻¹' S)ᶜ := hc.dense_compl ℝ
    obtain ⟨w, hwU, hwS⟩ := mem_closure_iff.mp (hd z) (g ⁻¹' U)
      (hU.preimage hg.continuous) (by simpa only [mem_preimage, hgz] using hxU)
    exact ⟨g w, hwU, hwS⟩
  · intro x
    obtain ⟨g, hg, hx⟩ := hl x
    have hc : (g ⁻¹' S).Countable := hS.countable.preimage hg.injective
    have hp := (hc.isPathConnected_compl_of_one_lt_rank hdim).isConnected.isPreconnected.image g
      hg.continuous.continuousOn
    have he : g '' (g ⁻¹' S)ᶜ = range g ∩ Sᶜ := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, rfl⟩, hz⟩
      · rintro ⟨⟨z, rfl⟩, hz⟩
        exact ⟨z, hz, rfl⟩
    exact ⟨range g, hg.isOpen_range, hx, he ▸ hp⟩

include I in
/-- Removing finitely many points from a boundaryless preconnected real
manifold of dimension at least two leaves a dense preconnected region. -/
theorem finite_compl_manifold_preconnected [PreconnectedSpace M]
    (hdim : 1 < Module.rank ℝ E) {S : Set M} (hS : S.Finite) :
    Dense Sᶜ ∧ IsPreconnected Sᶜ := by
  obtain ⟨hd, hl⟩ := finite_compl_local_traces hdim
    (exists_openEmbedding_model_neighborhood (I := I)) hS
  exact ⟨hd, isPreconnected_of_dense_local_traces hd hl⟩

end LichnerowiczObata
