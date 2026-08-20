/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Triangulation

/-!
# Fixed-vertex stars in a surface triangulation

A geometric triangulation of a topological surface has connected links.  The proof uses a
punctured surface chart inside the open barycentric star of a vertex.  If the fixed-vertex star
had two adjacency components, their finite closed face unions would separate that punctured
chart.
-/

open Set Topology
open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

namespace GeometricTriangulation

variable {S : Type*} [TopologicalSpace S] (T : GeometricTriangulation S)

private noncomputable def realizationVertex
    (v : T.Vertex) (f : T.Triangle) (hvf : v ∈ f.1) :
    T.realization :=
  ⟨Pi.single v 1, single_mem_stdSimplex ℝ v, by
    refine ⟨f.1, f.2, ?_⟩
    intro w hw
    have hwv : w ≠ v := by
      intro h
      subst w
      exact hw hvf
    simp [hwv]⟩

@[simp]
private theorem realizationVertex_val
    (v : T.Vertex) (f : T.Triangle) (hvf : v ∈ f.1) :
    (T.realizationVertex v f hvf).1 = Pi.single v 1 :=
  rfl

private noncomputable def approachRatio (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (1 / ((n : ℝ) + 1))

private theorem approachRatio_pos (n : ℕ) : 0 < approachRatio n := by
  unfold approachRatio
  positivity

private theorem approachRatio_lt_one (n : ℕ) : approachRatio n < 1 := by
  unfold approachRatio
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 := by
    exact (div_le_one (by positivity)).2 hn
  nlinarith

private theorem tendsto_approachRatio :
    Filter.Tendsto approachRatio Filter.atTop (𝓝 0) := by
  unfold approachRatio
  simpa only [mul_zero] using
    (tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1))
          Filter.atTop (𝓝 0)))

private noncomputable def approachPoint
    (v w : T.Vertex) (f : T.Triangle) (hvf : v ∈ f.1) (hwf : w ∈ f.1)
    (n : ℕ) : T.realization :=
  ⟨AffineMap.lineMap (k := ℝ)
      (Pi.single v (1 : ℝ) : T.Vertex → ℝ)
      (Pi.single w (1 : ℝ) : T.Vertex → ℝ) (approachRatio n), by
    have hr : approachRatio n ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨(approachRatio_pos n).le, (approachRatio_lt_one n).le⟩
    have hstd :
        AffineMap.lineMap (k := ℝ)
          (Pi.single v (1 : ℝ) : T.Vertex → ℝ)
          (Pi.single w (1 : ℝ) : T.Vertex → ℝ) (approachRatio n) ∈
          stdSimplex ℝ T.Vertex :=
      (convex_stdSimplex ℝ T.Vertex).lineMap_mem
        (single_mem_stdSimplex ℝ v) (single_mem_stdSimplex ℝ w) hr
    refine ⟨hstd, f.1, f.2, ?_⟩
    intro u hu
    have huv : u ≠ v := fun h ↦ hu (h ▸ hvf)
    have huw : u ≠ w := fun h ↦ hu (h ▸ hwf)
    simp [AffineMap.lineMap_apply, huv, huw]⟩

private theorem tendsto_approachPoint
    (v w : T.Vertex) (f : T.Triangle) (hvf : v ∈ f.1) (hwf : w ∈ f.1) :
    Filter.Tendsto (T.approachPoint v w f hvf hwf)
      Filter.atTop (𝓝 (T.realizationVertex v f hvf)) := by
  rw [tendsto_subtype_rng]
  change Filter.Tendsto
    (fun n ↦
      AffineMap.lineMap (k := ℝ)
        (Pi.single v (1 : ℝ) : T.Vertex → ℝ)
        (Pi.single w (1 : ℝ) : T.Vertex → ℝ) (approachRatio n))
    Filter.atTop (𝓝 (Pi.single v 1))
  have hcontinuous :
      Continuous
        (AffineMap.lineMap (k := ℝ)
          (Pi.single v (1 : ℝ) : T.Vertex → ℝ)
          (Pi.single w (1 : ℝ) : T.Vertex → ℝ)) :=
    AffineMap.lineMap_continuous
  simpa [Function.comp_def] using
    hcontinuous.continuousAt.tendsto.comp tendsto_approachRatio

private theorem approachPoint_mem_faceCarrier
    (v w : T.Vertex) (f : T.Triangle) (hvf : v ∈ f.1) (hwf : w ∈ f.1)
    (n : ℕ) :
    T.approachPoint v w f hvf hwf n ∈ T.toIntrinsic.faceCarrier f.1 := by
  intro u hu
  have huv : u ≠ v := fun h ↦ hu (h ▸ hvf)
  have huw : u ≠ w := fun h ↦ hu (h ▸ hwf)
  simp [approachPoint, AffineMap.lineMap_apply, huv, huw]

private theorem approachPoint_ne_vertex
    (v w : T.Vertex) (f : T.Triangle) (hvf : v ∈ f.1) (hwf : w ∈ f.1)
    (hvw : v ≠ w) (n : ℕ) :
    T.approachPoint v w f hvf hwf n ≠ T.realizationVertex v f hvf := by
  intro h
  have hcoord := congrArg (fun x : T.realization ↦ x.1 w) h
  have hwv : w ≠ v := Ne.symm hvw
  simp [approachPoint, AffineMap.lineMap_apply, realizationVertex, hwv,
    approachRatio_pos n |>.ne'] at hcoord

private theorem approachPoint_mem_openStar
    (v w : T.Vertex) (f : T.Triangle) (hvf : v ∈ f.1) (hwf : w ∈ f.1)
    (hvw : v ≠ w) (n : ℕ) :
    0 < (T.approachPoint v w f hvf hwf n).1 v := by
  have hwv : w ≠ v := Ne.symm hvw
  simp only [approachPoint, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, ne_eq, hwv, not_false_eq_true, Pi.single_eq_of_ne',
    Pi.single_eq_same, zero_sub, smul_eq_mul, mul_neg, mul_one, lt_neg_add_iff_add_lt, add_zero,
    gt_iff_lt]
  exact approachRatio_lt_one n

private theorem exists_other_vertex
    (v : T.Vertex) (f : T.Triangle) (_hvf : v ∈ f.1) :
    ∃ w ∈ f.1, v ≠ w := by
  have hcard : 1 < f.1.card := by
    rw [T.triangle_card f]
    decide
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  by_cases hav : a = v
  · exact ⟨b, hb, fun hvb ↦ hab (hav.trans hvb)⟩
  · exact ⟨a, ha, Ne.symm hav⟩

private theorem card_inter_le_one_of_not_reachable
    (v : T.Vertex) (root q r : T.Triangle)
    (hvq : v ∈ q.1) (hvr : v ∈ r.1)
    (hq :
      Relation.ReflTransGen
        (TriangleFamily.FaceAdjacentAtVertex T.faces v) root q)
    (hr :
      ¬ Relation.ReflTransGen
        (TriangleFamily.FaceAdjacentAtVertex T.faces v) root r) :
    (q.1 ∩ r.1).card ≤ 1 := by
  by_contra hcard
  have hlt : 1 < (q.1 ∩ r.1).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
  let w := if a = v then b else a
  have hwinter : w ∈ q.1 ∩ r.1 := by
    dsimp [w]
    split
    · exact hb
    · exact ha
  have hvw : v ≠ w := by
    dsimp [w]
    split
    next h =>
      intro hvb
      exact hab (h.trans hvb)
    next h => exact Ne.symm h
  have hadj :
      TriangleFamily.FaceAdjacentAtVertex T.faces v q r := by
    refine ⟨{v, w}, by simp [hvw], by simp, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hvq
      · exact (Finset.mem_inter.mp hwinter).1
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hvr
      · exact (Finset.mem_inter.mp hwinter).2
  exact hr (hq.tail hadj)

private theorem vertexPoint_eq_realizationVertex_of_positive
    (v : T.Vertex) (f : T.Triangle) (hvf : v ∈ f.1)
    (u : T.toIntrinsic.UsedVertex)
    (hpos : 0 < (T.toIntrinsic.vertexPoint u).1 v) :
    T.toIntrinsic.vertexPoint u = T.realizationVertex v f hvf := by
  have huv : u.1 = v := by
    by_contra hne
    have : (T.toIntrinsic.vertexPoint u).1 v = 0 := by
      simp [Moise.IntrinsicTwoComplex.vertexPoint, hne]
    linarith
  apply Subtype.ext
  simp [Moise.IntrinsicTwoComplex.vertexPoint, realizationVertex, huv]

/-- Every fixed-vertex face star in a geometric triangulation of a topological surface is
connected through edges containing that vertex. -/
theorem faces_isStrongVertexStarConnected
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    let _ := (inferInstance : IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S)
    TriangleFamily.IsStrongVertexStarConnected T.faces := by
  dsimp
  classical
  intro v f g hvf hvg
  let Adj :=
    TriangleFamily.FaceAdjacentAtVertex T.faces v
  by_cases hfg : Relation.ReflTransGen Adj f g
  · exact hfg
  let pR : T.realization := T.realizationVertex v f hvf
  let U : TopologicalSpace.Opens S :=
    ⟨{x | 0 < (T.homeo.symm x).1 v}, by
      exact isOpen_lt continuous_const
        ((continuous_apply v).comp
          (continuous_subtype_val.comp T.homeo.symm.continuous))⟩
  let p : U := ⟨T.homeo pR, by
    change 0 < (T.homeo.symm (T.homeo pR)).1 v
    simp [pR, realizationVertex]⟩
  obtain ⟨c, _hcfaithful, hcore⟩ :=
    Moise.exists_moiseChart_core_mem_nhds U p
  have hpDomain : p ∈ c.domain :=
    c.core_subset_domain (mem_of_mem_nhds hcore)
  let W : Set U := c.domain \ {p}
  have hWpath : IsPathConnected W := by
    exact c.isPathConnected_domain_diff_finite {p} (Set.finite_singleton p)
  let Reach : T.Triangle → Prop :=
    fun q ↦ Relation.ReflTransGen Adj f q
  let C : T.Triangle → Set U :=
    fun q ↦ {z | T.homeo.symm z.1 ∈ T.toIntrinsic.faceCarrier q.1}
  have hCclosed (q : T.Triangle) : IsClosed (C q) := by
    exact (T.toIntrinsic.faceCarrier_closed q.1).preimage
      (T.homeo.symm.continuous.comp continuous_subtype_val)
  let A : Set U := ⋃ q ∈ {q | Reach q}, C q
  let B : Set U := ⋃ q ∈ {q | ¬ Reach q}, C q
  have hAclosed : IsClosed A := by
    exact Set.toFinite {q | Reach q} |>.isClosed_biUnion
      (fun q _ ↦ hCclosed q)
  have hBclosed : IsClosed B := by
    exact Set.toFinite {q | ¬ Reach q} |>.isClosed_biUnion
      (fun q _ ↦ hCclosed q)
  have hWcover : W ⊆ A ∪ B := by
    intro z hz
    let x : T.realization := T.homeo.symm z.1
    rcases x.2.2 with ⟨q, hq, hxq⟩
    let q' : T.Triangle := ⟨q, hq⟩
    by_cases hreach : Reach q'
    · left
      exact Set.mem_iUnion₂_of_mem hreach hxq
    · right
      exact Set.mem_iUnion₂_of_mem hreach hxq
  have hWdisjoint : ∀ z ∈ W, ¬ (z ∈ A ∧ z ∈ B) := by
    intro z hzW hzAB
    rcases hzAB with ⟨hzA, hzB⟩
    simp only [A, B, Set.mem_iUnion, exists_prop] at hzA hzB
    obtain ⟨q, hqReach, hzq⟩ := hzA
    obtain ⟨r, hrReach, hzr⟩ := hzB
    have hzpos : 0 < (T.homeo.symm z.1).1 v := z.2
    have hvq : v ∈ q.1 := by
      by_contra hv
      have hzzero := hzq v hv
      linarith
    have hvr : v ∈ r.1 := by
      by_contra hv
      have hzzero := hzr v hv
      linarith
    have hcard : (q.1 ∩ r.1).card ≤ 1 :=
      T.card_inter_le_one_of_not_reachable v f q r hvq hvr hqReach hrReach
    have hzinter :
        T.homeo.symm z.1 ∈ T.toIntrinsic.faceCarrier (q.1 ∩ r.1) := by
      rw [← T.toIntrinsic.faceCarrier_inter]
      exact ⟨hzq, hzr⟩
    obtain ⟨u, hu⟩ :=
      T.toIntrinsic.exists_eq_vertexPoint_of_mem_faceCarrier_of_card_le_one
        q Finset.inter_subset_left hcard hzinter
    have huPos : 0 < (T.toIntrinsic.vertexPoint u).1 v := by
      rw [← hu]
      exact hzpos
    have hup :
        T.toIntrinsic.vertexPoint u = T.realizationVertex v f hvf :=
      T.vertexPoint_eq_realizationVertex_of_positive v f hvf u huPos
    have hzR : T.homeo.symm z.1 = pR := by
      exact hu.trans hup
    have hzp : z = p := by
      apply Subtype.ext
      apply T.homeo.symm.injective
      simpa [p] using hzR
    exact hzW.2 (by simp [hzp])
  have exists_face_point (q : T.Triangle) (hvq : v ∈ q.1) :
      ∃ z : U, z ∈ W ∧ z ∈ C q := by
    obtain ⟨w, hwq, hvw⟩ := T.exists_other_vertex v q hvq
    let zseq : ℕ → U := fun n ↦
      ⟨T.homeo (T.approachPoint v w q hvq hwq n), by
        change 0 <
          (T.homeo.symm (T.homeo (T.approachPoint v w q hvq hwq n))).1 v
        simpa using T.approachPoint_mem_openStar v w q hvq hwq hvw n⟩
    have hzseq : Filter.Tendsto zseq Filter.atTop (𝓝 p) := by
      rw [tendsto_subtype_rng]
      have h :=
        T.homeo.continuous.continuousAt.tendsto.comp
          (T.tendsto_approachPoint v w q hvq hwq)
      have h' :
          Filter.Tendsto
            (fun n ↦ T.homeo (T.approachPoint v w q hvq hwq n))
            Filter.atTop
            (𝓝 (T.homeo (T.realizationVertex v q hvq))) := by
        simpa only [Function.comp_def] using h
      convert h' using 1
      simp [p, pR, realizationVertex]
    have heventually : ∀ᶠ n in Filter.atTop, zseq n ∈ c.domain :=
      hzseq (c.isOpen_domain.mem_nhds hpDomain)
    obtain ⟨n, hn⟩ := heventually.exists
    refine ⟨zseq n, ⟨hn, ?_⟩, ?_⟩
    · intro hnp
      have hval : (zseq n).1 = p.1 :=
        congrArg Subtype.val (Set.mem_singleton_iff.mp hnp)
      have hhomeo :
          T.homeo (T.approachPoint v w q hvq hwq n) =
            T.homeo (T.realizationVertex v q hvq) := by
        simpa [zseq, p, pR, realizationVertex] using hval
      exact T.approachPoint_ne_vertex v w q hvq hwq hvw n
        (T.homeo.injective hhomeo)
    · change T.homeo.symm (zseq n).1 ∈ T.toIntrinsic.faceCarrier q.1
      simpa [zseq] using T.approachPoint_mem_faceCarrier v w q hvq hwq n
  obtain ⟨za, hzaW, hzaC⟩ := exists_face_point f hvf
  obtain ⟨zb, hzbW, hzbC⟩ := exists_face_point g hvg
  have hfReach : Reach f := Relation.ReflTransGen.refl
  have hzaA : za ∈ A := Set.mem_iUnion₂_of_mem hfReach hzaC
  have hzgNotReach : ¬ Reach g := hfg
  have hzbB : zb ∈ B := Set.mem_iUnion₂_of_mem hzgNotReach hzbC
  have hzaNotB : za ∉ B :=
    fun hzaB ↦ hWdisjoint za hzaW ⟨hzaA, hzaB⟩
  have hzbNotA : zb ∉ A :=
    fun hzbA ↦ hWdisjoint zb hzbW ⟨hzbA, hzbB⟩
  have hsepCover : W ⊆ Aᶜ ∪ Bᶜ := by
    intro z hzW
    by_cases hzA : z ∈ A
    · exact Or.inr (fun hzB ↦ hWdisjoint z hzW ⟨hzA, hzB⟩)
    · exact Or.inl hzA
  have hleft : (W ∩ Aᶜ).Nonempty := ⟨zb, hzbW, hzbNotA⟩
  have hright : (W ∩ Bᶜ).Nonempty := ⟨za, hzaW, hzaNotB⟩
  obtain ⟨z, hzW, hzA, hzB⟩ :=
    hWpath.isConnected.isPreconnected Aᶜ Bᶜ
      hAclosed.isOpen_compl hBclosed.isOpen_compl
      hsepCover hleft hright
  rcases hWcover hzW with hzA' | hzB'
  · exact (hzA hzA').elim
  · exact (hzB hzB').elim

end GeometricTriangulation

end ClassificationOfSurfaces
end Topology
end LeanEval
