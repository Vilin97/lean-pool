/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.AdaptiveFanComplex

/-!
# The locally finite adaptive fan triangulation

This file packages the conforming adaptive fan faces as the locally finite triangle complex used
in Rado's induction.  Its global vertex type contains exactly the geometric vertices which occur
in a fan face.  This no-junk representation is what lets compactness turn local finiteness into a
finite intrinsic triangulation.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex) (U : Set K.realization)
variable [K.AdaptiveSafety U]
variable [AdaptiveSafety.IsAdmissible (K := K) (U := U)]

/-- Geometric vertices which occur in at least one adaptive fan face. -/
abbrev AdaptiveFanVertex (hU : IsOpen U) :=
  {p : K.realization // ∃ f : K.AdaptiveFanFace U hU,
    p ∈ K.adaptiveFanFaceVertices U hU f}

/-- Include the three local vertices of one fan face in the global used-vertex type. -/
noncomputable def adaptiveFanVertexEmbedding (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    {p // p ∈ K.adaptiveFanFaceVertices U hU f} ↪ K.AdaptiveFanVertex U hU where
  toFun p := ⟨p.1, f, p.2⟩
  inj' := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun z : K.AdaptiveFanVertex U hU ↦ z.1) hpq

/-- The three vertices of a fan face, now regarded as global used vertices. -/
noncomputable def adaptiveGlobalFanFaceVertices (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) : Finset (K.AdaptiveFanVertex U hU) :=
  (K.adaptiveFanFaceVertices U hU f).attach.map
    (K.adaptiveFanVertexEmbedding U hU f)

theorem mem_adaptiveGlobalFanFaceVertices_iff (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) (v : K.AdaptiveFanVertex U hU) :
    v ∈ K.adaptiveGlobalFanFaceVertices U hU f ↔
      v.1 ∈ K.adaptiveFanFaceVertices U hU f := by
  constructor
  · intro hv
    obtain ⟨p, -, hp⟩ := Finset.mem_map.mp hv
    have hval : p.1 = v.1 := congrArg Subtype.val hp
    rw [← hval]
    exact p.2
  · intro hv
    let p : {p // p ∈ K.adaptiveFanFaceVertices U hU f} := ⟨v.1, hv⟩
    apply Finset.mem_map.mpr
    refine ⟨p, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rfl

/-- Relabel the local global vertices of a face by their underlying geometric points. -/
noncomputable def adaptiveFanFaceVertexEquiv (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f} ≃
      {p // p ∈ K.adaptiveFanFaceVertices U hU f} where
  toFun v := ⟨v.1.1,
    (K.mem_adaptiveGlobalFanFaceVertices_iff U hU f v.1).mp v.2⟩
  invFun p := ⟨⟨p.1, ⟨f, p.2⟩⟩,
    (K.mem_adaptiveGlobalFanFaceVertices_iff U hU f _).mpr p.2⟩
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

@[simp] theorem adaptiveFanFaceVertexEquiv_apply_val (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (v : {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f}) :
    (K.adaptiveFanFaceVertexEquiv U hU f v).1 = v.1.1 := rfl

/-- Relabel a simplex on global used vertices as a simplex on the face's geometric vertices. -/
noncomputable def adaptiveFanRelabelSimplex (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f}) :
    stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f} :=
  stdSimplex.map (K.adaptiveFanFaceVertexEquiv U hU f) x

/-- Relabeling preserves the zero-extended coordinate at every global used vertex. -/
theorem adaptiveFanRelabel_extended_apply (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f})
    (v : K.AdaptiveFanVertex U hU) :
    extendFaceCoordinates (K.adaptiveFanFaceVertices U hU f)
        (K.adaptiveFanRelabelSimplex U hU f x) v.1 =
      extendFaceCoordinates (K.adaptiveGlobalFanFaceVertices U hU f) x v := by
  classical
  by_cases hv : v ∈ K.adaptiveGlobalFanFaceVertices U hU f
  · have hp : v.1 ∈ K.adaptiveFanFaceVertices U hU f :=
      (K.mem_adaptiveGlobalFanFaceVertices_iff U hU f v).mp hv
    rw [extendFaceCoordinates_of_mem _ _ hp,
      extendFaceCoordinates_of_mem _ _ hv]
    simp only [adaptiveFanRelabelSimplex, stdSimplex.map_coe,
      FunOnFinite.linearMap_apply_apply]
    let q : {q // q ∈ K.adaptiveGlobalFanFaceVertices U hU f} := ⟨v, hv⟩
    have hfilter : Finset.univ.filter
        (fun z : {z // z ∈ K.adaptiveGlobalFanFaceVertices U hU f} ↦
          K.adaptiveFanFaceVertexEquiv U hU f z = ⟨v.1, hp⟩) = {q} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hz
        have hactual : z.1.1 = q.1.1 := by
          simpa only [K.adaptiveFanFaceVertexEquiv_apply_val U hU f] using
            congrArg
              (fun w : {p // p ∈ K.adaptiveFanFaceVertices U hU f} ↦ w.1) hz
        exact Subtype.ext (Subtype.ext hactual)
      · intro hz
        subst z
        apply Subtype.ext
        rfl
    rw [hfilter]
    simp [q]
  · have hp : v.1 ∉ K.adaptiveFanFaceVertices U hU f := by
      exact fun hp ↦ hv ((K.mem_adaptiveGlobalFanFaceVertices_iff U hU f v).mpr hp)
    rw [extendFaceCoordinates_of_notMem _ _ hp,
      extendFaceCoordinates_of_notMem _ _ hv]

/-- Equality of coordinates is invariant under relabeling a pair of adaptive fan faces. -/
theorem adaptiveFanRelabel_extended_eq_iff (hU : IsOpen U)
    {f g : K.AdaptiveFanFace U hU}
    {x : stdSimplex ℝ {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f}}
    {y : stdSimplex ℝ {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU g}} :
    extendFaceCoordinates (K.adaptiveFanFaceVertices U hU f)
        (K.adaptiveFanRelabelSimplex U hU f x) =
      extendFaceCoordinates (K.adaptiveFanFaceVertices U hU g)
        (K.adaptiveFanRelabelSimplex U hU g y) ↔
    extendFaceCoordinates (K.adaptiveGlobalFanFaceVertices U hU f) x =
      extendFaceCoordinates (K.adaptiveGlobalFanFaceVertices U hU g) y := by
  constructor
  · intro h
    funext v
    rw [← K.adaptiveFanRelabel_extended_apply U hU f x v,
      ← K.adaptiveFanRelabel_extended_apply U hU g y v,
      congrFun h v.1]
  · intro h
    funext p
    by_cases hpf : p ∈ K.adaptiveFanFaceVertices U hU f
    · let v : K.AdaptiveFanVertex U hU := ⟨p, f, hpf⟩
      have hv := congrFun h v
      rw [← K.adaptiveFanRelabel_extended_apply U hU f x v,
        ← K.adaptiveFanRelabel_extended_apply U hU g y v] at hv
      exact hv
    · by_cases hpg : p ∈ K.adaptiveFanFaceVertices U hU g
      · let v : K.AdaptiveFanVertex U hU := ⟨p, g, hpg⟩
        have hv := congrFun h v
        rw [← K.adaptiveFanRelabel_extended_apply U hU f x v,
          ← K.adaptiveFanRelabel_extended_apply U hU g y v] at hv
        exact hv
      · rw [extendFaceCoordinates_of_notMem _ _ hpf,
          extendFaceCoordinates_of_notMem _ _ hpg]

/-- One adaptive fan face parametrized by its global used vertices. -/
noncomputable def adaptiveGlobalFanFaceMap (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    stdSimplex ℝ {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f} → U :=
  fun x ↦ K.adaptiveFanFaceMap U hU f (K.adaptiveFanRelabelSimplex U hU f x)

theorem continuous_adaptiveGlobalFanFaceMap (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    Continuous (K.adaptiveGlobalFanFaceMap U hU f) :=
  (K.continuous_adaptiveFanFaceMap U hU f).comp
    (stdSimplex.continuous_map (K.adaptiveFanFaceVertexEquiv U hU f))

/-- Relabeling a fan face by global vertices does not change its geometric range. -/
theorem range_adaptiveGlobalFanFaceMap (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    Set.range (K.adaptiveGlobalFanFaceMap U hU f) =
      Set.range (K.adaptiveFanFaceMap U hU f) := by
  apply Set.Subset.antisymm
  · rintro p ⟨x, rfl⟩
    exact Set.mem_range_self _
  · rintro p ⟨x, rfl⟩
    let y := stdSimplex.map (K.adaptiveFanFaceVertexEquiv U hU f).symm x
    refine ⟨y, congrArg (K.adaptiveFanFaceMap U hU f) ?_⟩
    change stdSimplex.map (K.adaptiveFanFaceVertexEquiv U hU f) y = x
    dsimp only [y]
    rw [stdSimplex.map_comp_apply]
    have he : (K.adaptiveFanFaceVertexEquiv U hU f : _ → _) ∘
        (K.adaptiveFanFaceVertexEquiv U hU f).symm = id := by
      funext z
      exact (K.adaptiveFanFaceVertexEquiv U hU f).apply_symm_apply z
    rw [he, stdSimplex.map_id_apply]

/- Combining relabeling with the geometric overlap theorem is expensive because all four local
simplex index types are dependent.  Isolating it keeps construction of the complex inexpensive. -/
theorem adaptiveFanRelabeledFaceMap_eq_iff (hU : IsOpen U)
    {f g : K.AdaptiveFanFace U hU}
    {x : stdSimplex ℝ {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f}}
    {y : stdSimplex ℝ {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU g}} :
    K.adaptiveGlobalFanFaceMap U hU f x =
        K.adaptiveGlobalFanFaceMap U hU g y ↔
      extendFaceCoordinates (K.adaptiveGlobalFanFaceVertices U hU f) x =
        extendFaceCoordinates (K.adaptiveGlobalFanFaceVertices U hU g) y := by
  constructor
  · intro hmap
    apply (K.adaptiveFanRelabel_extended_eq_iff U hU).mp
    exact K.adaptiveFanExtendedCoordinates_eq_of_faceMap_eq U hU hmap
  · intro hcoords
    apply K.adaptiveFanFaceMap_eq_of_extendedCoordinates_eq U hU
    exact (K.adaptiveFanRelabel_extended_eq_iff U hU).mpr hcoords

/-- Distinct adaptive fan triangles have distinct global three-vertex sets.  Equality first
identifies the adaptive tile by its interior center.  After erasing that center, the two base
endpoint pairs agree; their common midpoint then identifies both the cyclic tile edge and the
consecutive interval in its ordered boundary-vertex list. -/
theorem adaptiveGlobalFanFaceVertices_injective (hU : IsOpen U) :
    Function.Injective (K.adaptiveGlobalFanFaceVertices U hU) := by
  classical
  intro f g hvertices
  have hlocal : K.adaptiveFanFaceVertices U hU f =
      K.adaptiveFanFaceVertices U hU g := by
    ext p
    constructor
    · intro hp
      let v : K.AdaptiveFanVertex U hU := ⟨p, f, hp⟩
      have hvf : v ∈ K.adaptiveGlobalFanFaceVertices U hU f :=
        (K.mem_adaptiveGlobalFanFaceVertices_iff U hU f v).mpr hp
      have hvg : v ∈ K.adaptiveGlobalFanFaceVertices U hU g := by
        rw [← hvertices]
        exact hvf
      exact (K.mem_adaptiveGlobalFanFaceVertices_iff U hU g v).mp hvg
    · intro hp
      let v : K.AdaptiveFanVertex U hU := ⟨p, g, hp⟩
      have hvg : v ∈ K.adaptiveGlobalFanFaceVertices U hU g :=
        (K.mem_adaptiveGlobalFanFaceVertices_iff U hU g v).mpr hp
      have hvf : v ∈ K.adaptiveGlobalFanFaceVertices U hU f := by
        rw [hvertices]
        exact hvg
      exact (K.mem_adaptiveGlobalFanFaceVertices_iff U hU f v).mp hvf
  have htile : f.1 = g.1 := by
    by_contra hfg
    apply K.adaptiveFaceCenter_not_mem_adaptiveFanFaceVertices_of_ne U hU hfg
    rw [← hlocal]
    simp [adaptiveFanFaceVertices]
  rcases f with ⟨t, i, a⟩
  rcases g with ⟨s, j, b⟩
  dsimp only at htile
  subst s
  let f : K.AdaptiveFanFace U hU := ⟨t, i, a⟩
  let g : K.AdaptiveFanFace U hU := ⟨t, j, b⟩
  have hcenterFirstF : K.adaptiveFaceCenter U t ≠
      K.adaptiveEdgeIntervalFirst U hU t i a :=
    K.adaptiveFaceCenter_ne_boundaryVertex U hU t
      ((K.mem_boundaryEdgeVertices_iff U hU t i _).mp
        (K.adaptiveEdgeIntervalFirst_mem_boundaryEdgeVertices U hU t i a)).1
  have hcenterSecondF : K.adaptiveFaceCenter U t ≠
      K.adaptiveEdgeIntervalSecond U hU t i a :=
    K.adaptiveFaceCenter_ne_boundaryVertex U hU t
      ((K.mem_boundaryEdgeVertices_iff U hU t i _).mp
        (K.adaptiveEdgeIntervalSecond_mem_boundaryEdgeVertices U hU t i a)).1
  have hcenterFirstG : K.adaptiveFaceCenter U t ≠
      K.adaptiveEdgeIntervalFirst U hU t j b :=
    K.adaptiveFaceCenter_ne_boundaryVertex U hU t
      ((K.mem_boundaryEdgeVertices_iff U hU t j _).mp
        (K.adaptiveEdgeIntervalFirst_mem_boundaryEdgeVertices U hU t j b)).1
  have hcenterSecondG : K.adaptiveFaceCenter U t ≠
      K.adaptiveEdgeIntervalSecond U hU t j b :=
    K.adaptiveFaceCenter_ne_boundaryVertex U hU t
      ((K.mem_boundaryEdgeVertices_iff U hU t j _).mp
        (K.adaptiveEdgeIntervalSecond_mem_boundaryEdgeVertices U hU t j b)).1
  have hbase :
      ({K.adaptiveEdgeIntervalFirst U hU t i a,
          K.adaptiveEdgeIntervalSecond U hU t i a} : Finset K.realization) =
        {K.adaptiveEdgeIntervalFirst U hU t j b,
          K.adaptiveEdgeIntervalSecond U hU t j b} := by
    have herase := congrArg
      (fun z : Finset K.realization ↦ z.erase (K.adaptiveFaceCenter U t)) hlocal
    simpa only [adaptiveFanFaceVertices, Finset.erase_insert,
      Finset.erase_eq_of_notMem, Finset.mem_insert, Finset.mem_singleton,
      not_or, not_false_eq_true, and_true, hcenterFirstF, hcenterSecondF,
      hcenterFirstG, hcenterSecondG] using herase
  have hendpoints :
      (K.adaptiveEdgeIntervalFirst U hU t i a =
          K.adaptiveEdgeIntervalFirst U hU t j b ∧
        K.adaptiveEdgeIntervalSecond U hU t i a =
          K.adaptiveEdgeIntervalSecond U hU t j b) ∨
      (K.adaptiveEdgeIntervalFirst U hU t i a =
          K.adaptiveEdgeIntervalSecond U hU t j b ∧
        K.adaptiveEdgeIntervalSecond U hU t i a =
          K.adaptiveEdgeIntervalFirst U hU t j b) := by
    have hp : K.adaptiveEdgeIntervalFirst U hU t i a =
          K.adaptiveEdgeIntervalFirst U hU t j b ∨
        K.adaptiveEdgeIntervalFirst U hU t i a =
          K.adaptiveEdgeIntervalSecond U hU t j b := by
      have hpMem : K.adaptiveEdgeIntervalFirst U hU t i a ∈
          ({K.adaptiveEdgeIntervalFirst U hU t i a,
            K.adaptiveEdgeIntervalSecond U hU t i a} : Finset K.realization) := by simp
      rw [hbase] at hpMem
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hpMem
    have hq : K.adaptiveEdgeIntervalSecond U hU t i a =
          K.adaptiveEdgeIntervalFirst U hU t j b ∨
        K.adaptiveEdgeIntervalSecond U hU t i a =
          K.adaptiveEdgeIntervalSecond U hU t j b := by
      have hqMem : K.adaptiveEdgeIntervalSecond U hU t i a ∈
          ({K.adaptiveEdgeIntervalFirst U hU t i a,
            K.adaptiveEdgeIntervalSecond U hU t i a} : Finset K.realization) := by simp
      rw [hbase] at hqMem
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hqMem
    rcases hp with hp | hp
    · refine Or.inl ⟨hp, ?_⟩
      exact hq.resolve_left (fun hqFirst ↦
        K.adaptiveEdgeIntervalFirst_ne_second U hU t i a (hp.trans hqFirst.symm))
    · refine Or.inr ⟨hp, ?_⟩
      exact hq.resolve_right (fun hqSecond ↦
        K.adaptiveEdgeIntervalFirst_ne_second U hU t i a (hp.trans hqSecond.symm))
  let r : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  let x := K.adaptiveFanBaseSimplexPath U hU f r
  let y := K.adaptiveFanBaseSimplexPath U hU g r
  have hxy : K.adaptiveFanFaceMap U hU f x =
      K.adaptiveFanFaceMap U hU g y := by
    change K.adaptiveFanBasePath U hU f r = K.adaptiveFanBasePath U hU g r
    apply Subtype.ext
    apply Subtype.ext
    rw [K.adaptiveFanBasePath_val_eq_lineMap U hU f r,
      K.adaptiveFanBasePath_val_eq_lineMap U hU g r]
    change AffineMap.lineMap
        (K.adaptiveEdgeIntervalFirst U hU t i a).1
        (K.adaptiveEdgeIntervalSecond U hU t i a).1 r.1 =
      AffineMap.lineMap
        (K.adaptiveEdgeIntervalFirst U hU t j b).1
        (K.adaptiveEdgeIntervalSecond U hU t j b).1 r.1
    rcases hendpoints with hsame | hswap
    · rw [hsame.1, hsame.2]
    · rw [hswap.1, hswap.2]
      ext k
      simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, r]
      ring
  have hxCenter : x (K.adaptiveFanCenterVertex U hU f) = 0 := by
    exact K.adaptiveFanBaseSimplexPath_apply_center U hU f r
  have hyCenter : y (K.adaptiveFanCenterVertex U hU g) = 0 := by
    exact K.adaptiveFanBaseSimplexPath_apply_center U hU g r
  have hxFirst : 0 < x (K.adaptiveFanFirstVertex U hU f) := by
    rw [K.adaptiveFanBaseSimplexPath_apply_first U hU f r]
    norm_num [r]
  have hxSecond : 0 < x (K.adaptiveFanSecondVertex U hU f) := by
    rw [K.adaptiveFanBaseSimplexPath_apply_second U hU f r]
    norm_num [r]
  have hyFirst : 0 < y (K.adaptiveFanFirstVertex U hU g) := by
    rw [K.adaptiveFanBaseSimplexPath_apply_first U hU g r]
    norm_num [r]
  have hySecond : 0 < y (K.adaptiveFanSecondVertex U hU g) := by
    rw [K.adaptiveFanBaseSimplexPath_apply_second U hU g r]
    norm_num [r]
  have hij : i = j :=
    K.adaptiveFanSide_eq_of_faceMap_eq_of_same_tile_of_base_weights_pos
      U hU t i j a b hxy hxCenter hyCenter hxFirst hxSecond hyFirst hySecond
  subst j
  have hab : a = b :=
    K.adaptiveFanInterval_eq_of_faceMap_eq_of_same_edge_of_base_weights_pos
      U hU t i a b hxy hxCenter hyCenter hxFirst hxSecond hyFirst hySecond
  subst b
  rfl

/- The conforming adaptive fan family as a locally finite triangle complex in the open
subspace. -/
/-- The `adaptiveLocallyFiniteTriangleComplex` declaration. -/
noncomputable abbrev adaptiveLocallyFiniteTriangleComplex (hU : IsOpen U) :
    LocallyFiniteTriangleComplex U where
  Vertex := K.AdaptiveFanVertex U hU
  vertexDecidableEq := inferInstance
  Face := K.AdaptiveFanFace U hU
  faceDecidableEq := inferInstance
  faceVertices := K.adaptiveGlobalFanFaceVertices U hU
  faceVertices_card := by
    intro f
    rw [adaptiveGlobalFanFaceVertices, Finset.card_map, Finset.card_attach,
      K.adaptiveFanFaceVertices_card U hU f]
  vertex_used := by
    rintro ⟨p, f, hp⟩
    exact ⟨f, (K.mem_adaptiveGlobalFanFaceVertices_iff U hU f _).mpr hp⟩
  faceMap := K.adaptiveGlobalFanFaceMap U hU
  faceMap_continuous := K.continuous_adaptiveGlobalFanFaceMap U hU
  faceMap_eq_iff := by
    intro f g x y
    change K.adaptiveGlobalFanFaceMap U hU f x =
        K.adaptiveGlobalFanFaceMap U hU g y ↔
      extendFaceCoordinates (K.adaptiveGlobalFanFaceVertices U hU f) x =
        extendFaceCoordinates (K.adaptiveGlobalFanFaceVertices U hU g) y
    exact K.adaptiveFanRelabeledFaceMap_eq_iff U hU
  locallyFinite := by
    simpa only [K.range_adaptiveGlobalFanFaceMap U hU] using
      K.locallyFinite_adaptiveFanFaceMap U hU

/-- The global adaptive fan complex covers the entire open subspace. -/
theorem adaptiveLocallyFiniteTriangleComplex_support (hU : IsOpen U) :
    (K.adaptiveLocallyFiniteTriangleComplex U hU).support = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  have hpTiles : p.1 ∈ ⋃ t : K.AdaptiveFace U, K.adaptiveFaceCarrier U t := by
    rw [K.iUnion_adaptiveFaceCarrier U hU]
    exact p.2
  obtain ⟨t, hpt⟩ := Set.mem_iUnion.mp hpTiles
  obtain ⟨i, j, x, hx⟩ :=
    K.exists_adaptiveFanFaceMap_eq_of_mem_adaptiveFaceCarrier U hU t hpt
  rw [LocallyFiniteTriangleComplex.support]
  apply Set.mem_iUnion.mpr
  refine ⟨(⟨t, i, j⟩ : K.AdaptiveFanFace U hU), ?_⟩
  change p ∈ Set.range (K.adaptiveGlobalFanFaceMap U hU ⟨t, i, j⟩)
  rw [K.range_adaptiveGlobalFanFaceMap U hU]
  refine ⟨x, hx.trans ?_⟩
  apply Subtype.ext
  rfl

/-- On a compact open subspace, the adaptive locally finite complex is an honest finite
geometric triangulation. -/
noncomputable def adaptiveGeometricTriangulation (hU : IsOpen U)
    [CompactSpace U] [T2Space U] : GeometricTriangulation U :=
  (K.adaptiveLocallyFiniteTriangleComplex U hU).toGeometricTriangulation
    (K.adaptiveLocallyFiniteTriangleComplex_support U hU)

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
