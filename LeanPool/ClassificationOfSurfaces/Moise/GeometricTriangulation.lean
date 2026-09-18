/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff

/-!
# Geometric triangulations

The faithful statement of "the space `S` admits a finite triangulation": `S` is homeomorphic to
the geometric realization of a finite two-dimensional simplicial complex.

The realization is concrete: for a finite vertex type `V` and a finite family `F` of faces
(3-element vertex sets), `GeometricRealization V F` is the subset of the standard simplex
`stdSimplex ℝ V` consisting of points supported on some face.  This is the classical geometric
realization by barycentric coordinates; it is a compact Hausdorff polyhedron by construction, so
the definition cannot be satisfied by junk witnesses (`Empty` face types, arbitrary `realization`
fields, and so on): the homeomorphism type pins `S` to an actual finite union of geometric
2-simplexes.

Semantic anchors (see `Moise/Countermodels.lean` and the Definition Faithfulness section of
`docs/AUTOFORMALIZATION_GUIDE.md`):

* must-imply: `GeometricTriangulation.compactSpace`, `GeometricTriangulation.t2Space`;
* positive example: the standard 2-simplex triangulates itself;
* non-example: `ℝ` and `ℚ` admit no geometric triangulation (they are not compact).
-/

/-- A finite closed cover of a preconnected set has a connected intersection graph.

This is the closed-cover counterpart of `IsPreconnected.transGen_of_iUnion`, whose open-cover
hypothesis is not available for the closed simplexes of a geometric realization. -/
theorem IsPreconnected.transGen_of_finite_iUnion
    {α ι : Type*} [TopologicalSpace α] [Finite ι] {s : ι → Set α}
    (hs : IsPreconnected (⋃ n, s n)) (hs' : ∀ i, IsClosed (s i))
    (i j : ι) (hi : (s i).Nonempty) (hj : (s j).Nonempty) :
    Relation.TransGen (fun a b ↦ (s a ∩ s b).Nonempty) i j := by
  by_contra hij
  let R := fun a b : ι ↦ (s a ∩ s b).Nonempty
  let S : Set ι := {k | Relation.TransGen R i k}
  let U : Set α := ⋃ k ∈ S, s k
  let V : Set α := ⋃ k ∈ Sᶜ, s k
  have hUclosed : IsClosed U := by
    exact Set.toFinite S |>.isClosed_biUnion fun k _ ↦ hs' k
  have hVclosed : IsClosed V := by
    exact Set.toFinite Sᶜ |>.isClosed_biUnion fun k _ ↦ hs' k
  have hsplit : (⋃ n, s n) = U ∪ V := iSup_split s (· ∈ S)
  have hUV : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    simp only [Set.mem_iUnion, exists_prop, Set.mem_compl_iff, U, V] at hxU hxV
    obtain ⟨k, hk, hxk⟩ := hxU
    obtain ⟨l, hl, hxl⟩ := hxV
    exact hl (hk.tail ⟨x, hxk, hxl⟩)
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  have hiS : i ∈ S := Relation.TransGen.single ⟨a, ha, ha⟩
  have haU : a ∈ U := Set.mem_iUnion₂_of_mem hiS ha
  have hjS : j ∉ S := hij
  have hbV : b ∈ V := Set.mem_iUnion₂_of_mem hjS hb
  have hcover : (⋃ n, s n) ⊆ Vᶜ ∪ Uᶜ := by
    intro x hx
    rcases hsplit.le hx with hxU | hxV
    · exact Or.inl (fun hxV ↦ Set.disjoint_left.mp hUV hxU hxV)
    · exact Or.inr (fun hxU ↦ Set.disjoint_left.mp hUV hxU hxV)
  have hUne : ((⋃ n, s n) ∩ Vᶜ).Nonempty :=
    ⟨a, Set.mem_iUnion_of_mem i ha,
      fun haV ↦ Set.disjoint_left.mp hUV haU haV⟩
  have hVne : ((⋃ n, s n) ∩ Uᶜ).Nonempty :=
    ⟨b, Set.mem_iUnion_of_mem j hb,
      fun hbU ↦ Set.disjoint_left.mp hUV hbU hbV⟩
  obtain ⟨x, hxall, hxV, hxU⟩ := hs Vᶜ Uᶜ
    hVclosed.isOpen_compl hUclosed.isOpen_compl hcover hUne hVne
  rcases hsplit.le hxall with hxU' | hxV'
  · exact hxU hxU'
  · exact hxV hxV'

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-!
### Barycentric coordinates on the standard simplex

Mathlib replaced the set-valued `stdSimplex 𝕜 ι : Set (ι → 𝕜)` by the bundled
`Convexity.StdSimplex`, whose elements carry a `Finsupp` of weights instead of a plain
coordinate function.  Every complex in this development parametrizes its faces by honest
barycentric coordinate functions `ι → ℝ`, so the section below keeps the set-valued simplex —
and exactly the slice of its API that this project uses — as a definition of its own.  The
statements and proofs are those of the corresponding Mathlib declarations, which are now
deprecated.
-/

section StandardSimplex

variable (𝕜 : Type*) (ι : Type*) [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι]

/-- The standard simplex in the space of functions `ι → 𝕜` is the set of vectors with
non-negative coordinates with total sum `1`. -/
def stdSimplex : Set (ι → 𝕜) :=
  {f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}

theorem stdSimplex_eq_inter :
    stdSimplex 𝕜 ι = (⋂ x, {f : ι → 𝕜 | 0 ≤ f x}) ∩ {f | ∑ x, f x = 1} := by
  ext f
  simp only [stdSimplex, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]

theorem convex_stdSimplex [IsOrderedRing 𝕜] : Convex 𝕜 (stdSimplex 𝕜 ι) := by
  refine fun f hf g hg a b ha hb hab => ⟨fun x => ?_, ?_⟩
  · apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1]
  · simp_rw [Pi.add_apply, Pi.smul_apply]
    rwa [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one]

variable {ι}

variable {𝕜} in
/-- All values of a function `f ∈ stdSimplex 𝕜 ι` belong to `[0, 1]`. -/
theorem mem_Icc_of_mem_stdSimplex [IsOrderedAddMonoid 𝕜] {f : ι → 𝕜}
    (hf : f ∈ stdSimplex 𝕜 ι) (x) : f x ∈ Set.Icc (0 : 𝕜) 1 :=
  ⟨hf.1 x, hf.2 ▸ Finset.single_le_sum (fun y _ => hf.1 y) (Finset.mem_univ x)⟩

/-- `stdSimplex 𝕜 ι` is a subset of the unit cube. -/
theorem stdSimplex_subset_Icc [IsOrderedAddMonoid 𝕜] : stdSimplex 𝕜 ι ⊆ Set.Icc 0 1 := by
  intro f h
  rw [← Set.pi_univ_Icc, Set.univ_pi_eq_iInter, Set.mem_iInter]
  simpa using fun i ↦ mem_Icc_of_mem_stdSimplex h i

variable [DecidableEq ι] [ZeroLEOneClass 𝕜]

theorem single_mem_stdSimplex (i : ι) : Pi.single i 1 ∈ stdSimplex 𝕜 ι :=
  ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ ↦ le_rfl⟩, by simp⟩

end StandardSimplex

section StandardSimplexTopology

variable (𝕜 ι : Type*) [Fintype ι] [TopologicalSpace 𝕜] [Semiring 𝕜] [PartialOrder 𝕜]
  [OrderClosedTopology 𝕜] [ContinuousAdd 𝕜]

/-- `stdSimplex 𝕜 ι` is closed. -/
theorem isClosed_stdSimplex : IsClosed (stdSimplex 𝕜 ι) := by
  rw [stdSimplex_eq_inter]
  apply IsClosed.inter
  · exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_eq (by fun_prop) continuous_const

/-- `stdSimplex 𝕜 ι` is compact. -/
theorem isCompact_stdSimplex [CompactIccSpace 𝕜] [IsOrderedAddMonoid 𝕜] :
    IsCompact (stdSimplex 𝕜 ι) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_stdSimplex 𝕜 ι) (stdSimplex_subset_Icc 𝕜)

instance stdSimplex.instCompactSpace_coe [CompactIccSpace 𝕜] [IsOrderedAddMonoid 𝕜] :
    CompactSpace (stdSimplex 𝕜 ι) :=
  isCompact_iff_compactSpace.mp <| isCompact_stdSimplex 𝕜 _

end StandardSimplexTopology

namespace stdSimplex

variable {S : Type*} [Semiring S] [PartialOrder S]
  {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

@[macro_inline]
instance : FunLike (stdSimplex S X) X S where
  coe s := s.val
  coe_injective := by aesop

@[ext high]
lemma ext {s t : stdSimplex S X} (h : (s : X → S) = t) : s = t := by
  ext : 1
  assumption

@[simp] lemma zero_le (s : stdSimplex S X) (x : X) : 0 ≤ s x := s.2.1 x

@[simp] lemma sum_eq_one (s : stdSimplex S X) : ∑ x, s x = 1 := s.2.2

@[simp] lemma add_eq_one (s : stdSimplex S (Fin 2)) : s 0 + s 1 = 1 := by
  simpa only [Fin.sum_univ_two] using sum_eq_one s

section

variable [IsOrderedRing S]

@[simp] lemma le_one (s : stdSimplex S X) (x : X) : s x ≤ 1 := by
  rw [← sum_eq_one s]
  exact Finset.single_le_sum (by simp) (by simp)

lemma image_linearMap (f : X → Y) :
    Set.image (FunOnFinite.linearMap S S f) (stdSimplex S X) ⊆ stdSimplex S Y := by
  classical
  rintro _ ⟨s, ⟨hs₀, hs₁⟩, rfl⟩
  refine ⟨fun y ↦ ?_, ?_⟩
  · rw [FunOnFinite.linearMap_apply_apply]
    exact Finset.sum_nonneg (by aesop)
  · simp only [FunOnFinite.linearMap_apply_apply, ← hs₁]
    exact Finset.sum_fiberwise Finset.univ f s

/-- The map `stdSimplex S X → stdSimplex S Y` that is induced by a map `f : X → Y`. -/
noncomputable def map (f : X → Y) (s : stdSimplex S X) : stdSimplex S Y :=
  ⟨FunOnFinite.linearMap S S f s, image_linearMap f (by aesop)⟩

@[simp] lemma map_coe (f : X → Y) (s : stdSimplex S X) :
    ⇑(map f s) = FunOnFinite.linearMap S S f s := rfl

@[simp] lemma map_id_apply (x : stdSimplex S X) : map id x = x := by
  aesop

lemma map_comp_apply (f : X → Y) (g : Y → Z) (x : stdSimplex S X) :
    map g (map f x) = map (g.comp f) x := by
  ext
  simp [FunOnFinite.linearMap_comp]

/-- The vertex corresponding to `x : X` in `stdSimplex S X`. -/
abbrev vertex [DecidableEq X] (x : X) : stdSimplex S X :=
  ⟨Pi.single x 1, single_mem_stdSimplex S x⟩

@[simp] lemma vertex_coe [DecidableEq X] (x : X) :
    ⇑(vertex (S := S) x) = Pi.single x 1 := rfl

@[simp] lemma map_vertex [DecidableEq X] [DecidableEq Y] (f : X → Y) (x : X) :
    map (S := S) f (vertex x) = vertex (f x) := by
  aesop

lemma continuous_map [TopologicalSpace S] [IsTopologicalSemiring S] (f : X → Y) :
    Continuous (map (S := S) f) :=
  Continuous.subtype_mk ((FunOnFinite.continuous_linearMap S S f).comp continuous_induced_dom) _

lemma vertex_injective [Nontrivial S] [DecidableEq X] :
    Function.Injective (vertex (S := S) (X := X)) := by
  intro x y h
  replace h := DFunLike.congr_fun h x
  by_contra!
  simp [Pi.single_eq_of_ne this] at h

instance [Nonempty X] : Nonempty (stdSimplex S X) := by
  classical
  exact ⟨vertex (Classical.arbitrary _)⟩

instance [Nontrivial S] [Nontrivial X] : Nontrivial (stdSimplex S X) where
  exists_pair_ne := by
    classical
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    exact ⟨vertex x, vertex y, fun h ↦ hxy (vertex_injective h)⟩

instance [Subsingleton X] : Subsingleton (stdSimplex S X) where
  allEq s t := by
    ext i
    have (u : stdSimplex S X) : u i = 1 := by
      rw [← sum_eq_one u, Finset.sum_eq_single i _ (by simp)]
      intro j _ hj
      exact (hj (Subsingleton.elim j i)).elim
    simp [this]

end

end stdSimplex

/-- The geometric realization of a finite family `F` of faces on a finite vertex type `V`: the
points of the standard simplex on `V` whose support lies inside some face of `F`.  For a face `t`
this carves out the geometric simplex spanned by `t`, so the realization is the finite union of
the geometric simplexes of `F`, glued along shared barycentric-coordinate faces. -/
def GeometricRealization (V : Type*) [Fintype V] (F : Finset (Finset V)) : Set (V → ℝ) :=
  {x | x ∈ stdSimplex ℝ V ∧ ∃ t ∈ F, ∀ v ∉ t, x v = 0}

/-- The geometric simplex carried by one finite set of vertices. -/
def GeometricFace (V : Type*) [Fintype V] (t : Finset V) : Set (V → ℝ) :=
  {x | x ∈ stdSimplex ℝ V ∧ ∀ v ∉ t, x v = 0}

namespace GeometricFace

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Semantic anchor: two barycentric faces meet in exactly their common face. -/
theorem inter (t u : Finset V) :
    GeometricFace V t ∩ GeometricFace V u = GeometricFace V (t ∩ u) := by
  ext x
  constructor
  · rintro ⟨⟨hx, ht⟩, _, hu⟩
    refine ⟨hx, ?_⟩
    intro v hv
    rw [Finset.mem_inter, not_and_or] at hv
    rcases hv with hv | hv
    · exact ht v hv
    · exact hu v hv
  · rintro ⟨hx, htu⟩
    refine ⟨⟨hx, ?_⟩, hx, ?_⟩
    · intro v hv
      exact htu v (fun hmem => hv (Finset.mem_inter.mp hmem).1)
    · intro v hv
      exact htu v (fun hmem => hv (Finset.mem_inter.mp hmem).2)

omit [DecidableEq V] in
/-- A barycentric face is nonempty exactly when it has a vertex. -/
theorem nonempty_iff (t : Finset V) :
    (GeometricFace V t).Nonempty ↔ t.Nonempty := by
  classical
  constructor
  · rintro ⟨x, hxstd, hxsupp⟩
    by_contra ht
    have ht' : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    have hxzero : x = 0 := by
      funext v
      exact hxsupp v (by simp [ht'])
    rw [hxzero] at hxstd
    norm_num [stdSimplex] at hxstd
  · rintro ⟨v, hv⟩
    refine ⟨Pi.single v 1, single_mem_stdSimplex ℝ v, ?_⟩
    intro w hw
    by_cases hwv : w = v
    · subst w
      exact (hw hv).elim
    · simp [hwv]

omit [DecidableEq V] in
/-- Each barycentric face is closed in the ambient coordinate space. -/
theorem isClosed (t : Finset V) :
    IsClosed (GeometricFace V t) := by
  classical
  have hrepr : GeometricFace V t =
      stdSimplex ℝ V ∩ ⋂ v ∈ {v : V | v ∉ t}, {x : V → ℝ | x v = 0} := by
    ext x
    simp [GeometricFace]
  rw [hrepr]
  exact (isClosed_stdSimplex ℝ V).inter
    (isClosed_biInter fun v _ ↦ isClosed_eq (continuous_apply v) continuous_const)

end GeometricFace

namespace GeometricRealization

variable {V : Type*} [Fintype V] {F : Finset (Finset V)}

/-- The global realization is literally the finite union of its geometric faces. -/
theorem eq_biUnion_geometricFace :
    GeometricRealization V F = ⋃ t ∈ F, GeometricFace V t := by
  ext x
  simp [GeometricRealization, GeometricFace]

theorem subset_stdSimplex : GeometricRealization V F ⊆ stdSimplex ℝ V :=
  fun _ hx => hx.1

theorem isClosed : IsClosed (GeometricRealization V F) := by
  have hrepr : GeometricRealization V F =
      stdSimplex ℝ V ∩ ⋃ t ∈ F, {x : V → ℝ | ∀ v ∉ t, x v = 0} := by
    ext x
    simp [GeometricRealization, Set.mem_iUnion]
  rw [hrepr]
  refine (isClosed_stdSimplex ℝ V).inter ?_
  refine Set.Finite.isClosed_biUnion F.finite_toSet ?_
  intro t _
  have hInter : {x : V → ℝ | ∀ v ∉ t, x v = 0} =
      ⋂ v ∈ {v : V | v ∉ t}, {x : V → ℝ | x v = 0} := by
    ext x
    simp
  rw [hInter]
  exact isClosed_biInter fun v _ => isClosed_eq (continuous_apply v) continuous_const

theorem isCompact : IsCompact (GeometricRealization V F) :=
  (isCompact_stdSimplex ℝ V).of_isClosed_subset isClosed subset_stdSimplex

instance : CompactSpace (GeometricRealization V F) :=
  isCompact_iff_compactSpace.mp isCompact

/-- The realization of the empty face family is empty. -/
theorem eq_empty_of_no_faces : GeometricRealization V (∅ : Finset (Finset V)) = ∅ := by
  ext x
  simp [GeometricRealization]

instance : IsEmpty (GeometricRealization V (∅ : Finset (Finset V))) :=
  Set.isEmpty_coe_sort.mpr eq_empty_of_no_faces

end GeometricRealization

namespace TriangleFamily

variable {Vertex : Type*} [DecidableEq Vertex]

/-- A listed maximal face of a finite triangle family. -/
abbrev Face (faces : Finset (Finset Vertex)) :=
  {t : Finset Vertex // t ∈ faces}

/-- The two-vertex faces occurring in a finite triangle family. -/
def edges (faces : Finset (Finset Vertex)) : Finset (Finset Vertex) :=
  faces.biUnion fun t => t.powersetCard 2

/-- Two listed triangles are dual-adjacent when they share a two-vertex face. -/
def FaceAdjacent (faces : Finset (Finset Vertex)) (f g : Face faces) : Prop :=
  ∃ e : Finset Vertex, e.card = 2 ∧ e ⊆ f.1 ∧ e ⊆ g.1

/-- Two listed triangles are adjacent at `v` when they share a two-vertex face containing `v`.

Unlike `FaceAdjacent`, this relation remembers the vertex star in which the adjacency step
occurs. -/
def FaceAdjacentAtVertex (faces : Finset (Finset Vertex)) (v : Vertex)
    (f g : Face faces) : Prop :=
  ∃ e : Finset Vertex, e.card = 2 ∧ v ∈ e ∧ e ⊆ f.1 ∧ e ⊆ g.1

/-- Two listed triangles meet when their vertex sets have a common vertex. -/
def FaceIntersects (faces : Finset (Finset Vertex)) (f g : Face faces) : Prop :=
  (f.1 ∩ g.1).Nonempty

omit [DecidableEq Vertex] in
theorem faceAdjacent_symm {faces : Finset (Finset Vertex)} {f g : Face faces}
    (h : FaceAdjacent faces f g) : FaceAdjacent faces g f := by
  rcases h with ⟨e, hecard, hef, heg⟩
  exact ⟨e, hecard, heg, hef⟩

omit [DecidableEq Vertex] in
/-- Fixed-vertex face adjacency is symmetric. -/
theorem faceAdjacentAtVertex_symm
    {faces : Finset (Finset Vertex)} {v : Vertex} {f g : Face faces}
    (h : FaceAdjacentAtVertex faces v f g) :
    FaceAdjacentAtVertex faces v g f := by
  rcases h with ⟨e, hecard, hve, hef, heg⟩
  exact ⟨e, hecard, hve, heg, hef⟩

omit [DecidableEq Vertex] in
/-- A fixed-vertex adjacency step is an ordinary dual-adjacency step. -/
theorem faceAdjacent_of_faceAdjacentAtVertex
    {faces : Finset (Finset Vertex)} {v : Vertex} {f g : Face faces}
    (h : FaceAdjacentAtVertex faces v f g) :
    FaceAdjacent faces f g := by
  rcases h with ⟨e, hecard, _hve, hef, heg⟩
  exact ⟨e, hecard, hef, heg⟩

omit [DecidableEq Vertex] in
/-- The left endpoint of a fixed-vertex adjacency step contains the fixed vertex. -/
theorem mem_left_of_faceAdjacentAtVertex
    {faces : Finset (Finset Vertex)} {v : Vertex} {f g : Face faces}
    (h : FaceAdjacentAtVertex faces v f g) : v ∈ f.1 := by
  rcases h with ⟨e, _hecard, hve, hef, _heg⟩
  exact hef hve

omit [DecidableEq Vertex] in
/-- The right endpoint of a fixed-vertex adjacency step contains the fixed vertex. -/
theorem mem_right_of_faceAdjacentAtVertex
    {faces : Finset (Finset Vertex)} {v : Vertex} {f g : Face faces}
    (h : FaceAdjacentAtVertex faces v f g) : v ∈ g.1 := by
  rcases h with ⟨e, _hecard, hve, _hef, heg⟩
  exact heg hve

/-- Faces in different dual components share at most one vertex. -/
theorem card_inter_le_one_of_not_faceAdjacent
    {faces : Finset (Finset Vertex)} {f g : Face faces}
    (h : ¬ FaceAdjacent faces f g) :
    (f.1 ∩ g.1).card ≤ 1 := by
  by_contra hcard
  have htwo : 2 ≤ (f.1 ∩ g.1).card := by omega
  obtain ⟨e, heSub, heCard⟩ := Finset.exists_subset_card_eq htwo
  apply h
  exact ⟨e, heCard, heSub.trans Finset.inter_subset_left,
    heSub.trans Finset.inter_subset_right⟩

omit [DecidableEq Vertex] in
theorem reflTransGen_faceAdjacent_symm {faces : Finset (Finset Vertex)}
    {f g : Face faces} (h : Relation.ReflTransGen (FaceAdjacent faces) f g) :
    Relation.ReflTransGen (FaceAdjacent faces) g f := by
  apply Relation.ReflTransGen.mono (fun _ _ hab => faceAdjacent_symm hab)
  exact h.swap

omit [DecidableEq Vertex] in
/-- A chain of fixed-vertex adjacency steps is an ordinary dual-adjacency chain. -/
theorem reflTransGen_faceAdjacent_of_faceAdjacentAtVertex
    {faces : Finset (Finset Vertex)} {v : Vertex} {f g : Face faces}
    (h : Relation.ReflTransGen (FaceAdjacentAtVertex faces v) f g) :
    Relation.ReflTransGen (FaceAdjacent faces) f g := by
  apply Relation.ReflTransGen.mono
    (fun _ _ hab => faceAdjacent_of_faceAdjacentAtVertex hab)
  exact h

omit [DecidableEq Vertex] in
/-- Fixed-vertex adjacency chains can be traversed in reverse. -/
theorem reflTransGen_faceAdjacentAtVertex_symm
    {faces : Finset (Finset Vertex)} {v : Vertex} {f g : Face faces}
    (h : Relation.ReflTransGen (FaceAdjacentAtVertex faces v) f g) :
    Relation.ReflTransGen (FaceAdjacentAtVertex faces v) g f := by
  apply Relation.ReflTransGen.mono
    (fun _ _ hab => faceAdjacentAtVertex_symm hab)
  exact h.swap

omit [DecidableEq Vertex] in
/-- Every endpoint reached from a face containing `v` through fixed-vertex adjacency still
contains `v`. -/
theorem mem_of_reflTransGen_faceAdjacentAtVertex
    {faces : Finset (Finset Vertex)} {v : Vertex} {f g : Face faces}
    (hvf : v ∈ f.1)
    (h : Relation.ReflTransGen (FaceAdjacentAtVertex faces v) f g) :
    v ∈ g.1 := by
  induction h with
  | refl => exact hvf
  | tail _h hstep _ih => exact mem_right_of_faceAdjacentAtVertex hstep

/-- Every two listed triangles are connected by a finite chain of shared edges. -/
def IsDualConnected (faces : Finset (Finset Vertex)) : Prop :=
  ∀ f g : Face faces, Relation.ReflTransGen (FaceAdjacent faces) f g

/-- Every pair of triangles incident to one vertex can be joined through shared edges.

For a triangulated surface this is the local connectedness assertion carried by the link of the
vertex. This compatibility predicate does not require its intermediate faces to remain incident
to that vertex; use `IsStrongVertexStarConnected` when that fixed-star invariant is needed. -/
def IsVertexStarConnected (faces : Finset (Finset Vertex)) : Prop :=
  ∀ (v : Vertex) (f g : Face faces), v ∈ f.1 → v ∈ g.1 →
    Relation.ReflTransGen (FaceAdjacent faces) f g

/-- Every pair of triangles incident to one vertex can be joined by a chain whose every adjacency
step shares an edge containing that same vertex. -/
def IsStrongVertexStarConnected (faces : Finset (Finset Vertex)) : Prop :=
  ∀ (v : Vertex) (f g : Face faces), v ∈ f.1 → v ∈ g.1 →
    Relation.ReflTransGen (FaceAdjacentAtVertex faces v) f g

omit [DecidableEq Vertex] in
/-- Strong fixed-star connectivity implies the legacy vertex-star connectivity predicate. -/
theorem IsStrongVertexStarConnected.isVertexStarConnected
    {faces : Finset (Finset Vertex)}
    (hstar : IsStrongVertexStarConnected faces) :
    IsVertexStarConnected faces := by
  intro v f g hvf hvg
  exact reflTransGen_faceAdjacent_of_faceAdjacentAtVertex
    (hstar v f g hvf hvg)

section Geometric

variable [Fintype Vertex]

/-- Geometric simplexes intersect exactly when their combinatorial faces share a vertex. -/
theorem geometricFace_inter_nonempty_iff
    {faces : Finset (Finset Vertex)} (f g : Face faces) :
    (GeometricFace Vertex f.1 ∩ GeometricFace Vertex g.1).Nonempty ↔
      FaceIntersects faces f g := by
  rw [GeometricFace.inter]
  simpa [FaceIntersects] using GeometricFace.nonempty_iff (f.1 ∩ g.1)

/-- Connectedness of a finite geometric realization connects all maximal faces through
nonempty intersections. -/
theorem isFaceIntersectionConnected_of_isPreconnected
    {faces : Finset (Finset Vertex)}
    (hface : ∀ f : Face faces, f.1.Nonempty)
    (hpre : IsPreconnected (GeometricRealization Vertex faces)) :
    ∀ f g : Face faces,
      Relation.ReflTransGen (FaceIntersects faces) f g := by
  have hunion :
      GeometricRealization Vertex faces =
        ⋃ f : Face faces, GeometricFace Vertex f.1 := by
    ext x
    simp [GeometricRealization, GeometricFace]
  have hpre' :
      IsPreconnected (⋃ f : Face faces, GeometricFace Vertex f.1) := by
    rw [← hunion]
    exact hpre
  intro f g
  have hchain := hpre'.transGen_of_finite_iUnion
    (fun f : Face faces ↦ GeometricFace.isClosed f.1) f g
    ((GeometricFace.nonempty_iff f.1).2 (hface f))
    ((GeometricFace.nonempty_iff g.1).2 (hface g))
  exact (Relation.ReflTransGen.mono
    (r := fun a b : Face faces ↦
      (GeometricFace Vertex a.1 ∩ GeometricFace Vertex b.1).Nonempty)
    (p := FaceIntersects faces)
    (fun a b h ↦ (geometricFace_inter_nonempty_iff a b).mp h))
    f g hchain.to_reflTransGen

end Geometric

/-- Connected vertex stars upgrade connectivity through arbitrary face intersections to
connectivity through shared edges. -/
theorem IsVertexStarConnected.isDualConnected
    {faces : Finset (Finset Vertex)}
    (hstar : IsVertexStarConnected faces)
    (hinter : ∀ f g : Face faces,
      Relation.ReflTransGen (FaceIntersects faces) f g) :
    IsDualConnected faces := by
  intro f g
  exact (Relation.reflTransGen_closed
    (r := FaceIntersects faces) (p := FaceAdjacent faces)
    (fun a b hab ↦ by
      rcases hab with ⟨v, hv⟩
      exact hstar v a b (Finset.mem_inter.mp hv).1
        (Finset.mem_inter.mp hv).2)) f g (hinter f g)
/-- Regard a face of a subfamily as a face of a larger family. -/
def faceOfSubset {faces faces' : Finset (Finset Vertex)} (h : faces ⊆ faces') :
    Face faces → Face faces' :=
  fun f => ⟨f.1, h f.2⟩

omit [DecidableEq Vertex] in
@[simp]
theorem faceOfSubset_val {faces faces' : Finset (Finset Vertex)} (h : faces ⊆ faces')
    (f : Face faces) : (faceOfSubset h f).1 = f.1 :=
  rfl

omit [DecidableEq Vertex] in
theorem faceAdjacent_faceOfSubset {faces faces' : Finset (Finset Vertex)}
    (h : faces ⊆ faces') {f g : Face faces} (hfg : FaceAdjacent faces f g) :
    FaceAdjacent faces' (faceOfSubset h f) (faceOfSubset h g) := by
  rcases hfg with ⟨e, hecard, hef, heg⟩
  exact ⟨e, hecard, hef, heg⟩

omit [DecidableEq Vertex] in
theorem reflTransGen_faceAdjacent_faceOfSubset
    {faces faces' : Finset (Finset Vertex)} (h : faces ⊆ faces') {f g : Face faces}
    (hfg : Relation.ReflTransGen (FaceAdjacent faces) f g) :
    Relation.ReflTransGen (FaceAdjacent faces') (faceOfSubset h f) (faceOfSubset h g) := by
  induction hfg with
  | refl => exact Relation.ReflTransGen.refl
  | tail _hab hbc ih =>
      exact ih.tail (faceAdjacent_faceOfSubset h hbc)

/-- Two dual-connected face families with a cross-adjacent pair have dual-connected union. -/
theorem isDualConnected_union {left right : Finset (Finset Vertex)}
    (hleft : IsDualConnected left) (hright : IsDualConnected right)
    (fleft : Face left) (fright : Face right)
    (hcross : FaceAdjacent (left ∪ right)
      (faceOfSubset Finset.subset_union_left fleft)
      (faceOfSubset Finset.subset_union_right fright)) :
    IsDualConnected (left ∪ right) := by
  intro f g
  rcases Finset.mem_union.mp f.2 with hf | hf <;>
    rcases Finset.mem_union.mp g.2 with hg | hg
  · let f' : Face left := ⟨f.1, hf⟩
    let g' : Face left := ⟨g.1, hg⟩
    have hpath := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_left (hleft f' g')
    simpa [f', g', faceOfSubset] using hpath
  · let f' : Face left := ⟨f.1, hf⟩
    let g' : Face right := ⟨g.1, hg⟩
    have hfirst := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_left (hleft f' fleft)
    have hlast := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_right (hright fright g')
    have hpath := (hfirst.tail hcross).trans hlast
    simpa [f', g', faceOfSubset] using hpath
  · let f' : Face right := ⟨f.1, hf⟩
    let g' : Face left := ⟨g.1, hg⟩
    have hfirst := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_right (hright f' fright)
    have hlast := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_left (hleft fleft g')
    have hpath := (hfirst.tail (faceAdjacent_symm hcross)).trans hlast
    simpa [f', g', faceOfSubset] using hpath
  · let f' : Face right := ⟨f.1, hf⟩
    let g' : Face right := ⟨g.1, hg⟩
    have hpath := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_right (hright f' g')
    simpa [f', g', faceOfSubset] using hpath

/-- A face from each family shares a genuine two-vertex edge in the union family. -/
def HasCrossEdge (left right : Finset (Finset Vertex)) : Prop :=
  ∃ (fleft : Face left) (fright : Face right),
      FaceAdjacent (left ∪ right)
        (faceOfSubset Finset.subset_union_left fleft)
        (faceOfSubset Finset.subset_union_right fright)

/-- Two dual-connected face families with a shared cross-edge have dual-connected union. -/
theorem isDualConnected_union_of_hasCrossEdge
    {left right : Finset (Finset Vertex)}
    (hleft : IsDualConnected left) (hright : IsDualConnected right)
    (hcross : HasCrossEdge left right) :
    IsDualConnected (left ∪ right) := by
  rcases hcross with ⟨fleft, fright, hcross⟩
  exact isDualConnected_union hleft hright fleft fright hcross

omit [DecidableEq Vertex] in
/-- A face family consisting of one triangle is dual-connected. -/
theorem isDualConnected_singleton (face : Finset Vertex) :
    IsDualConnected {face} := by
  intro f g
  have hfg : f = g := by
    apply Subtype.ext
    exact (Finset.mem_singleton.mp f.2).trans (Finset.mem_singleton.mp g.2).symm
  subst g
  exact Relation.ReflTransGen.refl

/-- Adding a triangle along an edge of a dual-connected family preserves dual connectivity. -/
theorem isDualConnected_insert {faces : Finset (Finset Vertex)}
    (hfaces : IsDualConnected faces) (face : Finset Vertex) (anchor : Face faces)
    (hcross : FaceAdjacent (insert face faces)
      ⟨face, Finset.mem_insert_self face faces⟩
      (faceOfSubset (Finset.subset_insert face faces) anchor)) :
    IsDualConnected (insert face faces) := by
  apply isDualConnected_union_of_hasCrossEdge
    (isDualConnected_singleton face) hfaces
  refine ⟨⟨face, Finset.mem_singleton_self face⟩, anchor, ?_⟩
  simpa [faceOfSubset] using hcross

/-- Strong fixed-star connectivity supplies dual connectivity whenever the face-intersection
graph is connected. -/
theorem IsStrongVertexStarConnected.isDualConnected
    {faces : Finset (Finset Vertex)}
    (hstar : IsStrongVertexStarConnected faces)
    (hinter : ∀ f g : Face faces,
      Relation.ReflTransGen (FaceIntersects faces) f g) :
    IsDualConnected faces :=
  hstar.isVertexStarConnected.isDualConnected hinter

/-- Incidence conditions making a finite family of triangles a connected pseudomanifold with
boundary: it is nonempty, no edge has valence above two, and its dual graph is connected. -/
structure SurfaceIncidence (faces : Finset (Finset Vertex)) : Prop where
  faces_nonempty : faces.Nonempty
  edge_valence_le_two :
    ∀ e ∈ edges faces, (faces.filter fun t => e ⊆ t).card ≤ 2
  dual_connected : IsDualConnected faces

end TriangleFamily

/-- A finite triangulation of the topological space `S` by geometric 2-simplexes: a finite vertex
type, a finite family of 3-element faces, and a homeomorphism from the geometric realization of
that family onto `S`.

There is no separate `realization` field to weaken: the realization is computed from the
combinatorial data, so a `GeometricTriangulation S` exists only when `S` really is a finite
two-dimensional polyhedron. -/
structure GeometricTriangulation (S : Type*) [TopologicalSpace S] where
  /-- The (finite) vertex type of the triangulation. -/
  Vertex : Type
  /-- The vertex type is finite. -/
  [vertexFintype : Fintype Vertex]
  /-- Vertices have decidable equality. -/
  [vertexDecidableEq : DecidableEq Vertex]
  /-- The faces: each is a set of vertices spanning a geometric 2-simplex. -/
  faces : Finset (Finset Vertex)
  /-- Every face has exactly three vertices, so the complex is purely two-dimensional. -/
  faces_card : ∀ t ∈ faces, t.card = 3
  /-- The geometric realization of the face family is homeomorphic to `S`. -/
  homeo : GeometricRealization Vertex faces ≃ₜ S

attribute [instance] GeometricTriangulation.vertexFintype
attribute [instance] GeometricTriangulation.vertexDecidableEq

/-- Expanded, independently inspectable form of `GeometricTriangulation`.

This theorem pins the public meaning of the structure: no realization or incidence data is hidden
behind an additional field. -/
theorem nonempty_geometricTriangulation_iff_explicit
    {S : Type*} [TopologicalSpace S] :
    Nonempty (GeometricTriangulation S) ↔
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
        (F : Finset (Finset V)),
        (∀ t ∈ F, t.card = 3) ∧ Nonempty (GeometricRealization V F ≃ₜ S) := by
  constructor
  · rintro ⟨T⟩
    exact ⟨T.Vertex, T.vertexFintype, T.vertexDecidableEq, T.faces,
      T.faces_card, ⟨T.homeo⟩⟩
  · rintro ⟨V, hVfinite, hVdecidable, F, hF, ⟨h⟩⟩
    let : Fintype V := hVfinite
    let : DecidableEq V := hVdecidable
    exact ⟨{ Vertex := V, faces := F, faces_card := hF, homeo := h }⟩

namespace GeometricTriangulation

variable {S : Type*} [TopologicalSpace S] (T : GeometricTriangulation S)

/-- Surface-incidence certificate for a faithful geometric triangulation. -/
abbrev SurfaceIncidence : Prop :=
  TriangleFamily.SurfaceIncidence T.faces

/-- The realization of the triangulation, as a polyhedron in barycentric coordinates. -/
abbrev realization : Set (T.Vertex → ℝ) :=
  GeometricRealization T.Vertex T.faces

include T in
/-- Must-imply anchor: a finitely triangulated space is compact.  This is what rules out the
empty/junk triangulations that satisfied the previous `SurfaceTriangulable` predicate. -/
theorem compactSpace : CompactSpace S :=
  Homeomorph.compactSpace T.homeo

include T in
/-- Must-imply anchor: a finitely triangulated space is Hausdorff (the realization is a subspace
of a finite product of lines). -/
theorem t2Space : T2Space S :=
  Topology.IsEmbedding.t2Space (Homeomorph.isEmbedding T.homeo.symm)

/-- A triangulation of a nonempty space has at least one two-dimensional face. -/
theorem faces_nonempty [Nonempty S] : T.faces.Nonempty := by
  let s : S := Classical.choice inferInstance
  rcases (T.homeo.symm s).2.2 with ⟨t, ht, _⟩
  exact ⟨t, ht⟩

/-- On a connected realization, local edge-connectedness of every vertex star is enough to
deduce global dual connectivity. -/
theorem faces_isDualConnected_of_isVertexStarConnected [ConnectedSpace S]
    (hstar : TriangleFamily.IsVertexStarConnected T.faces) :
    TriangleFamily.IsDualConnected T.faces := by
  let : ConnectedSpace T.realization :=
    T.homeo.connectedSpace_iff.mpr inferInstance
  have hpre : IsPreconnected (GeometricRealization T.Vertex T.faces) := by
    simpa only [Subtype.range_val] using
      (isPreconnected_range
        (continuous_subtype_val :
          Continuous (fun x : T.realization ↦ (x : T.Vertex → ℝ))))
  apply hstar.isDualConnected
  apply TriangleFamily.isFaceIntersectionConnected_of_isPreconnected _ hpre
  intro f
  rw [← Finset.card_pos, T.faces_card f.1 f.2]
  decide

/-- On a connected realization, strong fixed-star connectivity also implies global dual
connectivity. -/
theorem faces_isDualConnected_of_isStrongVertexStarConnected [ConnectedSpace S]
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces) :
    TriangleFamily.IsDualConnected T.faces :=
  T.faces_isDualConnected_of_isVertexStarConnected hstar.isVertexStarConnected

/-- A triangulation of a nonempty space has at least three available vertices. -/
theorem three_le_card_vertex [Nonempty S] : 3 ≤ Fintype.card T.Vertex := by
  obtain ⟨t, ht⟩ := T.faces_nonempty
  calc
    3 = t.card := (T.faces_card t ht).symm
    _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ t)
    _ = Fintype.card T.Vertex := Finset.card_univ

/-- The edges of the triangulation: the 2-element subsets of its faces. -/
def edges : Finset (Finset T.Vertex) :=
  T.faces.biUnion fun t => t.powersetCard 2

theorem card_of_mem_edges {e : Finset T.Vertex} (he : e ∈ T.edges) : e.card = 2 := by
  rcases Finset.mem_biUnion.mp he with ⟨t, _ht, het⟩
  exact (Finset.mem_powersetCard.mp het).2

theorem mem_edges_of_subset_face {e t : Finset T.Vertex} (ht : t ∈ T.faces) (het : e ⊆ t)
    (he : e.card = 2) : e ∈ T.edges :=
  Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_powersetCard.mpr ⟨het, he⟩⟩

/-- The edge type of the triangulation. -/
abbrev Edge : Type :=
  {e : Finset T.Vertex // e ∈ T.edges}

/-- The triangle (face) type of the triangulation. -/
abbrev Triangle : Type :=
  {t : Finset T.Vertex // t ∈ T.faces}

theorem edge_card (e : T.Edge) : e.1.card = 2 :=
  T.card_of_mem_edges e.2

theorem triangle_card (t : T.Triangle) : t.1.card = 3 :=
  T.faces_card t.1 t.2

/-- The chosen first endpoint of an edge. -/
noncomputable def edgeSource (e : T.Edge) : T.Vertex :=
  (Finset.card_eq_two.mp (T.edge_card e)).choose

/-- The chosen second endpoint of an edge. -/
noncomputable def edgeTarget (e : T.Edge) : T.Vertex :=
  (Finset.card_eq_two.mp (T.edge_card e)).choose_spec.choose

theorem edgeSource_ne_edgeTarget (e : T.Edge) : T.edgeSource e ≠ T.edgeTarget e :=
  (Finset.card_eq_two.mp (T.edge_card e)).choose_spec.choose_spec.1

theorem edge_eq_pair (e : T.Edge) : e.1 = {T.edgeSource e, T.edgeTarget e} :=
  (Finset.card_eq_two.mp (T.edge_card e)).choose_spec.choose_spec.2

theorem edgeSource_mem (e : T.Edge) : T.edgeSource e ∈ e.1 := by
  rw [T.edge_eq_pair e]
  simp

theorem edgeTarget_mem (e : T.Edge) : T.edgeTarget e ∈ e.1 := by
  rw [T.edge_eq_pair e]
  simp

/-- An edge is a boundary edge when it lies in exactly one face. -/
def IsBoundaryEdge (e : T.Edge) : Prop :=
  (T.faces.filter fun t => e.1 ⊆ t).card = 1

end GeometricTriangulation

end ClassificationOfSurfaces
end Topology
end LeanEval
