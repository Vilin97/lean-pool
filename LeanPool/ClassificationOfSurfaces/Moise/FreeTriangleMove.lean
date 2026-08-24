/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.FreeTriangle
import LeanPool.ClassificationOfSurfaces.Moise.ThinKiteMove

/-!
# The supported move at a free triangle

This file transports the normalized thin-kite move to an arbitrary plane triangle.  Compactness
supplies the small positive thickness required by the relative polygonal Schoenflies theorem.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- An affine equivalence of the plane, regarded as a homeomorphism. -/
noncomputable def affineEquivHomeomorph (e : Plane ≃ᵃ[ℝ] Plane) : Plane ≃ₜ Plane where
  toEquiv := e.toEquiv
  continuous_toFun := e.toAffineMap.continuous_of_finiteDimensional
  continuous_invFun := e.symm.toAffineMap.continuous_of_finiteDimensional

@[simp] theorem affineEquivHomeomorph_apply (e : Plane ≃ᵃ[ℝ] Plane) (p : Plane) :
    affineEquivHomeomorph e p = e p := rfl

@[simp] theorem affineEquivHomeomorph_symm_apply (e : Plane ≃ᵃ[ℝ] Plane) (p : Plane) :
    (affineEquivHomeomorph e).symm p = e.symm p := rfl

theorem affineEquivHomeomorph_image_segment (e : Plane ≃ᵃ[ℝ] Plane) (a b : Plane) :
    affineEquivHomeomorph e '' segment ℝ a b = segment ℝ (e a) (e b) := by
  exact image_segment ℝ e.toAffineMap a b

/-- Conjugate the normalized kite move by an affine coordinate system. -/
noncomputable def transportedThinKiteHomeomorph (e : Plane ≃ᵃ[ℝ] Plane)
    (δ : ℝ) (hδ : 0 < δ) : Plane ≃ₜ Plane :=
  (affineEquivHomeomorph e).symm.trans
    ((thinKiteAmbientHomeomorph δ hδ).trans (affineEquivHomeomorph e))

/-- The `transportedThinKitePatch` declaration. -/
def transportedThinKitePatch (e : Plane ≃ᵃ[ℝ] Plane) (δ : ℝ) : Set Plane :=
  e '' thinKitePatch δ

theorem transportedThinKiteHomeomorph_eqOn_compl (e : Plane ≃ᵃ[ℝ] Plane)
    (δ : ℝ) (hδ : 0 < δ) :
    Set.EqOn (transportedThinKiteHomeomorph e δ hδ) id
      (transportedThinKitePatch e δ)ᶜ := by
  intro p hp
  have hpre : e.symm p ∉ thinKitePatch δ := by
    intro hmem
    apply hp
    exact ⟨e.symm p, hmem, by simp⟩
  rw [transportedThinKiteHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply,
    affineEquivHomeomorph_symm_apply,
    thinKiteAmbientHomeomorph_eqOn_compl δ hδ hpre]
  simp

theorem transportedThinKiteHomeomorph_image_baseSegment (e : Plane ≃ᵃ[ℝ] Plane)
    (δ : ℝ) (hδ : 0 < δ) :
    transportedThinKiteHomeomorph e δ hδ ''
        segment ℝ (e (planePoint (-1) 0)) (e (planePoint 1 0)) =
      segment ℝ (e (planePoint (-1) 0)) (e (planePoint 0 1)) ∪
        segment ℝ (e (planePoint 1 0)) (e (planePoint 0 1)) := by
  have hsegment (a b : Plane) :
      segment ℝ (e a) (e b) = e '' segment ℝ a b := by
    exact (image_segment ℝ e.toAffineMap a b).symm
  rw [hsegment, hsegment, hsegment, ← Set.image_union,
    ← thinKiteAmbientHomeomorph_image_baseSegment δ hδ]
  ext p
  simp [transportedThinKiteHomeomorph, Set.mem_image]

/-- A sufficiently thin transported kite lies in every open neighborhood of its limiting
triangle. -/
theorem exists_thinKitePatch_subset_open (e : Plane ≃ᵃ[ℝ] Plane)
    (U : Set Plane) (hU : IsOpen U)
    (htriangle : e '' convexHull ℝ (Set.range kiteTrianglePosition) ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ transportedThinKitePatch e δ ⊆ U := by
  have hcompact : IsCompact diamondPatch := by
    rw [← diamondFanMesh_support 0 (by norm_num) (by norm_num)]
    exact (diamondFanMesh 0 (by norm_num) (by norm_num)).toPlaneComplex.isCompact_support
  have hcontinuous : Continuous fun z : ℝ × Plane => e (thinKiteMap z.1 z.2) := by
    apply e.toAffineMap.continuous_of_finiteDimensional.comp
    unfold thinKiteMap thinKiteScale planePoint
    fun_prop
  have heventually : ∀ᶠ δ in nhds (0 : ℝ),
      ∀ q ∈ diamondPatch, e (thinKiteMap δ q) ∈ U := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro q hq
    apply hcontinuous.continuousAt.eventually
    apply hU.mem_nhds
    apply htriangle
    exact ⟨thinKiteMap 0 q, thinKiteMap_zero_mem_triangle hq, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp heventually
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδball : δ ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [δ]
    rw [abs_of_nonneg (by positivity)]
    linarith
  refine ⟨δ, hδ, ?_⟩
  intro p hp
  obtain ⟨r, ⟨q, hq, rfl⟩, rfl⟩ := hp
  exact hball hδball q hq

/-- Uniform version of `exists_thinKitePatch_subset_open`: every smaller positive thickness
also lies in the prescribed open set. -/
theorem exists_eventually_transportedThinKitePatch_subset_open
    (e : Plane ≃ᵃ[ℝ] Plane) (U : Set Plane) (hU : IsOpen U)
    (htriangle : e '' convexHull ℝ (Set.range kiteTrianglePosition) ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      transportedThinKitePatch e δ ⊆ U := by
  have hopen : IsOpen (e ⁻¹' U) := hU.preimage e.toAffineMap.continuous_of_finiteDimensional
  have hpre : convexHull ℝ (Set.range kiteTrianglePosition) ⊆ e ⁻¹' U := by
    intro p hp
    exact htriangle ⟨p, hp, rfl⟩
  obtain ⟨ε, hε, hpatch⟩ :=
    exists_thinKitePatch_subset_open_normalized (e ⁻¹' U) hopen hpre
  refine ⟨ε, hε, fun δ hδ hδε p hp => ?_⟩
  obtain ⟨q, hq, rfl⟩ := hp
  exact hpatch δ hδ hδε hq

namespace TriangleMesh

variable (M : TriangleMesh)

/-- Order a triangle so that index `2` is a specified opposite vertex. -/
noncomputable def freeTriangleOrder (T : M.Triangle) (k : Fin 3) : Fin 3 → Plane :=
  fun i => M.position (M.orderedVertex T ((Equiv.swap 2 k) i))

theorem freeTriangleOrder_affineIndependent (T : M.Triangle) (k : Fin 3) :
    AffineIndependent ℝ (M.freeTriangleOrder T k) := by
  exact (M.orderedVertex_affineIndependent T).comp_embedding (Equiv.swap 2 k).toEmbedding

theorem range_freeTriangleOrder (T : M.Triangle) (k : Fin 3) :
    Set.range (M.freeTriangleOrder T k) = M.position '' (T.1 : Set M.Vertex) := by
  change Set.range ((M.position ∘ M.orderedVertex T) ∘ Equiv.swap 2 k) = _
  rw [EquivLike.range_comp]
  rw [Set.range_comp, M.range_orderedVertex T]

theorem triangle_eq_orderedVertices (T : M.Triangle) :
    T.1 = {M.orderedVertex T 0, M.orderedVertex T 1, M.orderedVertex T 2} := by
  ext v
  constructor
  · intro hv
    have hvRange : v ∈ Set.range (M.orderedVertex T) := by
      rw [M.range_orderedVertex T]
      exact hv
    obtain ⟨i, rfl⟩ := hvRange
    fin_cases i <;> simp
  · intro hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact M.orderedVertex_mem T 0
    · exact M.orderedVertex_mem T 1
    · exact M.orderedVertex_mem T 2

theorem triangleEdges_eq_orderedEdges (T : M.Triangle) :
    M.triangleEdges T.1 =
      {{M.orderedVertex T 0, M.orderedVertex T 1},
        {M.orderedVertex T 0, M.orderedVertex T 2},
        {M.orderedVertex T 1, M.orderedVertex T 2}} := by
  rw [triangleEdges, M.triangle_eq_orderedVertices T]
  have h01 : M.orderedVertex T 0 ≠ M.orderedVertex T 1 :=
    (M.orderedVertex_injective T).ne (by decide)
  have h02 : M.orderedVertex T 0 ≠ M.orderedVertex T 2 :=
    (M.orderedVertex_injective T).ne (by decide)
  have h12 : M.orderedVertex T 1 ≠ M.orderedVertex T 2 :=
    (M.orderedVertex_injective T).ne (by decide)
  ext e
  rw [Finset.mem_powersetCard]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hesub, hecard⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hecard
    have ha := hesub (by simp : a ∈ ({a, b} : Finset M.Vertex))
    have hb := hesub (by simp : b ∈ ({a, b} : Finset M.Vertex))
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
      subst a <;> subst b <;> simp_all [Finset.pair_comm]
  · intro he
    rcases he with rfl | rfl | rfl
    all_goals
      constructor
      · simp
      · simp_all

/-- Moise's first free-triangle case: the frontier meets the triangle in exactly its base edge. -/
def IsOneEdgeFreeTriangle (T : M.Triangle) (k : Fin 3) : Prop :=
  frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
    segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1)

/-- Moise's second free-triangle case: the frontier meets the triangle in exactly the two edges
through the apex. -/
def IsTwoEdgeFreeTriangle (T : M.Triangle) (k : Fin 3) : Prop :=
  frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
    segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
      segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)

/-- The `IsGeometricallyFreeTriangle` declaration. -/
def IsGeometricallyFreeTriangle (T : M.Triangle) : Prop :=
  ∃ k : Fin 3, M.IsOneEdgeFreeTriangle T k ∨ M.IsTwoEdgeFreeTriangle T k

/-- The relative interior of the base in the Figure 3.3 ordering misses both apex edges. -/
theorem freeTriangleBase_diff_endpoints_disjoint_apexEdges (T : M.Triangle) (k : Fin 3) :
    Disjoint
      (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) \
        {M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 1})
      (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
        segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)) := by
  let a := M.freeTriangleOrder T k 0
  let b := M.freeTriangleOrder T k 1
  let c := M.freeTriangleOrder T k 2
  have habc : AffineIndependent ℝ ![a, b, c] := by
    convert M.freeTriangleOrder_affineIndependent T k using 1
    funext i
    fin_cases i <;> rfl
  have hbac : AffineIndependent ℝ ![b, a, c] := by
    convert habc.comp_embedding (Equiv.swap (0 : Fin 3) 1).toEmbedding using 1
    funext i
    fin_cases i <;> rfl
  have h0 : segment ℝ a b ∩ segment ℝ a c = {a} := by
    simpa only [segment_symm ℝ b a] using
      (segment_inter_segment_of_affineIndependent (x := b) (y := a) (z := c) hbac)
  have h1 : segment ℝ a b ∩ segment ℝ b c = {b} :=
    segment_inter_segment_of_affineIndependent (x := a) (y := b) (z := c) habc
  rw [Set.disjoint_left]
  change ∀ ⦃x⦄, x ∈ segment ℝ a b \ {a, b} →
    x ∈ segment ℝ a c ∪ segment ℝ b c → False
  rintro x ⟨hxBase, hxEnds⟩ (hxApex0 | hxApex1)
  · have hx : x ∈ ({a} : Set Plane) := by
      rw [← h0]
      exact ⟨hxBase, hxApex0⟩
    exact hxEnds (Or.inl (Set.mem_singleton_iff.mp hx))
  · have hx : x ∈ ({b} : Set Plane) := by
      rw [← h1]
      exact ⟨hxBase, hxApex1⟩
    exact hxEnds (Or.inr (Set.mem_singleton_iff.mp hx))

/-- The abstract mesh edge underlying the base in the Figure 3.3 ordering. -/
noncomputable def freeTriangleBaseEdge (T : M.Triangle) (k : Fin 3) : Finset M.Vertex :=
  (Finset.univ.erase k).image (M.orderedVertex T)

/-- The first abstract edge from a base endpoint to the apex. -/
noncomputable def freeTriangleApexEdge0 (T : M.Triangle) (k : Fin 3) : Finset M.Vertex :=
  {M.orderedVertex T ((Equiv.swap 2 k) 0),
    M.orderedVertex T ((Equiv.swap 2 k) 2)}

/-- The second abstract edge from a base endpoint to the apex. -/
noncomputable def freeTriangleApexEdge1 (T : M.Triangle) (k : Fin 3) : Finset M.Vertex :=
  {M.orderedVertex T ((Equiv.swap 2 k) 1),
    M.orderedVertex T ((Equiv.swap 2 k) 2)}

theorem freeTriangleBaseEdge_card (T : M.Triangle) (k : Fin 3) :
    (M.freeTriangleBaseEdge T k).card = 2 := by
  rw [freeTriangleBaseEdge, Finset.card_image_of_injective _ (M.orderedVertex_injective T),
    Finset.card_erase_of_mem (Finset.mem_univ k)]
  decide

theorem freeTriangleBaseEdge_subset (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleBaseEdge T k ⊆ T.1 := by
  intro v hv
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  exact M.orderedVertex_mem T i

theorem freeTriangleBaseEdge_mem_edges (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleBaseEdge T k ∈ M.edges := by
  apply Finset.mem_biUnion.mpr
  exact ⟨T.1, T.2, Finset.mem_powersetCard.mpr
    ⟨M.freeTriangleBaseEdge_subset T k, M.freeTriangleBaseEdge_card T k⟩⟩

theorem freeTriangleApexEdge0_card (T : M.Triangle) (k : Fin 3) :
    (M.freeTriangleApexEdge0 T k).card = 2 := by
  rw [freeTriangleApexEdge0, Finset.card_pair]
  exact (M.orderedVertex_injective T).ne <| (Equiv.swap 2 k).injective.ne (by decide)

theorem freeTriangleApexEdge1_card (T : M.Triangle) (k : Fin 3) :
    (M.freeTriangleApexEdge1 T k).card = 2 := by
  rw [freeTriangleApexEdge1, Finset.card_pair]
  exact (M.orderedVertex_injective T).ne <| (Equiv.swap 2 k).injective.ne (by decide)

theorem freeTriangleApexEdge0_subset (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleApexEdge0 T k ⊆ T.1 := by
  intro v hv
  simp only [freeTriangleApexEdge0, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> exact M.orderedVertex_mem T _

theorem freeTriangleApexEdge1_subset (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleApexEdge1 T k ⊆ T.1 := by
  intro v hv
  simp only [freeTriangleApexEdge1, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> exact M.orderedVertex_mem T _

theorem freeTriangleApexEdge0_mem_edges (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleApexEdge0 T k ∈ M.edges := by
  apply Finset.mem_biUnion.mpr
  exact ⟨T.1, T.2, Finset.mem_powersetCard.mpr
    ⟨M.freeTriangleApexEdge0_subset T k, M.freeTriangleApexEdge0_card T k⟩⟩

theorem freeTriangleApexEdge1_mem_edges (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleApexEdge1 T k ∈ M.edges := by
  apply Finset.mem_biUnion.mpr
  exact ⟨T.1, T.2, Finset.mem_powersetCard.mpr
    ⟨M.freeTriangleApexEdge1_subset T k, M.freeTriangleApexEdge1_card T k⟩⟩

theorem image_freeTriangleBaseEdge (T : M.Triangle) (k : Fin 3) :
    M.position '' (M.freeTriangleBaseEdge T k : Set M.Vertex) =
      {M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 1} := by
  have hindices : (Finset.univ.erase k : Finset (Fin 3)) =
      {(Equiv.swap 2 k) 0, (Equiv.swap 2 k) 1} := by
    fin_cases k <;> decide
  rw [freeTriangleBaseEdge, hindices]
  rw [Finset.image_insert, Finset.image_singleton]
  ext p
  simp [freeTriangleOrder, eq_comm]

theorem freeTriangleBaseEdge_eq_orderedPair (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleBaseEdge T k =
      {M.orderedVertex T ((Equiv.swap 2 k) 0),
        M.orderedVertex T ((Equiv.swap 2 k) 1)} := by
  have hindices : (Finset.univ.erase k : Finset (Fin 3)) =
      {(Equiv.swap 2 k) 0, (Equiv.swap 2 k) 1} := by
    fin_cases k <;> decide
  rw [freeTriangleBaseEdge, hindices]
  rw [Finset.image_insert, Finset.image_singleton]

theorem freeTriangleBaseEdge_carrier (T : M.Triangle) (k : Fin 3) :
    convexHull ℝ (M.position '' (M.freeTriangleBaseEdge T k : Set M.Vertex)) =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
  rw [M.image_freeTriangleBaseEdge T k, convexHull_pair]

theorem freeTriangleApexEdge0_carrier (T : M.Triangle) (k : Fin 3) :
    convexHull ℝ (M.position '' (M.freeTriangleApexEdge0 T k : Set M.Vertex)) =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) := by
  rw [show M.position '' (M.freeTriangleApexEdge0 T k : Set M.Vertex) =
    {M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 2} by
      ext p
      simp [freeTriangleApexEdge0, freeTriangleOrder, eq_comm]]
  exact convexHull_pair _ _

theorem freeTriangleApexEdge1_carrier (T : M.Triangle) (k : Fin 3) :
    convexHull ℝ (M.position '' (M.freeTriangleApexEdge1 T k : Set M.Vertex)) =
      segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2) := by
  rw [show M.position '' (M.freeTriangleApexEdge1 T k : Set M.Vertex) =
    {M.freeTriangleOrder T k 1, M.freeTriangleOrder T k 2} by
      ext p
      simp [freeTriangleApexEdge1, freeTriangleOrder, eq_comm]]
  exact convexHull_pair _ _

theorem triangleEdges_eq_freeTriangleEdges (T : M.Triangle) (k : Fin 3) :
    M.triangleEdges T.1 =
      {M.freeTriangleBaseEdge T k, M.freeTriangleApexEdge0 T k,
        M.freeTriangleApexEdge1 T k} := by
  rw [M.triangleEdges_eq_orderedEdges T]
  have hindices : (Finset.univ.erase k : Finset (Fin 3)) =
      {(Equiv.swap 2 k) 0, (Equiv.swap 2 k) 1} := by
    fin_cases k <;> decide
  rw [freeTriangleBaseEdge, hindices]
  fin_cases k
  · ext e
    simp only [Fin.isValue, Finset.pair_comm, Finset.mem_insert,
      Finset.mem_singleton, Fin.zero_eta, Equiv.swap_apply_right,
      Equiv.swap_apply_def, Fin.reduceEq, ↓reduceIte, one_ne_zero,
      Finset.image_insert, Finset.image_singleton, freeTriangleApexEdge0,
      freeTriangleApexEdge1]
    tauto
  · ext e
    simp only [Fin.isValue, Finset.pair_comm, Finset.mem_insert,
      Finset.mem_singleton, Fin.mk_one, Equiv.swap_apply_def, Fin.reduceEq,
      ↓reduceIte, zero_ne_one, Finset.image_insert, Finset.image_singleton,
      freeTriangleApexEdge0, freeTriangleApexEdge1]
    have h10 : ({M.orderedVertex T 1, M.orderedVertex T 0} : Finset M.Vertex) =
        {M.orderedVertex T 0, M.orderedVertex T 1} := Finset.pair_comm _ _
    rw [h10]
    tauto
  · ext e
    simp only [Fin.isValue, Finset.pair_comm, Finset.mem_insert,
      Finset.mem_singleton, Fin.reduceFinMk, Equiv.swap_self,
      Equiv.refl_apply, Finset.image_insert, Finset.image_singleton,
      freeTriangleApexEdge0, freeTriangleApexEdge1]

/-- Every triangle vertex lies on one of the two apex edges. -/
theorem triangleVertex_mem_freeTriangleApexEdges (T : M.Triangle) (k : Fin 3)
    {v : M.Vertex} (hv : v ∈ T.1) :
    M.position v ∈
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
        segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2) := by
  have hvRange : v ∈ Set.range (M.orderedVertex T) := by
    rw [M.range_orderedVertex T]
    exact hv
  obtain ⟨i, rfl⟩ := hvRange
  fin_cases k <;> fin_cases i <;>
    simp [freeTriangleOrder, Equiv.swap_apply_def, left_mem_segment,
      right_mem_segment]

-- Normalizing all six finite-order cases for the three geometric edges exceeds the default.
/-- The frontier of a maximal triangle is covered by the base and the two apex edges in every
Figure 3.3 ordering. -/
theorem frontier_triangleCarrier_subset_freeTriangleEdges (T : M.Triangle) (k : Fin 3) :
    frontier (M.triangleCarrier T.1) ⊆
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) ∪
        (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
          segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)) := by
  intro p hp
  obtain ⟨e, hecard, heT, hpe⟩ := M.exists_edge_of_mem_frontier_triangle T.2 hp
  have he : e ∈ M.triangleEdges T.1 :=
    Finset.mem_powersetCard.mpr ⟨heT, hecard⟩
  have hcarrier (a b : M.Vertex) :
      convexHull ℝ (M.position '' (({a, b} : Finset M.Vertex) : Set M.Vertex)) =
        segment ℝ (M.position a) (M.position b) := by
    rw [show M.position '' (({a, b} : Finset M.Vertex) : Set M.Vertex) =
      {M.position a, M.position b} by ext q; simp [eq_comm]]
    exact convexHull_pair _ _
  rw [M.triangleEdges_eq_orderedEdges T] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  have hpEdges : p ∈
      segment ℝ (M.position (M.orderedVertex T 0)) (M.position (M.orderedVertex T 1)) ∪
        (segment ℝ (M.position (M.orderedVertex T 0)) (M.position (M.orderedVertex T 2)) ∪
          segment ℝ (M.position (M.orderedVertex T 1))
            (M.position (M.orderedVertex T 2))) := by
    rcases he with rfl | rfl | rfl
    · rw [hcarrier] at hpe
      exact Or.inl hpe
    · rw [hcarrier] at hpe
      exact Or.inr (Or.inl hpe)
    · rw [hcarrier] at hpe
      exact Or.inr (Or.inr hpe)
  have horder :
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) ∪
          (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
            segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)) =
        segment ℝ (M.position (M.orderedVertex T 0)) (M.position (M.orderedVertex T 1)) ∪
          (segment ℝ (M.position (M.orderedVertex T 0)) (M.position (M.orderedVertex T 2)) ∪
            segment ℝ (M.position (M.orderedVertex T 1))
              (M.position (M.orderedVertex T 2))) := by
    ext x
    simp only [Set.mem_union]
    have hsymm (a b : Plane) : x ∈ segment ℝ a b ↔ x ∈ segment ℝ b a := by
      rw [segment_symm]
    have h01 := hsymm (M.position (M.orderedVertex T 0))
      (M.position (M.orderedVertex T 1))
    have h02 := hsymm (M.position (M.orderedVertex T 0))
      (M.position (M.orderedVertex T 2))
    have h12 := hsymm (M.position (M.orderedVertex T 1))
      (M.position (M.orderedVertex T 2))
    fin_cases k
    · simp only [freeTriangleOrder, Fin.isValue, Fin.zero_eta, Equiv.swap_apply_right,
        Equiv.swap_apply_def, Fin.reduceEq, ↓reduceIte, one_ne_zero]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inr (h12.mpr h))
        · exact Or.inr (Or.inl (h02.mpr h))
        · exact Or.inl (h01.mpr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inr (h01.mp h))
        · exact Or.inr (Or.inl (h02.mp h))
        · exact Or.inl (h12.mp h)
    · simp only [freeTriangleOrder, Fin.isValue, Fin.mk_one, Equiv.swap_apply_def, Fin.reduceEq,
        ↓reduceIte, zero_ne_one]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (h12.mpr h))
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (h12.mp h))
    · simp [freeTriangleOrder]
  rwa [horder]

theorem freeTriangleBaseSegment_eq_oppositeEdgeCarrier (T : M.Triangle) (k : Fin 3) :
    segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) =
      convexHull ℝ ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane) := by
  fin_cases k
  · unfold freeTriangleOrder oppositeEdgePoints
    change segment ℝ (M.position (M.orderedVertex T 2))
        (M.position (M.orderedVertex T 1)) =
      convexHull ℝ (((Finset.univ.erase (0 : Fin 3)).image
        (M.position ∘ M.orderedVertex T) : Finset Plane) : Set Plane)
    rw [show (Finset.univ.erase (0 : Fin 3)) = {1, 2} by decide]
    simp [convexHull_pair, segment_symm]
  · unfold freeTriangleOrder oppositeEdgePoints
    change segment ℝ (M.position (M.orderedVertex T 0))
        (M.position (M.orderedVertex T 2)) =
      convexHull ℝ (((Finset.univ.erase (1 : Fin 3)).image
        (M.position ∘ M.orderedVertex T) : Finset Plane) : Set Plane)
    rw [show (Finset.univ.erase (1 : Fin 3)) = {0, 2} by decide]
    simp [convexHull_pair]
  · unfold freeTriangleOrder oppositeEdgePoints
    change segment ℝ (M.position (M.orderedVertex T 0))
        (M.position (M.orderedVertex T 1)) =
      convexHull ℝ (((Finset.univ.erase (2 : Fin 3)).image
        (M.position ∘ M.orderedVertex T) : Finset Plane) : Set Plane)
    rw [show (Finset.univ.erase (2 : Fin 3)) = {0, 1} by decide]
    simp [convexHull_pair]

theorem isGeometricallyFreeTriangle_of_boundaryEdges_card_one (T : M.Triangle)
    (hvertices : M.HasNoIsolatedFrontierVertex T.1)
    (hcard : (M.boundaryEdges T.1).card = 1) :
    M.IsGeometricallyFreeTriangle T := by
  obtain ⟨e, hboundary⟩ := Finset.card_eq_one.mp hcard
  have heMem : e ∈ M.boundaryEdges T.1 := by rw [hboundary]; simp
  have heData := M.mem_boundaryEdges_iff.mp heMem
  obtain ⟨k, hedge⟩ := M.exists_oppositeEdgePoints_eq T heData.1 heData.2.1
  refine ⟨k, Or.inl ?_⟩
  rw [IsOneEdgeFreeTriangle, M.frontier_inter_triangleCarrier_eq_boundaryEdges T.2 hvertices,
    hboundary]
  simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
  rw [M.freeTriangleBaseSegment_eq_oppositeEdgeCarrier T k, hedge, Finset.coe_image]

/-- Moise's second free-triangle case: if exactly two edges of a triangle lie on the mesh
frontier, their common endpoint can be chosen as the apex of the Figure 3.3 move. -/
theorem isGeometricallyFreeTriangle_of_boundaryEdges_card_two (T : M.Triangle)
    (hvertices : M.HasNoIsolatedFrontierVertex T.1)
    (hcard : (M.boundaryEdges T.1).card = 2) :
    M.IsGeometricallyFreeTriangle T := by
  have hproper : M.boundaryEdges T.1 ⊂ M.triangleEdges T.1 := by
    refine Finset.ssubset_iff_subset_ne.mpr
      ⟨M.boundaryEdges_subset_triangleEdges T.1, ?_⟩
    intro heq
    have := congrArg Finset.card heq
    rw [hcard, M.card_triangleEdges T.2] at this
    omega
  obtain ⟨e, heTriangle, heBoundary⟩ := Finset.exists_of_ssubset hproper
  have heData := Finset.mem_powersetCard.mp heTriangle
  obtain ⟨k, hedge⟩ := M.exists_oppositeEdgePoints_eq T heData.1 heData.2
  have hboundary : M.boundaryEdges T.1 = (M.triangleEdges T.1).erase e := by
    apply Finset.eq_of_subset_of_card_le
    · intro d hd
      exact Finset.mem_erase.mpr
        ⟨fun hde => heBoundary (hde ▸ hd), M.boundaryEdges_subset_triangleEdges T.1 hd⟩
    · rw [hcard, Finset.card_erase_of_mem heTriangle, M.card_triangleEdges T.2]
  have h01 : M.orderedVertex T 0 ≠ M.orderedVertex T 1 :=
    (M.orderedVertex_injective T).ne (by decide)
  have h02 : M.orderedVertex T 0 ≠ M.orderedVertex T 2 :=
    (M.orderedVertex_injective T).ne (by decide)
  have h12 : M.orderedVertex T 1 ≠ M.orderedVertex T 2 :=
    (M.orderedVertex_injective T).ne (by decide)
  have hEdge01Edge12 :
      {M.orderedVertex T 0, M.orderedVertex T 1} ≠
        ({M.orderedVertex T 1, M.orderedVertex T 2} : Finset M.Vertex) := by
    intro h
    have hs : ({M.orderedVertex T 0, M.orderedVertex T 1} : Set M.Vertex) =
        {M.orderedVertex T 1, M.orderedVertex T 2} := by
      simpa using congrArg (fun d : Finset M.Vertex => (d : Set M.Vertex)) h
    rw [Set.pair_eq_pair_iff] at hs
    exact hs.elim (fun h' => h01 h'.1) (fun h' => h02 h'.1)
  have hEdge02Edge12 :
      {M.orderedVertex T 0, M.orderedVertex T 2} ≠
        ({M.orderedVertex T 1, M.orderedVertex T 2} : Finset M.Vertex) := by
    intro h
    have hs : ({M.orderedVertex T 0, M.orderedVertex T 2} : Set M.Vertex) =
        {M.orderedVertex T 1, M.orderedVertex T 2} := by
      simpa using congrArg (fun d : Finset M.Vertex => (d : Set M.Vertex)) h
    rw [Set.pair_eq_pair_iff] at hs
    exact hs.elim (fun h' => h01 h'.1) (fun h' => h02 h'.1)
  have hEdge01Edge02 :
      {M.orderedVertex T 0, M.orderedVertex T 1} ≠
        ({M.orderedVertex T 0, M.orderedVertex T 2} : Finset M.Vertex) := by
    intro h
    have hs : ({M.orderedVertex T 0, M.orderedVertex T 1} : Set M.Vertex) =
        {M.orderedVertex T 0, M.orderedVertex T 2} := by
      simpa using congrArg (fun d : Finset M.Vertex => (d : Set M.Vertex)) h
    rw [Set.pair_eq_pair_iff] at hs
    exact hs.elim (fun h' => h12 h'.2) (fun h' => h02 h'.1)
  have hcarrier (a b : M.Vertex) :
      convexHull ℝ (M.position '' (({a, b} : Finset M.Vertex) : Set M.Vertex)) =
        segment ℝ (M.position a) (M.position b) := by
    rw [show M.position '' (({a, b} : Finset M.Vertex) : Set M.Vertex) =
      {M.position a, M.position b} by ext p; simp [eq_comm]]
    exact convexHull_pair _ _
  have hUnion (a b : Finset M.Vertex) :
      (⋃ d ∈ ({a, b} : Finset (Finset M.Vertex)),
        convexHull ℝ (M.position '' (d : Set M.Vertex))) =
        convexHull ℝ (M.position '' (a : Set M.Vertex)) ∪
          convexHull ℝ (M.position '' (b : Set M.Vertex)) := by
    ext p
    simp only [Set.mem_iUnion, Finset.mem_insert, Finset.mem_singleton, Set.mem_union]
    constructor
    · rintro ⟨d, rfl | rfl, hp⟩
      · exact Or.inl hp
      · exact Or.inr hp
    · rintro (hp | hp)
      · exact ⟨a, Or.inl rfl, hp⟩
      · exact ⟨b, Or.inr rfl, hp⟩
  refine ⟨k, Or.inr ?_⟩
  rw [IsTwoEdgeFreeTriangle,
    M.frontier_inter_triangleCarrier_eq_boundaryEdges T.2 hvertices, hboundary]
  fin_cases k
  · have he : e = {M.orderedVertex T 1, M.orderedVertex T 2} := by
      apply Finset.image_injective M.position_injective
      rw [← hedge]
      change Finset.image (M.position ∘ M.orderedVertex T)
          (Finset.univ.erase (0 : Fin 3)) = _
      rw [show Finset.univ.erase (0 : Fin 3) = {1, 2} by decide]
      simp
    rw [he, M.triangleEdges_eq_orderedEdges T]
    have herase :
        ({{M.orderedVertex T 0, M.orderedVertex T 1},
          {M.orderedVertex T 0, M.orderedVertex T 2},
          {M.orderedVertex T 1, M.orderedVertex T 2}} : Finset (Finset M.Vertex)).erase
            {M.orderedVertex T 1, M.orderedVertex T 2} =
          {{M.orderedVertex T 0, M.orderedVertex T 1},
            {M.orderedVertex T 0, M.orderedVertex T 2}} := by
      ext d
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hne, rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact (hne rfl).elim
      · rintro (rfl | rfl)
        · exact ⟨hEdge01Edge12, Or.inl rfl⟩
        · exact ⟨hEdge02Edge12, Or.inr (Or.inl rfl)⟩
    rw [herase]
    rw [hUnion]
    rw [hcarrier, hcarrier]
    simp [freeTriangleOrder, segment_symm, Equiv.swap_apply_def, Set.union_comm]
  · have he : e = {M.orderedVertex T 0, M.orderedVertex T 2} := by
      apply Finset.image_injective M.position_injective
      rw [← hedge]
      change Finset.image (M.position ∘ M.orderedVertex T)
          (Finset.univ.erase (1 : Fin 3)) = _
      rw [show Finset.univ.erase (1 : Fin 3) = {0, 2} by decide]
      simp
    rw [he, M.triangleEdges_eq_orderedEdges T]
    have herase :
        ({{M.orderedVertex T 0, M.orderedVertex T 1},
          {M.orderedVertex T 0, M.orderedVertex T 2},
          {M.orderedVertex T 1, M.orderedVertex T 2}} : Finset (Finset M.Vertex)).erase
            {M.orderedVertex T 0, M.orderedVertex T 2} =
          {{M.orderedVertex T 0, M.orderedVertex T 1},
            {M.orderedVertex T 1, M.orderedVertex T 2}} := by
      ext d
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hne, rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact (hne rfl).elim
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨hEdge01Edge02, Or.inl rfl⟩
        · exact ⟨hEdge02Edge12.symm, Or.inr (Or.inr rfl)⟩
    rw [herase]
    rw [hUnion]
    rw [hcarrier, hcarrier]
    simp only [freeTriangleOrder]
    simp only [Equiv.swap_apply_def]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, Fin.mk_one, zero_ne_one]
    rw [segment_symm ℝ (M.position (M.orderedVertex T 0))
      (M.position (M.orderedVertex T 1))]
    rw [segment_symm ℝ (M.position (M.orderedVertex T 1))
      (M.position (M.orderedVertex T 2))]
  · have he : e = {M.orderedVertex T 0, M.orderedVertex T 1} := by
      apply Finset.image_injective M.position_injective
      rw [← hedge]
      change Finset.image (M.position ∘ M.orderedVertex T)
          (Finset.univ.erase (2 : Fin 3)) = _
      rw [show Finset.univ.erase (2 : Fin 3) = {0, 1} by decide]
      simp
    rw [he, M.triangleEdges_eq_orderedEdges T]
    have herase :
        ({{M.orderedVertex T 0, M.orderedVertex T 1},
          {M.orderedVertex T 0, M.orderedVertex T 2},
          {M.orderedVertex T 1, M.orderedVertex T 2}} : Finset (Finset M.Vertex)).erase
            {M.orderedVertex T 0, M.orderedVertex T 1} =
          {{M.orderedVertex T 0, M.orderedVertex T 2},
            {M.orderedVertex T 1, M.orderedVertex T 2}} := by
      ext d
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hne, rfl | rfl | rfl⟩
        · exact (hne rfl).elim
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨hEdge01Edge02.symm, Or.inr (Or.inl rfl)⟩
        · exact ⟨hEdge01Edge12.symm, Or.inr (Or.inr rfl)⟩
    rw [herase]
    rw [hUnion]
    rw [hcarrier, hcarrier]
    simp [freeTriangleOrder]

/-- The finite conclusion used by Moise's cutting induction.  Once a weakly free triangle has
an edge-neighbor and no isolated frontier vertex, its frontier trace is one of the two
configurations in Figure 3.3. -/
theorem isGeometricallyFreeTriangle_of_isFreeTriangle
    (T U : M.Triangle) (hfree : M.IsFreeTriangle T.1)
    (hne : T.1 ≠ U.1) (hneighbors : M.AreEdgeNeighbors T.1 U.1)
    (hvertices : M.HasNoIsolatedFrontierVertex T.1) :
    M.IsGeometricallyFreeTriangle T := by
  have hnonempty := M.boundaryEdges_nonempty_of_isFreeTriangle hfree
  have hle : (M.boundaryEdges T.1).card ≤ 2 :=
    M.card_boundaryEdges_le_two_of_neighbor T.2 U.2 hne hneighbors
  have hcases : (M.boundaryEdges T.1).card = 1 ∨
      (M.boundaryEdges T.1).card = 2 := by
    have hpos : 0 < (M.boundaryEdges T.1).card := Finset.card_pos.mpr hnonempty
    omega
  rcases hcases with hcard | hcard
  · exact M.isGeometricallyFreeTriangle_of_boundaryEdges_card_one T hvertices hcard
  · exact M.isGeometricallyFreeTriangle_of_boundaryEdges_card_two T hvertices hcard

/-- The exact diagonal configuration in the hard branch of Moise Chapter 3, Theorem 3.  If a
weakly free triangle is not one of the Figure 3.3 configurations, it has one boundary edge and
an isolated opposite boundary vertex; the other two edges are the cutting diagonals. -/
theorem exists_cutting_diagonal_configuration
    (T U : M.Triangle) (hfree : M.IsFreeTriangle T.1)
    (hne : T.1 ≠ U.1) (hneighbors : M.AreEdgeNeighbors T.1 U.1)
    (hnot : ¬M.HasNoIsolatedFrontierVertex T.1) :
    ∃ a b v : M.Vertex,
      a ≠ b ∧ v ≠ a ∧ v ≠ b ∧
      T.1 = {a, b, v} ∧ M.boundaryEdges T.1 = {{a, b}} ∧
      M.position v ∈ frontier M.toPlaneComplex.support := by
  rw [HasNoIsolatedFrontierVertex] at hnot
  push Not at hnot
  obtain ⟨v, hvFrontier, hvTriangle, hvBoundary⟩ := hnot
  have hvT : v ∈ T.1 :=
    M.vertex_mem_triangle_of_frontier_not_mem_boundaryEdges T v hvFrontier hvTriangle hvBoundary
  have hnonempty := M.boundaryEdges_nonempty_of_isFreeTriangle hfree
  have hle : (M.boundaryEdges T.1).card ≤ 2 :=
    M.card_boundaryEdges_le_two_of_neighbor T.2 U.2 hne hneighbors
  have hcardCases : (M.boundaryEdges T.1).card = 1 ∨
      (M.boundaryEdges T.1).card = 2 := by
    have hpos : 0 < (M.boundaryEdges T.1).card := Finset.card_pos.mpr hnonempty
    omega
  have hcard : (M.boundaryEdges T.1).card = 1 := by
    rcases hcardCases with hcard | hcard
    · exact hcard
    · exfalso
      obtain ⟨e, f, hef, hboundary⟩ := Finset.card_eq_two.mp hcard
      have heMem : e ∈ M.boundaryEdges T.1 := by rw [hboundary]; simp
      have hfMem : f ∈ M.boundaryEdges T.1 := by rw [hboundary]; simp
      have heData := M.mem_boundaryEdges_iff.mp heMem
      have hfData := M.mem_boundaryEdges_iff.mp hfMem
      have hvNotE : v ∉ e := by
        intro hve
        exact hvBoundary e heMem (subset_convexHull ℝ _ ⟨v, hve, rfl⟩)
      have hvNotF : v ∉ f := by
        intro hvf
        exact hvBoundary f hfMem (subset_convexHull ℝ _ ⟨v, hvf, rfl⟩)
      have heraseCard : (T.1.erase v).card = 2 := by
        rw [Finset.card_erase_of_mem hvT, M.card_triangle T.1 T.2]
      have heErase : e = T.1.erase v :=
        Finset.eq_of_subset_of_card_le
          (fun w hw => Finset.mem_erase.mpr ⟨fun hwv => hvNotE (hwv ▸ hw), heData.1 hw⟩)
          (by rw [heData.2.1, heraseCard])
      have hfErase : f = T.1.erase v :=
        Finset.eq_of_subset_of_card_le
          (fun w hw => Finset.mem_erase.mpr ⟨fun hwv => hvNotF (hwv ▸ hw), hfData.1 hw⟩)
          (by rw [hfData.2.1, heraseCard])
      exact hef (heErase.trans hfErase.symm)
  obtain ⟨e, hboundary⟩ := Finset.card_eq_one.mp hcard
  have heMem : e ∈ M.boundaryEdges T.1 := by rw [hboundary]; simp
  have heData := M.mem_boundaryEdges_iff.mp heMem
  have hvNotE : v ∉ e := by
    intro hve
    exact hvBoundary e heMem (subset_convexHull ℝ _ ⟨v, hve, rfl⟩)
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp heData.2.1
  have hva : v ≠ a := fun h => hvNotE (h ▸ by simp)
  have hvb : v ≠ b := fun h => hvNotE (h ▸ by simp)
  have htriangle : T.1 = {a, b, v} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact heData.1 (by simp)
      · exact heData.1 (by simp)
      · exact hvT
    · rw [M.card_triangle T.1 T.2]
      have hcardTriple : ({a, b, v} : Finset M.Vertex).card = 3 := by
        simp [hab, Ne.symm hva, Ne.symm hvb]
      omega
  exact ⟨a, b, v, hab, hva, hvb, htriangle, hboundary, hvFrontier⟩

/-- Affine coordinates taking the normalized kite triangle to `T`. -/
noncomputable def freeTriangleAffineEquiv (T : M.Triangle) (k : Fin 3) : Plane ≃ᵃ[ℝ] Plane :=
  triangleAffineEquiv kiteTrianglePosition (M.freeTriangleOrder T k)
    kiteTrianglePosition_affineIndependent (M.freeTriangleOrder_affineIndependent T k)

@[simp] theorem freeTriangleAffineEquiv_apply_vertex (T : M.Triangle) (k i : Fin 3) :
    M.freeTriangleAffineEquiv T k (kiteTrianglePosition i) = M.freeTriangleOrder T k i := by
  exact triangleAffineEquiv_apply kiteTrianglePosition (M.freeTriangleOrder T k)
    kiteTrianglePosition_affineIndependent (M.freeTriangleOrder_affineIndependent T k) i

theorem freeTriangleAffineEquiv_image_triangle (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleAffineEquiv T k '' convexHull ℝ (Set.range kiteTrianglePosition) =
      M.triangleCarrier T.1 := by
  rw [triangleCarrier, ← M.range_freeTriangleOrder T k]
  exact triangleAffineEquiv_image_convexHull kiteTrianglePosition (M.freeTriangleOrder T k)
    kiteTrianglePosition_affineIndependent (M.freeTriangleOrder_affineIndependent T k)

/-- Every boundary edge other than the base of a one-edge move is avoided by all sufficiently
thin transported kites, except possibly at the two base endpoints. -/
theorem exists_transportedThinKitePatch_inter_boundaryEdge_subset_baseEndpoints
    (T : M.Triangle) (k : Fin 3)
    (htrace : frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1))
    (e : Finset M.Vertex) (he : M.IsBoundaryEdge e)
    (hne : e ≠ M.freeTriangleBaseEdge T k) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      transportedThinKitePatch (M.freeTriangleAffineEquiv T k) δ ∩
          convexHull ℝ (M.position '' (e : Set M.Vertex)) ⊆
        {M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 1} := by
  classical
  let E := M.freeTriangleAffineEquiv T k
  have hecard := M.card_of_mem_edges he.1
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hecard
  let a := E.symm (M.position v)
  let b := E.symm (M.position w)
  have hab : a ≠ b := by
    intro hab
    apply hvw
    apply M.position_injective
    simpa [a, b] using congrArg E hab
  have hcarrier :
      convexHull ℝ (M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex)) =
        segment ℝ (M.position v) (M.position w) := by
    rw [show M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex) =
      {M.position v, M.position w} by ext p; simp [eq_comm]]
    exact convexHull_pair _ _
  have hsegmentImage : E '' segment ℝ a b =
      segment ℝ (M.position v) (M.position w) := by
    calc
      E '' segment ℝ a b = segment ℝ (E a) (E b) :=
        image_segment ℝ E.toAffineMap a b
      _ = segment ℝ (M.position v) (M.position w) := by simp [a, b]
  have hbaseEdge := M.freeTriangleBaseEdge_mem_edges T k
  have hcommonCard :
      (({v, w} : Finset M.Vertex) ∩ M.freeTriangleBaseEdge T k).card ≤ 1 := by
    by_contra hcard
    have hcardTwo :
        (({v, w} : Finset M.Vertex) ∩ M.freeTriangleBaseEdge T k).card = 2 := by
      have hle := Finset.card_le_card
        (Finset.inter_subset_left : ({v, w} : Finset M.Vertex) ∩
          M.freeTriangleBaseEdge T k ⊆ {v, w})
      simp [hvw] at hle
      omega
    have heqLeft : ({v, w} : Finset M.Vertex) ∩ M.freeTriangleBaseEdge T k = {v, w} :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by simp [hvw, hcardTwo])
    have heqRight : ({v, w} : Finset M.Vertex) ∩ M.freeTriangleBaseEdge T k =
        M.freeTriangleBaseEdge T k :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [hcardTwo, M.freeTriangleBaseEdge_card T k])
    exact hne (heqLeft.symm.trans heqRight)
  have hinter : segment ℝ a b ∩ convexHull ℝ (Set.range kiteTrianglePosition) ⊆
      {planePoint (-1) 0, planePoint 1 0} := by
    intro p hp
    have hpEdge : E p ∈
        convexHull ℝ (M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex)) := by
      rw [hcarrier, ← hsegmentImage]
      exact ⟨p, hp.1, rfl⟩
    have hpTriangle : E p ∈ M.triangleCarrier T.1 := by
      rw [← M.freeTriangleAffineEquiv_image_triangle T k]
      exact ⟨p, hp.2, rfl⟩
    have hpFrontier := M.boundaryEdgeCarrier_subset_frontier he hpEdge
    have hpBase : E p ∈ convexHull ℝ
        (M.position '' (M.freeTriangleBaseEdge T k : Set M.Vertex)) := by
      rw [M.freeTriangleBaseEdge_carrier T k, ← htrace]
      exact ⟨hpFrontier, hpTriangle⟩
    have hpCommon : E p ∈ convexHull ℝ
        (M.position '' ((({v, w} : Finset M.Vertex) ∩
          M.freeTriangleBaseEdge T k : Finset M.Vertex) : Set M.Vertex)) := by
      rw [← M.edgeCarrier_inter_edgeCarrier he.1 hbaseEdge]
      exact ⟨hpEdge, hpBase⟩
    obtain hempty | hnonempty :=
        (({v, w} : Finset M.Vertex) ∩ M.freeTriangleBaseEdge T k).eq_empty_or_nonempty
    · rw [hempty] at hpCommon
      simp at hpCommon
    · obtain ⟨x, hx⟩ := hnonempty
      have hsingle : ({v, w} : Finset M.Vertex) ∩ M.freeTriangleBaseEdge T k = {x} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hx, fun y hy => ?_⟩
        by_contra hyx
        have hpair : ({x, y} : Finset M.Vertex) ⊆
            ({v, w} : Finset M.Vertex) ∩ M.freeTriangleBaseEdge T k := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        have := Finset.card_le_card hpair
        have hxy : x ≠ y := Ne.symm hyx
        have hcardPair : ({x, y} : Finset M.Vertex).card = 2 := by simp [hxy]
        rw [hcardPair] at this
        omega
      rw [hsingle] at hpCommon
      have hpEq : E p = M.position x := by simpa using hpCommon
      have hxBase : x ∈ M.freeTriangleBaseEdge T k := Finset.inter_subset_right hx
      have hxImage : M.position x ∈
          ({M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 1} : Set Plane) := by
        rw [← M.image_freeTriangleBaseEdge T k]
        exact ⟨x, hxBase, rfl⟩
      rcases hxImage with hx0 | hx1
      · left
        apply E.injective
        rw [hpEq, hx0]
        simpa [E, kiteTrianglePosition] using
          (M.freeTriangleAffineEquiv_apply_vertex T k 0).symm
      · right
        apply E.injective
        rw [hpEq, hx1]
        simpa [E, kiteTrianglePosition] using
          (M.freeTriangleAffineEquiv_apply_vertex T k 1).symm
  let v0 := M.orderedVertex T ((Equiv.swap 2 k) 0)
  let v1 := M.orderedVertex T ((Equiv.swap 2 k) 1)
  have hE0 : E (planePoint (-1) 0) = M.position v0 := by
    calc
      E (planePoint (-1) 0) = M.freeTriangleOrder T k 0 := by
        simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 0
      _ = M.position v0 := rfl
  have hE1 : E (planePoint 1 0) = M.position v1 := by
    calc
      E (planePoint 1 0) = M.freeTriangleOrder T k 1 := by
        simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 1
      _ = M.position v1 := rfl
  have hleftEndpoint : planePoint (-1) 0 ∈ segment ℝ a b →
      a = planePoint (-1) 0 ∨ b = planePoint (-1) 0 := by
    intro hleft
    have hpEdge : M.position v0 ∈
        convexHull ℝ (M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex)) := by
      rw [hcarrier, ← hsegmentImage, ← hE0]
      exact ⟨planePoint (-1) 0, hleft, rfl⟩
    have hv0 : v0 ∈ ({v, w} : Finset M.Vertex) :=
      M.vertex_mem_edge_of_position_mem_edgeCarrier T.2 (M.orderedVertex_mem T _) he.1 hpEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv0
    rcases hv0 with hv0 | hv0
    · left
      apply E.injective
      simp [a, hv0, hE0]
    · right
      apply E.injective
      simp [b, hv0, hE0]
  have hrightEndpoint : planePoint 1 0 ∈ segment ℝ a b →
      a = planePoint 1 0 ∨ b = planePoint 1 0 := by
    intro hright
    have hpEdge : M.position v1 ∈
        convexHull ℝ (M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex)) := by
      rw [hcarrier, ← hsegmentImage, ← hE1]
      exact ⟨planePoint 1 0, hright, rfl⟩
    have hv1 : v1 ∈ ({v, w} : Finset M.Vertex) :=
      M.vertex_mem_edge_of_position_mem_edgeCarrier T.2 (M.orderedVertex_mem T _) he.1 hpEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv1
    rcases hv1 with hv1 | hv1
    · left
      apply E.injective
      simp [a, hv1, hE1]
    · right
      apply E.injective
      simp [b, hv1, hE1]
  have hnotBoth : ¬(planePoint (-1) 0 ∈ segment ℝ a b ∧
      planePoint 1 0 ∈ segment ℝ a b) := by
    have hLR : planePoint (-1) 0 ≠ planePoint 1 0 := by
      intro h
      have := congrArg (fun p : Plane => p 0) h
      norm_num [planePoint] at this
    rintro ⟨hleft, hright⟩
    rcases hleftEndpoint hleft with ha0 | hb0
    · rcases hrightEndpoint hright with ha1 | hb1
      · exact hLR (ha0.symm.trans ha1)
      · have hv0 : v = v0 := by
          apply M.position_injective
          rw [← hE0, ← ha0]
          simp [a]
        have hw1 : w = v1 := by
          apply M.position_injective
          rw [← hE1, ← hb1]
          simp [b]
        apply hne
        rw [M.freeTriangleBaseEdge_eq_orderedPair T k, hv0, hw1]
    · rcases hrightEndpoint hright with ha1 | hb1
      · have hw0 : w = v0 := by
          apply M.position_injective
          rw [← hE0, ← hb0]
          simp [b]
        have hv1 : v = v1 := by
          apply M.position_injective
          rw [← hE1, ← ha1]
          simp [a]
        apply hne
        rw [M.freeTriangleBaseEdge_eq_orderedPair T k, hw0, hv1, Finset.pair_comm]
      · exact hLR (hb0.symm.trans hb1)
  obtain ⟨ε, hε, havoid⟩ := exists_thinKitePatch_inter_segment_subset_baseEndpoints
    hab hinter hleftEndpoint hrightEndpoint hnotBoth
  refine ⟨ε, hε, fun δ hδ hδε p hp => ?_⟩
  have hpEdge := hp.2
  obtain ⟨q, hqPatch, rfl⟩ := hp.1
  have hqSegment : q ∈ segment ℝ a b := by
    have : E q ∈ segment ℝ (M.position v) (M.position w) := by
      rwa [← hcarrier]
    rw [← hsegmentImage] at this
    obtain ⟨r, hr, hEq⟩ := this
    exact E.injective hEq ▸ hr
  rcases havoid δ hδ hδε ⟨hqPatch, hqSegment⟩ with hq | hq
  · left
    rw [hq]
    exact hE0
  · right
    rw [hq]
    exact hE1

private theorem exists_pos_uniform_finset {α : Type*}
    (s : Finset α) (P : α → ℝ → Prop)
    (hP : ∀ x ∈ s, ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε → P x δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ s, ∀ δ : ℝ, 0 < δ → δ < ε → P x δ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨1, by norm_num, by simp⟩
  | @insert x s hxs ih =>
      obtain ⟨εx, hεx, hx⟩ := hP x (Finset.mem_insert_self x s)
      obtain ⟨εs, hεs, hs⟩ := ih fun y hy => hP y (Finset.mem_insert_of_mem hy)
      refine ⟨min εx εs, lt_min hεx hεs, ?_⟩
      intro y hy δ hδ hδε
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact hx δ hδ (hδε.trans_le (min_le_left _ _))
      · exact hs y hy δ hδ (hδε.trans_le (min_le_right _ _))

/-- The one-edge Figure 3.3 push can be made relative both to a prescribed open set and to
the entire old boundary carrier away from the deleted triangle. -/
theorem exists_supported_triangle_push_fixing_boundaryCarrier
    (T : M.Triangle) (k : Fin 3)
    (htrace : frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1))
    (U : Set Plane) (hU : IsOpen U) (hTU : M.triangleCarrier T.1 ⊆ U) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ,
      Set.EqOn (transportedThinKiteHomeomorph (M.freeTriangleAffineEquiv T k) δ hδ)
          id Uᶜ ∧
        Set.EqOn (transportedThinKiteHomeomorph (M.freeTriangleAffineEquiv T k) δ hδ)
          id (M.boundaryCarrier \ M.triangleCarrier T.1) ∧
        transportedThinKiteHomeomorph (M.freeTriangleAffineEquiv T k) δ hδ ''
          segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) =
          segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
            segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2) := by
  classical
  let E := M.freeTriangleAffineEquiv T k
  obtain ⟨εU, hεU, hpatchU⟩ :=
      exists_eventually_transportedThinKitePatch_subset_open E U hU (by
    rw [M.freeTriangleAffineEquiv_image_triangle T k]
    exact hTU)
  let movingEdges := M.allBoundaryEdges.erase (M.freeTriangleBaseEdge T k)
  let P : Finset M.Vertex → ℝ → Prop := fun e δ =>
    transportedThinKitePatch E δ ∩
        convexHull ℝ (M.position '' (e : Set M.Vertex)) ⊆
      {M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 1}
  have hlocal : ∀ e ∈ movingEdges, ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 < δ → δ < ε → P e δ := by
    intro e he
    have heData := Finset.mem_erase.mp he
    exact M.exists_transportedThinKitePatch_inter_boundaryEdge_subset_baseEndpoints
      T k htrace e (M.mem_allBoundaryEdges_iff.mp heData.2) heData.1
  obtain ⟨εB, hεB, hpatchB⟩ := exists_pos_uniform_finset movingEdges P hlocal
  let δ := min εU εB / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδU : δ < εU := by
    dsimp [δ]
    have hmin := min_le_left εU εB
    nlinarith [lt_min hεU hεB]
  have hδB : δ < εB := by
    dsimp [δ]
    have hmin := min_le_right εU εB
    nlinarith [lt_min hεU hεB]
  refine ⟨δ, hδ, ?_, ?_, ?_⟩
  · intro p hp
    apply transportedThinKiteHomeomorph_eqOn_compl E δ hδ
    intro hmem
    exact hp (hpatchU δ hδ hδU hmem)
  · intro p hp
    apply transportedThinKiteHomeomorph_eqOn_compl E δ hδ
    intro hpPatch
    have hpBoundary := hp.1
    change p ∈ ⋃ e ∈ M.allBoundaryEdges,
      convexHull ℝ (M.position '' (e : Set M.Vertex)) at hpBoundary
    obtain ⟨e, hpBoundary⟩ := Set.mem_iUnion.mp hpBoundary
    obtain ⟨heBoundary, hpEdge⟩ := Set.mem_iUnion.mp hpBoundary
    by_cases heBase : e = M.freeTriangleBaseEdge T k
    · subst e
      apply hp.2
      exact convexHull_mono (Set.image_mono (M.freeTriangleBaseEdge_subset T k)) hpEdge
    · have heMoving : e ∈ movingEdges :=
        Finset.mem_erase.mpr ⟨heBase, heBoundary⟩
      have hpEndpoint := hpatchB e heMoving δ hδ hδB ⟨hpPatch, hpEdge⟩
      apply hp.2
      rcases hpEndpoint with rfl | rfl
      · exact subset_convexHull ℝ _ ⟨M.orderedVertex T ((Equiv.swap 2 k) 0),
          M.orderedVertex_mem T _, rfl⟩
      · exact subset_convexHull ℝ _ ⟨M.orderedVertex T ((Equiv.swap 2 k) 1),
          M.orderedVertex_mem T _, rfl⟩
  · have hmove := transportedThinKiteHomeomorph_image_baseSegment E δ hδ
    have h0 : E (planePoint (-1) 0) = M.freeTriangleOrder T k 0 := by
      simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 0
    have h1 : E (planePoint 1 0) = M.freeTriangleOrder T k 1 := by
      simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 1
    have h2 : E (planePoint 0 1) = M.freeTriangleOrder T k 2 := by
      simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 2
    simpa only [E, h0, h1, h2] using hmove

/-- Moise's Figure 3.3 move in an arbitrary free triangle coordinate system, with support in a
prescribed open neighborhood of that triangle. -/
theorem exists_supported_triangle_push (T : M.Triangle) (k : Fin 3)
    (U : Set Plane) (hU : IsOpen U) (hTU : M.triangleCarrier T.1 ⊆ U) :
    ∃ h : Plane ≃ₜ Plane,
      Set.EqOn h id Uᶜ ∧
        h '' segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) =
          segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
            segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2) := by
  let e := M.freeTriangleAffineEquiv T k
  obtain ⟨δ, hδ, hpatch⟩ := exists_thinKitePatch_subset_open e U hU (by
    rw [M.freeTriangleAffineEquiv_image_triangle T k]
    exact hTU)
  let h := transportedThinKiteHomeomorph e δ hδ
  refine ⟨h, ?_, ?_⟩
  · intro p hp
    apply transportedThinKiteHomeomorph_eqOn_compl e δ hδ
    intro hmem
    exact hp (hpatch hmem)
  · have hmove := transportedThinKiteHomeomorph_image_baseSegment e δ hδ
    have h0 : e (planePoint (-1) 0) = M.freeTriangleOrder T k 0 := by
      simpa [e, kiteTrianglePosition] using
        M.freeTriangleAffineEquiv_apply_vertex T k 0
    have h1 : e (planePoint 1 0) = M.freeTriangleOrder T k 1 := by
      simpa [e, kiteTrianglePosition] using
        M.freeTriangleAffineEquiv_apply_vertex T k 1
    have h2 : e (planePoint 0 1) = M.freeTriangleOrder T k 2 := by
      simpa [e, kiteTrianglePosition] using
        M.freeTriangleAffineEquiv_apply_vertex T k 2
    simpa only [h, h0, h1, h2] using hmove

/-- The inverse Figure 3.3 move removes a triangle whose two apex edges lie on the frontier. -/
theorem exists_supported_triangle_pull (T : M.Triangle) (k : Fin 3)
    (U : Set Plane) (hU : IsOpen U) (hTU : M.triangleCarrier T.1 ⊆ U) :
    ∃ h : Plane ≃ₜ Plane,
      Set.EqOn h id Uᶜ ∧
        h '' (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
          segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)) =
            segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
  obtain ⟨g, hgfix, hgmove⟩ := M.exists_supported_triangle_push T k U hU hTU
  refine ⟨g.symm, ?_, ?_⟩
  · intro p hp
    have hgp : g p = p := hgfix hp
    exact g.symm_apply_eq.mpr hgp.symm
  · rw [← hgmove, Set.image_image]
    simp

end TriangleMesh

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
