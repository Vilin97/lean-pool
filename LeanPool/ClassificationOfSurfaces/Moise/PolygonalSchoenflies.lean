/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.PLMoves
import LeanPool.ClassificationOfSurfaces.Moise.PolygonalPolyhedron
import LeanPool.ClassificationOfSurfaces.Moise.PolygonalCrosscut
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# The Schoenflies theorem for polygons

Statements following Moise, *Geometric Topology in Dimensions 2 and 3*:

* Ch. 2, Thm. 2: the closed region bounded by a polygon is a finite polyhedron — this is the
  triangulation theorem for polygonal disks, proved by cutting along the lines through the edges;
* Ch. 3, Thm. 5: any two polygons are equivalent under an ambient homeomorphism of the plane;
* Ch. 3, Thm. 7: the ambient homeomorphism can be chosen supported in any open set containing
  the closed region (the relative version used for gluing).

Only the polygonal case is stated.  The full Schoenflies theorem (Moise Ch. 9) comes *after* the
triangulation theorem in Moise and is not on this route's critical path.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- A triangle mesh with exactly one maximal triangle has triangular support. -/
theorem TriangleMesh.isTriangle_support_of_card_triangles_eq_one (M : TriangleMesh)
    (hcard : M.triangles.card = 1) : IsTriangle M.toPlaneComplex.support := by
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcard
  have htmem : t ∈ M.triangles := by rw [ht]; simp
  let T : M.Triangle := ⟨t, htmem⟩
  refine ⟨M.position ∘ M.orderedVertex T, M.orderedVertex_affineIndependent T, ?_⟩
  rw [M.toPlaneComplex_support, ht]
  simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
  rw [Set.range_comp, M.range_orderedVertex T]

/-- A finite sequence of supported free-triangle removals ending in one triangle.  The frontier
equality in `remove` is the exact geometric content of Moise's Figure 3.3 needed by the
Schoenflies induction. -/
inductive TriangleMesh.AmbientShellingIn (U : Set Plane) : TriangleMesh → Prop
  | single (M : TriangleMesh) (hcard : M.triangles.card = 1) : M.AmbientShellingIn U
  | remove (M : TriangleMesh) (t : Finset M.Vertex) (ht : t ∈ M.triangles)
      (g : Plane ≃ₜ Plane) (hfix : Set.EqOn g id Uᶜ)
      (hfrontier : g '' frontier M.toPlaneComplex.support =
        frontier (M.eraseTriangle t).toPlaneComplex.support)
      (tail : (M.eraseTriangle t).AmbientShellingIn U) : M.AmbientShellingIn U

/-- A shelling carrying the finite-PL certificate and support image equality required to
compose each elementary move on the whole current disk. -/
inductive TriangleMesh.PLAmbientShellingIn (U : Set Plane) : TriangleMesh → Prop
  | single (M : TriangleMesh) (hcard : M.triangles.card = 1) : M.PLAmbientShellingIn U
  | remove (M : TriangleMesh) (t : Finset M.Vertex) (ht : t ∈ M.triangles)
      (g : Plane ≃ₜ Plane) (hpl : FinitePLHomeomorphOn g M.toPlaneComplex.support)
      (hfix : Set.EqOn g id Uᶜ)
      (hsupport : g '' M.toPlaneComplex.support =
        (M.eraseTriangle t).toPlaneComplex.support)
      (hfrontier : g '' frontier M.toPlaneComplex.support =
        frontier (M.eraseTriangle t).toPlaneComplex.support)
      (tail : (M.eraseTriangle t).PLAmbientShellingIn U) : M.PLAmbientShellingIn U

/-- A supported ambient shelling composes to a single relative Schoenflies homeomorphism. -/
theorem TriangleMesh.AmbientShellingIn.straightens {M : TriangleMesh} {U : Set Plane}
    (S : M.AmbientShellingIn U) :
    ∃ h : Plane ≃ₜ Plane, ∃ C : Set Plane,
      IsTriangle C ∧ h '' frontier M.toPlaneComplex.support = frontier C ∧
        Set.EqOn h id Uᶜ := by
  induction S with
  | single M hcard =>
      refine ⟨Homeomorph.refl Plane, M.toPlaneComplex.support,
        M.isTriangle_support_of_card_triangles_eq_one hcard, ?_, ?_⟩
      · simp
      · intro p hp
        rfl
  | remove M t ht g hfix hmove tail ih =>
      obtain ⟨h, C, hC, hfrontier, hfixTail⟩ := ih
      refine ⟨g.trans h, C, hC, ?_, ?_⟩
      · change (fun x => h (g x)) '' frontier M.toPlaneComplex.support = frontier C
        rw [← Set.image_image]
        rw [hmove, hfrontier]
      · intro p hp
        change h (g p) = p
        rw [hfix hp]
        simpa using hfixTail hp

/-- A PL-aware shelling composes to a finite PL ambient straightening of its original disk. -/
theorem TriangleMesh.PLAmbientShellingIn.straightens {M : TriangleMesh} {U : Set Plane}
    (S : M.PLAmbientShellingIn U) :
    ∃ h : Plane ≃ₜ Plane, ∃ C : Set Plane,
      ∃ _ : FinitePLHomeomorphOn h M.toPlaneComplex.support,
      IsTriangle C ∧ h '' frontier M.toPlaneComplex.support = frontier C ∧
        h '' M.toPlaneComplex.support = C ∧ Set.EqOn h id Uᶜ := by
  induction S with
  | single M hcard =>
      refine ⟨Homeomorph.refl Plane, M.toPlaneComplex.support,
        FinitePLHomeomorphOn.refl M.toPlaneComplex M.toPlaneComplex_isPure2,
        M.isTriangle_support_of_card_triangles_eq_one hcard, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro p hp
        rfl
  | remove M t ht g hpl hfix hsupport hmove tail ih =>
      obtain ⟨h, C, hplTail, hC, hfrontier, hsupportTail, hfixTail⟩ := ih
      refine ⟨g.trans h, C, hpl.trans (hplTail.congrSet hsupport.symm), hC, ?_, ?_, ?_⟩
      · change (fun x => h (g x)) '' frontier M.toPlaneComplex.support = frontier C
        rw [← Set.image_image, hmove, hfrontier]
      · change (fun x => h (g x)) '' M.toPlaneComplex.support = C
        rw [← Set.image_image, hsupport, hsupportTail]
      · intro p hp
        change h (g p) = p
        rw [hfix hp]
        simpa using hfixTail hp

/-- An affine equivalence of the Euclidean plane is an ambient homeomorphism. -/
noncomputable def triangleAffineHomeomorph (p q : Fin 3 → Plane)
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q) : Plane ≃ₜ Plane where
  toEquiv := triangleAffineEquiv p q hp hq
  continuous_toFun := (triangleAffineEquiv p q hp hq).toAffineMap.continuous_of_finiteDimensional
  continuous_invFun :=
    (triangleAffineEquiv p q hp hq).symm.toAffineMap.continuous_of_finiteDimensional

/-- Moise Chapter 3, Theorem 2 for plane triangles: two nondegenerate closed triangles are
carried to one another by an affine ambient homeomorphism. -/
theorem triangle_ambient_homeomorphic {C C' : Set Plane} (hC : IsTriangle C)
    (hC' : IsTriangle C') :
    ∃ h : Plane ≃ₜ Plane, h '' C = C' ∧ h '' frontier C = frontier C' := by
  obtain ⟨p, hp, rfl⟩ := hC
  obtain ⟨q, hq, rfl⟩ := hC'
  let h := triangleAffineHomeomorph p q hp hq
  have himage : h '' convexHull ℝ (Set.range p) = convexHull ℝ (Set.range q) :=
    triangleAffineEquiv_image_convexHull p q hp hq
  refine ⟨h, himage, ?_⟩
  rw [h.image_frontier, himage]

/-! ## The edge complex of a polygon -/

/-- Polygon edges meet exactly in the convex hull of their shared abstract vertices. -/
theorem PolygonalCircle.edgeSegment_inter_eq_shared_vertices
    (J : PolygonalCircle) (i j : ZMod J.n) :
    J.edgeSegment i ∩ J.edgeSegment j =
      convexHull ℝ (J.vertex ''
        ((({i, i + 1} : Finset (ZMod J.n)) ∩ {j, j + 1} :
          Finset (ZMod J.n)) : Set (ZMod J.n))) := by
  have hpairCarrier (k : ZMod J.n) :
      convexHull ℝ (J.vertex '' (({k, k + 1} : Finset (ZMod J.n)) :
        Set (ZMod J.n))) = J.edgeSegment k := by
    rw [PolygonalCircle.edgeSegment, ← convexHull_pair]
    congr 1
    ext x
    simp [eq_comm]
  have hsucc (k : ZMod J.n) : k ≠ k + 1 := by
    intro hk
    exact J.adjacent_ne k (congrArg J.vertex hk)
  have htwo (k : ZMod J.n) : k ≠ k + 2 := by
    intro hk
    have hx : J.vertex k ∈ J.edgeSegment k ∩ J.edgeSegment (k + 1) := by
      constructor
      · exact left_mem_segment ℝ _ _
      · rw [PolygonalCircle.edgeSegment,
          show k + 1 + 1 = k + 2 by ring, ← hk]
        exact right_mem_segment ℝ _ _
    have hinter : J.edgeSegment k ∩ J.edgeSegment (k + 1) =
        {J.vertex (k + 1)} := by
      simpa only [PolygonalCircle.edgeSegment, add_assoc, one_add_one_eq_two] using
        J.consecutive_inter k
    rw [hinter] at hx
    exact J.adjacent_ne k (Set.mem_singleton_iff.mp hx)
  have hadjacent (k : ZMod J.n) :
      ({k, k + 1} : Finset (ZMod J.n)) ∩ {k + 1, k + 2} = {k + 1} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨(h | h), (h' | h')⟩
      · subst x
        exact (hsucc k h').elim
      · subst x
        exact (htwo k (by simpa [add_assoc] using h')).elim
      · subst x
        rfl
      · subst x
        rfl
    · rintro rfl
      exact ⟨Or.inr rfl, Or.inl rfl⟩
  by_cases hij : i = j
  · subst j
    rw [Finset.inter_self, hpairCarrier]
    simp
  by_cases hnext : j = i + 1
  · subst j
    have hfin :
        ({i, i + 1} : Finset (ZMod J.n)) ∩ {i + 1, i + 1 + 1} = {i + 1} := by
      convert hadjacent i using 1; ring
    change J.edgeSegment i ∩ J.edgeSegment (i + 1) = _
    rw [hfin, show convexHull ℝ (J.vertex '' (({i + 1} :
      Finset (ZMod J.n)) : Set (ZMod J.n))) = {J.vertex (i + 1)} by simp]
    simpa only [PolygonalCircle.edgeSegment, add_assoc, one_add_one_eq_two] using
      J.consecutive_inter i
  by_cases hprev : i = j + 1
  · have h := J.consecutive_inter j
    rw [Set.inter_comm] at h
    have hfin :
        ({j + 1, j + 1 + 1} : Finset (ZMod J.n)) ∩ {j, j + 1} = {j + 1} := by
      rw [Finset.inter_comm]
      convert hadjacent j using 1; ring
    rw [hprev]
    change J.edgeSegment (j + 1) ∩ J.edgeSegment j = _
    rw [hfin, show convexHull ℝ (J.vertex '' (({j + 1} :
      Finset (ZMod J.n)) : Set (ZMod J.n))) = {J.vertex (j + 1)} by simp]
    simpa only [PolygonalCircle.edgeSegment, add_assoc, one_add_one_eq_two] using h
  · have hdis := J.nonadjacent_disjoint i j hij hprev hnext
    have hdis' :
        segment ℝ (J.vertex i) (J.vertex (i + 1)) ∩
          segment ℝ (J.vertex j) (J.vertex (j + 1)) = ∅ :=
      hdis
    have hinter :
        ({i, i + 1} : Finset (ZMod J.n)) ∩ {j, j + 1} = ∅ := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨(rfl | rfl), (h | h)⟩
        · exact (hij h).elim
        · exact (hprev h).elim
        · exact (hnext h.symm).elim
        · exact (hij (add_right_cancel h)).elim
      · intro hx
        simp at hx
    change segment ℝ (J.vertex i) (J.vertex (i + 1)) ∩
      segment ℝ (J.vertex j) (J.vertex (j + 1)) = _
    rw [hdis', hinter]
    simp

/-- The nonempty abstract faces of the cyclic edges of a polygon. -/
noncomputable def PolygonalCircle.edgeFaces (J : PolygonalCircle) :
    Finset (Finset (ZMod J.n)) := by
  classical
  exact (Finset.univ : Finset (ZMod J.n)).biUnion fun i =>
    ({i, i + 1} : Finset (ZMod J.n)).powerset.filter (·.Nonempty)

theorem PolygonalCircle.mem_edgeFaces_iff (J : PolygonalCircle)
    {s : Finset (ZMod J.n)} :
    s ∈ J.edgeFaces ↔ s.Nonempty ∧ ∃ i, s ⊆ {i, i + 1} := by
  classical
  simp [PolygonalCircle.edgeFaces, and_comm]

/-- A polygon, regarded as its finite one-dimensional geometric complex. -/
noncomputable def PolygonalCircle.edgeComplex (J : PolygonalCircle) : PlaneComplex where
  Vertex := ZMod J.n
  position := J.vertex
  position_injective := J.vertex_injective
  simplexes := J.edgeFaces
  nonempty_of_mem := fun s hs => (J.mem_edgeFaces_iff.mp hs).1
  card_le_three := by
    intro s hs
    obtain ⟨-, i, hsi⟩ := J.mem_edgeFaces_iff.mp hs
    have hp : ({i, i + 1} : Finset (ZMod J.n)).card ≤ 2 := by
      rcases (Finset.card_pair_eq_one_or_two (a := i) (b := i + 1)) with h | h <;> omega
    exact (Finset.card_le_card hsi).trans hp |>.trans (by omega)
  down_closed := by
    intro s hs t hts ht
    obtain ⟨-, i, hsi⟩ := J.mem_edgeFaces_iff.mp hs
    exact J.mem_edgeFaces_iff.mpr ⟨ht, i, hts.trans hsi⟩
  affineIndependent := by
    intro s hs
    let A : Finset Plane := s.image J.vertex
    have hAcard : A.card ≤ 2 := by
      exact Finset.card_image_le.trans (by
        obtain ⟨-, i, hsi⟩ := J.mem_edgeFaces_iff.mp hs
        have hp : ({i, i + 1} : Finset (ZMod J.n)).card ≤ 2 := by
          rcases (Finset.card_pair_eq_one_or_two (a := i) (b := i + 1)) with h | h <;>
            omega
        exact (Finset.card_le_card hsi).trans hp)
    let e : s ↪ A :=
      { toFun := fun v =>
          ⟨J.vertex v, Finset.mem_image.mpr ⟨v, v.2, rfl⟩⟩
        inj' := by
          intro v w hvw
          apply Subtype.ext
          exact J.vertex_injective (congrArg Subtype.val hvw) }
    exact (affineIndependent_finset_of_card_le_two A hAcard).comp_embedding e
  face_inter := by
    intro s hs t ht
    have vertex_mem_of_mem_carrier
        {u : Finset (ZMod J.n)} (hu : u ∈ J.edgeFaces)
        {v : ZMod J.n}
        (hv : J.vertex v ∈ convexHull ℝ (J.vertex '' (u : Set (ZMod J.n)))) :
        v ∈ u := by
      obtain ⟨hune, i, hui⟩ := J.mem_edgeFaces_iff.mp hu
      have hupos : 0 < u.card := Finset.card_pos.mpr hune
      have hpairle : ({i, i + 1} : Finset (ZMod J.n)).card ≤ 2 := by
        rcases (Finset.card_pair_eq_one_or_two (a := i) (b := i + 1)) with h | h <;>
          omega
      have hule : u.card ≤ 2 := (Finset.card_le_card hui).trans hpairle
      rcases (show u.card = 1 ∨ u.card = 2 by omega) with huone | hutwo
      · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp huone
        have hvw : J.vertex v = J.vertex w := by simpa using hv
        simp [J.vertex_injective hvw]
      · have hueq : u = {i, i + 1} := by
          apply Finset.eq_of_subset_of_card_le hui
          have := Finset.card_le_card hui
          omega
        rw [hueq] at hv ⊢
        have hpair : convexHull ℝ (J.vertex '' (({i, i + 1} :
            Finset (ZMod J.n)) : Set (ZMod J.n))) = J.edgeSegment i := by
          rw [PolygonalCircle.edgeSegment, ← convexHull_pair]
          congr 1
          ext x
          simp [eq_comm]
        simpa only [Finset.mem_insert, Finset.mem_singleton] using
          (J.vertex_mem_edgeSegment_iff v i).mp (by
            rw [← hpair]
            exact hv)
    have hspos : 0 < s.card := Finset.card_pos.mpr (J.mem_edgeFaces_iff.mp hs).1
    have htpos : 0 < t.card := Finset.card_pos.mpr (J.mem_edgeFaces_iff.mp ht).1
    have hsle : s.card ≤ 2 := by
      obtain ⟨-, i, hsi⟩ := J.mem_edgeFaces_iff.mp hs
      have hp : ({i, i + 1} : Finset (ZMod J.n)).card ≤ 2 := by
        rcases (Finset.card_pair_eq_one_or_two (a := i) (b := i + 1)) with h | h <;>
          omega
      exact (Finset.card_le_card hsi).trans hp
    have htle : t.card ≤ 2 := by
      obtain ⟨-, i, hti⟩ := J.mem_edgeFaces_iff.mp ht
      have hp : ({i, i + 1} : Finset (ZMod J.n)).card ≤ 2 := by
        rcases (Finset.card_pair_eq_one_or_two (a := i) (b := i + 1)) with h | h <;>
          omega
      exact (Finset.card_le_card hti).trans hp
    rcases (show s.card = 1 ∨ s.card = 2 by omega) with hsone | hstwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
      apply Set.Subset.antisymm
      · intro x hx
        have hxv : x = J.vertex v := by simpa using hx.1
        subst x
        have hvt := vertex_mem_of_mem_carrier ht hx.2
        exact subset_convexHull ℝ _ ⟨v, by simpa using hvt, rfl⟩
      · intro x hx
        exact ⟨convexHull_mono (Set.image_mono Finset.inter_subset_left) hx,
          convexHull_mono (Set.image_mono Finset.inter_subset_right) hx⟩
    · rcases (show t.card = 1 ∨ t.card = 2 by omega) with htone | httwo
      · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp htone
        apply Set.Subset.antisymm
        · intro x hx
          have hxv : x = J.vertex v := by simpa using hx.2
          subst x
          have hvs := vertex_mem_of_mem_carrier hs hx.1
          exact subset_convexHull ℝ _ ⟨v, by simpa using hvs, rfl⟩
        · intro x hx
          exact ⟨convexHull_mono (Set.image_mono Finset.inter_subset_left) hx,
            convexHull_mono (Set.image_mono Finset.inter_subset_right) hx⟩
      · obtain ⟨-, i, hsi⟩ := J.mem_edgeFaces_iff.mp hs
        obtain ⟨-, j, htj⟩ := J.mem_edgeFaces_iff.mp ht
        have hseq : s = {i, i + 1} := by
          apply Finset.eq_of_subset_of_card_le hsi
          rw [Finset.card_pair (by
            intro hi
            exact J.adjacent_ne i (congrArg J.vertex hi))]
          exact hstwo.ge
        have hteq : t = {j, j + 1} := by
          apply Finset.eq_of_subset_of_card_le htj
          rw [Finset.card_pair (by
            intro hj
            exact J.adjacent_ne j (congrArg J.vertex hj))]
          exact httwo.ge
        subst s
        subst t
        rw [show convexHull ℝ (J.vertex '' (({i, i + 1} :
          Finset (ZMod J.n)) : Set (ZMod J.n))) = J.edgeSegment i by
            rw [PolygonalCircle.edgeSegment, ← convexHull_pair]
            congr 1
            ext x
            simp [eq_comm]]
        rw [show convexHull ℝ (J.vertex '' (({j, j + 1} :
          Finset (ZMod J.n)) : Set (ZMod J.n))) = J.edgeSegment j by
            rw [PolygonalCircle.edgeSegment, ← convexHull_pair]
            congr 1
            ext x
            simp [eq_comm]]
        exact J.edgeSegment_inter_eq_shared_vertices i j

/-- The support of the polygon edge complex is exactly the polygon carrier. -/
theorem PolygonalCircle.edgeComplex_support (J : PolygonalCircle) :
    J.edgeComplex.support = J.carrier := by
  have hpairCarrier (i : ZMod J.n) :
      J.edgeComplex.cellCarrier ({i, i + 1} : Finset (ZMod J.n)) =
        J.edgeSegment i := by
    change convexHull ℝ (J.vertex '' (({i, i + 1} : Finset (ZMod J.n)) :
      Set (ZMod J.n))) = segment ℝ (J.vertex i) (J.vertex (i + 1))
    rw [← convexHull_pair]
    congr 1
    ext x
    simp [eq_comm]
  apply Set.Subset.antisymm
  · intro x hx
    rw [PlaneComplex.support] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    obtain ⟨-, i, hsi⟩ := J.mem_edgeFaces_iff.mp hs
    apply J.edgeSegment_subset_carrier i
    have hxPair : x ∈ J.edgeComplex.cellCarrier
        ({i, i + 1} : Finset (ZMod J.n)) :=
      convexHull_mono (Set.image_mono hsi) hxs
    rw [hpairCarrier i] at hxPair
    exact hxPair
  · intro x hx
    rw [PolygonalCircle.carrier] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hxi⟩ := hx
    rw [← hpairCarrier i] at hxi
    exact J.edgeComplex.cellCarrier_subset_support
      (J.mem_edgeFaces_iff.mpr ⟨by simp, i, Finset.Subset.rfl⟩) hxi

/-- Removing finitely many points from a polygon carrier leaves a dense subset of that carrier.
This lets incidence arguments move away from the finite mesh vertex set. -/
theorem PolygonalCircle.carrier_subset_closure_sdiff_finite (J : PolygonalCircle)
    {F : Set Plane} (hF : F.Finite) :
    J.carrier ⊆ closure (J.carrier \ F) := by
  intro p hp
  obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
  let a := J.vertex i
  let b := J.vertex (i + 1)
  have hab : a ≠ b := J.adjacent_ne i
  let line : ℝ → Plane := AffineMap.lineMap a b
  let bad : Set ℝ := line ⁻¹' F
  have hbadFinite : bad.Finite := by
    apply hF.preimage (AffineMap.lineMap_injective ℝ hab).injOn
  have hdense : Dense badᶜ := hbadFinite.countable.dense_compl ℝ
  let good : Set ℝ := Set.Ioo (0 : ℝ) 1 ∩ badᶜ
  have hIooGood : Set.Ioo (0 : ℝ) 1 ⊆ closure good :=
    hdense.open_subset_closure_inter isOpen_Ioo
  have hgoodImage : line '' good ⊆ J.carrier \ F := by
    rintro q ⟨c, hc, rfl⟩
    refine ⟨J.edgeSegment_subset_carrier i ?_, hc.2⟩
    exact lineMap_mem_segment ℝ a b ⟨hc.1.1.le, hc.1.2.le⟩
  rw [PolygonalCircle.edgeSegment, segment_eq_image_lineMap] at hpi
  obtain ⟨c, hc, rfl⟩ := hpi
  have hcClosureIoo : c ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact hc
  have hcClosureGood : c ∈ closure good := by
    have : c ∈ closure (closure good) := closure_mono hIooGood hcClosureIoo
    simpa using this
  have hmemClosureImage : line c ∈ closure (line '' good) :=
    image_closure_subset_closure_image AffineMap.lineMap_continuous
      ⟨c, hcClosureGood, rfl⟩
  exact closure_mono hgoodImage hmemClosureImage

/-- For a mesh whose support is a polygonal disk, the support frontier is exactly the finite
union of its incidence-one edge carriers.  Polygonality rules out isolated frontier vertices. -/
theorem TriangleMesh.boundaryCarrier_eq_frontier_of_polygonalDisk
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion) :
    M.boundaryCarrier = frontier M.toPlaneComplex.support := by
  apply Set.Subset.antisymm M.boundaryCarrier_subset_frontier
  intro p hpFrontier
  have hpCarrier : p ∈ J.carrier := by
    rw [← J.frontier_closedRegion, ← hsupport]
    exact hpFrontier
  have hpClosure := J.carrier_subset_closure_sdiff_finite
    (Set.finite_range M.position) hpCarrier
  have hsub : J.carrier \ Set.range M.position ⊆ M.boundaryCarrier := by
    rintro q ⟨hqCarrier, hqNotVertex⟩
    have hqFrontier : q ∈ frontier M.toPlaneComplex.support := by
      rw [hsupport, J.frontier_closedRegion]
      exact hqCarrier
    have hqv : ∀ v : M.Vertex, q ≠ M.position v := by
      intro v hq
      exact hqNotVertex ⟨v, hq.symm⟩
    obtain ⟨e, he, hqe⟩ :=
      (M.mem_frontier_iff_exists_boundaryEdge_of_nonvertex hqv).mp hqFrontier
    simp only [TriangleMesh.boundaryCarrier, Set.mem_iUnion]
    exact ⟨e, M.mem_allBoundaryEdges_iff.mpr he, hqe⟩
  have hpBoundaryClosure : p ∈ closure M.boundaryCarrier := closure_mono hsub hpClosure
  rwa [M.isCompact_boundaryCarrier.isClosed.closure_eq] at hpBoundaryClosure

/-- Restrict a finite PL certificate on a polygonal disk to its polygonal frontier. -/
theorem FinitePLHomeomorphOn.isPLOnSet_polygonal_frontier
    {h : Plane ≃ₜ Plane} {A : Set Plane} (F : FinitePLHomeomorphOn h A)
    (J : PolygonalCircle) (hA : A = J.closedRegion) :
    IsPLOnSet J.carrier h := by
  let M := F.complex.toTriangleMesh
  let B := M.boundaryComplex
  have hMdisk : M.toPlaneComplex.support = J.closedRegion := by
    exact (F.complex.toTriangleMesh_support F.pure).trans (F.support_eq.trans hA)
  have hBsupport : B.support = J.carrier := by
    calc
      B.support = M.boundaryCarrier := M.boundaryComplex_support
      _ = frontier M.toPlaneComplex.support :=
        M.boundaryCarrier_eq_frontier_of_polygonalDisk J hMdisk
      _ = J.carrier := by rw [hMdisk, J.frontier_closedRegion]
  refine ⟨B, hBsupport, B, PlaneComplex.Subdivides.refl B, ?_⟩
  intro s hs
  have hsM : s ∈ M.toPlaneComplex.simplexes :=
    M.boundaryComplex_simplex_mem_toPlaneComplex hs
  obtain ⟨hsne, t, ht, hst⟩ := M.mem_faces_iff.mp hsM
  have hsF : s ∈ F.complex.simplexes := by
    apply F.complex.down_closed t (F.complex.mem_simplexes_of_mem_cells ht) s hst hsne
  exact F.affineOn s hsF

private theorem coordinate_mem_Icc_of_mem_segment {p q r : Plane}
    (hr : r ∈ segment ℝ p q) : min (p 0) (q 0) ≤ r 0 ∧ r 0 ≤ max (p 0) (q 0) := by
  rw [segment_eq_image_lineMap] at hr
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hr
  simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rcases le_total (p 0) (q 0) with hpq | hqp
  · rw [min_eq_left hpq, max_eq_right hpq]
    constructor
    · calc
        p 0 = (1 - t) * p 0 + t * p 0 := by ring
        _ ≤ (1 - t) * p 0 + t * q 0 := by gcongr
    · calc
        (1 - t) * p 0 + t * q 0 ≤ (1 - t) * q 0 + t * q 0 := by gcongr
        _ = q 0 := by ring
  · rw [min_eq_right hqp, max_eq_left hqp]
    constructor
    · calc
        q 0 = (1 - t) * q 0 + t * q 0 := by ring
        _ ≤ (1 - t) * p 0 + t * q 0 := by gcongr
    · calc
        (1 - t) * p 0 + t * q 0 ≤ (1 - t) * p 0 + t * p 0 := by gcongr
        _ = p 0 := by ring

/-- After the three Figure 3.3 base breakpoints have been made polygon vertices, each polygon
edge is contained in one base half or avoids the open base altogether. -/
theorem PolygonalCircle.edgeSegment_subset_normalized_baseHalf_or_disjoint
    (J : PolygonalCircle)
    (hbase : segment ℝ (planePoint (-1) 0) (planePoint 1 0) ⊆ J.carrier)
    (hleft : J.IsVertexPoint (planePoint (-1) 0))
    (hcenter : J.IsVertexPoint (planePoint 0 0))
    (hright : J.IsVertexPoint (planePoint 1 0)) (i : ZMod J.n) :
    J.edgeSegment i ⊆ segment ℝ (planePoint (-1) 0) (planePoint 0 0) ∨
      J.edgeSegment i ⊆ segment ℝ (planePoint 0 0) (planePoint 1 0) ∨
      Disjoint (J.edgeSegment i)
        (openSegment ℝ (planePoint (-1) 0) (planePoint 1 0)) := by
  by_cases hmeet : (J.edgeSegment i ∩
      openSegment ℝ (planePoint (-1) 0) (planePoint 1 0)).Nonempty
  swap
  · exact Or.inr <| Or.inr <| by
      rw [Set.disjoint_iff_inter_eq_empty]
      exact Set.not_nonempty_iff_eq_empty.mp hmeet
  obtain ⟨x, hxEdge, hxBase⟩ := hmeet
  have hPQ : planePoint (-1) 0 ≠ planePoint 1 0 := by
    intro h
    have := congrArg (fun p : Plane => p 0) h
    norm_num [planePoint] at this
  have haxis := J.edge_endpoints_on_axis_of_inter_openBase hPQ
    (by simp [planePoint]) (by simp [planePoint]) hbase hxEdge hxBase
  let a := J.vertex i
  let b := J.vertex (i + 1)
  have hab : a ≠ b := J.adjacent_ne i
  have hxCoord : -1 < x 0 ∧ x 0 < 1 := by
    rw [openSegment_eq_image_lineMap] at hxBase
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hxBase
    simp [AffineMap.lineMap_apply_module, planePoint]
    constructor <;> linarith
  have hxLine : x ∈ segment ℝ a b := hxEdge
  have special_endpoint {P : Plane} (hP : J.IsVertexPoint P)
      (hPmem : P ∈ segment ℝ a b) : P = a ∨ P = b := by
    simpa [a, b] using (hP.mem_edgeSegment_iff i).mp hPmem
  have endpointBounds (z w : Plane) (hz0 : z 1 = 0) (hw0 : w 1 = 0)
      (hx : x ∈ segment ℝ z w)
      (hspecial : ∀ {P : Plane}, J.IsVertexPoint P → P ∈ segment ℝ z w →
        P = z ∨ P = w) : -1 ≤ z 0 ∧ z 0 ≤ 1 := by
    constructor
    · by_contra hz
      have hzlt : z 0 < -1 := lt_of_not_ge hz
      have hwgt : -1 < w 0 := by
        have hb := coordinate_mem_Icc_of_mem_segment hx
        by_contra hw
        have hwle : w 0 ≤ -1 := le_of_not_gt hw
        rcases le_total (z 0) (w 0) with hzw' | hwz'
        · rw [min_eq_left hzw', max_eq_right hzw'] at hb
          linarith
        · rw [min_eq_right hwz', max_eq_left hwz'] at hb
          linarith
      have hleftMem : planePoint (-1) 0 ∈ segment ℝ z w := by
        apply mem_segment_of_horizontal
        · simpa [planePoint] using hz0
        · simpa [planePoint] using hw0
        · simpa [planePoint] using hzlt.le
        · simpa [planePoint] using hwgt.le
      have hleftEnd := hspecial hleft hleftMem
      rcases hleftEnd with hzEq | hwEq
      · have := congrArg (fun p : Plane => p 0) hzEq
        simp [planePoint] at this
        linarith
      · have hwCoord : w 0 = -1 := by
          have := congrArg (fun p : Plane => p 0) hwEq
          simpa [planePoint] using this.symm
        have hb := coordinate_mem_Icc_of_mem_segment hx
        rcases le_total (z 0) (w 0) with hzw' | hwz'
        · rw [min_eq_left hzw', max_eq_right hzw', hwCoord] at hb
          linarith
        · rw [min_eq_right hwz', max_eq_left hwz', hwCoord] at hb
          linarith
    · by_contra hz
      have hzgt : 1 < z 0 := lt_of_not_ge hz
      have hwlt : w 0 < 1 := by
        have hb := coordinate_mem_Icc_of_mem_segment hx
        by_contra hw
        have hwge : 1 ≤ w 0 := le_of_not_gt hw
        rcases le_total (z 0) (w 0) with hzw' | hwz'
        · rw [min_eq_left hzw', max_eq_right hzw'] at hb
          linarith
        · rw [min_eq_right hwz', max_eq_left hwz'] at hb
          linarith
      have hrightMem : planePoint 1 0 ∈ segment ℝ z w := by
        rw [segment_symm]
        apply mem_segment_of_horizontal
        · simpa [planePoint] using hw0
        · simpa [planePoint] using hz0
        · simpa [planePoint] using hwlt.le
        · simpa [planePoint] using hzgt.le
      have hrightEnd := hspecial hright hrightMem
      rcases hrightEnd with hzEq | hwEq
      · have := congrArg (fun p : Plane => p 0) hzEq
        simp [planePoint] at this
        linarith
      · have hwCoord : w 0 = 1 := by
          have := congrArg (fun p : Plane => p 0) hwEq
          simpa [planePoint] using this.symm
        have hb := coordinate_mem_Icc_of_mem_segment hx
        rcases le_total (z 0) (w 0) with hzw' | hwz'
        · rw [min_eq_left hzw', max_eq_right hzw', hwCoord] at hb
          linarith
        · rw [min_eq_right hwz', max_eq_left hwz', hwCoord] at hb
          linarith
  have haBounds := endpointBounds a b haxis.1 haxis.2 hxLine
    (fun hP hPmem => special_endpoint hP hPmem)
  have hbBounds := endpointBounds b a haxis.2 haxis.1 (by rwa [segment_symm])
    (fun hP hPmem => (special_endpoint hP (by rwa [segment_symm] at hPmem)).symm)
  have segment_subset_of_bounds {u v : Plane} (hu0 : u 1 = 0) (hv0 : v 1 = 0)
      (hulo : -1 ≤ u 0) (hvhi : v 0 ≤ 0) (huv : u 0 ≤ v 0) :
      segment ℝ u v ⊆ segment ℝ (planePoint (-1) 0) (planePoint 0 0) := by
    intro p hp
    have hpAxis : p 1 = 0 := by
      rw [segment_eq_image_lineMap] at hp
      obtain ⟨t, ht, rfl⟩ := hp
      simp [AffineMap.lineMap_apply_module, hu0, hv0]
    have hpCoord : -1 ≤ p 0 ∧ p 0 ≤ 0 := by
      have hpBetween := coordinate_mem_Icc_of_mem_segment hp
      rw [min_eq_left huv, max_eq_right huv] at hpBetween
      exact ⟨hulo.trans hpBetween.1, hpBetween.2.trans hvhi⟩
    apply mem_segment_of_horizontal
    · simpa [planePoint] using hpAxis.symm
    · simpa [planePoint] using hpAxis.symm
    · simpa [planePoint] using hpCoord.1
    · simpa [planePoint] using hpCoord.2
  have right_subset_of_bounds {u v : Plane} (hu0 : u 1 = 0) (hv0 : v 1 = 0)
      (hu0c : 0 ≤ u 0) (hvhi : v 0 ≤ 1) (huv : u 0 ≤ v 0) :
      segment ℝ u v ⊆ segment ℝ (planePoint 0 0) (planePoint 1 0) := by
    intro p hp
    have hpAxis : p 1 = 0 := by
      rw [segment_eq_image_lineMap] at hp
      obtain ⟨t, ht, rfl⟩ := hp
      simp [AffineMap.lineMap_apply_module, hu0, hv0]
    have hpCoord : 0 ≤ p 0 ∧ p 0 ≤ 1 := by
      have hpBetween := coordinate_mem_Icc_of_mem_segment hp
      rw [min_eq_left huv, max_eq_right huv] at hpBetween
      exact ⟨hu0c.trans hpBetween.1, hpBetween.2.trans hvhi⟩
    apply mem_segment_of_horizontal
    · simpa [planePoint] using hpAxis.symm
    · simpa [planePoint] using hpAxis.symm
    · simpa [planePoint] using hpCoord.1
    · simpa [planePoint] using hpCoord.2
  by_cases ha0 : a 0 ≤ 0
  · by_cases hb0 : b 0 ≤ 0
    · left
      change segment ℝ a b ⊆ _
      rcases le_total (a 0) (b 0) with hab0 | hba0
      · exact segment_subset_of_bounds haxis.1 haxis.2 haBounds.1 hb0 hab0
      · rw [segment_symm]
        exact segment_subset_of_bounds haxis.2 haxis.1 hbBounds.1 ha0 hba0
    · have hbpos : 0 < b 0 := lt_of_not_ge hb0
      have hcenterMem : planePoint 0 0 ∈ segment ℝ a b :=
        mem_segment_of_horizontal haxis.1 (by simpa [planePoint] using haxis.2)
          (by simpa [planePoint] using ha0) (by simpa [planePoint] using hbpos.le)
      rcases (hcenter.mem_edgeSegment_iff i).mp hcenterMem with haEq | hbEq
      · right; left
        change segment ℝ a b ⊆ _
        have haCoord : a 0 = 0 := by
          have := congrArg (fun p : Plane => p 0) haEq
          simpa [planePoint] using this.symm
        exact right_subset_of_bounds haxis.1 haxis.2 haCoord.ge hbBounds.2
          (by linarith)
      · have := congrArg (fun p : Plane => p 0) hbEq
        simp [planePoint] at this
        linarith
  · have hapos : 0 < a 0 := lt_of_not_ge ha0
    by_cases hb0 : b 0 ≤ 0
    · have hcenterMem : planePoint 0 0 ∈ segment ℝ a b := by
        rw [segment_symm]
        exact mem_segment_of_horizontal haxis.2 (by simpa [planePoint] using haxis.1)
          (by simpa [planePoint] using hb0) (by simpa [planePoint] using hapos.le)
      rcases (hcenter.mem_edgeSegment_iff i).mp hcenterMem with haEq | hbEq
      · have := congrArg (fun p : Plane => p 0) haEq
        simp [planePoint] at this
        linarith
      · right; left
        change segment ℝ a b ⊆ _
        have hbCoord : b 0 = 0 := by
          have := congrArg (fun p : Plane => p 0) hbEq
          simpa [planePoint] using this.symm
        rw [segment_symm]
        exact right_subset_of_bounds haxis.2 haxis.1 hbCoord.ge haBounds.2
          (by linarith)
    · right; left
      change segment ℝ a b ⊆ _
      rcases le_total (a 0) (b 0) with hab0 | hba0
      · exact right_subset_of_bounds haxis.1 haxis.2 hapos.le hbBounds.2 hab0
      · rw [segment_symm]
        exact right_subset_of_bounds haxis.2 haxis.1 (lt_of_not_ge hb0).le
          haBounds.2 hba0

/-- Once the three Figure 3.3 breakpoints are vertices, the normalized thin-kite move carries
the polygon to another polygon.  Away from the standard triangle only pointwise fixation is
needed; inside it, the old polygon has exactly the horizontal base trace. -/
theorem PolygonalCircle.exists_thinKite_image
    (K : PolygonalCircle) (δ : ℝ) (hδ : 0 < δ)
    (hbase : segment ℝ (planePoint (-1) 0) (planePoint 1 0) ⊆ K.carrier)
    (hleft : K.IsVertexPoint (planePoint (-1) 0))
    (hcenter : K.IsVertexPoint (planePoint 0 0))
    (hright : K.IsVertexPoint (planePoint 1 0))
    (htrace : K.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) =
      segment ℝ (planePoint (-1) 0) (planePoint 1 0))
    (hfix : Set.EqOn (thinKiteAmbientHomeomorph δ hδ) id
      (K.carrier \ convexHull ℝ (Set.range kiteTrianglePosition))) :
    ∃ K' : PolygonalCircle,
      K'.carrier = thinKiteAmbientHomeomorph δ hδ '' K.carrier := by
  let h := thinKiteAmbientHomeomorph δ hδ
  have hleftFix : h (planePoint (-1) 0) = planePoint (-1) 0 := by
    have hm := thinKiteAmbientHomeomorph_leftSpoke δ hδ 0 (by simp)
    simpa [h, AffineMap.lineMap_apply_module] using hm
  have hrightFix : h (planePoint 1 0) = planePoint 1 0 := by
    have hm := thinKiteAmbientHomeomorph_rightSpoke δ hδ 0 (by simp)
    simpa [h, AffineMap.lineMap_apply_module] using hm
  have hedge : ∀ i : ZMod K.n,
      h '' K.edgeSegment i = segment ℝ (h (K.vertex i)) (h (K.vertex (i + 1))) := by
    intro i
    rcases K.edgeSegment_subset_normalized_baseHalf_or_disjoint
        hbase hleft hcenter hright i with hleftEdge | hrightEdge | hdisjoint
    · exact thinKiteAmbientHomeomorph_image_segment_of_endpoints_mem_leftSpoke
        δ hδ (hleftEdge (left_mem_segment ℝ _ _))
          (hleftEdge (right_mem_segment ℝ _ _))
    · exact thinKiteAmbientHomeomorph_image_segment_of_endpoints_mem_rightSpoke
        δ hδ (hrightEdge (left_mem_segment ℝ _ _))
          (hrightEdge (right_mem_segment ℝ _ _))
    · have heq : Set.EqOn h id (K.edgeSegment i) := by
        intro p hp
        by_cases hpTriangle : p ∈ convexHull ℝ (Set.range kiteTrianglePosition)
        · have hpBase : p ∈
              segment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
            rw [← htrace]
            exact ⟨K.edgeSegment_subset_carrier i hp, hpTriangle⟩
          have hpNotOpen : p ∉
              openSegment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
            exact fun hpOpen => Set.disjoint_left.mp hdisjoint hp hpOpen
          have hpEndpoint : p = planePoint (-1) 0 ∨ p = planePoint 1 0 := by
            rw [← insert_endpoints_openSegment] at hpBase
            simp only [Set.mem_insert_iff] at hpBase
            rcases hpBase with hpLeft | hpRight | hpOpen
            · exact Or.inl hpLeft
            · exact Or.inr hpRight
            · exact False.elim (hpNotOpen hpOpen)
          rcases hpEndpoint with rfl | rfl
          · exact hleftFix
          · exact hrightFix
        · exact hfix ⟨K.edgeSegment_subset_carrier i hp, hpTriangle⟩
      have himage : h '' K.edgeSegment i = K.edgeSegment i := by
        apply Set.Subset.antisymm
        · rintro p ⟨q, hq, rfl⟩
          rw [heq hq]
          exact hq
        · intro p hp
          exact ⟨p, hp, by simpa using heq hp⟩
      rw [himage, heq (left_mem_segment ℝ _ _),
        heq (right_mem_segment ℝ _ _)]
      rfl
  exact ⟨K.mapHomeomorph h hedge, K.mapHomeomorph_carrier h hedge⟩

private theorem exists_pos_uniform_fintype {I : Type*} [Finite I] [Nonempty I]
    (P : I → ℝ → Prop)
    (hP : ∀ i, ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε → P i δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ∀ δ : ℝ, 0 < δ → δ < ε → P i δ := by
  classical
  letI := Fintype.ofFinite I
  let values : Finset ℝ := Finset.univ.image fun i => Classical.choose (hP i)
  have hvalues : values.Nonempty := by
    let i : I := Classical.choice inferInstance
    exact ⟨Classical.choose (hP i), Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let ε := values.min' hvalues
  have hε : 0 < ε := by
    have hmem : ε ∈ values := Finset.min'_mem values hvalues
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    rw [← hi]
    exact (Classical.choose_spec (hP i)).1
  refine ⟨ε, hε, ?_⟩
  intro i δ hδ hδε
  apply (Classical.choose_spec (hP i)).2 δ hδ
  exact hδε.trans_le (Finset.min'_le values
    (Classical.choose (hP i)) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

/-- A sufficiently thin normalized kite fixes a refined polygon outside the standard triangle.
This is the finite boundary-avoidance step used in the inverse, two-edge Figure 3.3 move. -/
theorem PolygonalCircle.exists_thinKite_fixing_outside_triangle
    (K : PolygonalCircle)
    (hleft : K.IsVertexPoint (planePoint (-1) 0))
    (hcenter : K.IsVertexPoint (planePoint 0 0))
    (hright : K.IsVertexPoint (planePoint 1 0))
    (htrace : K.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) =
      segment ℝ (planePoint (-1) 0) (planePoint 1 0))
    (W : Set Plane) (hW : IsOpen W)
    (htriangleW : convexHull ℝ (Set.range kiteTrianglePosition) ⊆ W) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, thinKitePatch δ ⊆ W ∧
      Set.EqOn (thinKiteAmbientHomeomorph δ hδ) id
        (K.carrier \ convexHull ℝ (Set.range kiteTrianglePosition)) := by
  classical
  let openBase := openSegment ℝ (planePoint (-1) 0) (planePoint 1 0)
  let endpoints : Set Plane := {planePoint (-1) 0, planePoint 1 0}
  have hbaseTriangle : segment ℝ (planePoint (-1) 0) (planePoint 1 0) ⊆
      convexHull ℝ (Set.range kiteTrianglePosition) := by
    apply (convex_convexHull ℝ _).segment_subset
    · exact subset_convexHull ℝ _ ⟨0, by simp [kiteTrianglePosition]⟩
    · exact subset_convexHull ℝ _ ⟨1, by simp [kiteTrianglePosition]⟩
  let P : ZMod K.n → ℝ → Prop := fun i δ =>
    Disjoint (K.edgeSegment i) openBase →
      thinKitePatch δ ∩ K.edgeSegment i ⊆ endpoints
  have hlocal : ∀ i, ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 < δ → δ < ε → P i δ := by
    intro i
    by_cases hdisjoint : Disjoint (K.edgeSegment i) openBase
    swap
    · exact ⟨1, by norm_num, fun _ _ _ hd => False.elim (hdisjoint hd)⟩
    have hinter : K.edgeSegment i ∩
        convexHull ℝ (Set.range kiteTrianglePosition) ⊆ endpoints := by
      rintro p ⟨hpEdge, hpTriangle⟩
      have hpBase : p ∈ segment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
        rw [← htrace]
        exact ⟨K.edgeSegment_subset_carrier i hpEdge, hpTriangle⟩
      have hpNotOpen : p ∉ openBase := fun hpOpen =>
        Set.disjoint_left.mp hdisjoint hpEdge hpOpen
      rw [← insert_endpoints_openSegment] at hpBase
      simp only [Set.mem_insert_iff] at hpBase
      rcases hpBase with hp | hp | hp
      · exact Or.inl hp
      · exact Or.inr hp
      · exact False.elim (hpNotOpen hp)
    have hleftEndpoint : planePoint (-1) 0 ∈ K.edgeSegment i →
        K.vertex i = planePoint (-1) 0 ∨ K.vertex (i + 1) = planePoint (-1) 0 := by
      intro hp
      rcases (hleft.mem_edgeSegment_iff i).mp hp with hp | hp
      · exact Or.inl hp.symm
      · exact Or.inr hp.symm
    have hrightEndpoint : planePoint 1 0 ∈ K.edgeSegment i →
        K.vertex i = planePoint 1 0 ∨ K.vertex (i + 1) = planePoint 1 0 := by
      intro hp
      rcases (hright.mem_edgeSegment_iff i).mp hp with hp | hp
      · exact Or.inl hp.symm
      · exact Or.inr hp.symm
    have hnotBoth : ¬(planePoint (-1) 0 ∈ K.edgeSegment i ∧
        planePoint 1 0 ∈ K.edgeSegment i) := by
      rintro ⟨hL, hR⟩
      have hcenterBase : planePoint 0 0 ∈ openBase := by
        change planePoint 0 0 ∈
          openSegment ℝ (planePoint (-1) 0) (planePoint 1 0)
        rw [openSegment_eq_image_lineMap]
        refine ⟨(1 : ℝ) / 2, by norm_num, ?_⟩
        ext j
        fin_cases j <;> simp [AffineMap.lineMap_apply_module, planePoint] ; norm_num
      have hcenterEdge : planePoint 0 0 ∈ K.edgeSegment i :=
        (convex_segment (𝕜 := ℝ) (K.vertex i) (K.vertex (i + 1))).segment_subset
          hL hR (openSegment_subset_segment ℝ _ _ hcenterBase)
      exact Set.disjoint_left.mp hdisjoint hcenterEdge hcenterBase
    obtain ⟨ε, hε, havoid⟩ :=
      exists_thinKitePatch_inter_segment_subset_baseEndpoints
        (K.adjacent_ne i) hinter hleftEndpoint hrightEndpoint hnotBoth
    exact ⟨ε, hε, fun δ hδ hδε _ => havoid δ hδ hδε⟩
  obtain ⟨εA, hεA, havoid⟩ := exists_pos_uniform_fintype P hlocal
  obtain ⟨εW, hεW, hpatchW⟩ :=
    exists_thinKitePatch_subset_open_normalized W hW htriangleW
  let δ := min εA εW / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδA : δ < εA := by
    dsimp [δ]
    nlinarith [min_le_left εA εW, lt_min hεA hεW]
  have hδW : δ < εW := by
    dsimp [δ]
    nlinarith [min_le_right εA εW, lt_min hεA hεW]
  refine ⟨δ, hδ, hpatchW δ hδ hδW, ?_⟩
  intro p hp
  obtain ⟨i, hpEdge⟩ := Set.mem_iUnion.mp hp.1
  have hdisjoint : Disjoint (K.edgeSegment i) openBase := by
    rcases K.edgeSegment_subset_normalized_baseHalf_or_disjoint
        (by
          intro q hq
          have : q ∈ K.carrier ∩
              convexHull ℝ (Set.range kiteTrianglePosition) := by
            rw [htrace]
            exact hq
          exact this.1)
        hleft hcenter hright i with hL | hR | hd
    · apply False.elim
      apply hp.2
      apply hbaseTriangle
      rw [baseSegment_eq_spokes]
      exact Or.inl (hL hpEdge)
    · apply False.elim
      apply hp.2
      apply hbaseTriangle
      rw [baseSegment_eq_spokes]
      right
      rw [segment_symm]
      exact hR hpEdge
    · exact hd
  apply thinKiteAmbientHomeomorph_eqOn_compl δ hδ
  intro hpPatch
  have hpEndpoint := havoid i δ hδ hδA hdisjoint ⟨hpPatch, hpEdge⟩
  rcases hpEndpoint with hpLeft | hpRight
  · apply hp.2
    rw [hpLeft]
    exact subset_convexHull ℝ _ ⟨0, by simp [kiteTrianglePosition]⟩
  · apply hp.2
    rw [hpRight]
    exact subset_convexHull ℝ _ ⟨1, by simp [kiteTrianglePosition]⟩

/-- In a triangulated polygonal disk with more than one maximal triangle, every maximal
triangle has an edge-neighbor.  A triangle attached only at vertices would make its open
interior a clopen piece of the connected polygon interior. -/
theorem TriangleMesh.exists_edgeNeighbor_of_polygonalDisk (M : TriangleMesh)
    (J : PolygonalCircle) (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) (hmore : 1 < M.triangles.card) :
    ∃ U : M.Triangle, T.1 ≠ U.1 ∧ M.AreEdgeNeighbors T.1 U.1 := by
  by_contra hexists
  have hNoNeighbor {u : Finset M.Vertex} (hu : u ∈ M.triangles) (hne : T.1 ≠ u) :
      ¬M.AreEdgeNeighbors T.1 u := by
    intro hneighbor
    exact hexists ⟨⟨u, hu⟩, hne, hneighbor⟩
  have hAllBoundary : ∀ e ∈ M.triangleEdges T.1, M.IsBoundaryEdge e := by
    intro e he
    have heData := Finset.mem_powersetCard.mp he
    have heEdges : e ∈ M.edges := by
      apply Finset.mem_biUnion.mpr
      exact ⟨T.1, T.2, Finset.mem_powersetCard.mpr heData⟩
    have hincident : M.incidentTriangles e = {T.1} := by
      ext u
      constructor
      · intro hu
        have huData := M.mem_incidentTriangles_iff.mp hu
        rw [Finset.mem_singleton]
        by_contra hne
        exact hNoNeighbor huData.1 (fun h => hne h.symm)
          ⟨e, heData.2, heData.1, huData.2⟩
      · intro hu
        rw [Finset.mem_singleton] at hu
        subst u
        exact M.mem_incidentTriangles_iff.mpr ⟨T.2, heData.1⟩
    exact ⟨heEdges, by rw [hincident]; simp⟩
  have hfrontierTriangle : frontier (M.triangleCarrier T.1) ⊆
      frontier M.toPlaneComplex.support := by
    intro p hp
    obtain ⟨e, hecard, heT, hpEdge⟩ := M.exists_edge_of_mem_frontier_triangle T.2 hp
    have heTriangle : e ∈ M.triangleEdges T.1 :=
      Finset.mem_powersetCard.mpr ⟨heT, hecard⟩
    exact M.boundaryEdgeCarrier_subset_frontier (hAllBoundary e heTriangle) hpEdge
  have hfrontierCarrier : frontier (M.triangleCarrier T.1) ⊆ J.carrier := by
    rw [← J.frontier_closedRegion, ← hsupport]
    exact hfrontierTriangle
  have htriangleSubset : M.triangleCarrier T.1 ⊆ M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset T.1
      (Set.subset_iUnion_of_subset T.2 (by rfl))
  have hInteriorSubset : interior (M.triangleCarrier T.1) ⊆ J.interiorRegion := by
    rw [← J.interior_closedRegion, ← hsupport]
    exact interior_mono htriangleSubset
  have hCarrierClosed : IsClosed (M.triangleCarrier T.1) :=
    (T.1.finite_toSet.image M.position).isClosed_convexHull ℝ
  have hcover : J.interiorRegion ⊆
      interior (M.triangleCarrier T.1) ∪ (M.triangleCarrier T.1)ᶜ := by
    intro p hp
    by_cases hpT : p ∈ M.triangleCarrier T.1
    · left
      exact (mem_interior_iff_notMem_frontier hpT).mpr fun hpFrontier =>
        (show p ∈ J.carrierᶜ by
          rw [← J.interior_union_exterior]
          exact Or.inl hp) (hfrontierCarrier hpFrontier)
    · exact Or.inr hpT
  have hdisjoint : Disjoint (interior (M.triangleCarrier T.1))
      (M.triangleCarrier T.1)ᶜ := by
    rw [Set.disjoint_left]
    intro p hpInterior hpCompl
    exact hpCompl (interior_subset hpInterior)
  obtain ⟨p, hpT⟩ := M.interior_triangleCarrier_nonempty T
  have hpInside := hInteriorSubset hpT
  have hallInside : J.interiorRegion ⊆ interior (M.triangleCarrier T.1) :=
    J.isConnected_interiorRegion.isPreconnected.subset_left_of_subset_union
      isOpen_interior hCarrierClosed.isOpen_compl hdisjoint hcover ⟨p, hpInside, hpT⟩
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp hmore
  let u := if haT : a = T.1 then b else a
  have hu : u ∈ M.triangles := by
    dsimp [u]
    split_ifs with haT
    · exact hb
    · exact ha
  have hune : T.1 ≠ u := by
    dsimp [u]
    split_ifs with haT
    · exact fun h => hab (haT.trans h)
    · exact fun h => haT h.symm
  let U : M.Triangle := ⟨u, hu⟩
  obtain ⟨q, hqU⟩ := M.interior_triangleCarrier_nonempty U
  have hUCarrierSubset : M.triangleCarrier U.1 ⊆ M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset U.1
      (Set.subset_iUnion_of_subset U.2 (by rfl))
  have hqInside : q ∈ J.interiorRegion := by
    rw [← J.interior_closedRegion, ← hsupport]
    exact interior_mono hUCarrierSubset hqU
  exact Set.disjoint_left.mp (M.disjoint_interior_triangleCarrier hune)
    (hallInside hqInside) hqU

/-- If a polygonal-disk mesh has another triangle, some point of the polygon frontier lies
outside any prescribed maximal triangle. -/
theorem TriangleMesh.exists_carrier_not_mem_triangleCarrier_of_polygonalDisk
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) (hmore : 1 < M.triangles.card) :
    ∃ p ∈ J.carrier, p ∉ M.triangleCarrier T.1 := by
  obtain ⟨U, hTU, -⟩ := M.exists_edgeNeighbor_of_polygonalDisk J hsupport T hmore
  have hsupportNotSubset :
      ¬M.toPlaneComplex.support ⊆ M.triangleCarrier T.1 := by
    intro hall
    have hUCarrierSubset : M.triangleCarrier U.1 ⊆ M.toPlaneComplex.support := by
      rw [M.toPlaneComplex_support]
      exact Set.subset_iUnion_of_subset U.1
        (Set.subset_iUnion_of_subset U.2 (by rfl))
    have hUInteriorSubset :
        interior (M.triangleCarrier U.1) ⊆ M.triangleCarrier T.1 :=
      interior_subset.trans (hUCarrierSubset.trans hall)
    have hUInteriorSubsetInterior :
        interior (M.triangleCarrier U.1) ⊆ interior (M.triangleCarrier T.1) :=
      interior_maximal hUInteriorSubset isOpen_interior
    obtain ⟨p, hpU⟩ := M.interior_triangleCarrier_nonempty U
    exact Set.disjoint_left.mp (M.disjoint_interior_triangleCarrier hTU)
      (hUInteriorSubsetInterior hpU) hpU
  obtain ⟨p, hpSupport, hpT⟩ := Set.not_subset.mp hsupportNotSubset
  have hTClosed : IsClosed (M.triangleCarrier T.1) :=
    (T.1.finite_toSet.image M.position).isClosed_convexHull ℝ
  obtain ⟨f, u, hfT, hufp⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (M.position '' (T.1 : Set M.Vertex))) hTClosed hpT
  obtain ⟨q, hqSupport, hqMax⟩ :=
    M.toPlaneComplex.isCompact_support.exists_isMaxOn
      ⟨p, hpSupport⟩ f.continuous.continuousOn
  have hqT : q ∉ M.triangleCarrier T.1 := by
    intro hqT
    have := hfT q hqT
    have hpq := hqMax hpSupport
    change f p ≤ f q at hpq
    linarith
  have hfne : f ≠ 0 := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by rw [M.card_triangle T.1 T.2]; omega)
    have hvT : M.position v ∈ M.triangleCarrier T.1 :=
      subset_convexHull ℝ _ ⟨v, hv, rfl⟩
    intro hfzero
    have hleft := hfT (M.position v) hvT
    rw [hfzero] at hleft hufp
    simp only [zero_apply] at hleft hufp
    linarith
  have hqFrontier : q ∈ frontier M.toPlaneComplex.support := by
    apply (mem_frontier_iff_notMem_interior hqSupport).mpr
    intro hqInterior
    obtain ⟨y, hy⟩ : ∃ y : Plane, f y ≠ 0 := by
      by_contra h
      push Not at h
      apply hfne
      ext y
      simpa using h y
    let d : Plane := if 0 < f y then y else -y
    have hfd : 0 < f d := by
      dsimp [d]
      split_ifs with hypos
      · exact hypos
      · simp only [map_neg, Left.neg_pos_iff]
        exact lt_of_le_of_ne (le_of_not_gt hypos) hy
    have hdne : d ≠ 0 := by
      intro hd
      rw [hd] at hfd
      simp at hfd
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
      (mem_interior_iff_mem_nhds.mp hqInterior)
    let δ : ℝ := ε / (2 * ‖d‖)
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    let z : Plane := q + δ • d
    have hzBall : z ∈ Metric.ball q ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      change ‖q + δ • d - q‖ < ε
      rw [add_sub_cancel_left]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      dsimp [δ]
      have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hdne
      field_simp
      linarith
    have hzSupport : z ∈ M.toPlaneComplex.support := hball hzBall
    have hzGreater : f q < f z := by
      dsimp [z]
      rw [map_add, map_smul]
      change f q < f q + δ * f d
      nlinarith
    exact (not_lt_of_ge (hqMax hzSupport)) hzGreater
  refine ⟨q, ?_, hqT⟩
  rw [hsupport, J.frontier_closedRegion] at hqFrontier
  exact hqFrontier

/-- The proved starting point of Moise Chapter 3, Theorem 3: a nontrivial triangulated
polygonal disk has a weakly free triangle, and that triangle has an edge-neighbor. -/
theorem TriangleMesh.exists_freeTriangle_with_neighbor_of_polygonalDisk
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (hmore : 1 < M.triangles.card) :
    ∃ T U : M.Triangle, M.IsFreeTriangle T.1 ∧ T.1 ≠ U.1 ∧
      M.AreEdgeNeighbors T.1 U.1 := by
  have hne : M.triangles.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨t, htFree⟩ := M.exists_free_triangle_of_triangles_nonempty hne
  let T : M.Triangle := ⟨t, htFree.1⟩
  obtain ⟨U, hTU, hneighbor⟩ :=
    M.exists_edgeNeighbor_of_polygonalDisk J hsupport T hmore
  exact ⟨T, U, htFree, hTU, hneighbor⟩

/-- Moise Chapter 3, Theorem 3, preliminary step: a nontrivial triangulated polygonal disk has
two distinct triangles containing incidence-one edges. -/
theorem TriangleMesh.exists_two_freeTriangles_of_polygonalDisk
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (hmore : 1 < M.triangles.card) :
    ∃ T U : M.Triangle,
      T.1 ≠ U.1 ∧ M.IsFreeTriangle T.1 ∧ M.IsFreeTriangle U.1 := by
  obtain ⟨T, -, hTfree, -, -⟩ :=
    M.exists_freeTriangle_with_neighbor_of_polygonalDisk J hsupport hmore
  obtain ⟨q, hqCarrier, hqT⟩ :=
    M.exists_carrier_not_mem_triangleCarrier_of_polygonalDisk J hsupport T hmore
  have hqClosure : q ∈ closure (J.carrier \ Set.range M.position) :=
    J.carrier_subset_closure_sdiff_finite (Set.finite_range M.position) hqCarrier
  have hTClosed : IsClosed (M.triangleCarrier T.1) :=
    (T.1.finite_toSet.image M.position).isClosed_convexHull ℝ
  obtain ⟨r, hrT, hrCarrier, hrNotVertex⟩ :=
    (mem_closure_iff.mp hqClosure) (M.triangleCarrier T.1)ᶜ
      hTClosed.isOpen_compl hqT
  have hrFrontier : r ∈ frontier M.toPlaneComplex.support := by
    rw [hsupport, J.frontier_closedRegion]
    exact hrCarrier
  have hrv : ∀ v : M.Vertex, r ≠ M.position v := by
    intro v hrv
    apply hrNotVertex
    exact ⟨v, hrv.symm⟩
  obtain ⟨u, hu, e, heBoundary, heu, hre⟩ :=
    M.exists_boundaryEdge_through_frontier_point hrFrontier hrv
  let U : M.Triangle := ⟨u, hu⟩
  have hTU : T.1 ≠ U.1 := by
    intro h
    apply hrT
    apply convexHull_mono (Set.image_mono ?_) hre
    intro v hv
    rw [h]
    exact heu hv
  exact ⟨T, U, hTU, hTfree, hu, e, heBoundary, heu⟩

/-- In a two-triangle polygonal disk, each maximal triangle has exactly its two outer edges on
the boundary. -/
theorem TriangleMesh.boundaryEdges_card_two_of_card_triangles_eq_two
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) (hcard : M.triangles.card = 2) :
    (M.boundaryEdges T.1).card = 2 := by
  have hmore : 1 < M.triangles.card := by omega
  obtain ⟨U, hTU, hneighbors⟩ :=
    M.exists_edgeNeighbor_of_polygonalDisk J hsupport T hmore
  obtain ⟨e, hecard, heT, heU⟩ := hneighbors
  have hpairCard : ({T.1, U.1} : Finset (Finset M.Vertex)).card = 2 := by
    simp [hTU]
  have htriangles : M.triangles = {T.1, U.1} := by
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      rw [Finset.mem_insert, Finset.mem_singleton]
      by_contra hnot
      push Not at hnot
      have hthree : 2 < M.triangles.card :=
        Finset.two_lt_card_iff.mpr ⟨T.1, U.1, t, T.2, U.2, ht,
          hTU, Ne.symm hnot.1, Ne.symm hnot.2⟩
      omega
    · rw [hcard, hpairCard]
  have heEdge : e ∈ M.edges := by
    apply Finset.mem_biUnion.mpr
    exact ⟨T.1, T.2, Finset.mem_powersetCard.mpr ⟨heT, hecard⟩⟩
  have heNotBoundary : ¬M.IsBoundaryEdge e := by
    intro heBoundary
    have hTi : T.1 ∈ M.incidentTriangles e :=
      M.mem_incidentTriangles_iff.mpr ⟨T.2, heT⟩
    have hUi : U.1 ∈ M.incidentTriangles e :=
      M.mem_incidentTriangles_iff.mpr ⟨U.2, heU⟩
    have htwo : 2 ≤ (M.incidentTriangles e).card :=
      Finset.one_lt_card.mpr ⟨T.1, hTi, U.1, hUi, hTU⟩
    rw [heBoundary.2] at htwo
    omega
  have hboundary : M.boundaryEdges T.1 = (M.triangleEdges T.1).erase e := by
    ext d
    rw [M.mem_boundaryEdges_iff, Finset.mem_erase]
    constructor
    · rintro ⟨hdT, hdcard, hdBoundary⟩
      refine ⟨?_, Finset.mem_powersetCard.mpr ⟨hdT, hdcard⟩⟩
      intro hde
      exact heNotBoundary (hde ▸ hdBoundary)
    · rintro ⟨hde, hdTriangle⟩
      have hdData := Finset.mem_powersetCard.mp hdTriangle
      refine ⟨hdData.1, hdData.2, ?_⟩
      have hdEdge : d ∈ M.edges := by
        apply Finset.mem_biUnion.mpr
        exact ⟨T.1, T.2, hdTriangle⟩
      refine ⟨hdEdge, ?_⟩
      have hincident : M.incidentTriangles d = {T.1} := by
        ext s
        rw [M.mem_incidentTriangles_iff, Finset.mem_singleton]
        constructor
        · rintro ⟨hs, hds⟩
          rw [htriangles, Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with rfl | hsU
          · rfl
          · exfalso
            subst s
            have hinterD := M.triangle_inter_eq_edge hTU hdData.2 hdData.1 hds
            have hinterE := M.triangle_inter_eq_edge hTU hecard heT heU
            apply hde
            exact hinterD.symm.trans hinterE
        · rintro rfl
          exact ⟨T.2, hdData.1⟩
      rw [hincident]
      simp
  rw [hboundary, Finset.card_erase_of_mem]
  · rw [M.card_triangleEdges T.2]
  · exact Finset.mem_powersetCard.mpr ⟨heT, hecard⟩

/-- Both maximal triangles of a two-triangle polygonal disk are Figure 3.3 free triangles. -/
theorem TriangleMesh.isGeometricallyFreeTriangle_of_card_triangles_eq_two
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) (hcard : M.triangles.card = 2) :
    M.IsGeometricallyFreeTriangle T := by
  have hboundary :=
    M.boundaryEdges_card_two_of_card_triangles_eq_two J hsupport T hcard
  exact M.isGeometricallyFreeTriangle_of_boundaryEdges_card_two T
    (M.hasNoIsolatedFrontierVertex_of_boundaryEdges_card_two T hboundary) hboundary

/-- The two non-boundary edges in the hard free-triangle configuration are genuine chords:
away from their endpoints they lie in the polygon interior. -/
theorem TriangleMesh.cuttingDiagonals_interior_of_polygonalDisk
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) {a b v : M.Vertex}
    (hab : a ≠ b) (hva : v ≠ a) (hvb : v ≠ b)
    (htriangle : T.1 = {a, b, v})
    (hboundary : M.boundaryEdges T.1 = {{a, b}}) :
    (convexHull ℝ (M.position '' (({a, v} : Finset M.Vertex) : Set M.Vertex)) \
        (M.position '' (({a, v} : Finset M.Vertex) : Set M.Vertex)) ⊆ J.interiorRegion) ∧
      (convexHull ℝ (M.position '' (({b, v} : Finset M.Vertex) : Set M.Vertex)) \
        (M.position '' (({b, v} : Finset M.Vertex) : Set M.Vertex)) ⊆ J.interiorRegion) := by
  have havCard : ({a, v} : Finset M.Vertex).card = 2 := by simp [Ne.symm hva]
  have hbvCard : ({b, v} : Finset M.Vertex).card = 2 := by simp [Ne.symm hvb]
  have havT : ({a, v} : Finset M.Vertex) ⊆ T.1 := by
    rw [htriangle]
    simp
  have hbvT : ({b, v} : Finset M.Vertex) ⊆ T.1 := by
    rw [htriangle]
    simp
  have havNotBoundary : ¬M.IsBoundaryEdge {a, v} := by
    intro havBoundary
    have havMem : ({a, v} : Finset M.Vertex) ∈ M.boundaryEdges T.1 :=
      M.mem_boundaryEdges_iff.mpr ⟨havT, havCard, havBoundary⟩
    rw [hboundary, Finset.mem_singleton] at havMem
    have hs : ({a, v} : Set M.Vertex) = {a, b} := by
      simpa using congrArg (fun e : Finset M.Vertex => (e : Set M.Vertex)) havMem
    rw [Set.pair_eq_pair_iff] at hs
    exact hs.elim (fun h => hvb h.2) (fun h => hab h.1)
  have hbvNotBoundary : ¬M.IsBoundaryEdge {b, v} := by
    intro hbvBoundary
    have hbvMem : ({b, v} : Finset M.Vertex) ∈ M.boundaryEdges T.1 :=
      M.mem_boundaryEdges_iff.mpr ⟨hbvT, hbvCard, hbvBoundary⟩
    rw [hboundary, Finset.mem_singleton] at hbvMem
    have hs : ({b, v} : Set M.Vertex) = {a, b} := by
      simpa using congrArg (fun e : Finset M.Vertex => (e : Set M.Vertex)) hbvMem
    rw [Set.pair_eq_pair_iff] at hs
    exact hs.elim (fun h => hab h.1.symm) (fun h => hva h.2)
  constructor
  · rw [← J.interior_closedRegion, ← hsupport]
    exact M.edgeCarrier_diff_vertices_subset_interior_support
      T.2 havCard havT havNotBoundary
  · rw [← J.interior_closedRegion, ← hsupport]
    exact M.edgeCarrier_diff_vertices_subset_interior_support
      T.2 hbvCard hbvT hbvNotBoundary

/-- A bad weakly free triangle supplies the two proper polygonal crosscuts used in Moise's
cutting induction. -/
theorem TriangleMesh.exists_realizedProperChords_of_badFreeTriangle
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T U : M.Triangle) (hfree : M.IsFreeTriangle T.1)
    (hne : T.1 ≠ U.1) (hneighbors : M.AreEdgeNeighbors T.1 U.1)
    (hnot : ¬M.HasNoIsolatedFrontierVertex T.1) :
    ∃ a b v : M.Vertex, ∃ Cav Cbv : J.ProperChord,
      T.1 = {a, b, v} ∧ M.boundaryEdges T.1 = {{a, b}} ∧
      Cav.P = M.position a ∧ Cav.Q = M.position v ∧
      Cbv.P = M.position b ∧ Cbv.Q = M.position v := by
  obtain ⟨a, b, v, hab, hva, hvb, htriangle, hboundary, hvFrontier⟩ :=
    M.exists_cutting_diagonal_configuration T U hfree hne hneighbors hnot
  obtain ⟨havInterior, hbvInterior⟩ :=
    M.cuttingDiagonals_interior_of_polygonalDisk J hsupport T hab hva hvb
      htriangle hboundary
  have habMem : ({a, b} : Finset M.Vertex) ∈ M.boundaryEdges T.1 := by
    rw [hboundary]
    simp
  have habBoundary := (M.mem_boundaryEdges_iff.mp habMem).2.2
  have haFrontier : M.position a ∈ frontier M.toPlaneComplex.support :=
    M.boundaryEdgeCarrier_subset_frontier habBoundary
      (subset_convexHull ℝ _ ⟨a, by simp, rfl⟩)
  have hbFrontier : M.position b ∈ frontier M.toPlaneComplex.support :=
    M.boundaryEdgeCarrier_subset_frontier habBoundary
      (subset_convexHull ℝ _ ⟨b, by simp, rfl⟩)
  have frontier_eq : frontier M.toPlaneComplex.support = J.carrier := by
    rw [hsupport, J.frontier_closedRegion]
  have havImage : M.position '' (({a, v} : Finset M.Vertex) : Set M.Vertex) =
      {M.position a, M.position v} := by
    ext p
    simp [eq_comm]
  have hbvImage : M.position '' (({b, v} : Finset M.Vertex) : Set M.Vertex) =
      {M.position b, M.position v} := by
    ext p
    simp [eq_comm]
  let Cav : J.ProperChord :=
    { P := M.position a
      Q := M.position v
      ne := M.position_injective.ne (Ne.symm hva)
      P_mem := frontier_eq ▸ haFrontier
      Q_mem := frontier_eq ▸ hvFrontier
      interior_subset := by
        rw [← convexHull_pair, ← havImage]
        exact havInterior }
  let Cbv : J.ProperChord :=
    { P := M.position b
      Q := M.position v
      ne := M.position_injective.ne (Ne.symm hvb)
      P_mem := frontier_eq ▸ hbFrontier
      Q_mem := frontier_eq ▸ hvFrontier
      interior_subset := by
        rw [← convexHull_pair, ← hbvImage]
        exact hbvInterior }
  exact ⟨a, b, v, Cav, Cbv, htriangle, hboundary, rfl, rfl, rfl, rfl⟩

/-- A bad weakly free triangle supplies two proper polygonal crosscuts. -/
theorem TriangleMesh.exists_properChords_of_badFreeTriangle
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T U : M.Triangle) (hfree : M.IsFreeTriangle T.1)
    (hne : T.1 ≠ U.1) (hneighbors : M.AreEdgeNeighbors T.1 U.1)
    (hnot : ¬M.HasNoIsolatedFrontierVertex T.1) :
    ∃ a b v : M.Vertex,
      T.1 = {a, b, v} ∧ M.boundaryEdges T.1 = {{a, b}} ∧
      Nonempty (J.ProperChord) ∧ Nonempty (J.ProperChord) := by
  obtain ⟨a, b, v, Cav, Cbv, htriangle, hboundary, -, -, -, -⟩ :=
    M.exists_realizedProperChords_of_badFreeTriangle J hsupport T U hfree hne hneighbors hnot
  exact ⟨a, b, v, htriangle, hboundary, ⟨Cav⟩, ⟨Cbv⟩⟩

/-- The hard free-triangle branch produces a theta crosscut realized by an actual mesh edge. -/
theorem TriangleMesh.exists_meshCrosscut_of_badFreeTriangle
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T U : M.Triangle) (hfree : M.IsFreeTriangle T.1)
    (hne : T.1 ≠ U.1) (hneighbors : M.AreEdgeNeighbors T.1 U.1)
    (hnot : ¬M.HasNoIsolatedFrontierVertex T.1) :
    ∃ G : PolygonalTheta, Nonempty (G.MeshCrosscut M) := by
  obtain ⟨a, b, v, Cav, Cbv, htriangle, hboundary, hCavP, hCavQ, -, -⟩ :=
    M.exists_realizedProperChords_of_badFreeTriangle J hsupport T U hfree hne hneighbors hnot
  obtain ⟨G, hGcarrier, hGP, hGQ, hGB3⟩ := Cav.exists_polygonalTheta
  have hav : a ≠ v := by
    intro hav
    apply Cav.ne
    rw [hCavP, hCavQ, hav]
  have hedgeCard : ({a, v} : Finset M.Vertex).card = 2 := by
    simp [hav]
  have hedgeSubset : ({a, v} : Finset M.Vertex) ⊆ T.1 := by
    rw [htriangle]
    simp
  have hedgeMem : ({a, v} : Finset M.Vertex) ∈ M.edges := by
    apply Finset.mem_biUnion.mpr
    exact ⟨T.1, T.2, Finset.mem_powersetCard.mpr ⟨hedgeSubset, hedgeCard⟩⟩
  have hclosed : G.J12.closedRegion = J.closedRegion := by
    rw [G.J12.closedRegion_eq_union, J.closedRegion_eq_union]
    have hinter := (PolygonalCircle.regions_eq_of_carrier_eq hGcarrier).1
    rw [hinter, hGcarrier]
  have hchord : convexHull ℝ
      (M.position '' (({a, v} : Finset M.Vertex) : Set M.Vertex)) = G.B3 := by
    rw [show M.position '' (({a, v} : Finset M.Vertex) : Set M.Vertex) =
      {M.position a, M.position v} by ext p; simp [eq_comm]]
    rw [convexHull_pair, hGB3, hCavP, hCavQ]
  refine ⟨G, ⟨{
    support_eq := hsupport.trans hclosed.symm
    chordEdge := {a, v}
    chordEdge_mem := hedgeMem
    chordVertices := by
      rw [show M.position '' (({a, v} : Finset M.Vertex) : Set M.Vertex) =
        {M.position a, M.position v} by ext p; simp [eq_comm]]
      rw [hGP, hGQ, hCavP, hCavQ]
    chordCarrier := hchord }⟩⟩

/-- In the two-frontier-edge Figure 3.3 case, the opposite edge is a proper chord of the
polygonal disk. -/
noncomputable def TriangleMesh.twoEdgeFreeBaseChord
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k) :
    J.ProperChord where
  P := M.freeTriangleOrder T k 0
  Q := M.freeTriangleOrder T k 1
  ne := (M.freeTriangleOrder_affineIndependent T k).injective.ne (by decide)
  P_mem := by
    rw [← J.frontier_closedRegion, ← hsupport]
    have hp : M.freeTriangleOrder T k 0 ∈
        frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 := by
      rw [hfree]
      exact Or.inl (left_mem_segment ℝ _ _)
    exact hp.1
  Q_mem := by
    rw [← J.frontier_closedRegion, ← hsupport]
    have hq : M.freeTriangleOrder T k 1 ∈
        frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 := by
      rw [hfree]
      exact Or.inr (left_mem_segment ℝ _ _)
    exact hq.1
  interior_subset := by
    intro p hp
    have hpTriangle : p ∈ M.triangleCarrier T.1 := by
      have hpBase : p ∈ convexHull ℝ
          (M.position '' (M.freeTriangleBaseEdge T k : Set M.Vertex)) := by
        rw [M.freeTriangleBaseEdge_carrier T k]
        exact hp.1
      exact convexHull_mono (Set.image_mono (M.freeTriangleBaseEdge_subset T k)) hpBase
    have hpNotApex : p ∉
        segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
          segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2) :=
      fun hpApex => Set.disjoint_left.mp
        (M.freeTriangleBase_diff_endpoints_disjoint_apexEdges T k) hp hpApex
    have hpNotCarrier : p ∉ J.carrier := by
      intro hpCarrier
      have hpFrontier : p ∈ frontier M.toPlaneComplex.support := by
        rw [hsupport, J.frontier_closedRegion]
        exact hpCarrier
      exact hpNotApex (hfree ▸ ⟨hpFrontier, hpTriangle⟩)
    have hpClosed : p ∈ J.closedRegion := by
      rw [← hsupport, M.toPlaneComplex_support]
      exact Set.mem_iUnion_of_mem T.1
        (Set.mem_iUnion_of_mem T.2 hpTriangle)
    rw [J.closedRegion_eq_union] at hpClosed
    exact hpClosed.resolve_right hpNotCarrier

/-- The proper chord in a two-edge ear is realized by the corresponding mesh edge. -/
theorem TriangleMesh.exists_meshCrosscut_of_twoEdgeFreeTriangle
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k) :
    ∃ G : PolygonalTheta, ∃ C : G.MeshCrosscut M,
      C.chordEdge = M.freeTriangleBaseEdge T k := by
  let C := M.twoEdgeFreeBaseChord J hsupport T k hfree
  obtain ⟨G, hGcarrier, hGP, hGQ, hGB3⟩ := C.exists_polygonalTheta
  have hclosed : G.J12.closedRegion = J.closedRegion := by
    rw [G.J12.closedRegion_eq_union, J.closedRegion_eq_union]
    have hinter := (PolygonalCircle.regions_eq_of_carrier_eq hGcarrier).1
    rw [hinter, hGcarrier]
  refine ⟨G, {
    support_eq := hsupport.trans hclosed.symm
    chordEdge := M.freeTriangleBaseEdge T k
    chordEdge_mem := M.freeTriangleBaseEdge_mem_edges T k
    chordVertices := by
      rw [M.image_freeTriangleBaseEdge T k, hGP, hGQ]
      rfl
    chordCarrier := by
      rw [M.freeTriangleBaseEdge_carrier T k, hGB3]
      rfl }, rfl⟩

/-- In the one-edge Figure 3.3 case, the base is exactly an incidence-one mesh edge. -/
theorem TriangleMesh.isBoundaryEdge_freeTriangleBaseEdge_of_oneEdgeFree
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    M.IsBoundaryEdge (M.freeTriangleBaseEdge T k) := by
  let e := M.freeTriangleBaseEdge T k
  obtain ⟨p, hpEdge, hpv⟩ := M.exists_nonvertex_mem_edgeCarrier
    (M.freeTriangleBaseEdge_card T k)
  have hpBase : p ∈ segment ℝ (M.freeTriangleOrder T k 0)
      (M.freeTriangleOrder T k 1) := by
    rwa [← M.freeTriangleBaseEdge_carrier T k]
  have hpTrace : p ∈ frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 := by
    rw [hfree]
    exact hpBase
  obtain ⟨d, hdBoundary, hpd⟩ :=
    (M.mem_frontier_iff_exists_boundaryEdge_of_nonvertex hpv).mp hpTrace.1
  have hed : e = d := M.edge_eq_of_nonvertex_mem_edgeCarriers
    (M.freeTriangleBaseEdge_mem_edges T k) hdBoundary.1 hpEdge hpd hpv
  change M.IsBoundaryEdge e
  rw [hed]
  exact hdBoundary

private theorem TriangleMesh.not_isBoundaryEdge_freeTriangleApexEdge0_of_oneEdgeFree
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    ¬M.IsBoundaryEdge (M.freeTriangleApexEdge0 T k) := by
  intro hedgeBoundary
  obtain ⟨p, hpEdge, hpv⟩ := M.exists_nonvertex_mem_edgeCarrier
    (M.freeTriangleApexEdge0_card T k)
  have hpApex : p ∈ segment ℝ (M.freeTriangleOrder T k 0)
      (M.freeTriangleOrder T k 2) := by
    rwa [← M.freeTriangleApexEdge0_carrier T k]
  have hpFrontier := M.mem_frontier_of_mem_boundaryEdge hedgeBoundary hpEdge hpv
  have hpTriangle : p ∈ M.triangleCarrier T.1 :=
    convexHull_mono (Set.image_mono (M.freeTriangleApexEdge0_subset T k)) hpEdge
  have hpBase : p ∈ segment ℝ (M.freeTriangleOrder T k 0)
      (M.freeTriangleOrder T k 1) := hfree ▸ ⟨hpFrontier, hpTriangle⟩
  have hpEnds : p ∉ ({M.freeTriangleOrder T k 0,
      M.freeTriangleOrder T k 1} : Set Plane) := by
    rintro (hp0 | hp1)
    · exact hpv (M.orderedVertex T ((Equiv.swap 2 k) 0)) hp0
    · exact hpv (M.orderedVertex T ((Equiv.swap 2 k) 1)) hp1
  exact Set.disjoint_left.mp
    (M.freeTriangleBase_diff_endpoints_disjoint_apexEdges T k)
    ⟨hpBase, hpEnds⟩ (Or.inl hpApex)

private theorem TriangleMesh.not_isBoundaryEdge_freeTriangleApexEdge1_of_oneEdgeFree
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    ¬M.IsBoundaryEdge (M.freeTriangleApexEdge1 T k) := by
  intro hedgeBoundary
  obtain ⟨p, hpEdge, hpv⟩ := M.exists_nonvertex_mem_edgeCarrier
    (M.freeTriangleApexEdge1_card T k)
  have hpApex : p ∈ segment ℝ (M.freeTriangleOrder T k 1)
      (M.freeTriangleOrder T k 2) := by
    rwa [← M.freeTriangleApexEdge1_carrier T k]
  have hpFrontier := M.mem_frontier_of_mem_boundaryEdge hedgeBoundary hpEdge hpv
  have hpTriangle : p ∈ M.triangleCarrier T.1 :=
    convexHull_mono (Set.image_mono (M.freeTriangleApexEdge1_subset T k)) hpEdge
  have hpBase : p ∈ segment ℝ (M.freeTriangleOrder T k 0)
      (M.freeTriangleOrder T k 1) := hfree ▸ ⟨hpFrontier, hpTriangle⟩
  have hpEnds : p ∉ ({M.freeTriangleOrder T k 0,
      M.freeTriangleOrder T k 1} : Set Plane) := by
    rintro (hp0 | hp1)
    · exact hpv (M.orderedVertex T ((Equiv.swap 2 k) 0)) hp0
    · exact hpv (M.orderedVertex T ((Equiv.swap 2 k) 1)) hp1
  exact Set.disjoint_left.mp
    (M.freeTriangleBase_diff_endpoints_disjoint_apexEdges T k)
    ⟨hpBase, hpEnds⟩ (Or.inr hpApex)

/-- A non-boundary edge of `T` is carried by the support remaining after `T` is deleted. -/
theorem TriangleMesh.edgeCarrier_subset_eraseTriangle_support_of_not_boundary
    (M : TriangleMesh) (T : M.Triangle) {e : Finset M.Vertex}
    (hecard : e.card = 2) (heT : e ⊆ T.1) (heNotBoundary : ¬M.IsBoundaryEdge e) :
    convexHull ℝ (M.position '' (e : Set M.Vertex)) ⊆
      (M.eraseTriangle T.1).toPlaneComplex.support := by
  have hcard := M.card_incidentTriangles_eq_two_of_not_boundary
    T.2 hecard heT heNotBoundary
  have hTmem : T.1 ∈ M.incidentTriangles e :=
    M.mem_incidentTriangles_iff.mpr ⟨T.2, heT⟩
  have hother : ∃ u ∈ M.incidentTriangles e, u ≠ T.1 := by
    by_contra h
    push Not at h
    have hsingle : M.incidentTriangles e = {T.1} := by
      ext u
      constructor
      · exact fun hu => Finset.mem_singleton.mpr (h u hu)
      · intro hu
        rw [Finset.mem_singleton.mp hu]
        exact hTmem
    rw [hsingle] at hcard
    simp at hcard
  obtain ⟨u, hu, huT⟩ := hother
  have huData := M.mem_incidentTriangles_iff.mp hu
  rw [TriangleMesh.toPlaneComplex_support]
  exact Set.subset_iUnion_of_subset u <| Set.subset_iUnion_of_subset
    (Finset.mem_erase.mpr ⟨huT, huData.1⟩)
      (convexHull_mono (Set.image_mono huData.2))

/-- In the one-edge case, the surviving support attaches to the deleted triangle exactly along
the two apex edges. -/
theorem TriangleMesh.eraseTriangle_support_inter_triangleCarrier_of_oneEdgeFree
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
        segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2) := by
  let e0 := M.freeTriangleApexEdge0 T k
  let e1 := M.freeTriangleApexEdge1 T k
  have hbaseBoundary := M.isBoundaryEdge_freeTriangleBaseEdge_of_oneEdgeFree T k hfree
  have he0Not := M.not_isBoundaryEdge_freeTriangleApexEdge0_of_oneEdgeFree T k hfree
  have he1Not := M.not_isBoundaryEdge_freeTriangleApexEdge1_of_oneEdgeFree T k hfree
  apply Set.Subset.antisymm
  · rintro p ⟨hpErase, hpT⟩
    rw [TriangleMesh.toPlaneComplex_support] at hpErase
    simp only [TriangleMesh.eraseTriangle_triangles, Set.mem_iUnion] at hpErase
    obtain ⟨u, hu, hpU⟩ := hpErase
    have huData := Finset.mem_erase.mp hu
    let U : M.Triangle := ⟨u, huData.2⟩
    let e : Finset M.Vertex := T.1 ∩ U.1
    have hpInter : p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
      rw [show e = T.1 ∩ U.1 by rfl, ← M.triangle_inter T.1 T.2 U.1 U.2]
      exact ⟨hpT, hpU⟩
    have heCardLe : e.card ≤ 2 := by
      have hesub : e ⊆ T.1 := by
        intro v hv
        exact Finset.inter_subset_left hv
      have hle : e.card ≤ T.1.card := Finset.card_le_card hesub
      rw [M.card_triangle T.1 T.2] at hle
      by_contra h
      have heCard : e.card = 3 := by omega
      have heT : e = T.1 := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_left (by rw [heCard, M.card_triangle T.1 T.2])
      have hsub : T.1 ⊆ U.1 := by
        rw [← heT]
        exact Finset.inter_subset_right
      have hTU : T.1 = U.1 := Finset.eq_of_subset_of_card_le hsub (by
        rw [M.card_triangle T.1 T.2, M.card_triangle U.1 U.2])
      exact huData.1 hTU.symm
    have heNonempty : e.Nonempty := by
      by_contra h
      have heEmpty := Finset.not_nonempty_iff_eq_empty.mp h
      rw [heEmpty] at hpInter
      simp at hpInter
    have heCardCases : e.card = 1 ∨ e.card = 2 := by
      have hpos := Finset.card_pos.mpr heNonempty
      omega
    rcases heCardCases with heCard | heCard
    · obtain ⟨v, heq⟩ := Finset.card_eq_one.mp heCard
      have hpv : p = M.position v := by
        rw [heq] at hpInter
        simpa using hpInter
      have hvT : v ∈ T.1 := by
        have hvE : v ∈ e := by rw [heq]; simp
        exact Finset.inter_subset_left hvE
      rw [hpv]
      exact M.triangleVertex_mem_freeTriangleApexEdges T k hvT
    · have heTriangle : e ∈ M.triangleEdges T.1 :=
        Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left, heCard⟩
      have heNotBoundary : ¬M.IsBoundaryEdge e := by
        intro heBoundary
        have hTinc : T.1 ∈ M.incidentTriangles e :=
          M.mem_incidentTriangles_iff.mpr ⟨T.2, Finset.inter_subset_left⟩
        have hUinc : U.1 ∈ M.incidentTriangles e :=
          M.mem_incidentTriangles_iff.mpr ⟨U.2, Finset.inter_subset_right⟩
        have htwo : 1 < (M.incidentTriangles e).card :=
          Finset.one_lt_card.mpr ⟨T.1, hTinc, U.1, hUinc, huData.1.symm⟩
        rw [heBoundary.2] at htwo
        omega
      rw [M.triangleEdges_eq_freeTriangleEdges T k] at heTriangle
      simp only [Finset.mem_insert, Finset.mem_singleton] at heTriangle
      rcases heTriangle with heBase | he0 | he1
      · exact False.elim <| heNotBoundary (heBase ▸ hbaseBoundary)
      · left
        rw [← M.freeTriangleApexEdge0_carrier T k, ← he0]
        exact hpInter
      · right
        rw [← M.freeTriangleApexEdge1_carrier T k, ← he1]
        exact hpInter
  · rintro p (hp0 | hp1)
    · have hpEdge : p ∈ convexHull ℝ
          (M.position '' (M.freeTriangleApexEdge0 T k : Set M.Vertex)) := by
        rwa [M.freeTriangleApexEdge0_carrier T k]
      exact ⟨M.edgeCarrier_subset_eraseTriangle_support_of_not_boundary T
          (M.freeTriangleApexEdge0_card T k)
          (M.freeTriangleApexEdge0_subset T k) he0Not hpEdge,
        convexHull_mono (Set.image_mono (M.freeTriangleApexEdge0_subset T k)) hpEdge⟩
    · have hpEdge : p ∈ convexHull ℝ
          (M.position '' (M.freeTriangleApexEdge1 T k : Set M.Vertex)) := by
        rwa [M.freeTriangleApexEdge1_carrier T k]
      exact ⟨M.edgeCarrier_subset_eraseTriangle_support_of_not_boundary T
          (M.freeTriangleApexEdge1_card T k)
          (M.freeTriangleApexEdge1_subset T k) he1Not hpEdge,
        convexHull_mono (Set.image_mono (M.freeTriangleApexEdge1_subset T k)) hpEdge⟩

/-- Exact frontier update in the one-edge Figure 3.3 case. -/
theorem TriangleMesh.frontier_eraseTriangle_support_of_oneEdgeFree
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      (frontier M.toPlaneComplex.support \ M.triangleCarrier T.1) ∪
        (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
          segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)) := by
  rw [M.frontier_eraseTriangle_support T,
    M.eraseTriangle_support_inter_triangleCarrier_of_oneEdgeFree T k hfree]

/-- The old frontier splits into the unchanged part outside the ear and its one-edge trace. -/
theorem TriangleMesh.frontier_eq_outside_triangle_union_base_of_oneEdgeFree
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    frontier M.toPlaneComplex.support =
      (frontier M.toPlaneComplex.support \ M.triangleCarrier T.1) ∪
        segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
  apply Set.Subset.antisymm
  · intro p hp
    by_cases hpT : p ∈ M.triangleCarrier T.1
    · exact Or.inr (hfree ▸ ⟨hp, hpT⟩)
    · exact Or.inl ⟨hp, hpT⟩
  · rintro p (hp | hp)
    · exact hp.1
    · exact (hfree.symm ▸ hp).1

/-- In the two-edge case the old frontier is its unchanged outside part together with the two
apex edges. -/
theorem TriangleMesh.frontier_eq_outside_triangle_union_apex_of_twoEdgeFree
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsTwoEdgeFreeTriangle T k) :
    frontier M.toPlaneComplex.support =
      (frontier M.toPlaneComplex.support \ M.triangleCarrier T.1) ∪
        (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
          segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)) := by
  apply Set.Subset.antisymm
  · intro p hp
    by_cases hpT : p ∈ M.triangleCarrier T.1
    · exact Or.inr (hfree ▸ ⟨hp, hpT⟩)
    · exact Or.inl ⟨hp, hpT⟩
  · rintro p (hp | hp)
    · exact hp.1
    · exact (hfree.symm ▸ hp).1

/-- A Figure 3.3 push which fixes the old frontier away from the ear realizes the exact
one-edge deletion frontier. -/
theorem TriangleMesh.image_frontier_eq_eraseTriangle_frontier_of_oneEdgeFree
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) (g : Plane ≃ₜ Plane)
    (hfix : Set.EqOn g id
      (frontier M.toPlaneComplex.support \ M.triangleCarrier T.1))
    (hmove : g '' segment ℝ (M.freeTriangleOrder T k 0)
        (M.freeTriangleOrder T k 1) =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
        segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)) :
    g '' frontier M.toPlaneComplex.support =
      frontier (M.eraseTriangle T.1).toPlaneComplex.support := by
  rw [M.frontier_eq_outside_triangle_union_base_of_oneEdgeFree T k hfree,
    Set.image_union, hmove,
    M.frontier_eraseTriangle_support_of_oneEdgeFree T k hfree]
  congr 1
  apply Set.Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    rw [hfix hq]
    exact hq
  · intro p hp
    exact ⟨p, hp, hfix hp⟩

/-- The supported thin-kite construction realizes the exact one-edge frontier update while
remaining the identity off any prescribed neighborhood of the ear. -/
theorem TriangleMesh.exists_supported_frontier_move_of_oneEdgeFree
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k)
    (U : Set Plane) (hU : IsOpen U) (hTU : M.triangleCarrier T.1 ⊆ U) :
    ∃ g : Plane ≃ₜ Plane, Set.EqOn g id Uᶜ ∧
      g '' frontier M.toPlaneComplex.support =
        frontier (M.eraseTriangle T.1).toPlaneComplex.support := by
  obtain ⟨δ, hδ, hfixU, hfixBoundary, hmove⟩ :=
    M.exists_supported_triangle_push_fixing_boundaryCarrier T k hfree U hU hTU
  let g := transportedThinKiteHomeomorph (M.freeTriangleAffineEquiv T k) δ hδ
  refine ⟨g, hfixU, M.image_frontier_eq_eraseTriangle_frontier_of_oneEdgeFree
    T k hfree g ?_ hmove⟩
  intro p hp
  apply hfixBoundary
  rw [M.boundaryCarrier_eq_frontier_of_polygonalDisk J hsupport]
  exact hp

namespace PolygonalTheta.MeshCrosscut

variable {G : PolygonalTheta} {M : TriangleMesh} (C : G.MeshCrosscut M)

/-- If a two-edge Figure 3.3 triangle lies on the first side of its base crosscut, that whole
side is exactly the closed triangle. -/
theorem side13Mesh_support_eq_triangleCarrier_of_twoEdgeFree
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k)
    (hbase : G.B3 = segment ℝ (M.freeTriangleOrder T k 0)
      (M.freeTriangleOrder T k 1))
    (hT13 : T.1 ∈ C.side13Mesh.triangles) :
    C.side13Mesh.toPlaneComplex.support = M.triangleCarrier T.1 := by
  have htriangleSubset : M.triangleCarrier T.1 ⊆
      C.side13Mesh.toPlaneComplex.support := by
    rw [TriangleMesh.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset T.1
      (Set.subset_iUnion_of_subset hT13 subset_rfl)
  have hsideInterior : G.J13.interiorRegion ⊆
      interior (M.triangleCarrier T.1) := by
    have hcover : G.J13.interiorRegion ⊆
        interior (M.triangleCarrier T.1) ∪ (M.triangleCarrier T.1)ᶜ := by
      intro p hp13
      by_cases hpT : p ∈ M.triangleCarrier T.1
      · left
        apply (mem_interior_iff_notMem_frontier hpT).mpr
        intro hpFrontier
        rcases M.frontier_triangleCarrier_subset_freeTriangleEdges T k hpFrontier with
          hpBase | hpApex
        · have hpB3 : p ∈ G.B3 := by rwa [hbase]
          have hpCarrier13 : p ∈ G.J13.carrier := by
            rw [G.carrier13]
            exact Or.inr hpB3
          have hpCompl13 : p ∈ G.J13.carrierᶜ := by
            rw [← G.J13.interior_union_exterior]
            exact Or.inl hp13
          exact hpCompl13 hpCarrier13
        · have hpOld : p ∈ frontier M.toPlaneComplex.support :=
            (hfree.symm ▸ hpApex).1
          have hpCarrier12 : p ∈ G.J12.carrier := by
            rwa [C.support_eq, G.J12.frontier_closedRegion] at hpOld
          have hpInterior12 := G.interior13_subset_interior12 hp13
          have hpCompl12 : p ∈ G.J12.carrierᶜ := by
            rw [← G.J12.interior_union_exterior]
            exact Or.inl hpInterior12
          exact hpCompl12 hpCarrier12
      · exact Or.inr hpT
    have hclosed : IsClosed (M.triangleCarrier T.1) :=
      (T.1.finite_toSet.image M.position).isClosed_convexHull ℝ
    have hdisjoint : Disjoint (interior (M.triangleCarrier T.1))
        (M.triangleCarrier T.1)ᶜ := by
      exact Set.disjoint_left.mpr fun _ hp hpc => hpc (interior_subset hp)
    obtain ⟨p, hpT⟩ := M.interior_triangleCarrier_nonempty T
    have hp13 := (C.mem_side13Mesh_triangles_iff.mp hT13).2 hpT
    exact G.J13.isConnected_interiorRegion.isPreconnected.subset_left_of_subset_union
      isOpen_interior hclosed.isOpen_compl hdisjoint hcover ⟨p, hp13, hpT⟩
  apply Set.Subset.antisymm
  · rw [C.side13Mesh_support, PolygonalCircle.closedRegion,
      ← M.closure_interior_triangleCarrier T]
    exact closure_mono hsideInterior
  · exact htriangleSubset

/-- Symmetric form: if the ear lies on the second side, that side is the closed triangle. -/
theorem side23Mesh_support_eq_triangleCarrier_of_twoEdgeFree
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k)
    (hbase : G.B3 = segment ℝ (M.freeTriangleOrder T k 0)
      (M.freeTriangleOrder T k 1))
    (hT23 : T.1 ∈ C.side23Mesh.triangles) :
    C.side23Mesh.toPlaneComplex.support = M.triangleCarrier T.1 := by
  exact C.swap12.side13Mesh_support_eq_triangleCarrier_of_twoEdgeFree
    (G := G.swap12) T k hfree hbase hT23

/-- In the preceding situation, the first side contains no maximal triangle besides the ear. -/
theorem side13Mesh_triangles_eq_singleton_of_twoEdgeFree
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k)
    (hbase : G.B3 = segment ℝ (M.freeTriangleOrder T k 0)
      (M.freeTriangleOrder T k 1))
    (hT13 : T.1 ∈ C.side13Mesh.triangles) :
    C.side13Mesh.triangles = {T.1} := by
  classical
  change (C.side13Mesh.triangles : Finset (Finset M.Vertex)) =
    ({T.1} : Finset (Finset M.Vertex))
  have hsupport := C.side13Mesh_support_eq_triangleCarrier_of_twoEdgeFree
    T k hfree hbase hT13
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hT13, ?_⟩
  intro u hu
  have huM := (C.mem_side13Mesh_triangles_iff.mp hu).1
  let U : M.Triangle := ⟨u, huM⟩
  obtain ⟨p, hpU⟩ := M.interior_triangleCarrier_nonempty U
  have hpSide : p ∈ C.side13Mesh.toPlaneComplex.support := by
    rw [TriangleMesh.toPlaneComplex_support]
    exact Set.mem_iUnion_of_mem u
      (Set.mem_iUnion_of_mem hu (interior_subset hpU))
  have hpTCarrier : p ∈ M.triangleCarrier T.1 := by rwa [hsupport] at hpSide
  have hpTInterior : p ∈ interior (M.triangleCarrier T.1) :=
    interior_mono (by
      intro q hq
      have hqSide : q ∈ C.side13Mesh.toPlaneComplex.support := by
        rw [TriangleMesh.toPlaneComplex_support]
        exact Set.mem_iUnion_of_mem u (Set.mem_iUnion_of_mem hu hq)
      rwa [hsupport] at hqSide) hpU
  exact M.eq_of_interior_triangleCarrier_inter_nonempty T U
    ⟨p, hpTInterior, hpU⟩ |>.symm

/-- Once the first crosscut side is the ear, the second side is exactly the mesh obtained by
deleting that ear. -/
theorem side23Mesh_support_eq_eraseTriangle_of_twoEdgeFree
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k)
    (hbase : G.B3 = segment ℝ (M.freeTriangleOrder T k 0)
      (M.freeTriangleOrder T k 1))
    (hT13 : T.1 ∈ C.side13Mesh.triangles) :
    C.side23Mesh.toPlaneComplex.support =
      (M.eraseTriangle T.1).toPlaneComplex.support := by
  have hsingle := C.side13Mesh_triangles_eq_singleton_of_twoEdgeFree
    T k hfree hbase hT13
  have htriangles : C.side23Mesh.triangles = M.triangles.erase T.1 := by
    ext u
    constructor
    · intro hu23
      have huM := (C.mem_side23Mesh_triangles_iff.mp hu23).1
      apply Finset.mem_erase.mpr
      refine ⟨?_, huM⟩
      intro huT
      have hT23 : T.1 ∈ C.side23Mesh.triangles := huT ▸ hu23
      exact Finset.disjoint_left.mp C.disjoint_side_triangles hT13 hT23
    · intro hu
      have huData := Finset.mem_erase.mp hu
      have huUnion : u ∈ C.side13Mesh.triangles ∪ C.side23Mesh.triangles := by
        rw [C.side_triangles_union]
        exact huData.2
      rcases Finset.mem_union.mp huUnion with hu13 | hu23
      · have huT : u = T.1 := by
          rw [hsingle] at hu13
          exact Finset.mem_singleton.mp hu13
        exact False.elim (huData.1 huT)
      · exact hu23
  rw [TriangleMesh.toPlaneComplex_support, TriangleMesh.toPlaneComplex_support,
    TriangleMesh.eraseTriangle_triangles, htriangles]
  rfl

/-- Symmetric form: if the ear lies on the second side, the first side is the erased mesh. -/
theorem side13Mesh_support_eq_eraseTriangle_of_twoEdgeFree
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k)
    (hbase : G.B3 = segment ℝ (M.freeTriangleOrder T k 0)
      (M.freeTriangleOrder T k 1))
    (hT23 : T.1 ∈ C.side23Mesh.triangles) :
    C.side13Mesh.toPlaneComplex.support =
      (M.eraseTriangle T.1).toPlaneComplex.support := by
  have h := C.swap12.side23Mesh_support_eq_eraseTriangle_of_twoEdgeFree
    (G := G.swap12) T k hfree hbase hT23
  exact h

/-- Away from the triangle incident to the new chord, cutting a polygonal disk does not change
the frontier trace on a mesh triangle.  This is the transport lemma used in Moise's strengthened
free-triangle induction. -/
theorem frontier_inter_triangleCarrier_side13 {t : Finset M.Vertex}
    (ht : t ∈ C.side13Mesh.triangles) (hchord : ¬C.chordEdge ⊆ t) :
    frontier M.toPlaneComplex.support ∩ M.triangleCarrier t =
      frontier C.side13Mesh.toPlaneComplex.support ∩
        C.side13Mesh.triangleCarrier t := by
  have htM := (C.mem_side13Mesh_triangles_iff.mp ht).1
  have htriangleSubset : M.triangleCarrier t ⊆ G.J13.closedRegion := by
    rw [← C.side13Mesh_support]
    rw [TriangleMesh.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset t
      (Set.subset_iUnion_of_subset ht (by rfl))
  have hedgeCard : C.chordEdge.card = 2 :=
    M.card_of_mem_edges C.chordEdge_mem
  have htFace : t ∈ M.toPlaneComplex.simplexes :=
    M.mem_faces_iff.mpr ⟨Finset.card_pos.mp (by rw [M.card_triangle t htM]; omega),
      t, htM, subset_rfl⟩
  have hedgeFace : C.chordEdge ∈ M.toPlaneComplex.simplexes := by
    obtain ⟨u, hu, heu⟩ := Finset.mem_biUnion.mp C.chordEdge_mem
    have heuData := Finset.mem_powersetCard.mp heu
    exact M.mem_faces_iff.mpr
      ⟨Finset.card_pos.mp (by rw [hedgeCard]; omega), u, hu, heuData.1⟩
  have hface := M.toPlaneComplex.face_inter t htFace C.chordEdge hedgeFace
  change M.triangleCarrier t ∩
      convexHull ℝ (M.position '' (C.chordEdge : Set M.Vertex)) =
        convexHull ℝ (M.position '' ((t ∩ C.chordEdge : Finset M.Vertex) : Set M.Vertex))
    at hface
  have hinterCard : (t ∩ C.chordEdge).card ≤ 1 := by
    have hle := Finset.card_le_card
      (Finset.inter_subset_right : t ∩ C.chordEdge ⊆ C.chordEdge)
    rw [hedgeCard] at hle
    by_contra hnot
    have hcard : (t ∩ C.chordEdge).card = 2 := by omega
    have heq : t ∩ C.chordEdge = C.chordEdge :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hcard, hedgeCard])
    apply hchord
    intro v hv
    have : v ∈ t ∩ C.chordEdge := by rw [heq]; exact hv
    exact (Finset.mem_inter.mp this).1
  have hchordMeet : M.triangleCarrier t ∩ G.B3 ⊆ {G.P, G.Q} := by
    intro x hx
    have hxCommon : x ∈ convexHull ℝ
        (M.position '' ((t ∩ C.chordEdge : Finset M.Vertex) : Set M.Vertex)) := by
      rw [← hface, C.chordCarrier]
      exact hx
    obtain hempty | hne := (t ∩ C.chordEdge).eq_empty_or_nonempty
    · rw [hempty] at hxCommon
      simp at hxCommon
    · obtain ⟨v, hv⟩ := hne
      have hsingleton : t ∩ C.chordEdge = {v} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hv, fun w hw => ?_⟩
        by_contra hwv
        have hpairs : ({v, w} : Finset M.Vertex) ⊆ t ∩ C.chordEdge := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        have hvw : v ≠ w := Ne.symm hwv
        have htwo : ({v, w} : Finset M.Vertex).card = 2 := by simp [hvw]
        have := Finset.card_le_card hpairs
        rw [htwo] at this
        omega
      rw [hsingleton] at hxCommon
      have hxv : x = M.position v := by simpa using hxCommon
      rw [hxv]
      have hvEdge : v ∈ C.chordEdge := (Finset.mem_inter.mp hv).2
      rw [← C.chordVertices]
      exact ⟨v, hvEdge, rfl⟩
  rw [C.support_eq, C.side13Mesh_support,
    G.J12.frontier_closedRegion, G.J13.frontier_closedRegion]
  rw [G.carrier12, G.carrier13]
  ext x
  constructor
  · rintro ⟨hxBoundary, hxTriangle⟩
    refine ⟨?_, hxTriangle⟩
    rcases hxBoundary with hxB1 | hxB2
    · exact Or.inl hxB1
    · by_cases hxEndpoint : x ∈ ({G.P, G.Q} : Set Plane)
      · left
        rcases hxEndpoint with (rfl | rfl)
        · exact G.P_mem_B1
        · exact G.Q_mem_B1
      · have hxExterior := G.B2_diff_endpoints_subset_exterior13 ⟨hxB2, hxEndpoint⟩
        have hxClosed := htriangleSubset hxTriangle
        rw [G.J13.closedRegion_eq_union] at hxClosed
        rcases hxClosed with hxInterior | hxCarrier
        · exact False.elim <|
            Set.disjoint_left.mp G.J13.disjoint_interior_exterior hxInterior hxExterior
        · have hxCompl : x ∈ G.J13.carrierᶜ := by
            rw [← G.J13.interior_union_exterior]
            exact Or.inr hxExterior
          exact False.elim (hxCompl hxCarrier)
  · rintro ⟨hxBoundary, hxTriangle⟩
    refine ⟨?_, hxTriangle⟩
    rcases hxBoundary with hxB1 | hxB3
    · exact Or.inl hxB1
    · have hxEndpoint := hchordMeet ⟨hxTriangle, hxB3⟩
      left
      rcases hxEndpoint with (rfl | rfl)
      · exact G.P_mem_B1
      · exact G.Q_mem_B1

/-- The symmetric frontier-trace transport theorem for the other cut subdisk. -/
theorem frontier_inter_triangleCarrier_side23 {t : Finset M.Vertex}
    (ht : t ∈ C.side23Mesh.triangles) (hchord : ¬C.chordEdge ⊆ t) :
    frontier M.toPlaneComplex.support ∩ M.triangleCarrier t =
      frontier C.side23Mesh.toPlaneComplex.support ∩
        C.side23Mesh.triangleCarrier t := by
  have ht' : t ∈ C.swap12.side13Mesh.triangles := by
    change t ∈ C.side23Mesh.triangles
    exact ht
  have h := C.swap12.frontier_inter_triangleCarrier_side13
    (G := G.swap12) (M := M) (t := t) ht' hchord
  simpa using h

/-- A geometrically free triangle not incident to the cut edge remains geometrically free after
the first cut subdisk is glued back into the original polygonal disk. -/
theorem isGeometricallyFreeTriangle_of_side13
    (T : C.side13Mesh.Triangle)
    (hfree : C.side13Mesh.IsGeometricallyFreeTriangle T)
    (hchord : ¬C.chordEdge ⊆ T.1) :
    M.IsGeometricallyFreeTriangle
      ⟨T.1, (C.mem_side13Mesh_triangles_iff.mp T.2).1⟩ := by
  obtain ⟨k, hfree | hfree⟩ := hfree
  · refine ⟨k, Or.inl ?_⟩
    rw [TriangleMesh.IsOneEdgeFreeTriangle]
    rw [C.frontier_inter_triangleCarrier_side13 T.2 hchord]
    exact hfree
  · refine ⟨k, Or.inr ?_⟩
    rw [TriangleMesh.IsTwoEdgeFreeTriangle]
    rw [C.frontier_inter_triangleCarrier_side13 T.2 hchord]
    exact hfree

/-- The symmetric geometric-freeness transport theorem for the second cut subdisk. -/
theorem isGeometricallyFreeTriangle_of_side23
    (T : C.side23Mesh.Triangle)
    (hfree : C.side23Mesh.IsGeometricallyFreeTriangle T)
    (hchord : ¬C.chordEdge ⊆ T.1) :
    M.IsGeometricallyFreeTriangle
      ⟨T.1, (C.mem_side23Mesh_triangles_iff.mp T.2).1⟩ := by
  obtain ⟨k, hfree | hfree⟩ := hfree
  · refine ⟨k, Or.inl ?_⟩
    rw [TriangleMesh.IsOneEdgeFreeTriangle]
    rw [C.frontier_inter_triangleCarrier_side23 T.2 hchord]
    exact hfree
  · refine ⟨k, Or.inr ?_⟩
    rw [TriangleMesh.IsTwoEdgeFreeTriangle]
    rw [C.frontier_inter_triangleCarrier_side23 T.2 hchord]
    exact hfree

/-- Each cut subdisk has a maximal triangle incident to the new chord edge. -/
theorem exists_side13_triangle_chordEdge_subset :
    ∃ T : C.side13Mesh.Triangle, C.chordEdge ⊆ T.1 := by
  have hedgeCard := M.card_of_mem_edges C.chordEdge_mem
  obtain ⟨p, hpEdge, hpv⟩ := M.exists_nonvertex_mem_edgeCarrier hedgeCard
  have hpB3 : p ∈ G.B3 := by rwa [← C.chordCarrier]
  have hpSupport : p ∈ C.side13Mesh.toPlaneComplex.support := by
    rw [C.side13Mesh_support, G.J13.closedRegion_eq_union, G.carrier13]
    exact Or.inr (Or.inr hpB3)
  rw [TriangleMesh.toPlaneComplex_support] at hpSupport
  simp only [Set.mem_iUnion] at hpSupport
  obtain ⟨t, ht, hpt⟩ := hpSupport
  have htM := (C.mem_side13Mesh_triangles_iff.mp ht).1
  obtain ⟨s, hs, hes⟩ := Finset.mem_biUnion.mp C.chordEdge_mem
  have hesData := Finset.mem_powersetCard.mp hes
  have het : C.chordEdge ⊆ t :=
    M.edge_subset_of_nonvertex_mem_triangleCarrier hedgeCard hesData.1 hs htM
      hpEdge hpt hpv
  exact ⟨⟨t, ht⟩, het⟩

/-- The symmetric chord-incidence existence theorem. -/
theorem exists_side23_triangle_chordEdge_subset :
    ∃ T : C.side23Mesh.Triangle, C.chordEdge ⊆ T.1 := by
  have hedgeCard := M.card_of_mem_edges C.chordEdge_mem
  obtain ⟨p, hpEdge, hpv⟩ := M.exists_nonvertex_mem_edgeCarrier hedgeCard
  have hpB3 : p ∈ G.B3 := by rwa [← C.chordCarrier]
  have hpSupport : p ∈ C.side23Mesh.toPlaneComplex.support := by
    rw [C.side23Mesh_support, G.J23.closedRegion_eq_union, G.carrier23]
    exact Or.inr (Or.inr hpB3)
  rw [TriangleMesh.toPlaneComplex_support] at hpSupport
  simp only [Set.mem_iUnion] at hpSupport
  obtain ⟨t, ht, hpt⟩ := hpSupport
  have htM := (C.mem_side23Mesh_triangles_iff.mp ht).1
  obtain ⟨s, hs, hes⟩ := Finset.mem_biUnion.mp C.chordEdge_mem
  have hesData := Finset.mem_powersetCard.mp hes
  have het : C.chordEdge ⊆ t :=
    M.edge_subset_of_nonvertex_mem_triangleCarrier hedgeCard hesData.1 hs htM
      hpEdge hpt hpv
  exact ⟨⟨t, ht⟩, het⟩

/-- On either side of a crosscut there is at most one maximal triangle containing the chord. -/
theorem side13_triangle_eq_of_chordEdge_subset
    (T U : C.side13Mesh.Triangle)
    (hT : C.chordEdge ⊆ T.1) (hU : C.chordEdge ⊆ U.1) : T.1 = U.1 := by
  by_contra hTU
  obtain ⟨V, hV⟩ := C.exists_side23_triangle_chordEdge_subset
  have hTM := (C.mem_side13Mesh_triangles_iff.mp T.2).1
  have hUM := (C.mem_side13Mesh_triangles_iff.mp U.2).1
  have hVM := (C.mem_side23Mesh_triangles_iff.mp V.2).1
  have hTi : T.1 ∈ M.incidentTriangles C.chordEdge :=
    M.mem_incidentTriangles_iff.mpr ⟨hTM, hT⟩
  have hUi : U.1 ∈ M.incidentTriangles C.chordEdge :=
    M.mem_incidentTriangles_iff.mpr ⟨hUM, hU⟩
  have hVi : V.1 ∈ M.incidentTriangles C.chordEdge :=
    M.mem_incidentTriangles_iff.mpr ⟨hVM, hV⟩
  have hVT : V.1 ≠ T.1 := by
    intro h
    have hT13 : (T.1 : Finset M.Vertex) ∈ C.side13Mesh.triangles := T.2
    have hV13 : (V.1 : Finset M.Vertex) ∈ C.side13Mesh.triangles := h.symm ▸ hT13
    have hV23 : (V.1 : Finset M.Vertex) ∈ C.side23Mesh.triangles := V.2
    exact Finset.disjoint_left.mp C.disjoint_side_triangles hV13 hV23
  have hUV := M.incidentTriangle_eq_of_ne
    (M.card_of_mem_edges C.chordEdge_mem) hTi hUi hVi (Ne.symm hTU) hVT
  have hV23 : (V.1 : Finset M.Vertex) ∈ C.side23Mesh.triangles := V.2
  have hU23 : (U.1 : Finset M.Vertex) ∈ C.side23Mesh.triangles := hUV.symm ▸ hV23
  have hU13 : (U.1 : Finset M.Vertex) ∈ C.side13Mesh.triangles := U.2
  exact Finset.disjoint_left.mp C.disjoint_side_triangles hU13 hU23

/-- Symmetric uniqueness on the second cut subdisk. -/
theorem side23_triangle_eq_of_chordEdge_subset
    (T U : C.side23Mesh.Triangle)
    (hT : C.chordEdge ⊆ T.1) (hU : C.chordEdge ⊆ U.1) : T.1 = U.1 := by
  have hT' : T.1 ∈ C.swap12.side13Mesh.triangles := by
    change T.1 ∈ C.side23Mesh.triangles
    exact T.2
  have hU' : U.1 ∈ C.swap12.side13Mesh.triangles := by
    change U.1 ∈ C.side23Mesh.triangles
    exact U.2
  let T' : C.swap12.side13Mesh.Triangle := ⟨T.1, hT'⟩
  let U' : C.swap12.side13Mesh.Triangle := ⟨U.1, hU'⟩
  exact C.swap12.side13_triangle_eq_of_chordEdge_subset
    (G := G.swap12) (M := M) T' U' hT hU

/-- If one cut subdisk consists of a single triangle, the two edges other than the chord are
boundary edges of the original disk. -/
theorem exists_geometricallyFreeTriangle_of_side13_card_one
    (hcard : C.side13Mesh.triangles.card = 1) :
    ∃ T : C.side13Mesh.Triangle,
      M.IsGeometricallyFreeTriangle
        ⟨T.1, (C.mem_side13Mesh_triangles_iff.mp T.2).1⟩ := by
  obtain ⟨T, hchordT⟩ := C.exists_side13_triangle_chordEdge_subset
  have hedgeCard := M.card_of_mem_edges C.chordEdge_mem
  have hchordNotBoundary : ¬M.IsBoundaryEdge C.chordEdge := by
    intro hboundary
    obtain ⟨x, hxB3, hxEndpoint⟩ := G.chord_interior_nonempty
    have hxInterior12 : x ∈ G.J12.interiorRegion :=
      (G.chord_subset hxB3).resolve_left hxEndpoint
    have hxInteriorSupport : x ∈ interior M.toPlaneComplex.support := by
      rw [C.support_eq, G.J12.interior_closedRegion]
      exact hxInterior12
    have hxFrontierSupport : x ∈ frontier M.toPlaneComplex.support :=
      M.boundaryEdgeCarrier_subset_frontier hboundary (by rwa [C.chordCarrier])
    exact Set.disjoint_left.mp disjoint_interior_frontier
      hxInteriorSupport hxFrontierSupport
  have hTM := (C.mem_side13Mesh_triangles_iff.mp T.2).1
  have hboundary :
      M.boundaryEdges T.1 = (M.triangleEdges T.1).erase C.chordEdge := by
    ext d
    rw [show d ∈ M.boundaryEdges T.1 ↔
        d ⊆ T.1 ∧ d.card = 2 ∧ M.IsBoundaryEdge d from
      M.mem_boundaryEdges_iff]
    rw [Finset.mem_erase]
    constructor
    · rintro ⟨hdT, hdcard, hdBoundary⟩
      refine ⟨?_, Finset.mem_powersetCard.mpr ⟨hdT, hdcard⟩⟩
      intro hde
      exact hchordNotBoundary (hde ▸ hdBoundary)
    · rintro ⟨hdne, hdTriangle⟩
      have hdData := Finset.mem_powersetCard.mp hdTriangle
      have hdEdge : d ∈ M.edges := by
        apply Finset.mem_biUnion.mpr
        exact ⟨T.1, hTM, hdTriangle⟩
      refine ⟨hdData.1, hdData.2, hdEdge, ?_⟩
      by_contra hdNotBoundary
      have hdNotBoundary' : ¬M.IsBoundaryEdge d :=
        fun h => hdNotBoundary h.2
      have hincidentCard := M.card_incidentTriangles_eq_two_of_not_boundary
        hTM hdData.2 hdData.1 hdNotBoundary'
      have hTi : T.1 ∈ M.incidentTriangles d :=
        M.mem_incidentTriangles_iff.mpr ⟨hTM, hdData.1⟩
      have hother : ∃ u ∈ M.incidentTriangles d, u ≠ T.1 := by
        by_contra h
        push Not at h
        have hsingleton : M.incidentTriangles d = {T.1} := by
          ext u
          constructor
          · exact fun hu => Finset.mem_singleton.mpr (h u hu)
          · intro hu
            rw [Finset.mem_singleton.mp hu]
            exact hTi
        have hone : (M.incidentTriangles d).card = 1 := by
          calc
            (M.incidentTriangles d).card =
                ({(T.1 : Finset M.Vertex)} : Finset (Finset M.Vertex)).card :=
              congrArg Finset.card hsingleton
            _ = 1 := Finset.card_singleton _
        omega
      obtain ⟨u, hui, huT⟩ := hother
      have huData := M.mem_incidentTriangles_iff.mp hui
      let U : M.Triangle := ⟨u, huData.1⟩
      have hu23 : u ∈ C.side23Mesh.triangles := by
        rcases C.triangle_interior_side U with hu13 | hu23
        · have hu13Mem : (u : Finset M.Vertex) ∈ C.side13Mesh.triangles :=
            C.mem_side13Mesh_triangles_iff.mpr ⟨huData.1, hu13⟩
          have huEq : u = T.1 := by
            by_contra hne
            have htwo : 1 < C.side13Mesh.triangles.card :=
              Finset.one_lt_card.mpr ⟨T.1, T.2, u, hu13Mem, Ne.symm hne⟩
            omega
          exact False.elim (huT huEq)
        · exact C.mem_side23Mesh_triangles_iff.mpr ⟨huData.1, hu23⟩
      obtain ⟨p, hpD, hpv⟩ := M.exists_nonvertex_mem_edgeCarrier hdData.2
      have hp13 : p ∈ G.J13.closedRegion := by
        rw [← C.side13Mesh_support, TriangleMesh.toPlaneComplex_support]
        exact Set.mem_iUnion_of_mem T.1 <|
          Set.mem_iUnion_of_mem T.2 <| convexHull_mono (Set.image_mono hdData.1) hpD
      have hp23 : p ∈ G.J23.closedRegion := by
        rw [← C.side23Mesh_support, TriangleMesh.toPlaneComplex_support]
        exact Set.mem_iUnion_of_mem u <|
          Set.mem_iUnion_of_mem hu23 <| convexHull_mono (Set.image_mono huData.2) hpD
      have hpB3 : p ∈ G.B3 := by
        rw [← G.closedRegion13_inter_closedRegion23]
        exact ⟨hp13, hp23⟩
      have hde : d = C.chordEdge :=
        M.edge_eq_of_nonvertex_mem_edgeCarriers hdEdge C.chordEdge_mem
          hpD (by rwa [C.chordCarrier]) hpv
      exact hdne hde
  have hboundaryCard : (M.boundaryEdges T.1).card = 2 := by
    rw [hboundary, Finset.card_erase_of_mem]
    · rw [M.card_triangleEdges hTM]
    · exact Finset.mem_powersetCard.mpr ⟨hchordT, hedgeCard⟩
  have hnoIsolated :=
    M.hasNoIsolatedFrontierVertex_of_boundaryEdges_card_two
      ⟨T.1, hTM⟩ hboundaryCard
  exact ⟨T, M.isGeometricallyFreeTriangle_of_boundaryEdges_card_two
    ⟨T.1, hTM⟩ hnoIsolated hboundaryCard⟩

/-- Symmetric one-triangle-side conclusion. -/
theorem exists_geometricallyFreeTriangle_of_side23_card_one
    (hcard : C.side23Mesh.triangles.card = 1) :
    ∃ T : C.side23Mesh.Triangle,
      M.IsGeometricallyFreeTriangle
        ⟨T.1, (C.mem_side23Mesh_triangles_iff.mp T.2).1⟩ := by
  have hcard' : C.swap12.side13Mesh.triangles.card = 1 := by
    change C.side23Mesh.triangles.card = 1
    exact hcard
  obtain ⟨T, hT⟩ := C.swap12.exists_geometricallyFreeTriangle_of_side13_card_one
    (G := G.swap12) (M := M) hcard'
  have hT23 : T.1 ∈ C.side23Mesh.triangles := by
    have hT' := T.2
    change T.1 ∈ C.side23Mesh.triangles at hT'
    exact hT'
  exact ⟨⟨T.1, hT23⟩, hT⟩

end PolygonalTheta.MeshCrosscut

/-- Removing a two-frontier-edge Figure 3.3 ear leaves another polygonal disk.  The proof uses
the proper base chord and the exact two-side decomposition from Chapter 2. -/
theorem TriangleMesh.exists_polygonalDisk_eraseTriangle_of_twoEdgeFree
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k) :
    ∃ J' : PolygonalCircle,
      (M.eraseTriangle T.1).toPlaneComplex.support = J'.closedRegion ∧
        J'.closedRegion ∩ M.triangleCarrier T.1 =
          segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
  obtain ⟨G, C, hCedge⟩ :=
    M.exists_meshCrosscut_of_twoEdgeFreeTriangle J hsupport T k hfree
  have hbase : G.B3 = segment ℝ (M.freeTriangleOrder T k 0)
      (M.freeTriangleOrder T k 1) := by
    calc
      G.B3 = convexHull ℝ
          (M.position '' (M.freeTriangleBaseEdge T k : Set M.Vertex)) :=
        by rw [← hCedge]; exact C.chordCarrier.symm
      _ = segment ℝ (M.freeTriangleOrder T k 0)
          (M.freeTriangleOrder T k 1) := M.freeTriangleBaseEdge_carrier T k
  rcases C.triangle_interior_side T with hT13 | hT23
  · have hmem : T.1 ∈ C.side13Mesh.triangles :=
      C.mem_side13Mesh_triangles_iff.mpr ⟨T.2, hT13⟩
    have hremaining := (C.side23Mesh_support_eq_eraseTriangle_of_twoEdgeFree
      T k hfree hbase hmem).symm.trans C.side23Mesh_support
    have htriangle : M.triangleCarrier T.1 = G.J13.closedRegion :=
      (C.side13Mesh_support_eq_triangleCarrier_of_twoEdgeFree
        T k hfree hbase hmem).symm.trans C.side13Mesh_support
    refine ⟨G.J23, hremaining, ?_⟩
    rw [htriangle, Set.inter_comm, G.closedRegion13_inter_closedRegion23, hbase]
  · have hmem : T.1 ∈ C.side23Mesh.triangles :=
      C.mem_side23Mesh_triangles_iff.mpr ⟨T.2, hT23⟩
    have hremaining := (C.side13Mesh_support_eq_eraseTriangle_of_twoEdgeFree
      T k hfree hbase hmem).symm.trans C.side13Mesh_support
    have htriangle : M.triangleCarrier T.1 = G.J23.closedRegion :=
      (C.side23Mesh_support_eq_triangleCarrier_of_twoEdgeFree
        T k hfree hbase hmem).symm.trans C.side23Mesh_support
    refine ⟨G.J13, hremaining, ?_⟩
    rw [htriangle, G.closedRegion13_inter_closedRegion23, hbase]

/-- Moise Chapter 3, Theorem 3 in the strengthened form used by the induction: every nontrivial
triangulated polygonal disk has at least two geometrically free maximal triangles. -/
theorem TriangleMesh.exists_two_geometricallyFreeTriangles_of_polygonalDisk
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (hmore : 1 < M.triangles.card) :
    ∃ T U : M.Triangle, T.1 ≠ U.1 ∧
      M.IsGeometricallyFreeTriangle T ∧ M.IsGeometricallyFreeTriangle U := by
  classical
  induction hcardM : M.triangles.card using Nat.strong_induction_on generalizing M J with
  | h n ih =>
    obtain ⟨T, U, hTU, hTfree, hUfree⟩ :=
      M.exists_two_freeTriangles_of_polygonalDisk J hsupport hmore
    obtain ⟨NT, hTNT, hTneighbor⟩ :=
      M.exists_edgeNeighbor_of_polygonalDisk J hsupport T hmore
    obtain ⟨NU, hUNU, hUneighbor⟩ :=
      M.exists_edgeNeighbor_of_polygonalDisk J hsupport U hmore
    have hardCase (X N : M.Triangle) (hXfree : M.IsFreeTriangle X.1)
        (hXN : X.1 ≠ N.1) (hneighbor : M.AreEdgeNeighbors X.1 N.1)
        (hbad : ¬M.HasNoIsolatedFrontierVertex X.1) :
        ∃ T U : M.Triangle, T.1 ≠ U.1 ∧
          M.IsGeometricallyFreeTriangle T ∧ M.IsGeometricallyFreeTriangle U := by
      obtain ⟨G, ⟨C⟩⟩ :=
        M.exists_meshCrosscut_of_badFreeTriangle J hsupport X N
          hXfree hXN hneighbor hbad
      have hside13 : ∃ A : C.side13Mesh.Triangle,
          M.IsGeometricallyFreeTriangle
            ⟨A.1, (C.mem_side13Mesh_triangles_iff.mp A.2).1⟩ := by
        by_cases hcard : C.side13Mesh.triangles.card = 1
        · exact C.exists_geometricallyFreeTriangle_of_side13_card_one hcard
        · have hmore13 : 1 < C.side13Mesh.triangles.card := by
            have hpos := Finset.card_pos.mpr C.side13_triangles_nonempty
            omega
          obtain ⟨A, B, hAB, hAgeom, hBgeom⟩ := ih
            C.side13Mesh.triangles.card
            (by simpa [hcardM] using C.card_side13_triangles_lt)
            C.side13Mesh G.J13 C.side13Mesh_support hmore13 rfl
          by_cases hAchord : C.chordEdge ⊆ A.1
          · have hBchord : ¬C.chordEdge ⊆ B.1 := by
              intro hBchord
              exact hAB (C.side13_triangle_eq_of_chordEdge_subset A B hAchord hBchord)
            exact ⟨B, C.isGeometricallyFreeTriangle_of_side13 B hBgeom hBchord⟩
          · exact ⟨A, C.isGeometricallyFreeTriangle_of_side13 A hAgeom hAchord⟩
      have hside23 : ∃ A : C.side23Mesh.Triangle,
          M.IsGeometricallyFreeTriangle
            ⟨A.1, (C.mem_side23Mesh_triangles_iff.mp A.2).1⟩ := by
        by_cases hcard : C.side23Mesh.triangles.card = 1
        · exact C.exists_geometricallyFreeTriangle_of_side23_card_one hcard
        · have hmore23 : 1 < C.side23Mesh.triangles.card := by
            have hpos := Finset.card_pos.mpr C.side23_triangles_nonempty
            omega
          obtain ⟨A, B, hAB, hAgeom, hBgeom⟩ := ih
            C.side23Mesh.triangles.card
            (by simpa [hcardM] using C.card_side23_triangles_lt)
            C.side23Mesh G.J23 C.side23Mesh_support hmore23 rfl
          by_cases hAchord : C.chordEdge ⊆ A.1
          · have hBchord : ¬C.chordEdge ⊆ B.1 := by
              intro hBchord
              exact hAB (C.side23_triangle_eq_of_chordEdge_subset A B hAchord hBchord)
            exact ⟨B, C.isGeometricallyFreeTriangle_of_side23 B hBgeom hBchord⟩
          · exact ⟨A, C.isGeometricallyFreeTriangle_of_side23 A hAgeom hAchord⟩
      obtain ⟨A, hAgeom⟩ := hside13
      obtain ⟨B, hBgeom⟩ := hside23
      let AM : M.Triangle :=
        ⟨A.1, (C.mem_side13Mesh_triangles_iff.mp A.2).1⟩
      let BM : M.Triangle :=
        ⟨B.1, (C.mem_side23Mesh_triangles_iff.mp B.2).1⟩
      have hAB : AM.1 ≠ BM.1 := by
        intro h
        have hB13 : B.1 ∈ C.side13Mesh.triangles := by
          have hA13 : A.1 ∈ C.side13Mesh.triangles := A.2
          exact h.symm ▸ hA13
        exact Finset.disjoint_left.mp C.disjoint_side_triangles hB13 B.2
      exact ⟨AM, BM, hAB, hAgeom, hBgeom⟩
    by_cases hTvertices : M.HasNoIsolatedFrontierVertex T.1
    · have hTgeom := M.isGeometricallyFreeTriangle_of_isFreeTriangle
        T NT hTfree hTNT hTneighbor hTvertices
      by_cases hUvertices : M.HasNoIsolatedFrontierVertex U.1
      · exact ⟨T, U, hTU, hTgeom,
          M.isGeometricallyFreeTriangle_of_isFreeTriangle
            U NU hUfree hUNU hUneighbor hUvertices⟩
      · exact hardCase U NU hUfree hUNU hUneighbor hUvertices
    · exact hardCase T NT hTfree hTNT hTneighbor hTvertices

namespace PolygonalCircle

variable (J : PolygonalCircle)

/-- A compact set with nonempty interior and polygonal frontier is the closed region bounded by
that polygon.  This recognition lemma lets Figure 3.3 identify the new disk from its frontier. -/
theorem eq_closedRegion_of_isCompact_frontier_eq
    {S : Set Plane} (hS : IsCompact S) (hfrontier : frontier S = J.carrier)
    (hinterior : (interior S).Nonempty) :
    S = J.closedRegion := by
  have hSclosed := hS.isClosed
  have hExteriorCover : J.exteriorRegion ⊆ interior S ∪ Sᶜ := by
    intro p hpExt
    by_cases hpS : p ∈ S
    · left
      apply (mem_interior_iff_notMem_frontier hpS).mpr
      intro hpFrontier
      have hpCarrier : p ∈ J.carrier := hfrontier ▸ hpFrontier
      have hpCompl : p ∈ J.carrierᶜ := by
        rw [← J.interior_union_exterior]
        exact Or.inr hpExt
      exact hpCompl hpCarrier
    · exact Or.inr hpS
  have hExteriorNotS : (J.exteriorRegion ∩ Sᶜ).Nonempty := by
    by_contra h
    have hExtSub : J.exteriorRegion ⊆ S := by
      intro p hpExt
      by_contra hpS
      exact h ⟨p, hpExt, hpS⟩
    exact J.not_isBounded_exteriorRegion (hS.isBounded.subset hExtSub)
  have hExteriorSub : J.exteriorRegion ⊆ Sᶜ :=
    J.isConnected_exteriorRegion.isPreconnected.subset_right_of_subset_union
      isOpen_interior hSclosed.isOpen_compl
      (Set.disjoint_left.mpr fun _ hpInt hpCompl => hpCompl (interior_subset hpInt))
      hExteriorCover hExteriorNotS
  have hSSub : S ⊆ J.closedRegion := by
    intro p hpS
    by_cases hpCarrier : p ∈ J.carrier
    · rw [J.closedRegion_eq_union]
      exact Or.inr hpCarrier
    · have hpSplit : p ∈ J.interiorRegion ∪ J.exteriorRegion := by
        rw [J.interior_union_exterior]
        exact hpCarrier
      rcases hpSplit with hpInt | hpExt
      · rw [J.closedRegion_eq_union]
        exact Or.inl hpInt
      · exact False.elim (hExteriorSub hpExt hpS)
  obtain ⟨p, hpInteriorS⟩ := hinterior
  have hpNotCarrier : p ∉ J.carrier := by
    rw [← hfrontier]
    exact fun hpFrontier =>
      Set.disjoint_left.mp disjoint_interior_frontier hpInteriorS hpFrontier
  have hpInteriorJ : p ∈ J.interiorRegion := by
    have hpSplit : p ∈ J.interiorRegion ∪ J.exteriorRegion := by
      rw [J.interior_union_exterior]
      exact hpNotCarrier
    exact hpSplit.resolve_right fun hpExt => hExteriorSub hpExt (interior_subset hpInteriorS)
  have hInteriorCover : J.interiorRegion ⊆ interior S ∪ Sᶜ := by
    intro q hqInt
    by_cases hqS : q ∈ S
    · left
      apply (mem_interior_iff_notMem_frontier hqS).mpr
      intro hqFrontier
      have hqCarrier : q ∈ J.carrier := hfrontier ▸ hqFrontier
      have hqCompl : q ∈ J.carrierᶜ := by
        rw [← J.interior_union_exterior]
        exact Or.inl hqInt
      exact hqCompl hqCarrier
    · exact Or.inr hqS
  have hInteriorSub : J.interiorRegion ⊆ interior S :=
    J.isConnected_interiorRegion.isPreconnected.subset_left_of_subset_union
      isOpen_interior hSclosed.isOpen_compl
      (Set.disjoint_left.mpr fun _ hpInt hpCompl => hpCompl (interior_subset hpInt))
      hInteriorCover ⟨p, hpInteriorJ, hpInteriorS⟩
  apply Set.Subset.antisymm hSSub
  rw [J.closedRegion_eq_union]
  exact Set.union_subset (hInteriorSub.trans interior_subset)
    (by rw [← hfrontier]; exact frontier_subset_closure.trans_eq hSclosed.closure_eq)

/-- A homeomorphism carrying the frontier of one polygonal mesh disk to another carries the
whole closed disk to the other closed disk. -/
theorem TriangleMesh.image_support_eq_of_polygonalDisk_frontier
    (M : TriangleMesh) (J' : PolygonalCircle)
    (htriangles : M.triangles.Nonempty)
    (g : Plane ≃ₜ Plane) (N : TriangleMesh)
    (hfrontier : g '' frontier M.toPlaneComplex.support =
      frontier N.toPlaneComplex.support)
    (hN : N.toPlaneComplex.support = J'.closedRegion) :
    g '' M.toPlaneComplex.support = N.toPlaneComplex.support := by
  have hcompact : IsCompact (g '' M.toPlaneComplex.support) :=
    M.toPlaneComplex.isCompact_support.image g.continuous
  have hfrontierImage :
      frontier (g '' M.toPlaneComplex.support) = J'.carrier := by
    rw [← g.image_frontier, hfrontier, hN, J'.frontier_closedRegion]
  have hinterior : (interior (g '' M.toPlaneComplex.support)).Nonempty := by
    obtain ⟨t, ht⟩ := htriangles
    let T : M.Triangle := ⟨t, ht⟩
    obtain ⟨p, hp⟩ := M.interior_triangleCarrier_nonempty T
    have htriangle : M.triangleCarrier t ⊆ M.toPlaneComplex.support := by
      rw [M.toPlaneComplex_support]
      exact Set.subset_iUnion_of_subset t
        (Set.subset_iUnion_of_subset ht subset_rfl)
    refine ⟨g p, ?_⟩
    rw [← g.image_interior]
    exact ⟨p, interior_mono htriangle hp, rfl⟩
  exact (J'.eq_closedRegion_of_isCompact_frontier_eq
    hcompact hfrontierImage hinterior).trans hN.symm

/-- The one-edge Figure 3.3 move removes an ear through polygonal disks, relative to any open
neighborhood of that ear. -/
theorem TriangleMesh.exists_supported_polygonalDisk_move_of_oneEdgeFree
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k)
    (hmore : 1 < M.triangles.card)
    (U : Set Plane) (hU : IsOpen U) (hTU : M.triangleCarrier T.1 ⊆ U) :
    ∃ g : Plane ≃ₜ Plane, ∃ J' : PolygonalCircle,
      ∃ _ : FinitePLHomeomorphOn g M.toPlaneComplex.support,
      Set.EqOn g id Uᶜ ∧
        g '' frontier M.toPlaneComplex.support =
          frontier (M.eraseTriangle T.1).toPlaneComplex.support ∧
        (M.eraseTriangle T.1).toPlaneComplex.support = J'.closedRegion := by
  classical
  let E := M.freeTriangleAffineEquiv T k
  have h0 : E (planePoint (-1) 0) = M.freeTriangleOrder T k 0 := by
    simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 0
  have h1 : E (planePoint 1 0) = M.freeTriangleOrder T k 1 := by
    simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 1
  have h2 : E (planePoint 0 1) = M.freeTriangleOrder T k 2 := by
    simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 2
  have hbaseImage : E '' segment ℝ (planePoint (-1) 0) (planePoint 1 0) =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
    change affineEquivHomeomorph E ''
      segment ℝ (planePoint (-1) 0) (planePoint 1 0) = _
    simpa only [h0, h1] using affineEquivHomeomorph_image_segment E
      (planePoint (-1) 0) (planePoint 1 0)
  have htriangleImage : E '' convexHull ℝ (Set.range kiteTrianglePosition) =
      M.triangleCarrier T.1 := M.freeTriangleAffineEquiv_image_triangle T k
  have hedgeNormalize : ∀ i : ZMod J.n,
      affineEquivHomeomorph E.symm '' J.edgeSegment i =
        segment ℝ (E.symm (J.vertex i)) (E.symm (J.vertex (i + 1))) := by
    intro i
    exact affineEquivHomeomorph_image_segment E.symm _ _
  let L := J.mapHomeomorph (affineEquivHomeomorph E.symm) hedgeNormalize
  have hLcarrier : L.carrier = E.symm '' J.carrier := by
    exact J.mapHomeomorph_carrier (affineEquivHomeomorph E.symm) hedgeNormalize
  have hbaseTriangle : segment ℝ (planePoint (-1) 0) (planePoint 1 0) ⊆
      convexHull ℝ (Set.range kiteTrianglePosition) := by
    apply (convex_convexHull ℝ (Set.range kiteTrianglePosition)).segment_subset
    · apply subset_convexHull
      exact ⟨0, by simp [kiteTrianglePosition]⟩
    · apply subset_convexHull
      exact ⟨1, by simp [kiteTrianglePosition]⟩
  have htraceL : L.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) =
      segment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
    apply Set.Subset.antisymm
    · rintro p ⟨hpL, hpTriangle⟩
      rw [hLcarrier] at hpL
      obtain ⟨q, hqJ, hqp⟩ := hpL
      have hq : q = E p := by
        apply E.symm.injective
        simpa using hqp
      have hpFrontier : E p ∈ frontier M.toPlaneComplex.support := by
        rw [hsupport, J.frontier_closedRegion]
        simpa [hq] using hqJ
      have hpWorldTriangle : E p ∈ M.triangleCarrier T.1 := by
        rw [← htriangleImage]
        exact ⟨p, hpTriangle, rfl⟩
      have hpWorldBase : E p ∈
          segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
        rw [← hfree]
        exact ⟨hpFrontier, hpWorldTriangle⟩
      rw [← hbaseImage] at hpWorldBase
      obtain ⟨r, hr, hrp⟩ := hpWorldBase
      exact E.injective hrp ▸ hr
    · intro p hpBase
      have hpWorldBase : E p ∈
          segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
        rw [← hbaseImage]
        exact ⟨p, hpBase, rfl⟩
      have hpFrontier : E p ∈ frontier M.toPlaneComplex.support := by
        exact (hfree.symm ▸ hpWorldBase).1
      have hpJ : E p ∈ J.carrier := by
        rwa [hsupport, J.frontier_closedRegion] at hpFrontier
      constructor
      · rw [hLcarrier]
        exact ⟨E p, hpJ, by simp⟩
      · exact hbaseTriangle hpBase
  let F : Finset Plane :=
    {planePoint (-1) 0, planePoint 0 0, planePoint 1 0}
  have hF : ∀ p ∈ F, p ∈ L.carrier := by
    intro p hp
    have hpBase : p ∈ segment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact left_mem_segment ℝ _ _
      · rw [baseSegment_eq_spokes]
        exact Or.inl (right_mem_segment ℝ _ _)
      · exact right_mem_segment ℝ _ _
    have : p ∈ L.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) := by
      rw [htraceL]
      exact hpBase
    exact this.1
  obtain ⟨K, hKcarrier, hKF⟩ := L.exists_refinement_vertices F hF
  have hleft : K.IsVertexPoint (planePoint (-1) 0) := hKF _ (by simp [F])
  have hcenter : K.IsVertexPoint (planePoint 0 0) := hKF _ (by simp [F])
  have hright : K.IsVertexPoint (planePoint 1 0) := hKF _ (by simp [F])
  have htraceK : K.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) =
      segment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
    rw [hKcarrier, htraceL]
  have hbaseK : segment ℝ (planePoint (-1) 0) (planePoint 1 0) ⊆ K.carrier := by
    intro p hp
    rw [hKcarrier]
    have : p ∈ L.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) := by
      rw [htraceL]
      exact hp
    exact this.1
  obtain ⟨δ, hδ, hfixU, hfixBoundary, hmove⟩ :=
    M.exists_supported_triangle_push_fixing_boundaryCarrier T k hfree U hU hTU
  let thin := thinKiteAmbientHomeomorph δ hδ
  let g := transportedThinKiteHomeomorph E δ hδ
  have g_apply (p : Plane) : g p = E (thin (E.symm p)) := rfl
  have hfixK : Set.EqOn thin id
      (K.carrier \ convexHull ℝ (Set.range kiteTrianglePosition)) := by
    intro p hp
    have hpL : p ∈ L.carrier := hKcarrier ▸ hp.1
    rw [hLcarrier] at hpL
    obtain ⟨q, hqJ, hqp⟩ := hpL
    have hq : q = E p := by
      apply E.symm.injective
      simpa using hqp
    have hpJ : E p ∈ J.carrier := hq ▸ hqJ
    have hpBoundary : E p ∈ M.boundaryCarrier := by
      rw [M.boundaryCarrier_eq_frontier_of_polygonalDisk J hsupport,
        hsupport, J.frontier_closedRegion]
      exact hpJ
    have hpNotTriangle : E p ∉ M.triangleCarrier T.1 := by
      intro hpTriangle
      rw [← htriangleImage] at hpTriangle
      obtain ⟨r, hr, hrp⟩ := hpTriangle
      apply hp.2
      have : r = p := E.injective hrp
      simpa [this] using hr
    have hg := hfixBoundary ⟨hpBoundary, hpNotTriangle⟩
    change thin p = p
    have hge : E (thin p) = E p := by
      change g (E p) = E p at hg
      rw [g_apply, E.symm_apply_apply] at hg
      exact hg
    exact E.injective hge
  obtain ⟨H, hHcarrier⟩ := K.exists_thinKite_image δ hδ hbaseK
    hleft hcenter hright htraceK hfixK
  have hedgeWorld : ∀ i : ZMod H.n,
      affineEquivHomeomorph E '' H.edgeSegment i =
        segment ℝ (E (H.vertex i)) (E (H.vertex (i + 1))) := by
    intro i
    exact affineEquivHomeomorph_image_segment E _ _
  let J' := H.mapHomeomorph (affineEquivHomeomorph E) hedgeWorld
  have hJ'carrier : J'.carrier = g '' J.carrier := by
    dsimp [J']
    rw [H.mapHomeomorph_carrier (affineEquivHomeomorph E) hedgeWorld,
      hHcarrier, hKcarrier, hLcarrier]
    ext p
    simp only [Set.mem_image]
    constructor
    · rintro ⟨q, ⟨r, ⟨s, hs, hsr⟩, hrq⟩, hqp⟩
      refine ⟨s, hs, ?_⟩
      calc
        g s = E (thin (E.symm s)) := g_apply s
        _ = E (thin r) := congrArg (fun z => E (thin z)) hsr
        _ = E q := congrArg E hrq
        _ = p := hqp
    · rintro ⟨s, hs, hsp⟩
      refine ⟨thin (E.symm s), ⟨E.symm s, ⟨s, hs, rfl⟩, rfl⟩, ?_⟩
      change E (thin (E.symm s)) = p
      exact (g_apply s).symm.trans hsp
  have hfrontier : g '' frontier M.toPlaneComplex.support =
      frontier (M.eraseTriangle T.1).toPlaneComplex.support :=
    M.image_frontier_eq_eraseTriangle_frontier_of_oneEdgeFree T k hfree g
      (by
        intro p hp
        exact hfixBoundary ⟨(by
          rw [M.boundaryCarrier_eq_frontier_of_polygonalDisk J hsupport]
          exact hp.1), hp.2⟩)
      hmove
  have hnewFrontier : frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      J'.carrier := by
    calc
      frontier (M.eraseTriangle T.1).toPlaneComplex.support =
          g '' frontier M.toPlaneComplex.support := hfrontier.symm
      _ = g '' J.carrier := by rw [hsupport, J.frontier_closedRegion]
      _ = J'.carrier := hJ'carrier.symm
  have hinterior : (interior (M.eraseTriangle T.1).toPlaneComplex.support).Nonempty := by
    have hcard := M.card_eraseTriangle_triangles T.2
    have hpos : 0 < (M.eraseTriangle T.1).triangles.card := by omega
    obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
    let R : (M.eraseTriangle T.1).Triangle := ⟨t, ht⟩
    obtain ⟨p, hp⟩ := (M.eraseTriangle T.1).interior_triangleCarrier_nonempty R
    refine ⟨p, interior_mono ?_ hp⟩
    rw [(M.eraseTriangle T.1).toPlaneComplex_support]
    intro q hq
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht, hq⟩⟩
  have hremaining : (M.eraseTriangle T.1).toPlaneComplex.support = J'.closedRegion :=
    J'.eq_closedRegion_of_isCompact_frontier_eq
      (M.eraseTriangle T.1).toPlaneComplex.isCompact_support hnewFrontier hinterior
  exact ⟨g, J',
    transportedThinKiteHomeomorphFinitePLOn E δ hδ M.toPlaneComplex
      M.toPlaneComplex_isPure2,
    hfixU, hfrontier, hremaining⟩

/-- The inverse two-edge Figure 3.3 move removes an ear through polygonal disks, relative to any
open neighborhood of the ear. -/
theorem TriangleMesh.exists_supported_polygonalDisk_move_of_twoEdgeFree
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k)
    (U : Set Plane) (hU : IsOpen U) (hTU : M.triangleCarrier T.1 ⊆ U) :
    ∃ g : Plane ≃ₜ Plane, ∃ J' : PolygonalCircle,
      ∃ _ : FinitePLHomeomorphOn g M.toPlaneComplex.support,
      Set.EqOn g id Uᶜ ∧
        g '' frontier M.toPlaneComplex.support =
          frontier (M.eraseTriangle T.1).toPlaneComplex.support ∧
        (M.eraseTriangle T.1).toPlaneComplex.support = J'.closedRegion := by
  classical
  obtain ⟨J', hremaining, hregionInter⟩ :=
    M.exists_polygonalDisk_eraseTriangle_of_twoEdgeFree J hsupport T k hfree
  let E := M.freeTriangleAffineEquiv T k
  have h0 : E (planePoint (-1) 0) = M.freeTriangleOrder T k 0 := by
    simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 0
  have h1 : E (planePoint 1 0) = M.freeTriangleOrder T k 1 := by
    simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 1
  have h2 : E (planePoint 0 1) = M.freeTriangleOrder T k 2 := by
    simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 2
  have hbaseImage : E '' segment ℝ (planePoint (-1) 0) (planePoint 1 0) =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
    change affineEquivHomeomorph E ''
      segment ℝ (planePoint (-1) 0) (planePoint 1 0) = _
    simpa only [h0, h1] using affineEquivHomeomorph_image_segment E
      (planePoint (-1) 0) (planePoint 1 0)
  have htriangleImage : E '' convexHull ℝ (Set.range kiteTrianglePosition) =
      M.triangleCarrier T.1 := M.freeTriangleAffineEquiv_image_triangle T k
  have htraceWorld : J'.carrier ∩ M.triangleCarrier T.1 =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
    apply Set.Subset.antisymm
    · rintro p ⟨hpCarrier, hpTriangle⟩
      rw [← hregionInter]
      constructor
      · rw [J'.closedRegion_eq_union]
        exact Or.inr hpCarrier
      · exact hpTriangle
    · intro p hpBase
      have hpData : p ∈ J'.closedRegion ∩ M.triangleCarrier T.1 := by
        rw [hregionInter]
        exact hpBase
      have hpFrontier : p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support := by
        rw [M.frontier_eraseTriangle_support T]
        exact Or.inr ⟨hremaining ▸ hpData.1, hpData.2⟩
      rw [hremaining, J'.frontier_closedRegion] at hpFrontier
      exact ⟨hpFrontier, hpData.2⟩
  have hedgeNormalize : ∀ i : ZMod J'.n,
      affineEquivHomeomorph E.symm '' J'.edgeSegment i =
        segment ℝ (E.symm (J'.vertex i)) (E.symm (J'.vertex (i + 1))) := by
    intro i
    exact affineEquivHomeomorph_image_segment E.symm _ _
  let L := J'.mapHomeomorph (affineEquivHomeomorph E.symm) hedgeNormalize
  have hLcarrier : L.carrier = E.symm '' J'.carrier :=
    J'.mapHomeomorph_carrier (affineEquivHomeomorph E.symm) hedgeNormalize
  have htraceL : L.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) =
      segment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
    apply Set.Subset.antisymm
    · rintro p ⟨hpL, hpTriangle⟩
      rw [hLcarrier] at hpL
      obtain ⟨q, hq, hqp⟩ := hpL
      have hqE : q = E p := by
        apply E.symm.injective
        simpa using hqp
      have hpWorld : E p ∈ J'.carrier ∩ M.triangleCarrier T.1 := by
        constructor
        · simpa [hqE] using hq
        · rw [← htriangleImage]
          exact ⟨p, hpTriangle, rfl⟩
      have hpBase := htraceWorld ▸ hpWorld
      rw [← hbaseImage] at hpBase
      obtain ⟨r, hr, hrp⟩ := hpBase
      exact E.injective hrp ▸ hr
    · intro p hpBase
      have hpWorldBase : E p ∈
          segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
        rw [← hbaseImage]
        exact ⟨p, hpBase, rfl⟩
      have hpWorld := htraceWorld.symm ▸ hpWorldBase
      constructor
      · rw [hLcarrier]
        exact ⟨E p, hpWorld.1, by simp⟩
      · rw [← htriangleImage] at hpWorld
        obtain ⟨r, hr, hrp⟩ := hpWorld.2
        exact E.injective hrp ▸ hr
  let F : Finset Plane :=
    {planePoint (-1) 0, planePoint 0 0, planePoint 1 0}
  have hF : ∀ p ∈ F, p ∈ L.carrier := by
    intro p hp
    have hpBase : p ∈ segment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact left_mem_segment ℝ _ _
      · rw [baseSegment_eq_spokes]
        exact Or.inl (right_mem_segment ℝ _ _)
      · exact right_mem_segment ℝ _ _
    have : p ∈ L.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) := by
      rw [htraceL]
      exact hpBase
    exact this.1
  obtain ⟨K, hKcarrier, hKF⟩ := L.exists_refinement_vertices F hF
  have hleft : K.IsVertexPoint (planePoint (-1) 0) := hKF _ (by simp [F])
  have hcenter : K.IsVertexPoint (planePoint 0 0) := hKF _ (by simp [F])
  have hright : K.IsVertexPoint (planePoint 1 0) := hKF _ (by simp [F])
  have htraceK : K.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) =
      segment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
    rw [hKcarrier, htraceL]
  let W := E ⁻¹' U
  have hW : IsOpen W := hU.preimage E.toAffineMap.continuous_of_finiteDimensional
  have htriangleW : convexHull ℝ (Set.range kiteTrianglePosition) ⊆ W := by
    intro p hp
    exact hTU (htriangleImage ▸ ⟨p, hp, rfl⟩)
  obtain ⟨δ, hδ, hpatchW, hfixK⟩ :=
    K.exists_thinKite_fixing_outside_triangle hleft hcenter hright htraceK
      W hW htriangleW
  let thin := thinKiteAmbientHomeomorph δ hδ
  let push := transportedThinKiteHomeomorph E δ hδ
  have push_apply (p : Plane) : push p = E (thin (E.symm p)) := rfl
  have hfixU : Set.EqOn push id Uᶜ := by
    intro p hp
    apply transportedThinKiteHomeomorph_eqOn_compl E δ hδ
    intro hpPatch
    obtain ⟨q, hq, rfl⟩ := hpPatch
    exact hp (hpatchW hq)
  have hfixWorld : Set.EqOn push id
      (J'.carrier \ M.triangleCarrier T.1) := by
    intro p hp
    have hpK : E.symm p ∈ K.carrier := by
      rw [hKcarrier, hLcarrier]
      exact ⟨p, hp.1, rfl⟩
    have hpNotTriangle : E.symm p ∉
        convexHull ℝ (Set.range kiteTrianglePosition) := by
      intro hpTriangle
      apply hp.2
      rw [← htriangleImage]
      exact ⟨E.symm p, hpTriangle, by simp⟩
    have hpFix := hfixK ⟨hpK, hpNotTriangle⟩
    change push p = p
    rw [push_apply, hpFix]
    simp
  have hnewFrontier : frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      (frontier M.toPlaneComplex.support \ M.triangleCarrier T.1) ∪
        segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
    rw [M.frontier_eraseTriangle_support T, hremaining, hregionInter]
  have hfixOutside : Set.EqOn push id
      (frontier M.toPlaneComplex.support \ M.triangleCarrier T.1) := by
    intro p hp
    apply hfixWorld
    constructor
    · have hpNew : p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support := by
        rw [hnewFrontier]
        exact Or.inl hp
      rwa [hremaining, J'.frontier_closedRegion] at hpNew
    · exact hp.2
  have hmove : push '' segment ℝ (M.freeTriangleOrder T k 0)
        (M.freeTriangleOrder T k 1) =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
        segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2) :=
    by simpa only [push, h0, h1, h2] using
      transportedThinKiteHomeomorph_image_baseSegment E δ hδ
  have hpush : push '' frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      frontier M.toPlaneComplex.support := by
    rw [hnewFrontier, Set.image_union, hmove]
    conv_rhs =>
      rw [M.frontier_eq_outside_triangle_union_apex_of_twoEdgeFree T k hfree]
    congr 1
    apply Set.Subset.antisymm
    · rintro p ⟨q, hq, rfl⟩
      rw [hfixOutside hq]
      exact hq
    · intro p hp
      exact ⟨p, hp, hfixOutside hp⟩
  let pull := push.symm
  have hpullFix : Set.EqOn pull id Uᶜ := by
    intro p hp
    have hpp : push p = p := hfixU hp
    exact push.symm_apply_eq.mpr hpp.symm
  have hpull : pull '' frontier M.toPlaneComplex.support =
      frontier (M.eraseTriangle T.1).toPlaneComplex.support := by
    rw [← hpush, Set.image_image]
    simp [pull]
  exact ⟨pull, J',
    transportedThinKiteHomeomorphSymmFinitePLOn E δ hδ M.toPlaneComplex
      M.toPlaneComplex_isPure2,
    hpullFix, hpull, hremaining⟩

/-- **Theorem boundary** (Moise Ch. 2, Thm. 2: polygonal disks are finite polyhedra).

The closed region bounded by a polygon is the support of a finite, purely two-dimensional plane
complex.  Moise's proof cuts the region by the finitely many lines through the polygon's edges
and triangulates each convex piece. -/
theorem closedRegion_is_polyhedron :
    ∃ K : PlaneComplex, K.support = J.closedRegion ∧ K.IsPure2 := by
  exact ⟨J.closedRegionMesh.toPlaneComplex, J.closedRegionMesh_support,
    J.closedRegionMesh.toPlaneComplex_isPure2⟩

/-- The closed region bounded by a polygon admits a geometric triangulation.

This is real glue (not a boundary): it consumes `closedRegion_is_polyhedron` (Moise Ch. 2,
Thm. 2) and the realization bridge `PlaneComplex.toGeometricTriangulation`. -/
theorem closedRegion_triangulable :
    Nonempty (GeometricTriangulation J.closedRegion) := by
  obtain ⟨K, hsupport, hpure⟩ := J.closedRegion_is_polyhedron
  obtain ⟨T⟩ := K.toGeometricTriangulation hpure
  exact ⟨{ T with homeo := T.homeo.trans (Homeomorph.setCongr hsupport) }⟩

/-- **Theorem boundary** (Moise Ch. 3, Thm. 7: the relative Schoenflies theorem for polygons).

The straightening homeomorphism can be chosen to fix everything outside a prescribed open set
containing the closed region: `h` sends the polygon to the frontier of a triangle and is the
identity off `U`.  This is the version used to reconcile chart triangulations without disturbing
the part of the complex already built. -/
theorem polygonal_schoenflies_rel (U : Set Plane) (hU : IsOpen U)
    (hregion : J.closedRegion ⊆ U) :
    ∃ h : Plane ≃ₜ Plane,
      ∃ _ : FinitePLHomeomorphOn h J.closedRegionMesh.toPlaneComplex.support,
        (∃ C : Set Plane, IsTriangle C ∧ h '' J.carrier = frontier C ∧
          h '' J.closedRegion = C) ∧
          Set.EqOn h id Uᶜ := by
  have hshelling : J.closedRegionMesh.PLAmbientShellingIn U := by
    have shelling (M : TriangleMesh) (K : PolygonalCircle)
        (hsupport : M.toPlaneComplex.support = K.closedRegion)
        (hsubset : M.toPlaneComplex.support ⊆ U) : M.PLAmbientShellingIn U := by
      induction hcardM : M.triangles.card using Nat.strong_induction_on generalizing M K with
      | h n ih =>
          have htriangles : M.triangles.Nonempty := by
            by_contra hempty
            have hempty' : M.triangles = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
            have hsupportEmpty : M.toPlaneComplex.support = ∅ := by
              rw [M.toPlaneComplex_support, hempty']
              simp
            have hvertexClosed : K.vertex 0 ∈ K.closedRegion := by
              rw [K.closedRegion_eq_union]
              exact Or.inr (K.vertex_mem_carrier 0)
            rw [← hsupport, hsupportEmpty] at hvertexClosed
            exact hvertexClosed
          have hpos : 0 < M.triangles.card := Finset.card_pos.mpr htriangles
          by_cases hcard : M.triangles.card = 1
          · exact TriangleMesh.PLAmbientShellingIn.single M hcard
          · have hmore : 1 < M.triangles.card := by omega
            obtain ⟨T, -, -, hTfree, -⟩ :=
              M.exists_two_geometricallyFreeTriangles_of_polygonalDisk K hsupport hmore
            have hTU : M.triangleCarrier T.1 ⊆ U := by
              intro p hp
              apply hsubset
              rw [M.toPlaneComplex_support]
              exact Set.mem_iUnion_of_mem T.1 (Set.mem_iUnion_of_mem T.2 hp)
            have hcardErase := M.card_eraseTriangle_triangles T.2
            have hlt : (M.eraseTriangle T.1).triangles.card < M.triangles.card := by omega
            have hsubsetErase : (M.eraseTriangle T.1).toPlaneComplex.support ⊆ U :=
              (M.eraseTriangle_support_subset T.1).trans hsubset
            obtain ⟨k, hTone | hTtwo⟩ := hTfree
            · obtain ⟨g, K', hpl, hfix, hfrontier, hsupport'⟩ :=
                PolygonalCircle.TriangleMesh.exists_supported_polygonalDisk_move_of_oneEdgeFree
                  M K hsupport
                  T k hTone hmore U hU hTU
              have himage :=
                PolygonalCircle.TriangleMesh.image_support_eq_of_polygonalDisk_frontier
                  M K' htriangles g (M.eraseTriangle T.1) hfrontier hsupport'
              have htail := ih (M.eraseTriangle T.1).triangles.card
                (by simpa [hcardM] using hlt) (M.eraseTriangle T.1) K'
                hsupport' hsubsetErase rfl
              exact TriangleMesh.PLAmbientShellingIn.remove M T.1 T.2 g hpl hfix
                himage hfrontier htail
            · obtain ⟨g, K', hpl, hfix, hfrontier, hsupport'⟩ :=
                PolygonalCircle.TriangleMesh.exists_supported_polygonalDisk_move_of_twoEdgeFree
                  M K hsupport
                  T k hTtwo U hU hTU
              have himage :=
                PolygonalCircle.TriangleMesh.image_support_eq_of_polygonalDisk_frontier
                  M K' htriangles g (M.eraseTriangle T.1) hfrontier hsupport'
              have htail := ih (M.eraseTriangle T.1).triangles.card
                (by simpa [hcardM] using hlt) (M.eraseTriangle T.1) K'
                hsupport' hsubsetErase rfl
              exact TriangleMesh.PLAmbientShellingIn.remove M T.1 T.2 g hpl hfix
                himage hfrontier htail
    exact shelling J.closedRegionMesh J J.closedRegionMesh_support
      (J.closedRegionMesh_support.trans_le hregion)
  obtain ⟨h, C, hpl, hC, hfrontier, hsupportImage, hfix⟩ := hshelling.straightens
  refine ⟨h, hpl, ⟨C, hC, ?_, ?_⟩, hfix⟩
  · rw [← J.frontier_closedRegion, ← J.closedRegionMesh_support]
    exact hfrontier
  · rw [← J.closedRegionMesh_support]
    exact hsupportImage

/-- Moise Ch. 3, Thm. 5: any two polygons in the plane are equivalent under an ambient
homeomorphism.  This follows from relative straightening and the affine equivalence of the two
resulting triangles. -/
theorem polygonal_schoenflies (J' : PolygonalCircle) :
    ∃ h : Plane ≃ₜ Plane, h '' J.carrier = J'.carrier := by
  obtain ⟨h, -, ⟨C, hC, hJC, -⟩, -⟩ := J.polygonal_schoenflies_rel Set.univ isOpen_univ
    (Set.subset_univ _)
  obtain ⟨h', -, ⟨C', hC', hJ'C', -⟩, -⟩ := J'.polygonal_schoenflies_rel Set.univ isOpen_univ
    (Set.subset_univ _)
  obtain ⟨a, -, ha⟩ := triangle_ambient_homeomorphic hC hC'
  refine ⟨h.trans (a.trans h'.symm), ?_⟩
  have hfun : ⇑(h.trans (a.trans h'.symm)) =
      fun x => h'.symm (a (h x)) := by
    funext x
    rfl
  rw [hfun]
  rw [← Set.image_image h'.symm (fun x => a (h x)), ← Set.image_image a h]
  rw [hJC, ha, ← hJ'C']
  rw [Set.image_image]
  simp

end PolygonalCircle

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
