/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicComplex

/-!
# Midpoint subdivision of an intrinsic two-complex

This file constructs the intrinsic 1-to-4 subdivision used to make the source of Moise's
PL-approximation theorem fine.  A new vertex is attached to every old edge.  Each old triangle is
then divided into its three corner triangles and its central triangle.  Since edge midpoints are
indexed by the old edge itself, the construction is automatically coherent across adjacent
faces.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex)

@[simp] theorem zmod3_three_add (i : ZMod 3) : 3 + i = i :=
  (by decide : ∀ i : ZMod 3, 3 + i = i) i

@[simp] theorem zmod3_add_three (i : ZMod 3) : i + 3 = i :=
  (by decide : ∀ i : ZMod 3, i + 3 = i) i

@[simp] theorem zmod3_one_add (i : ZMod 3) : 1 + i = i + 1 := by abel

@[simp] theorem zmod3_two_add (i : ZMod 3) : 2 + i = i + 2 := by abel

@[simp] theorem zmod3_add_two_add_one (i : ZMod 3) : i + 2 + 1 = i :=
  (by decide : ∀ i : ZMod 3, i + 2 + 1 = i) i

@[simp] theorem zmod3_add_one_add_one (i : ZMod 3) : i + 1 + 1 = i + 2 := by ring

@[simp] theorem zmod3_add_one_add_two (i : ZMod 3) : i + 1 + 2 = i :=
  (by decide : ∀ i : ZMod 3, i + 1 + 2 = i) i

@[simp] theorem zmod3_add_two_add_two (i : ZMod 3) : i + 2 + 2 = i + 1 :=
  (by decide : ∀ i : ZMod 3, i + 2 + 2 = i + 1) i

/-- Vertices of the midpoint subdivision: old vertices and one new vertex for every old edge. -/
abbrev MidpointVertex := K.Vertex ⊕ K.Edge

/-- The corner triangle at the `i`-th vertex of an old face. -/
noncomputable def midpointCornerFace (t : K.Face) (i : ZMod 3) :
    Finset K.MidpointVertex :=
  {Sum.inl (K.faceVertex t i), Sum.inr (K.faceEdge t i),
    Sum.inr (K.faceEdge t (i + 2))}

/-- The central triangle of the midpoint subdivision of an old face. -/
noncomputable def midpointCentralFace (t : K.Face) : Finset K.MidpointVertex :=
  Finset.univ.image (fun i : ZMod 3 => Sum.inr (K.faceEdge t i))

/-- The four midpoint triangles belonging to one old face. -/
noncomputable def midpointFacesOver (t : K.Face) : Finset (Finset K.MidpointVertex) :=
  (Finset.univ.image (K.midpointCornerFace t)) ∪ {K.midpointCentralFace t}

/-- All maximal faces in the midpoint subdivision. -/
noncomputable def midpointFaces : Finset (Finset K.MidpointVertex) :=
  K.faces.attach.biUnion K.midpointFacesOver

theorem faceEdge_ne_add_two (t : K.Face) (i : ZMod 3) :
    K.faceEdge t i ≠ K.faceEdge t (i + 2) := by
  intro h
  apply K.faceEdge_ne_next t (i + 2)
  have hcycle : i + 2 + 1 = i :=
    (by decide : ∀ i : ZMod 3, i + 2 + 1 = i) i
  rw [hcycle]
  exact h.symm

theorem faceEdge_injective (t : K.Face) : Function.Injective (K.faceEdge t) := by
  intro i j hij
  by_contra hne
  have hcases : j = i + 1 ∨ j = i + 2 := by
    rcases (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j with
      h | h | h
    · exact (hne h.symm).elim
    · exact Or.inl h
    · exact Or.inr h
  rcases hcases with rfl | rfl
  · exact K.faceEdge_ne_next t i hij
  · exact K.faceEdge_ne_add_two t i hij

theorem midpointCornerFace_card (t : K.Face) (i : ZMod 3) :
    (K.midpointCornerFace t i).card = 3 := by
  simp [midpointCornerFace, K.faceEdge_ne_add_two t i]

theorem midpointCentralFace_card (t : K.Face) :
    (K.midpointCentralFace t).card = 3 := by
  rw [midpointCentralFace, Finset.card_image_iff.mpr]
  · decide
  · intro i _ j _ hij
    exact K.faceEdge_injective t (Sum.inr.inj hij)

theorem midpointFacesOver_card (t : K.Face) {s : Finset K.MidpointVertex}
    (hs : s ∈ K.midpointFacesOver t) : s.card = 3 := by
  rw [midpointFacesOver, Finset.mem_union] at hs
  rcases hs with hs | hs
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    exact K.midpointCornerFace_card t i
  · rw [Finset.mem_singleton.mp hs]
    exact K.midpointCentralFace_card t

/-- The finite abstract complex underlying midpoint subdivision. -/
noncomputable def midpointComplex : IntrinsicTwoComplex where
  Vertex := K.MidpointVertex
  faces := K.midpointFaces
  faces_card := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := Finset.mem_biUnion.mp hs
    exact K.midpointFacesOver_card t hst

@[simp] theorem midpointComplex_faces : K.midpointComplex.faces = K.midpointFaces := rfl

/-- Every refined face remembers an old face which contains it geometrically. -/
theorem exists_parentFace_of_mem_midpointFaces
    {s : Finset K.MidpointVertex} (hs : s ∈ K.midpointFaces) :
    ∃ t : K.Face, s ∈ K.midpointFacesOver t := by
  obtain ⟨t, ht, hst⟩ := Finset.mem_biUnion.mp hs
  exact ⟨t, hst⟩

/-- A chosen parent of a midpoint-subdivision face.  Geometric arguments use only
`midpointFace_mem_parent`; uniqueness is not needed for the adaptive open-complex
construction. -/
noncomputable def midpointParentFace (s : K.midpointComplex.Face) : K.Face :=
  Classical.choose (K.exists_parentFace_of_mem_midpointFaces s.2)

theorem midpointFace_mem_parent (s : K.midpointComplex.Face) :
    s.1 ∈ K.midpointFacesOver (K.midpointParentFace s) :=
  Classical.choose_spec (K.exists_parentFace_of_mem_midpointFaces s.2)

/-- Canonical old barycentric position of a midpoint-subdivision vertex. -/
noncomputable def midpointPosition : K.MidpointVertex → (K.Vertex → ℝ)
  | Sum.inl v => Pi.single v 1
  | Sum.inr e => fun v => if v ∈ e.1 then (2 : ℝ)⁻¹ else 0

@[simp] theorem midpointPosition_old (v : K.Vertex) :
    K.midpointPosition (Sum.inl v) = Pi.single v 1 := rfl

@[simp] theorem midpointPosition_edge_apply (e : K.Edge) (v : K.Vertex) :
    K.midpointPosition (Sum.inr e) v = if v ∈ e.1 then (2 : ℝ)⁻¹ else 0 := rfl

theorem midpointPosition_nonneg (w : K.MidpointVertex) (u : K.Vertex) :
    0 ≤ K.midpointPosition w u := by
  rcases w with v | e
  · by_cases h : u = v
    · subst u
      simp [midpointPosition]
    · simp [midpointPosition, h]
  · simp only [midpointPosition]
    split_ifs <;> norm_num

theorem sum_midpointPosition (w : K.MidpointVertex) :
    ∑ v, K.midpointPosition w v = 1 := by
  rcases w with v | e
  · simp [midpointPosition]
  · simp [midpointPosition, K.card_of_mem_edges e.2]

/-- Affine barycentric evaluation from midpoint coordinates to old coordinates. -/
noncomputable def midpointEvalAffine :
    (K.MidpointVertex → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ) :=
  (∑ w, (LinearMap.proj w).smulRight (K.midpointPosition w)).toAffineMap

@[simp] theorem midpointEvalAffine_apply (x : K.MidpointVertex → ℝ) :
    K.midpointEvalAffine x = ∑ w, x w • K.midpointPosition w := by
  simp [midpointEvalAffine]

theorem midpointEvalAffine_eq_sum_of_support {x : K.MidpointVertex → ℝ}
    {s : Finset K.MidpointVertex} (hsupp : ∀ w ∉ s, x w = 0) :
    K.midpointEvalAffine x = ∑ w ∈ s, x w • K.midpointPosition w := by
  rw [K.midpointEvalAffine_apply]
  exact (Finset.sum_subset (Finset.subset_univ s)
    (fun w _ hw => by rw [hsupp w hw, zero_smul])).symm

theorem sum_eq_sum_of_midpointSupport {x : K.MidpointVertex → ℝ}
    {s : Finset K.MidpointVertex} (hsupp : ∀ w ∉ s, x w = 0) :
    ∑ w, x w = ∑ w ∈ s, x w :=
  (Finset.sum_subset (Finset.subset_univ s) (fun w _ hw => hsupp w hw)).symm

theorem exists_faceVertex_eq_of_mem (t : K.Face) {v : K.Vertex} (hv : v ∈ t.1) :
    ∃ i : ZMod 3, K.faceVertex t i = v := by
  let j : Fin 3 := (K.faceVertexEquiv t).symm ⟨v, hv⟩
  let i : ZMod 3 := ZMod.finEquiv 3 j
  refine ⟨i, ?_⟩
  simp [faceVertex, i, j]

theorem midpointCentralFace_eq (t : K.Face) (i : ZMod 3) :
    K.midpointCentralFace t =
      {Sum.inr (K.faceEdge t i), Sum.inr (K.faceEdge t (i + 1)),
        Sum.inr (K.faceEdge t (i + 2))} := by
  rw [midpointCentralFace]
  have hu : (Finset.univ : Finset (ZMod 3)) = {i, i + 1, i + 2} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j
  rw [hu]
  simp

theorem midpointEval_corner_self
    (t : K.Face) (i : ZMod 3) {x : K.MidpointVertex → ℝ}
    (hx : ∀ w ∉ K.midpointCornerFace t i, x w = 0) :
    K.midpointEvalAffine x (K.faceVertex t i) =
      x (Sum.inl (K.faceVertex t i)) +
        (x (Sum.inr (K.faceEdge t i)) + x (Sum.inr (K.faceEdge t (i + 2)))) / 2 := by
  rw [K.midpointEvalAffine_eq_sum_of_support hx]
  simp [midpointCornerFace, midpointPosition, K.faceVertex_ne_next t i,
    K.faceVertex_ne_add_two t i, K.faceEdge_ne_add_two t i]
  ring

theorem midpointEval_corner_next
    (t : K.Face) (i : ZMod 3) {x : K.MidpointVertex → ℝ}
    (hx : ∀ w ∉ K.midpointCornerFace t i, x w = 0) :
    K.midpointEvalAffine x (K.faceVertex t (i + 1)) =
      x (Sum.inr (K.faceEdge t i)) / 2 := by
  have h12 : K.faceVertex t (i + 1) ≠ K.faceVertex t (i + 2) := by
    simpa only [add_assoc, one_add_one_eq_two] using K.faceVertex_ne_next t (i + 1)
  have h10 : K.faceVertex t (i + 1) ≠ K.faceVertex t i :=
    (K.faceVertex_ne_next t i).symm
  rw [K.midpointEvalAffine_eq_sum_of_support hx]
  simp [midpointCornerFace, midpointPosition, K.faceEdge_ne_add_two t i,
    h12, h10]
  ring

theorem midpointEval_corner_prev
    (t : K.Face) (i : ZMod 3) {x : K.MidpointVertex → ℝ}
    (hx : ∀ w ∉ K.midpointCornerFace t i, x w = 0) :
    K.midpointEvalAffine x (K.faceVertex t (i + 2)) =
      x (Sum.inr (K.faceEdge t (i + 2))) / 2 := by
  have h20 : K.faceVertex t (i + 2) ≠ K.faceVertex t i :=
    (K.faceVertex_ne_add_two t i).symm
  have h21 : K.faceVertex t (i + 2) ≠ K.faceVertex t (i + 1) := by
    simpa only [add_assoc, one_add_one_eq_two] using (K.faceVertex_ne_next t (i + 1)).symm
  rw [K.midpointEvalAffine_eq_sum_of_support hx]
  simp [midpointCornerFace, midpointPosition, K.faceEdge_ne_add_two t i, h20, h21]
  ring

theorem midpointEval_central_coord
    (t : K.Face) (i : ZMod 3) {x : K.MidpointVertex → ℝ}
    (hx : ∀ w ∉ K.midpointCentralFace t, x w = 0) :
    K.midpointEvalAffine x (K.faceVertex t i) =
      (x (Sum.inr (K.faceEdge t i)) +
        x (Sum.inr (K.faceEdge t (i + 2)))) / 2 := by
  have h12 : K.faceVertex t (i + 1) ≠ K.faceVertex t (i + 2) := by
    simpa only [add_assoc, one_add_one_eq_two] using K.faceVertex_ne_next t (i + 1)
  have he01 : K.faceEdge t i ≠ K.faceEdge t (i + 1) := K.faceEdge_ne_next t i
  have he02 : K.faceEdge t i ≠ K.faceEdge t (i + 2) := K.faceEdge_ne_add_two t i
  have he12 : K.faceEdge t (i + 1) ≠ K.faceEdge t (i + 2) := by
    simpa only [add_assoc, one_add_one_eq_two] using K.faceEdge_ne_next t (i + 1)
  rw [K.midpointEvalAffine_eq_sum_of_support hx, K.midpointCentralFace_eq t i]
  simp [midpointPosition, he01, he02, he12, K.faceVertex_ne_next t i,
    K.faceVertex_ne_add_two t i]
  ring

/-- Coefficient of an old vertex recovered from a point of the subdivided simplex. -/
noncomputable def midpointRecoverOld (p : K.Vertex → ℝ) (v : K.Vertex) : ℝ :=
  max (2 * p v - 1) 0

/-- Coefficient of an edge midpoint recovered from old barycentric coordinates.  The formula is
symmetric in the two endpoints despite the arbitrary endpoint ordering. -/
noncomputable def midpointRecoverEdge (p : K.Vertex → ℝ) (e : K.Edge) : ℝ :=
  max 0 (min (2 * p (K.edgeFirst e))
    (min (2 * p (K.edgeSecond e))
      (2 * (p (K.edgeFirst e) + p (K.edgeSecond e)) - 1)))

/-- The inverse-coordinate formula for midpoint evaluation. -/
noncomputable def midpointRecover (p : K.Vertex → ℝ) : K.MidpointVertex → ℝ
  | Sum.inl v => K.midpointRecoverOld p v
  | Sum.inr e => K.midpointRecoverEdge p e

theorem midpointRecoverEdge_faceEdge (p : K.Vertex → ℝ) (t : K.Face) (i : ZMod 3) :
    K.midpointRecoverEdge p (K.faceEdge t i) =
      max 0 (min (2 * p (K.faceVertex t i))
        (min (2 * p (K.faceVertex t (i + 1)))
          (2 * (p (K.faceVertex t i) + p (K.faceVertex t (i + 1))) - 1))) := by
  rcases K.faceEdge_endpoint_order t i with h | h
  · simp [midpointRecoverEdge, h.1, h.2]
  · simp only [midpointRecoverEdge, h.1, h.2]
    congr 1
    ac_rfl

/-- Every old edge contained in a face is one of its three cyclic edges. -/
theorem exists_faceEdge_eq_of_subset (t : K.Face) (e : K.Edge) (het : e.1 ⊆ t.1) :
    ∃ i : ZMod 3, K.faceEdge t i = e := by
  obtain ⟨i, hi⟩ := K.exists_faceVertex_eq_of_mem t (het (K.edgeFirst_mem e))
  obtain ⟨j, hj⟩ := K.exists_faceVertex_eq_of_mem t (het (K.edgeSecond_mem e))
  have hij : i ≠ j := by
    intro h
    apply K.edgeFirst_ne_edgeSecond e
    rw [← hi, ← hj, h]
  rcases (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j with
    h | h | h
  · exact (hij h.symm).elim
  · subst j
    refine ⟨i, ?_⟩
    apply Subtype.ext
    rw [K.faceEdge_val, K.edge_eq_pair, hi, hj]
  · subst j
    refine ⟨i + 2, ?_⟩
    apply Subtype.ext
    rw [K.faceEdge_val, K.edge_eq_pair]
    simp only [zmod3_add_two_add_one]
    rw [hi, hj]
    ext v
    simp [or_comm]

theorem faceEdge_subset_face (t : K.Face) (i : ZMod 3) :
    (K.faceEdge t i).1 ⊆ t.1 := by
  intro v hv
  simp only [K.faceEdge_val, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact K.faceVertex_mem t i
  · exact K.faceVertex_mem t (i + 1)

/-- Every vertex of a refined face is supported on its parent old face. -/
theorem midpointPosition_support_of_mem_face
    (t : K.Face) {s : Finset K.MidpointVertex} (hs : s ∈ K.midpointFacesOver t)
    {w : K.MidpointVertex} (hw : w ∈ s) {v : K.Vertex} (hv : v ∉ t.1) :
    K.midpointPosition w v = 0 := by
  rw [midpointFacesOver, Finset.mem_union] at hs
  rcases hs with hs | hs
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    simp only [midpointCornerFace, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact Pi.single_eq_of_ne (fun h => hv (by rw [h]; exact K.faceVertex_mem t i)) 1
    · have hvi : v ≠ K.faceVertex t i :=
        fun h => hv (by rw [h]; exact K.faceVertex_mem t i)
      have hvj : v ≠ K.faceVertex t (i + 1) :=
        fun h => hv (by rw [h]; exact K.faceVertex_mem t (i + 1))
      simp [midpointPosition, hvi, hvj]
    · have hvi : v ≠ K.faceVertex t (i + 2) :=
        fun h => hv (by rw [h]; exact K.faceVertex_mem t (i + 2))
      have hvj : v ≠ K.faceVertex t (i + 2 + 1) :=
        fun h => hv (by rw [h]; exact K.faceVertex_mem t (i + 2 + 1))
      have hv0 : v ≠ K.faceVertex t i :=
        fun h => hv (by rw [h]; exact K.faceVertex_mem t i)
      simp [midpointPosition, hvi, hv0]
  · rw [Finset.mem_singleton.mp hs] at hw
    rw [midpointCentralFace] at hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
    have hvi : v ≠ K.faceVertex t i :=
      fun h => hv (by rw [h]; exact K.faceVertex_mem t i)
    have hvj : v ≠ K.faceVertex t (i + 1) :=
      fun h => hv (by rw [h]; exact K.faceVertex_mem t (i + 1))
    simp [midpointPosition, hvi, hvj]

/-- The affine midpoint evaluation sends a refined face into its parent old face. -/
theorem midpointEvalAffine_support
    (t : K.Face) {s : Finset K.MidpointVertex} (hs : s ∈ K.midpointFacesOver t)
    {x : K.MidpointVertex → ℝ} (hxs : ∀ w ∉ s, x w = 0) {v : K.Vertex}
    (hv : v ∉ t.1) :
    K.midpointEvalAffine x v = 0 := by
  classical
  rw [K.midpointEvalAffine_apply, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro w _
  by_cases hw : w ∈ s
  · rw [Pi.smul_apply, K.midpointPosition_support_of_mem_face t hs hw hv, smul_zero]
  · rw [hxs w hw, zero_smul]
    rfl

/-- Every old vertex of a parent face receives positive weight from at least one vertex of each
midpoint child. -/
theorem exists_midpointPosition_pos_of_mem_parent
    (t : K.Face) {s : Finset K.MidpointVertex} (hs : s ∈ K.midpointFacesOver t)
    {v : K.Vertex} (hv : v ∈ t.1) :
    ∃ w ∈ s, 0 < K.midpointPosition w v := by
  obtain ⟨j, rfl⟩ := K.exists_faceVertex_eq_of_mem t hv
  rw [midpointFacesOver, Finset.mem_union] at hs
  rcases hs with hcorner | hcentral
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hcorner
    rcases (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j with
      hji | hji | hji
    · subst j
      refine ⟨Sum.inl (K.faceVertex t i), ?_, ?_⟩
      · simp [midpointCornerFace]
      · simp [midpointPosition]
    · subst j
      refine ⟨Sum.inr (K.faceEdge t i), ?_, ?_⟩
      · simp [midpointCornerFace]
      · simp [midpointPosition]
    · subst j
      refine ⟨Sum.inr (K.faceEdge t (i + 2)), ?_, ?_⟩
      · simp [midpointCornerFace]
      · simp [midpointPosition]
  · rw [Finset.mem_singleton.mp hcentral]
    refine ⟨Sum.inr (K.faceEdge t j), ?_, ?_⟩
    · simp [midpointCentralFace]
    · simp [midpointPosition]

/-- A point with strictly positive coordinates on a midpoint child maps to a point with strictly
positive coordinates on its parent. -/
theorem midpointEvalAffine_pos_on_parent
    (t : K.Face) {s : Finset K.MidpointVertex} (hs : s ∈ K.midpointFacesOver t)
    {x : K.MidpointVertex → ℝ} (hxs : ∀ w ∉ s, x w = 0)
    (hx0 : ∀ w, 0 ≤ x w) (hxpos : ∀ w ∈ s, 0 < x w)
    {v : K.Vertex} (hv : v ∈ t.1) :
    0 < K.midpointEvalAffine x v := by
  obtain ⟨w, hws, hwpos⟩ := K.exists_midpointPosition_pos_of_mem_parent t hs hv
  rw [K.midpointEvalAffine_eq_sum_of_support hxs, Finset.sum_apply]
  apply Finset.sum_pos'
  · intro q hq
    exact mul_nonneg (hx0 q) (K.midpointPosition_nonneg q v)
  · exact ⟨w, hws, mul_pos (hxpos w hws) hwpos⟩

/-- A midpoint child has a unique old parent triangle. -/
theorem midpointFacesOver_parent_unique
    {t u : K.Face} {s : Finset K.MidpointVertex}
    (hst : s ∈ K.midpointFacesOver t)
    (hsu : s ∈ K.midpointFacesOver u) :
    t = u := by
  let x : K.MidpointVertex → ℝ :=
    fun w ↦ if w ∈ s then 1 else 0
  have hxs : ∀ w ∉ s, x w = 0 := by
    intro w hw
    simp [x, hw]
  have hx0 : ∀ w, 0 ≤ x w := by
    intro w
    simp only [x]
    split_ifs <;> norm_num
  have hxpos : ∀ w ∈ s, 0 < x w := by
    intro w hw
    simp [x, hw]
  apply Subtype.ext
  apply Finset.Subset.antisymm
  · intro v hvt
    by_contra hvu
    have hpos :=
      K.midpointEvalAffine_pos_on_parent t hst hxs hx0 hxpos hvt
    have hzero :=
      K.midpointEvalAffine_support u hsu hxs hvu
    rw [hzero] at hpos
    exact (lt_irrefl 0 hpos)
  · intro v hvu
    by_contra hvt
    have hpos :=
      K.midpointEvalAffine_pos_on_parent u hsu hxs hx0 hxpos hvu
    have hzero :=
      K.midpointEvalAffine_support t hst hxs hvt
    rw [hzero] at hpos
    exact (lt_irrefl 0 hpos)

/-- Inside one old parent, a refined edge joining an old vertex to an old-edge midpoint belongs
to at most one midpoint child. -/
theorem midpointFacesOver_mixed_edge_card_le_one
    (t : K.Face) (v : K.Vertex) (e : K.Edge) :
    ((K.midpointFacesOver t).filter fun s ↦
      ({Sum.inl v, Sum.inr e} : Finset K.MidpointVertex) ⊆ s).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  obtain ⟨haOver, haEdge⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbOver, hbEdge⟩ := Finset.mem_filter.mp hb
  rw [midpointFacesOver, Finset.mem_union] at haOver hbOver
  rcases haOver with haCorner | haCentral
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp haCorner
    rcases hbOver with hbCorner | hbCentral
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hbCorner
      have hvi :
          v = K.faceVertex t i := by
        have hv := haEdge
          (Finset.mem_insert_self (Sum.inl v) {Sum.inr e})
        simpa [midpointCornerFace] using hv
      have hvj :
          v = K.faceVertex t j := by
        have hv := hbEdge
          (Finset.mem_insert_self (Sum.inl v) {Sum.inr e})
        simpa [midpointCornerFace] using hv
      have hij : i = j :=
        K.faceVertex_injective t (hvi.symm.trans hvj)
      rw [hij]
    · rw [Finset.mem_singleton.mp hbCentral] at hbEdge
      have hv := hbEdge
        (Finset.mem_insert_self (Sum.inl v) {Sum.inr e})
      simp [midpointCentralFace] at hv
  · rw [Finset.mem_singleton.mp haCentral] at haEdge
    have hv := haEdge
      (Finset.mem_insert_self (Sum.inl v) {Sum.inr e})
    simp [midpointCentralFace] at hv

/-- An old edge whose midpoint occurs in a midpoint child belongs to that child's parent. -/
theorem edge_subset_parent_of_midpoint_mem
    (t : K.Face) {s : Finset K.MidpointVertex} (hs : s ∈ K.midpointFacesOver t)
    (e : K.Edge) (he : Sum.inr e ∈ s) :
    e.1 ⊆ t.1 := by
  rw [midpointFacesOver, Finset.mem_union] at hs
  rcases hs with hcorner | hcentral
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hcorner
    simp only [midpointCornerFace, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with he | he | he
    · exact (Sum.inr_ne_inl he).elim
    · rw [Sum.inr.inj he]
      exact K.faceEdge_subset_face t i
    · rw [Sum.inr.inj he]
      exact K.faceEdge_subset_face t (i + 2)
  · rw [Finset.mem_singleton.mp hcentral, midpointCentralFace] at he
    obtain ⟨i, -, he⟩ := Finset.mem_image.mp he
    rw [← Sum.inr.inj he]
    exact K.faceEdge_subset_face t i

/-- A midpoint child contains at most one old vertex. -/
theorem oldVertex_eq_of_mem_midpointFace
    (t : K.Face) {s : Finset K.MidpointVertex} (hs : s ∈ K.midpointFacesOver t)
    {v w : K.Vertex} (hv : Sum.inl v ∈ s) (hw : Sum.inl w ∈ s) :
    v = w := by
  rw [midpointFacesOver, Finset.mem_union] at hs
  rcases hs with hcorner | hcentral
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hcorner
    have hv' : v = K.faceVertex t i := by
      simpa [midpointCornerFace] using hv
    have hw' : w = K.faceVertex t i := by
      simpa [midpointCornerFace] using hw
    exact hv'.trans hw'.symm
  · rw [Finset.mem_singleton.mp hcentral, midpointCentralFace] at hv
    simp at hv

/-- Two distinct edges of a triangular face cover the whole face. -/
theorem faceEdge_union_eq_face_of_ne
    (t : K.Face) {i j : ZMod 3} (hij : i ≠ j) :
    (K.faceEdge t i).1 ∪ (K.faceEdge t j).1 = t.1 := by
  rcases (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j with
    h | h | h
  · exact (hij h.symm).elim
  · subst j
    apply Finset.Subset.antisymm
    · exact Finset.union_subset (K.faceEdge_subset_face t i)
        (K.faceEdge_subset_face t (i + 1))
    · intro v hv
      obtain ⟨k, rfl⟩ := K.exists_faceVertex_eq_of_mem t hv
      rcases (by decide :
          ∀ i k : ZMod 3, k = i ∨ k = i + 1 ∨ k = i + 2) i k with
        rfl | rfl | rfl <;> simp []
  · subst j
    apply Finset.Subset.antisymm
    · exact Finset.union_subset (K.faceEdge_subset_face t i)
        (K.faceEdge_subset_face t (i + 2))
    · intro v hv
      obtain ⟨k, rfl⟩ := K.exists_faceVertex_eq_of_mem t hv
      rcases (by decide :
          ∀ i k : ZMod 3, k = i ∨ k = i + 1 ∨ k = i + 2) i k with
        rfl | rfl | rfl <;> simp []

/-- Two distinct old edges determine their triangular parent. -/
theorem face_eq_of_two_edges_subset
    {t u : K.Face} {e d : K.Edge} (hed : e ≠ d)
    (het : e.1 ⊆ t.1) (hdt : d.1 ⊆ t.1)
    (heu : e.1 ⊆ u.1) (hdu : d.1 ⊆ u.1) :
    t = u := by
  obtain ⟨i, hi⟩ := K.exists_faceEdge_eq_of_subset t e het
  obtain ⟨j, hj⟩ := K.exists_faceEdge_eq_of_subset t d hdt
  obtain ⟨k, hk⟩ := K.exists_faceEdge_eq_of_subset u e heu
  obtain ⟨l, hl⟩ := K.exists_faceEdge_eq_of_subset u d hdu
  have hij : i ≠ j := by
    intro h
    apply hed
    rw [← hi, ← hj, h]
  have hkl : k ≠ l := by
    intro h
    apply hed
    rw [← hk, ← hl, h]
  apply Subtype.ext
  calc
    t.1 = (K.faceEdge t i).1 ∪ (K.faceEdge t j).1 :=
      (K.faceEdge_union_eq_face_of_ne t hij).symm
    _ = e.1 ∪ d.1 := by rw [hi, hj]
    _ = (K.faceEdge u k).1 ∪ (K.faceEdge u l).1 := by rw [hk, hl]
    _ = u.1 := K.faceEdge_union_eq_face_of_ne u hkl

/-- In a fixed parent, two distinct midpoint vertices determine at most one corner child. -/
theorem midpointCornerFace_eq_of_two_midpoints_mem
    (t : K.Face) {i j : ZMod 3} {e d : K.Edge} (hed : e ≠ d)
    (hei : Sum.inr e ∈ K.midpointCornerFace t i)
    (hdi : Sum.inr d ∈ K.midpointCornerFace t i)
    (hej : Sum.inr e ∈ K.midpointCornerFace t j)
    (hdj : Sum.inr d ∈ K.midpointCornerFace t j) :
    K.midpointCornerFace t i = K.midpointCornerFace t j := by
  have hei' :
      e = K.faceEdge t i ∨ e = K.faceEdge t (i + 2) := by
    simpa [midpointCornerFace] using hei
  have hdi' :
      d = K.faceEdge t i ∨ d = K.faceEdge t (i + 2) := by
    simpa [midpointCornerFace] using hdi
  have hej' :
      e = K.faceEdge t j ∨ e = K.faceEdge t (j + 2) := by
    simpa [midpointCornerFace] using hej
  have hdj' :
      d = K.faceEdge t j ∨ d = K.faceEdge t (j + 2) := by
    simpa [midpointCornerFace] using hdj
  have hi :
      (e = K.faceEdge t i ∧ d = K.faceEdge t (i + 2)) ∨
        (e = K.faceEdge t (i + 2) ∧ d = K.faceEdge t i) := by
    rcases hei' with hei' | hei' <;> rcases hdi' with hdi' | hdi'
    · exact (hed (hei'.trans hdi'.symm)).elim
    · exact Or.inl ⟨hei', hdi'⟩
    · exact Or.inr ⟨hei', hdi'⟩
    · exact (hed (hei'.trans hdi'.symm)).elim
  have hj :
      (e = K.faceEdge t j ∧ d = K.faceEdge t (j + 2)) ∨
        (e = K.faceEdge t (j + 2) ∧ d = K.faceEdge t j) := by
    rcases hej' with hej' | hej' <;> rcases hdj' with hdj' | hdj'
    · exact (hed (hej'.trans hdj'.symm)).elim
    · exact Or.inl ⟨hej', hdj'⟩
    · exact Or.inr ⟨hej', hdj'⟩
    · exact (hed (hej'.trans hdj'.symm)).elim
  have hswap :
      ∀ a b : ZMod 3, a = b + 2 → a + 2 = b → False := by decide
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · have hij : i = j :=
      K.faceEdge_injective t (hi.1.symm.trans hj.1)
    rw [hij]
  · have h₁ : i = j + 2 :=
      K.faceEdge_injective t (hi.1.symm.trans hj.1)
    have h₂ : i + 2 = j :=
      K.faceEdge_injective t (hi.2.symm.trans hj.2)
    exact (hswap i j h₁ h₂).elim
  · have h₁ : j = i + 2 :=
      K.faceEdge_injective t (hj.1.symm.trans hi.1)
    have h₂ : j + 2 = i :=
      K.faceEdge_injective t (hj.2.symm.trans hi.2)
    exact (hswap j i h₁ h₂).elim
  · have hij : i + 2 = j + 2 :=
      K.faceEdge_injective t (hi.1.symm.trans hj.1)
    have : i = j := add_right_cancel hij
    rw [this]

/-- Within one old parent, the corner children incident to two distinct midpoint vertices form
a set of cardinality at most one. -/
theorem midpointCornerFaces_pair_card_le_one
    (t : K.Face) (e d : K.Edge) (hed : e ≠ d) :
    ((Finset.univ.image (K.midpointCornerFace t)).filter fun s ↦
      ({Sum.inr e, Sum.inr d} : Finset K.MidpointVertex) ⊆ s).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  obtain ⟨haCorner, haEdge⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbCorner, hbEdge⟩ := Finset.mem_filter.mp hb
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp haCorner
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hbCorner
  apply K.midpointCornerFace_eq_of_two_midpoints_mem t hed
  · exact haEdge (by simp)
  · exact haEdge (by simp)
  · exact hbEdge (by simp)
  · exact hbEdge (by simp)

/-- Inside one old parent, a refined edge joining two old-edge midpoints belongs to at most two
midpoint children (one corner and the central child). -/
theorem midpointFacesOver_midpoint_edge_card_le_two
    (t : K.Face) (e d : K.Edge) (hed : e ≠ d) :
    ((K.midpointFacesOver t).filter fun s ↦
      ({Sum.inr e, Sum.inr d} : Finset K.MidpointVertex) ⊆ s).card ≤ 2 := by
  rw [midpointFacesOver, Finset.filter_union]
  refine (Finset.card_union_le _ _).trans ?_
  have hcorner := K.midpointCornerFaces_pair_card_le_one t e d hed
  have hcentral :
      (({K.midpointCentralFace t} : Finset (Finset K.MidpointVertex)).filter fun s ↦
        ({Sum.inr e, Sum.inr d} : Finset K.MidpointVertex) ⊆ s).card ≤ 1 := by
    exact (Finset.card_filter_le _ _).trans (by simp)
  omega

/-- Globally, a mixed old-vertex/midpoint edge inherits the valence bound of its old edge. -/
theorem midpoint_mixed_edge_valence
    (hK : K.HasSurfaceEdgeValence) (v : K.Vertex) (e : K.Edge) :
    (K.midpointComplex.faces.filter fun s ↦
      ({Sum.inl v, Sum.inr e} : Finset K.MidpointVertex) ⊆ s).card ≤ 2 := by
  let I := K.midpointComplex.faces.filter fun s ↦
    ({Sum.inl v, Sum.inr e} : Finset K.MidpointVertex) ⊆ s
  let P := K.faces.filter fun t ↦ e.1 ⊆ t
  let parentMap : I → P := fun s ↦ by
    let sf : K.midpointComplex.Face :=
      ⟨s.1, (Finset.mem_filter.mp s.2).1⟩
    refine ⟨K.midpointParentFace sf, Finset.mem_filter.mpr ⟨
      (K.midpointParentFace sf).2, ?_⟩⟩
    exact K.edge_subset_parent_of_midpoint_mem
      (K.midpointParentFace sf) (K.midpointFace_mem_parent sf) e
      ((Finset.mem_filter.mp s.2).2 (by simp))
  have hinj : Function.Injective parentMap := by
    intro a b hab
    have hparent :
        K.midpointParentFace
            (⟨a.1, (Finset.mem_filter.mp a.2).1⟩ : K.midpointComplex.Face) =
          K.midpointParentFace
            (⟨b.1, (Finset.mem_filter.mp b.2).1⟩ : K.midpointComplex.Face) :=
      by
        have hparent := congrArg Subtype.val hab
        apply Subtype.ext
        simpa only [parentMap] using hparent
    apply Subtype.ext
    apply Finset.card_le_one_iff.mp
      (K.midpointFacesOver_mixed_edge_card_le_one
        (K.midpointParentFace
          (⟨a.1, (Finset.mem_filter.mp a.2).1⟩ : K.midpointComplex.Face)) v e)
    · exact Finset.mem_filter.mpr ⟨
        K.midpointFace_mem_parent
          (⟨a.1, (Finset.mem_filter.mp a.2).1⟩ : K.midpointComplex.Face),
        (Finset.mem_filter.mp a.2).2⟩
    · exact Finset.mem_filter.mpr ⟨by
        rw [hparent]
        exact K.midpointFace_mem_parent
          (⟨b.1, (Finset.mem_filter.mp b.2).1⟩ : K.midpointComplex.Face),
        (Finset.mem_filter.mp b.2).2⟩
  change I.card ≤ 2
  exact (Finset.card_le_card_of_injective hinj).trans (hK e.1 e.2)

/-- Equality-normalized form of `midpoint_mixed_edge_valence`, convenient when the two
endpoints of the unordered edge are presented in the opposite order. -/
theorem midpoint_mixed_edge_valence_of_eq
    (hK : K.HasSurfaceEdgeValence) (v : K.Vertex) (e : K.Edge)
    (q : Finset K.MidpointVertex)
    (hq : q = {Sum.inl v, Sum.inr e}) :
    (K.midpointComplex.faces.filter fun s ↦ q ⊆ s).card ≤ 2 := by
  subst q
  exact K.midpoint_mixed_edge_valence hK v e

/-- Globally, an edge joining two distinct old-edge midpoints is contained in at most two
midpoint children.  The two old edges determine a single parent triangle. -/
theorem midpoint_midpoint_edge_valence
    (e d : K.Edge) (hed : e ≠ d) :
    (K.midpointComplex.faces.filter fun s ↦
      ({Sum.inr e, Sum.inr d} : Finset K.MidpointVertex) ⊆ s).card ≤ 2 := by
  let I := K.midpointComplex.faces.filter fun s ↦
    ({Sum.inr e, Sum.inr d} : Finset K.MidpointVertex) ⊆ s
  by_cases hI : I.Nonempty
  · obtain ⟨s, hs⟩ := hI
    let sf : K.midpointComplex.Face :=
      ⟨s, (Finset.mem_filter.mp hs).1⟩
    let t := K.midpointParentFace sf
    let J := (K.midpointFacesOver t).filter fun q ↦
      ({Sum.inr e, Sum.inr d} : Finset K.MidpointVertex) ⊆ q
    have heT : e.1 ⊆ t.1 :=
      K.edge_subset_parent_of_midpoint_mem t (K.midpointFace_mem_parent sf) e
        ((Finset.mem_filter.mp hs).2 (by simp))
    have hdT : d.1 ⊆ t.1 :=
      K.edge_subset_parent_of_midpoint_mem t (K.midpointFace_mem_parent sf) d
        ((Finset.mem_filter.mp hs).2 (by simp))
    have hsub : I ⊆ J := by
      intro q hq
      let qf : K.midpointComplex.Face :=
        ⟨q, (Finset.mem_filter.mp hq).1⟩
      let u := K.midpointParentFace qf
      have heU : e.1 ⊆ u.1 :=
        K.edge_subset_parent_of_midpoint_mem u (K.midpointFace_mem_parent qf) e
          ((Finset.mem_filter.mp hq).2 (by simp))
      have hdU : d.1 ⊆ u.1 :=
        K.edge_subset_parent_of_midpoint_mem u (K.midpointFace_mem_parent qf) d
          ((Finset.mem_filter.mp hq).2 (by simp))
      have htu : t = u :=
        K.face_eq_of_two_edges_subset hed heT hdT heU hdU
      exact Finset.mem_filter.mpr ⟨by
        rw [htu]
        exact K.midpointFace_mem_parent qf,
        (Finset.mem_filter.mp hq).2⟩
    change I.card ≤ 2
    exact (Finset.card_le_card hsub).trans
      (K.midpointFacesOver_midpoint_edge_card_le_two t e d hed)
  · have hEmpty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    change I.card ≤ 2
    simp [hEmpty]

/-- Midpoint subdivision preserves the surface edge-valence bound. -/
theorem hasSurfaceEdgeValence_midpointComplex
    (hK : K.HasSurfaceEdgeValence) :
    K.midpointComplex.HasSurfaceEdgeValence := by
  intro q hq
  obtain ⟨a, b, hab, rfl⟩ :=
    Finset.card_eq_two.mp (K.midpointComplex.card_of_mem_edges hq)
  rcases a with v | e <;> rcases b with w | d
  · obtain ⟨s, hs, hsub⟩ :=
      K.midpointComplex.exists_face_of_mem_edges hq
    let sf : K.midpointComplex.Face := ⟨s, hs⟩
    have hvw : v = w :=
      K.oldVertex_eq_of_mem_midpointFace
        (K.midpointParentFace sf) (K.midpointFace_mem_parent sf)
        (hsub (Finset.mem_insert_self _ _))
        (hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    exact (hab (congrArg Sum.inl hvw)).elim
  · exact K.midpoint_mixed_edge_valence hK v d
  · exact K.midpoint_mixed_edge_valence_of_eq hK w e _
      (Finset.pair_comm _ _)
  · exact K.midpoint_midpoint_edge_valence e d fun hed ↦
      hab (congrArg Sum.inr hed)

theorem midpointRecoverOld_corner
    (t : K.Face) (i : ZMod 3) {x : K.MidpointVertex → ℝ}
    (hx : ∀ w ∉ K.midpointCornerFace t i, x w = 0)
    (hx0 : ∀ w, 0 ≤ x w) (hx1 : ∑ w, x w = 1) (v : K.Vertex) :
    K.midpointRecoverOld (K.midpointEvalAffine x) v = x (Sum.inl v) := by
  have hsum : x (Sum.inl (K.faceVertex t i)) +
      x (Sum.inr (K.faceEdge t i)) + x (Sum.inr (K.faceEdge t (i + 2))) = 1 := by
    rw [K.sum_eq_sum_of_midpointSupport hx] at hx1
    simpa [midpointCornerFace, K.faceEdge_ne_add_two t i, add_assoc] using hx1
  by_cases hv : v ∈ t.1
  · obtain ⟨j, rfl⟩ := K.exists_faceVertex_eq_of_mem t hv
    rcases (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j with
      h | h | h
    · subst j
      unfold midpointRecoverOld
      rw [K.midpointEval_corner_self t i hx]
      have heq : 2 * (x (Sum.inl (K.faceVertex t i)) +
          (x (Sum.inr (K.faceEdge t i)) +
            x (Sum.inr (K.faceEdge t (i + 2)))) / 2) - 1 =
          x (Sum.inl (K.faceVertex t i)) := by linarith
      rw [heq, max_eq_left (hx0 _)]
    · subst j
      unfold midpointRecoverOld
      rw [K.midpointEval_corner_next t i hx]
      have hle : x (Sum.inr (K.faceEdge t i)) ≤ 1 := by
        linarith [hx0 (Sum.inl (K.faceVertex t i)),
          hx0 (Sum.inr (K.faceEdge t (i + 2)))]
      rw [max_eq_right (by linarith)]
      exact (hx (Sum.inl (K.faceVertex t (i + 1))) (by
        simp [midpointCornerFace, (K.faceVertex_ne_next t i).symm])).symm
    · subst j
      unfold midpointRecoverOld
      rw [K.midpointEval_corner_prev t i hx]
      have hle : x (Sum.inr (K.faceEdge t (i + 2))) ≤ 1 := by
        linarith [hx0 (Sum.inl (K.faceVertex t i)),
          hx0 (Sum.inr (K.faceEdge t i))]
      rw [max_eq_right (by linarith)]
      exact (hx (Sum.inl (K.faceVertex t (i + 2))) (by
        simp [midpointCornerFace, (K.faceVertex_ne_add_two t i).symm])).symm
  · have hface : K.midpointCornerFace t i ∈ K.midpointFacesOver t := by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hp : K.midpointEvalAffine x v = 0 :=
      K.midpointEvalAffine_support t hface hx hv
    unfold midpointRecoverOld
    rw [hp]
    simp only [mul_zero, zero_sub, max_eq_right (by norm_num : (-1 : ℝ) ≤ 0)]
    have hvi : v ≠ K.faceVertex t i :=
      fun h => hv (by rw [h]; exact K.faceVertex_mem t i)
    exact (hx (Sum.inl v) (by simp [midpointCornerFace, hvi])).symm

theorem midpointRecoverOld_central
    (t : K.Face) {x : K.MidpointVertex → ℝ}
    (hx : ∀ w ∉ K.midpointCentralFace t, x w = 0)
    (hx0 : ∀ w, 0 ≤ x w) (hx1 : ∑ w, x w = 1) (v : K.Vertex) :
    K.midpointRecoverOld (K.midpointEvalAffine x) v = x (Sum.inl v) := by
  by_cases hv : v ∈ t.1
  · obtain ⟨i, rfl⟩ := K.exists_faceVertex_eq_of_mem t hv
    have hsum : x (Sum.inr (K.faceEdge t i)) +
        x (Sum.inr (K.faceEdge t (i + 1))) +
        x (Sum.inr (K.faceEdge t (i + 2))) = 1 := by
      rw [K.sum_eq_sum_of_midpointSupport hx] at hx1
      have he01 : K.faceEdge t i ≠ K.faceEdge t (i + 1) := K.faceEdge_ne_next t i
      have he02 : K.faceEdge t i ≠ K.faceEdge t (i + 2) := K.faceEdge_ne_add_two t i
      have he12 : K.faceEdge t (i + 1) ≠ K.faceEdge t (i + 2) := by
        simpa only [zmod3_add_one_add_one] using K.faceEdge_ne_next t (i + 1)
      simpa [K.midpointCentralFace_eq t i, he01, he02, he12, add_assoc] using hx1
    unfold midpointRecoverOld
    rw [K.midpointEval_central_coord t i hx]
    have hnonpos : 2 * ((x (Sum.inr (K.faceEdge t i)) +
        x (Sum.inr (K.faceEdge t (i + 2)))) / 2) - 1 ≤ 0 := by
      linarith [hx0 (Sum.inr (K.faceEdge t (i + 1)))]
    rw [max_eq_right hnonpos]
    exact (hx (Sum.inl (K.faceVertex t i)) (by simp [midpointCentralFace])).symm
  · have hface : K.midpointCentralFace t ∈ K.midpointFacesOver t :=
      Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hp : K.midpointEvalAffine x v = 0 :=
      K.midpointEvalAffine_support t hface hx hv
    unfold midpointRecoverOld
    rw [hp]
    simp only [mul_zero, zero_sub,
      max_eq_right (by norm_num : (-1 : ℝ) ≤ 0)]
    exact (hx (Sum.inl v) (by simp [midpointCentralFace])).symm

theorem midpointRecoverEdge_corner
    (t : K.Face) (i : ZMod 3) {x : K.MidpointVertex → ℝ}
    (hx : ∀ w ∉ K.midpointCornerFace t i, x w = 0)
    (hx0 : ∀ w, 0 ≤ x w) (hx1 : ∑ w, x w = 1) (e : K.Edge) :
    K.midpointRecoverEdge (K.midpointEvalAffine x) e = x (Sum.inr e) := by
  let A := x (Sum.inl (K.faceVertex t i))
  let B := x (Sum.inr (K.faceEdge t i))
  let C := x (Sum.inr (K.faceEdge t (i + 2)))
  have hsum : A + B + C = 1 := by
    rw [K.sum_eq_sum_of_midpointSupport hx] at hx1
    simpa [A, B, C, midpointCornerFace, K.faceEdge_ne_add_two t i, add_assoc] using hx1
  have hA0 : 0 ≤ A := hx0 _
  have hB0 : 0 ≤ B := hx0 _
  have hC0 : 0 ≤ C := hx0 _
  by_cases het : e.1 ⊆ t.1
  · obtain ⟨j, rfl⟩ := K.exists_faceEdge_eq_of_subset t e het
    rcases (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j with
      h | h | h
    · subst j
      rw [K.midpointRecoverEdge_faceEdge, K.midpointEval_corner_self t i hx,
        K.midpointEval_corner_next t i hx]
      have hpSelf : 2 * (A + (B + C) / 2) = 1 + A := by linarith
      have hthird : 2 * (A + (B + C) / 2 + B / 2) - 1 = A + B := by linarith
      change max 0 (min (2 * (A + (B + C) / 2))
        (min (2 * (B / 2))
          (2 * (A + (B + C) / 2 + B / 2) - 1))) = B
      rw [hpSelf, show 2 * (B / 2) = B by ring, hthird]
      have hinner : min B (A + B) = B := min_eq_left (by linarith)
      rw [hinner, min_eq_right (by linarith), max_eq_right hB0]
    · subst j
      rw [K.midpointRecoverEdge_faceEdge, K.midpointEval_corner_next t i hx]
      simp only [zmod3_add_one_add_one]
      rw [
        K.midpointEval_corner_prev t i hx]
      have hthird : 2 * (B / 2 + C / 2) - 1 = -A := by linarith
      rw [hthird]
      have hnonpos : min (2 * (B / 2)) (min (2 * (C / 2)) (-A)) ≤ 0 :=
        (min_le_right _ _).trans ((min_le_right _ _).trans (neg_nonpos.mpr hA0))
      rw [max_eq_left hnonpos]
      exact (hx (Sum.inr (K.faceEdge t (i + 1))) (by
        have h10 : K.faceEdge t (i + 1) ≠ K.faceEdge t i :=
          (K.faceEdge_ne_next t i).symm
        have h12 : K.faceEdge t (i + 1) ≠ K.faceEdge t (i + 2) := by
          simpa only [zmod3_add_one_add_one] using K.faceEdge_ne_next t (i + 1)
        simp [midpointCornerFace, h10, h12])).symm
    · subst j
      rw [K.midpointRecoverEdge_faceEdge, K.midpointEval_corner_prev t i hx]
      simp only [zmod3_add_two_add_one]
      rw [
        K.midpointEval_corner_self t i hx]
      have hpSelf : 2 * (A + (B + C) / 2) = 1 + A := by linarith
      have hthird : 2 * (C / 2 + (A + (B + C) / 2)) - 1 = A + C := by linarith
      change max 0 (min (2 * (C / 2))
        (min (2 * (A + (B + C) / 2))
          (2 * (C / 2 + (A + (B + C) / 2)) - 1))) = C
      rw [show 2 * (C / 2) = C by ring, hpSelf, hthird]
      have hinner : min (1 + A) (A + C) = A + C := min_eq_right (by linarith)
      rw [hinner, min_eq_left (by linarith), max_eq_right hC0]
  · have hnotmem : Sum.inr e ∉ K.midpointCornerFace t i := by
      simp only [midpointCornerFace, Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨Sum.inr_ne_inl, ?_, ?_⟩
      · intro heq
        apply het
        rw [Sum.inr.inj heq]
        exact K.faceEdge_subset_face t i
      · intro heq
        apply het
        rw [Sum.inr.inj heq]
        exact K.faceEdge_subset_face t (i + 2)
    have hface : K.midpointCornerFace t i ∈ K.midpointFacesOver t := by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hend : K.edgeFirst e ∉ t.1 ∨ K.edgeSecond e ∉ t.1 := by
      by_contra h
      simp only [not_or, not_not] at h
      apply het
      rw [K.edge_eq_pair]
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact h.1
      · exact h.2
    rw [midpointRecoverEdge]
    rcases hend with hfirst | hsecond
    · rw [K.midpointEvalAffine_support t hface hx hfirst, mul_zero]
      have hle : min 0
          (min (2 * K.midpointEvalAffine x (K.edgeSecond e))
            (2 * (0 + K.midpointEvalAffine x (K.edgeSecond e)) - 1)) ≤ 0 :=
        min_le_left _ _
      rw [max_eq_left hle]
      exact (hx (Sum.inr e) hnotmem).symm
    · rw [K.midpointEvalAffine_support t hface hx hsecond, mul_zero]
      have hle : min 0
          (2 * (K.midpointEvalAffine x (K.edgeFirst e) + 0) - 1) ≤ 0 := min_le_left _ _
      have hle' : min (2 * K.midpointEvalAffine x (K.edgeFirst e))
          (min 0 (2 * (K.midpointEvalAffine x (K.edgeFirst e) + 0) - 1)) ≤ 0 :=
        (min_le_right _ _).trans hle
      rw [max_eq_left hle']
      exact (hx (Sum.inr e) hnotmem).symm

theorem midpointRecoverEdge_central
    (t : K.Face) {x : K.MidpointVertex → ℝ}
    (hx : ∀ w ∉ K.midpointCentralFace t, x w = 0)
    (hx0 : ∀ w, 0 ≤ x w) (hx1 : ∑ w, x w = 1) (e : K.Edge) :
    K.midpointRecoverEdge (K.midpointEvalAffine x) e = x (Sum.inr e) := by
  by_cases het : e.1 ⊆ t.1
  · obtain ⟨i, rfl⟩ := K.exists_faceEdge_eq_of_subset t e het
    let A := x (Sum.inr (K.faceEdge t i))
    let B := x (Sum.inr (K.faceEdge t (i + 1)))
    let C := x (Sum.inr (K.faceEdge t (i + 2)))
    have hsum : A + B + C = 1 := by
      rw [K.sum_eq_sum_of_midpointSupport hx] at hx1
      have he01 : K.faceEdge t i ≠ K.faceEdge t (i + 1) := K.faceEdge_ne_next t i
      have he02 : K.faceEdge t i ≠ K.faceEdge t (i + 2) := K.faceEdge_ne_add_two t i
      have he12 : K.faceEdge t (i + 1) ≠ K.faceEdge t (i + 2) := by
        simpa only [zmod3_add_one_add_one] using K.faceEdge_ne_next t (i + 1)
      simpa [A, B, C, K.midpointCentralFace_eq t i, he01, he02, he12,
        add_assoc] using hx1
    have hA0 : 0 ≤ A := hx0 _
    have hB0 : 0 ≤ B := hx0 _
    have hC0 : 0 ≤ C := hx0 _
    rw [K.midpointRecoverEdge_faceEdge, K.midpointEval_central_coord t i hx]
    have hnext := K.midpointEval_central_coord t (i + 1) hx
    simp only [zmod3_add_one_add_two] at hnext
    rw [hnext]
    change max 0 (min (2 * ((A + C) / 2))
      (min (2 * ((B + A) / 2))
        (2 * ((A + C) / 2 + (B + A) / 2) - 1))) = A
    have hfirst : 2 * ((A + C) / 2) = A + C := by ring
    have hsecond : 2 * ((B + A) / 2) = B + A := by ring
    have hthird : 2 * ((A + C) / 2 + (B + A) / 2) - 1 = A := by linarith
    rw [hfirst, hsecond, hthird]
    have hinner : min (B + A) A = A := min_eq_right (by linarith)
    rw [hinner, min_eq_right (by linarith), max_eq_right hA0]
  · have hnotmem : Sum.inr e ∉ K.midpointCentralFace t := by
      intro he
      rw [midpointCentralFace] at he
      obtain ⟨j, -, heq⟩ := Finset.mem_image.mp he
      apply het
      rw [← Sum.inr.inj heq]
      exact K.faceEdge_subset_face t j
    have hface : K.midpointCentralFace t ∈ K.midpointFacesOver t :=
      Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hend : K.edgeFirst e ∉ t.1 ∨ K.edgeSecond e ∉ t.1 := by
      by_contra h
      simp only [not_or, not_not] at h
      apply het
      rw [K.edge_eq_pair]
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact h.1
      · exact h.2
    rw [midpointRecoverEdge]
    rcases hend with hfirst | hsecond
    · rw [K.midpointEvalAffine_support t hface hx hfirst, mul_zero]
      have hle : min 0
          (min (2 * K.midpointEvalAffine x (K.edgeSecond e))
            (2 * (0 + K.midpointEvalAffine x (K.edgeSecond e)) - 1)) ≤ 0 :=
        min_le_left _ _
      rw [max_eq_left hle]
      exact (hx (Sum.inr e) hnotmem).symm
    · rw [K.midpointEvalAffine_support t hface hx hsecond, mul_zero]
      have hle : min 0
          (2 * (K.midpointEvalAffine x (K.edgeFirst e) + 0) - 1) ≤ 0 := min_le_left _ _
      have hle' : min (2 * K.midpointEvalAffine x (K.edgeFirst e))
          (min 0 (2 * (K.midpointEvalAffine x (K.edgeFirst e) + 0) - 1)) ≤ 0 :=
        (min_le_right _ _).trans hle
      rw [max_eq_left hle']
      exact (hx (Sum.inr e) hnotmem).symm

/-- Midpoint coordinates are uniquely recovered from their old barycentric image. -/
theorem midpointRecover_midpointEvalAffine (x : K.midpointComplex.realization) :
    K.midpointRecover (K.midpointEvalAffine x.1) = x.1 := by
  obtain ⟨s, hs, hxs⟩ := x.2.2
  obtain ⟨t, hst⟩ := K.exists_parentFace_of_mem_midpointFaces hs
  have hst' : s ∈ K.midpointFacesOver t := hst
  have hcases : s ∈ Finset.univ.image (K.midpointCornerFace t) ∨
      s ∈ {K.midpointCentralFace t} := Finset.mem_union.mp hst'
  funext w
  rcases hcases with hcorner | hcentral
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hcorner
    rcases w with v | e
    · exact K.midpointRecoverOld_corner t i hxs x.2.1.1 x.2.1.2 v
    · exact K.midpointRecoverEdge_corner t i hxs x.2.1.1 x.2.1.2 e
  · rw [Finset.mem_singleton.mp hcentral] at hxs
    rcases w with v | e
    · exact K.midpointRecoverOld_central t hxs x.2.1.1 x.2.1.2 v
    · exact K.midpointRecoverEdge_central t hxs x.2.1.1 x.2.1.2 e

theorem injective_midpointEvalAffine_on_realization :
    Function.Injective (fun x : K.midpointComplex.realization => K.midpointEvalAffine x.1) := by
  intro x y hxy
  apply Subtype.ext
  exact (K.midpointRecover_midpointEvalAffine x).symm.trans
    ((congrArg K.midpointRecover hxy).trans (K.midpointRecover_midpointEvalAffine y))

theorem face_eq_image_faceVertex (t : K.Face) :
    t.1 = Finset.univ.image (K.faceVertex t) := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, rfl⟩ := K.exists_faceVertex_eq_of_mem t hv
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  · intro hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    exact K.faceVertex_mem t i

theorem sum_faceVertex_coords (t : K.Face) (p : K.Vertex → ℝ)
    (hsupp : ∀ v ∉ t.1, p v = 0) (hsum : ∑ v, p v = 1) (i : ZMod 3) :
    p (K.faceVertex t i) + p (K.faceVertex t (i + 1)) +
      p (K.faceVertex t (i + 2)) = 1 := by
  have hsum' : ∑ v ∈ t.1, p v = 1 := by
    rw [← hsum]
    exact Finset.sum_subset (Finset.subset_univ t.1) (fun v _ hv => hsupp v hv)
  rw [K.face_eq_image_faceVertex t, Finset.sum_image] at hsum'
  · have hu : (Finset.univ : Finset (ZMod 3)) = {i, i + 1, i + 2} := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      exact (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j
    rw [hu] at hsum'
    have hi01 : i ≠ i + 1 := (by decide : ∀ i : ZMod 3, i ≠ i + 1) i
    have hi02 : i ≠ i + 2 := (by decide : ∀ i : ZMod 3, i ≠ i + 2) i
    have hi12 : i + 1 ≠ i + 2 := (by decide : ∀ i : ZMod 3, i + 1 ≠ i + 2) i
    simpa [hi01, hi02, hi12, add_assoc] using hsum'
  · exact fun a _ b _ hab => K.faceVertex_injective t hab

/-- Explicit inverse coordinates in a corner triangle. -/
noncomputable def midpointCornerWeights (t : K.Face) (i : ZMod 3)
    (p : K.Vertex → ℝ) : K.MidpointVertex → ℝ := fun w =>
  if w = Sum.inl (K.faceVertex t i) then 2 * p (K.faceVertex t i) - 1
  else if w = Sum.inr (K.faceEdge t i) then 2 * p (K.faceVertex t (i + 1))
  else if w = Sum.inr (K.faceEdge t (i + 2)) then 2 * p (K.faceVertex t (i + 2))
  else 0

@[simp] theorem midpointCornerWeights_old (t : K.Face) (i : ZMod 3)
    (p : K.Vertex → ℝ) :
    K.midpointCornerWeights t i p (Sum.inl (K.faceVertex t i)) =
      2 * p (K.faceVertex t i) - 1 := by
  simp [midpointCornerWeights]

@[simp] theorem midpointCornerWeights_nextEdge (t : K.Face) (i : ZMod 3)
    (p : K.Vertex → ℝ) :
    K.midpointCornerWeights t i p (Sum.inr (K.faceEdge t i)) =
      2 * p (K.faceVertex t (i + 1)) := by
  simp [midpointCornerWeights]

@[simp] theorem midpointCornerWeights_prevEdge (t : K.Face) (i : ZMod 3)
    (p : K.Vertex → ℝ) :
    K.midpointCornerWeights t i p (Sum.inr (K.faceEdge t (i + 2))) =
      2 * p (K.faceVertex t (i + 2)) := by
  simp [midpointCornerWeights,
    (K.faceEdge_ne_add_two t i).symm]

theorem midpointCornerWeights_support (t : K.Face) (i : ZMod 3)
    (p : K.Vertex → ℝ) :
    ∀ w ∉ K.midpointCornerFace t i, K.midpointCornerWeights t i p w = 0 := by
  intro w hw
  simp only [midpointCornerWeights]
  split_ifs with h₁ h₂ h₃
  · exact (hw (by simp [midpointCornerFace, h₁])).elim
  · exact (hw (by simp [midpointCornerFace, h₂])).elim
  · exact (hw (by simp [midpointCornerFace, h₃])).elim
  · rfl

theorem midpointCornerWeights_nonneg (t : K.Face) (i : ZMod 3)
    (p : K.Vertex → ℝ) (hp0 : ∀ v, 0 ≤ p v)
    (hi : (2 : ℝ)⁻¹ ≤ p (K.faceVertex t i)) :
    ∀ w, 0 ≤ K.midpointCornerWeights t i p w := by
  intro w
  simp only [midpointCornerWeights]
  split_ifs <;> linarith [hp0 (K.faceVertex t (i + 1)),
    hp0 (K.faceVertex t (i + 2))]

theorem sum_midpointCornerWeights (t : K.Face) (i : ZMod 3)
    (p : K.Vertex → ℝ)
    (hsum : p (K.faceVertex t i) + p (K.faceVertex t (i + 1)) +
      p (K.faceVertex t (i + 2)) = 1) :
    ∑ w, K.midpointCornerWeights t i p w = 1 := by
  rw [K.sum_eq_sum_of_midpointSupport (K.midpointCornerWeights_support t i p)]
  simp [midpointCornerFace, K.faceEdge_ne_add_two t i]
  linarith

/-- Explicit inverse coordinates in the central triangle. -/
noncomputable def midpointCentralWeights (t : K.Face) (p : K.Vertex → ℝ) :
    K.MidpointVertex → ℝ := fun w =>
  ∑ i : ZMod 3, if w = Sum.inr (K.faceEdge t i) then
    1 - 2 * p (K.faceVertex t (i + 2)) else 0

@[simp] theorem midpointCentralWeights_edge (t : K.Face) (p : K.Vertex → ℝ)
    (i : ZMod 3) :
    K.midpointCentralWeights t p (Sum.inr (K.faceEdge t i)) =
      1 - 2 * p (K.faceVertex t (i + 2)) := by
  rw [midpointCentralWeights]
  calc
    (∑ j : ZMod 3, if Sum.inr (K.faceEdge t i) = Sum.inr (K.faceEdge t j) then
        1 - 2 * p (K.faceVertex t (j + 2)) else 0) =
        (if Sum.inr (K.faceEdge t i) = Sum.inr (K.faceEdge t i) then
          1 - 2 * p (K.faceVertex t (i + 2)) else 0) := by
      apply Fintype.sum_eq_single i
      intro j hji
      rw [if_neg]
      intro h
      exact hji (K.faceEdge_injective t (Sum.inr.inj h).symm)
    _ = 1 - 2 * p (K.faceVertex t (i + 2)) := by simp

theorem midpointCentralWeights_support (t : K.Face) (p : K.Vertex → ℝ) :
    ∀ w ∉ K.midpointCentralFace t, K.midpointCentralWeights t p w = 0 := by
  intro w hw
  rw [midpointCentralWeights]
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg]
  intro h
  apply hw
  rw [midpointCentralFace]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h.symm⟩

theorem midpointCentralWeights_nonneg (t : K.Face) (p : K.Vertex → ℝ)
    (hle : ∀ i : ZMod 3, p (K.faceVertex t i) ≤ (2 : ℝ)⁻¹) :
    ∀ w, 0 ≤ K.midpointCentralWeights t p w := by
  intro w
  rw [midpointCentralWeights]
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · linarith [hle (i + 2)]
  · rfl

theorem sum_midpointCentralWeights (t : K.Face) (p : K.Vertex → ℝ)
    (hsum : p (K.faceVertex t 0) + p (K.faceVertex t 1) +
      p (K.faceVertex t 2) = 1) :
    ∑ w, K.midpointCentralWeights t p w = 1 := by
  rw [K.sum_eq_sum_of_midpointSupport (K.midpointCentralWeights_support t p),
    K.midpointCentralFace_eq t 0]
  have he01 : K.faceEdge t 0 ≠ K.faceEdge t 1 := K.faceEdge_ne_next t 0
  have he02 : K.faceEdge t 0 ≠ K.faceEdge t 2 := K.faceEdge_ne_add_two t 0
  have he12 : K.faceEdge t 1 ≠ K.faceEdge t 2 := by
    have h12 : (1 : ZMod 3) + 1 = 2 := by decide
    simpa only [h12] using K.faceEdge_ne_next t 1
  rw [Finset.sum_insert (by simp [he01, he02]),
    Finset.sum_insert (by simp [he12]), Finset.sum_singleton,
    K.midpointCentralWeights_edge, K.midpointCentralWeights_edge,
    K.midpointCentralWeights_edge]
  simp only [zero_add]
  have h12 : (1 : ZMod 3) + 2 = 0 := by decide
  have h22 : (2 : ZMod 3) + 2 = 1 := by decide
  rw [h12, h22]
  linarith

/-- The four named midpoint children of an old face cover that old face. -/
theorem exists_midpoint_preimage_in_face (T : K.Face) (p : K.realization)
    (hpt : p ∈ K.faceCarrier T.1) :
    ∃ (x : K.midpointComplex.realization) (s : Finset K.MidpointVertex),
      s ∈ K.midpointFacesOver T ∧ x ∈ K.midpointComplex.faceCarrier s ∧
        K.midpointEvalAffine x.1 = p.1 := by
  have hsum (i : ZMod 3) : p.1 (K.faceVertex T i) +
      p.1 (K.faceVertex T (i + 1)) + p.1 (K.faceVertex T (i + 2)) = 1 :=
    K.sum_faceVertex_coords T p.1 hpt p.2.1.2 i
  by_cases hhigh : ∃ i : ZMod 3, (2 : ℝ)⁻¹ ≤ p.1 (K.faceVertex T i)
  · obtain ⟨i, hi⟩ := hhigh
    let y := K.midpointCornerWeights T i p.1
    have hy0 : ∀ w, 0 ≤ y w := K.midpointCornerWeights_nonneg T i p.1 p.2.1.1 hi
    have hy1 : ∑ w, y w = 1 := K.sum_midpointCornerWeights T i p.1 (hsum i)
    have hySupp : ∀ w ∉ K.midpointCornerFace T i, y w = 0 :=
      K.midpointCornerWeights_support T i p.1
    have hfaceOver : K.midpointCornerFace T i ∈ K.midpointFacesOver T := by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hface : K.midpointCornerFace T i ∈ K.midpointComplex.faces := by
      change K.midpointCornerFace T i ∈ K.midpointFaces
      rw [midpointFaces]
      exact Finset.mem_biUnion.mpr ⟨T, by simp, hfaceOver⟩
    let z : K.midpointComplex.realization :=
      ⟨y, ⟨hy0, hy1⟩, K.midpointCornerFace T i, hface, hySupp⟩
    refine ⟨z, K.midpointCornerFace T i, hfaceOver, hySupp, ?_⟩
    change K.midpointEvalAffine y = p.1
    funext v
    by_cases hv : v ∈ T.1
    · obtain ⟨j, rfl⟩ := K.exists_faceVertex_eq_of_mem T hv
      rcases (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j with
        h | h | h
      · subst j
        rw [K.midpointEval_corner_self T i hySupp]
        simp only [y, K.midpointCornerWeights_old, K.midpointCornerWeights_nextEdge,
          K.midpointCornerWeights_prevEdge]
        linarith [hsum i]
      · subst j
        rw [K.midpointEval_corner_next T i hySupp]
        simp [y]
      · subst j
        rw [K.midpointEval_corner_prev T i hySupp]
        simp [y]
    · rw [K.midpointEvalAffine_support T hfaceOver hySupp hv, hpt v hv]
  · have hle : ∀ i : ZMod 3, p.1 (K.faceVertex T i) ≤ (2 : ℝ)⁻¹ := by
      intro i
      exact le_of_not_ge (fun hi => hhigh ⟨i, hi⟩)
    let y := K.midpointCentralWeights T p.1
    have hy0 : ∀ w, 0 ≤ y w := K.midpointCentralWeights_nonneg T p.1 hle
    have hy1 : ∑ w, y w = 1 := K.sum_midpointCentralWeights T p.1 (hsum 0)
    have hySupp : ∀ w ∉ K.midpointCentralFace T, y w = 0 :=
      K.midpointCentralWeights_support T p.1
    have hfaceOver : K.midpointCentralFace T ∈ K.midpointFacesOver T :=
      Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hface : K.midpointCentralFace T ∈ K.midpointComplex.faces := by
      change K.midpointCentralFace T ∈ K.midpointFaces
      rw [midpointFaces]
      exact Finset.mem_biUnion.mpr ⟨T, by simp, hfaceOver⟩
    let z : K.midpointComplex.realization :=
      ⟨y, ⟨hy0, hy1⟩, K.midpointCentralFace T, hface, hySupp⟩
    refine ⟨z, K.midpointCentralFace T, hfaceOver, hySupp, ?_⟩
    change K.midpointEvalAffine y = p.1
    funext v
    by_cases hv : v ∈ T.1
    · obtain ⟨i, rfl⟩ := K.exists_faceVertex_eq_of_mem T hv
      rw [K.midpointEval_central_coord T i hySupp]
      simp only [y, K.midpointCentralWeights_edge]
      have hcycle : i + 2 + 2 = i + 1 := zmod3_add_two_add_two i
      rw [hcycle]
      linarith [hsum i]
    · rw [K.midpointEvalAffine_support T hfaceOver hySupp hv, hpt v hv]

/-- The four midpoint triangles cover every old face, hence the whole realization. -/
theorem surjective_midpointEvalAffine_on_realization :
    ∀ p : K.realization, ∃ x : K.midpointComplex.realization,
      K.midpointEvalAffine x.1 = p.1 := by
  intro p
  obtain ⟨t, ht, hpt⟩ := p.2.2
  obtain ⟨x, s, -, -, hx⟩ :=
    K.exists_midpoint_preimage_in_face ⟨t, ht⟩ p hpt
  exact ⟨x, hx⟩

theorem midpointEvalAffine_nonneg (x : K.midpointComplex.realization) (v : K.Vertex) :
    0 ≤ K.midpointEvalAffine x.1 v := by
  classical
  rw [show K.midpointEvalAffine x.1 = ∑ w, x.1 w • K.midpointPosition w from
    K.midpointEvalAffine_apply x.1, Finset.sum_apply]
  exact Finset.sum_nonneg fun w _ =>
    mul_nonneg (x.2.1.1 w) (K.midpointPosition_nonneg w v)

theorem sum_midpointEvalAffine (x : K.midpointComplex.realization) :
    ∑ v, K.midpointEvalAffine x.1 v = 1 := by
  classical
  rw [show K.midpointEvalAffine x.1 = ∑ w, x.1 w • K.midpointPosition w from
    K.midpointEvalAffine_apply x.1]
  simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    ∑ v, ∑ w, x.1 w * K.midpointPosition w v =
        ∑ w, ∑ v, x.1 w * K.midpointPosition w v := Finset.sum_comm
    _ = ∑ w, x.1 w * ∑ v, K.midpointPosition w v := by
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.mul_sum]
    _ = ∑ w, x.1 w := by
      apply Finset.sum_congr rfl
      intro w _
      rw [show ∑ v, K.midpointPosition w v = 1 from K.sum_midpointPosition w]
      exact mul_one _
    _ = 1 := x.2.1.2

/-- Canonical affine map from the midpoint realization into the old realization. -/
noncomputable def midpointEval (x : K.midpointComplex.realization) : K.realization := by
  refine ⟨K.midpointEvalAffine x.1,
    ⟨K.midpointEvalAffine_nonneg x, K.sum_midpointEvalAffine x⟩, ?_⟩
  obtain ⟨s, hs, hxs⟩ := x.2.2
  obtain ⟨t, hst⟩ := K.exists_parentFace_of_mem_midpointFaces hs
  exact ⟨t.1, t.2, fun v hv => K.midpointEvalAffine_support t hst hxs hv⟩

@[simp] theorem midpointEval_val (x : K.midpointComplex.realization) :
    (K.midpointEval x).1 = K.midpointEvalAffine x.1 := rfl

theorem continuous_midpointEval : Continuous K.midpointEval := by
  apply Continuous.subtype_mk
  exact K.midpointEvalAffine.continuous_of_finiteDimensional.comp continuous_subtype_val

theorem midpointEval_mem_parentFace
    (t : K.Face) {s : Finset K.MidpointVertex} (hs : s ∈ K.midpointFacesOver t)
    (x : K.midpointComplex.realization) (hx : x ∈ K.midpointComplex.faceCarrier s) :
    K.midpointEval x ∈ K.faceCarrier t.1 := by
  intro v hv
  exact K.midpointEvalAffine_support t hs hx hv

theorem midpointEval_affineOnFace
    {s : Finset K.MidpointVertex} (_ : s ∈ K.midpointFaces) :
    ∃ a : (K.MidpointVertex → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ),
      ∀ x : K.midpointComplex.realization,
        x ∈ K.midpointComplex.faceCarrier s → (K.midpointEval x).1 = a x.1 :=
  ⟨K.midpointEvalAffine, fun _ _ => rfl⟩

theorem injective_midpointEval : Function.Injective K.midpointEval := by
  intro x y hxy
  apply K.injective_midpointEvalAffine_on_realization
  exact congrArg Subtype.val hxy

theorem surjective_midpointEval : Function.Surjective K.midpointEval := by
  intro p
  obtain ⟨x, hx⟩ := K.surjective_midpointEvalAffine_on_realization p
  exact ⟨x, Subtype.ext hx⟩

/-- The canonical midpoint realization map is a homeomorphism. -/
noncomputable def midpointHomeomorph :
    K.midpointComplex.realization ≃ₜ K.realization :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective K.midpointEval
      ⟨K.injective_midpointEval, K.surjective_midpointEval⟩)
    K.continuous_midpointEval

@[simp] theorem midpointHomeomorph_apply (x : K.midpointComplex.realization) :
    K.midpointHomeomorph x = K.midpointEval x := rfl

/-- The intrinsic 1-to-4 midpoint subdivision, with its canonical faithful realization map. -/
noncomputable def midpointSubdivision : K.Subdivision where
  refined := K.midpointComplex
  homeo := K.midpointHomeomorph
  affineOnFace := by
    intro s hs
    exact K.midpointEval_affineOnFace hs
  subordinate := by
    intro s hs
    obtain ⟨t, hst⟩ := K.exists_parentFace_of_mem_midpointFaces hs
    exact ⟨t.1, t.2, fun x hx => K.midpointEval_mem_parentFace t hst x hx⟩

@[simp] theorem midpointSubdivision_refined :
    K.midpointSubdivision.refined = K.midpointComplex := rfl

theorem midpointSubdivision_homeo_apply (x : K.midpointComplex.realization) :
    K.midpointSubdivision.homeo x = K.midpointEval x := rfl

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
