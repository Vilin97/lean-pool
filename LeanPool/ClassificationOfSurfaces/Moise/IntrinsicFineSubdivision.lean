/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicMidpointSubdivision
import LeanPool.ClassificationOfSurfaces.Moise.FrontierGlue

/-!
# Fine subdivisions of intrinsic two-complexes

The midpoint subdivision is quantitatively faithful: on every iteration, the image diameter of
each new face is at most half that of its parent.  This supplies the finite fine-subdivision and
open-subcomplex extraction used in the compact form of Moise Chapter 8, Theorem 2.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex)

/-- The barycentric realization point at a specified vertex of a specified maximal face. -/
noncomputable def facePoint (t : K.Face) (v : t.1) : K.realization :=
  K.vertexPoint ⟨v.1, t.1, t.2, v.2⟩

@[simp] theorem facePoint_val (t : K.Face) (v : t.1) :
    (K.facePoint t v).1 = Pi.single v.1 1 := rfl

theorem facePoint_mem_faceCarrier (t : K.Face) (v : t.1) :
    K.facePoint t v ∈ K.faceCarrier t.1 :=
  (K.vertexPoint_mem_faceCarrier_iff ⟨v.1, t.1, t.2, v.2⟩ t.1).mpr v.2

theorem sum_face_coords (t : K.Face) (x : K.realization)
    (hx : x ∈ K.faceCarrier t.1) :
    ∑ v : t.1, x.1 v.1 = 1 := by
  rw [Finset.sum_coe_sort]
  calc
    ∑ v ∈ t.1, x.1 v = ∑ v, x.1 v :=
      Finset.sum_subset (Finset.subset_univ t.1) (fun v _ hv => hx v hv)
    _ = 1 := x.2.1.2

theorem face_affineCombination_eq (t : K.Face) (x : K.realization)
    (hx : x ∈ K.faceCarrier t.1) :
    (Finset.univ.affineCombination ℝ
      (fun v : t.1 => (K.facePoint t v).1) (fun v => x.1 v.1)) = x.1 := by
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (K.sum_face_coords t x hx)]
  funext w
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, K.facePoint_val]
  by_cases hw : w ∈ t.1
  · let v : t.1 := ⟨w, hw⟩
    rw [Finset.sum_eq_single v]
    · simp [v]
    · intro u _ huv
      have huw : u.1 ≠ w := fun h => huv (Subtype.ext h)
      simp [huw]
    · simp
  · have hxw : x.1 w = 0 := hx w hw
    rw [hxw]
    apply Finset.sum_eq_zero
    intro v _
    have hvw : v.1 ≠ w := fun h => hw (h ▸ v.2)
    simp [hvw]

/-- An affine image of a face lies in the convex hull of the images of its three vertices. -/
theorem affine_mem_convexHull_facePoints
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : K.Face) (a : (K.Vertex → ℝ) →ᵃ[ℝ] E)
    (x : K.realization) (hx : x ∈ K.faceCarrier t.1) :
    a x.1 ∈ convexHull ℝ
      (Set.range fun v : t.1 => a (K.facePoint t v).1) := by
  let w : t.1 → ℝ := fun v => x.1 v.1
  have hw0 : ∀ v ∈ (Finset.univ : Finset t.1), 0 ≤ w v :=
    fun v _ => x.2.1.1 v.1
  have hw1 : ∑ v ∈ (Finset.univ : Finset t.1), w v = 1 := by
    simpa only [Finset.sum_const_zero, w] using K.sum_face_coords t x hx
  have hmem := affineCombination_mem_convexHull hw0 hw1
    (v := fun v : t.1 => a (K.facePoint t v).1)
  have heq : a x.1 = (Finset.univ.affineCombination ℝ
      (fun v : t.1 => a (K.facePoint t v).1) w) := by
    calc
      a x.1 = a (Finset.univ.affineCombination ℝ
          (fun v : t.1 => (K.facePoint t v).1) w) := by
        rw [K.face_affineCombination_eq t x hx]
      _ = Finset.univ.affineCombination ℝ
          (a ∘ fun v : t.1 => (K.facePoint t v).1) w :=
        Finset.map_affineCombination _ _ _ hw1 a
      _ = Finset.univ.affineCombination ℝ
          (fun v : t.1 => a (K.facePoint t v).1) w := rfl
  rwa [← heq] at hmem

/-- Distances in an affine image of one face are bounded by a distance between vertex images. -/
theorem exists_facePoints_dist_ge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : K.Face) (a : (K.Vertex → ℝ) →ᵃ[ℝ] E)
    (x y : K.realization) (hx : x ∈ K.faceCarrier t.1)
    (hy : y ∈ K.faceCarrier t.1) :
    ∃ v w : t.1,
      dist (a x.1) (a y.1) ≤
        dist (a (K.facePoint t v).1) (a (K.facePoint t w).1) := by
  obtain ⟨p, ⟨v, rfl⟩, q, ⟨w, rfl⟩, hpq⟩ :=
    convexHull_exists_dist_ge2
      (K.affine_mem_convexHull_facePoints t a x hx)
      (K.affine_mem_convexHull_facePoints t a y hy)
  exact ⟨v, w, hpq⟩

/-- Affine maps preserve midpoints. -/
theorem affine_map_midpoint
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : E →ᵃ[ℝ] F) (x y : E) :
    a (midpoint ℝ x y) = midpoint ℝ (a x) (a y) := by
  let s : Finset Bool := {false, true}
  let p : Bool → E := fun b => if b then y else x
  let w : Bool → ℝ := fun _ => (2 : ℝ)⁻¹
  have hw : ∑ i ∈ s, w i = 1 := by simp [s, w]
  have hs : s.affineCombination ℝ p w = midpoint ℝ x y := by
    simp only [s, p, w, Finset.affineCombination_eq_linear_combination, hw,
      Finset.sum_insert, Finset.mem_singleton, Bool.false_eq_true, not_false_eq_true,
      Finset.sum_singleton, ite_false, ite_true, midpoint, AffineMap.lineMap_apply_module]
    congr 1
    norm_num
  have ht : s.affineCombination ℝ (a ∘ p) w = midpoint ℝ (a x) (a y) := by
    simp only [s, p, w, Finset.affineCombination_eq_linear_combination, hw,
      Finset.sum_insert, Finset.mem_singleton, Bool.false_eq_true, not_false_eq_true,
      Finset.sum_singleton, Function.comp_apply, ite_false, ite_true, midpoint,
      AffineMap.lineMap_apply_module]
    congr 1
    norm_num
  rw [← hs, Finset.map_affineCombination s p w hw a, ht]

theorem midpointPosition_faceEdge (t : K.Face) (i : ZMod 3) :
    K.midpointPosition (Sum.inr (K.faceEdge t i)) =
      midpoint ℝ (Pi.single (K.faceVertex t i) 1 : K.Vertex → ℝ)
        (Pi.single (K.faceVertex t (i + 1)) 1 : K.Vertex → ℝ) := by
  funext v
  by_cases hvi : v = K.faceVertex t i
  · subst v
    simp [midpoint, AffineMap.lineMap_apply_module, K.faceVertex_ne_next t i]
    norm_num
  · by_cases hvj : v = K.faceVertex t (i + 1)
    · subst v
      simp [midpoint, AffineMap.lineMap_apply_module, hvi]
    · have hvEdge : v ∉ (K.faceEdge t i).1 := by
        simp [hvi, hvj]
      simp [midpointPosition, midpoint, AffineMap.lineMap_apply_module, hvi, hvj]

theorem midpointEval_facePoint
    (s : K.midpointComplex.Face) (w : s.1) :
    (K.midpointEval (K.midpointComplex.facePoint s w)).1 =
      K.midpointPosition w.1 := by
  rw [K.midpointEval_val]
  rw [show K.midpointEvalAffine (K.midpointComplex.facePoint s w).1 =
      ∑ u : K.MidpointVertex,
        (K.midpointComplex.facePoint s w).1 u • K.midpointPosition u from
    K.midpointEvalAffine_apply (K.midpointComplex.facePoint s w).1]
  simp only [K.midpointComplex.facePoint_val]
  let q : K.MidpointVertex := w.1
  change (∑ u : K.MidpointVertex,
    (Pi.single q 1 : K.MidpointVertex → ℝ) u • K.midpointPosition u) =
      K.midpointPosition q
  rw [Finset.sum_eq_single q]
  · simp []
  · intro u _ huw
    simp [huw]
  · simp

theorem midpointEvalAffine_facePoint
    (s : K.midpointComplex.Face) (w : s.1) :
    K.midpointEvalAffine (K.midpointComplex.facePoint s w).1 =
      K.midpointPosition w.1 := by
  simpa only [← K.midpointEval_val] using K.midpointEval_facePoint s w

/-- A mesh bound measured after transporting each refined face into the original realization. -/
def Subdivision.MeshLE {K : IntrinsicTwoComplex} (R : K.Subdivision) (d : ℝ) : Prop :=
  ∀ t ∈ R.refined.faces, ∀ x ∈ R.refined.faceCarrier t,
    ∀ y ∈ R.refined.faceCarrier t, dist (R.homeo x) (R.homeo y) ≤ d

theorem Subdivision.meshLE_nonneg {K : IntrinsicTwoComplex} {R : K.Subdivision} {d : ℝ}
    (hR : R.MeshLE d) (t : R.refined.Face) : 0 ≤ d := by
  have htpos : 0 < t.1.card := by rw [R.refined.faces_card t.1 t.2]; decide
  obtain ⟨v, hv⟩ := Finset.card_pos.mp htpos
  let p := R.refined.facePoint t ⟨v, hv⟩
  simpa only [dist_self] using hR t.1 t.2 p
    (R.refined.facePoint_mem_faceCarrier t _) p
    (R.refined.facePoint_mem_faceCarrier t _)

theorem dist_midpointPosition_corner_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : K.Face) (i : ZMod 3) (a : (K.Vertex → ℝ) →ᵃ[ℝ] E)
    {d : ℝ} (hd : 0 ≤ d)
    (hvertex : ∀ j k : ZMod 3,
      dist (a (Pi.single (K.faceVertex t j) 1))
        (a (Pi.single (K.faceVertex t k) 1)) ≤ d)
    {w z : K.MidpointVertex} (hw : w ∈ K.midpointCornerFace t i)
    (hz : z ∈ K.midpointCornerFace t i) :
    dist (a (K.midpointPosition w)) (a (K.midpointPosition z)) ≤ d / 2 := by
  let P : ZMod 3 → E := fun j => a (Pi.single (K.faceVertex t j) 1)
  have hedge (j : ZMod 3) :
      a (K.midpointPosition (Sum.inr (K.faceEdge t j))) =
        midpoint ℝ (P j) (P (j + 1)) := by
    rw [K.midpointPosition_faceEdge t j, affine_map_midpoint]
  have hold (j : ZMod 3) :
      a (K.midpointPosition (Sum.inl (K.faceVertex t j))) = P j := rfl
  have hw' : w = Sum.inl (K.faceVertex t i) ∨
      w = Sum.inr (K.faceEdge t i) ∨
      w = Sum.inr (K.faceEdge t (i + 2)) := by
    simpa [midpointCornerFace] using hw
  have hz' : z = Sum.inl (K.faceVertex t i) ∨
      z = Sum.inr (K.faceEdge t i) ∨
      z = Sum.inr (K.faceEdge t (i + 2)) := by
    simpa [midpointCornerFace] using hz
  rcases hw' with rfl | rfl | rfl <;> rcases hz' with rfl | rfl | rfl
  · rw [hold, dist_self]
    positivity
  · rw [hold, hedge, dist_left_midpoint]
    norm_num
    calc
      (1 / 2 : ℝ) * dist (P i) (P (i + 1)) ≤ (1 / 2) * d :=
        mul_le_mul_of_nonneg_left (hvertex i (i + 1)) (by norm_num)
      _ = d / 2 := by ring
  · rw [hold, hedge]
    have hcycle : i + 2 + 1 = i := zmod3_add_two_add_one i
    rw [hcycle, dist_right_midpoint]
    norm_num
    calc
      (1 / 2 : ℝ) * dist (P (i + 2)) (P i) ≤ (1 / 2) * d :=
        mul_le_mul_of_nonneg_left (hvertex (i + 2) i) (by norm_num)
      _ = d / 2 := by ring
  · rw [hedge, hold, dist_midpoint_left]
    norm_num
    calc
      (1 / 2 : ℝ) * dist (P i) (P (i + 1)) ≤ (1 / 2) * d :=
        mul_le_mul_of_nonneg_left (hvertex i (i + 1)) (by norm_num)
      _ = d / 2 := by ring
  · rw [hedge, dist_self]
    positivity
  · rw [hedge, hedge]
    have hcycle : i + 2 + 1 = i := zmod3_add_two_add_one i
    rw [hcycle, midpoint_comm (R := ℝ) (P (i + 2)) (P i)]
    calc
      dist (midpoint ℝ (P i) (P (i + 1)))
          (midpoint ℝ (P i) (P (i + 2))) ≤
          (dist (P i) (P i) + dist (P (i + 1)) (P (i + 2))) / 2 :=
        dist_midpoint_midpoint_le _ _ _ _
      _ ≤ d / 2 := by simp only [dist_self, zero_add]; gcongr; exact hvertex _ _
  · rw [hedge, hold]
    have hcycle : i + 2 + 1 = i := zmod3_add_two_add_one i
    rw [hcycle, dist_midpoint_right]
    norm_num
    calc
      (1 / 2 : ℝ) * dist (P (i + 2)) (P i) ≤ (1 / 2) * d :=
        mul_le_mul_of_nonneg_left (hvertex (i + 2) i) (by norm_num)
      _ = d / 2 := by ring
  · rw [hedge, hedge]
    have hcycle : i + 2 + 1 = i := zmod3_add_two_add_one i
    rw [hcycle, midpoint_comm (R := ℝ) (P (i + 2)) (P i), dist_comm]
    calc
      dist (midpoint ℝ (P i) (P (i + 1)))
          (midpoint ℝ (P i) (P (i + 2))) ≤
          (dist (P i) (P i) + dist (P (i + 1)) (P (i + 2))) / 2 :=
        dist_midpoint_midpoint_le _ _ _ _
      _ ≤ d / 2 := by simp only [dist_self, zero_add]; gcongr; exact hvertex _ _
  · rw [hedge, dist_self]
    positivity

theorem dist_midpointPosition_central_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : K.Face) (a : (K.Vertex → ℝ) →ᵃ[ℝ] E)
    {d : ℝ} (hd : 0 ≤ d)
    (hvertex : ∀ j k : ZMod 3,
      dist (a (Pi.single (K.faceVertex t j) 1))
        (a (Pi.single (K.faceVertex t k) 1)) ≤ d)
    {w z : K.MidpointVertex} (hw : w ∈ K.midpointCentralFace t)
    (hz : z ∈ K.midpointCentralFace t) :
    dist (a (K.midpointPosition w)) (a (K.midpointPosition z)) ≤ d / 2 := by
  let P : ZMod 3 → E := fun j => a (Pi.single (K.faceVertex t j) 1)
  have hedge (j : ZMod 3) :
      a (K.midpointPosition (Sum.inr (K.faceEdge t j))) =
        midpoint ℝ (P j) (P (j + 1)) := by
    rw [K.midpointPosition_faceEdge t j, affine_map_midpoint]
  rw [midpointCentralFace] at hw hz
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
  rcases (by decide : ∀ j k : ZMod 3, k = j ∨ k = j + 1 ∨ k = j + 2) j k with
    rfl | rfl | rfl
  · rw [hedge, dist_self]
    positivity
  · rw [hedge, hedge, midpoint_comm (R := ℝ) (P j) (P (j + 1))]
    calc
      dist (midpoint ℝ (P (j + 1)) (P j))
          (midpoint ℝ (P (j + 1)) (P (j + 1 + 1))) ≤
          (dist (P (j + 1)) (P (j + 1)) +
            dist (P j) (P (j + 1 + 1))) / 2 :=
        dist_midpoint_midpoint_le _ _ _ _
      _ ≤ d / 2 := by simp only [dist_self, zero_add]; gcongr; exact hvertex _ _
  · rw [hedge, hedge]
    have hcycle : j + 2 + 1 = j := zmod3_add_two_add_one j
    rw [hcycle, midpoint_comm (R := ℝ) (P (j + 2)) (P j)]
    calc
      dist (midpoint ℝ (P j) (P (j + 1)))
          (midpoint ℝ (P j) (P (j + 2))) ≤
          (dist (P j) (P j) + dist (P (j + 1)) (P (j + 2))) / 2 :=
        dist_midpoint_midpoint_le _ _ _ _
      _ ≤ d / 2 := by simp only [dist_self, zero_add]; gcongr; exact hvertex _ _



/-- One midpoint subdivision halves every existing mesh bound. -/
theorem Subdivision.meshLE_trans_midpoint
    {K : IntrinsicTwoComplex} (R : K.Subdivision) {d : ℝ}
    (hR : R.MeshLE d) :
    (R.trans R.refined.midpointSubdivision).MeshLE (d / 2) := by
  intro s hs x hx y hy
  change dist (R.homeo (R.refined.midpointHomeomorph x))
    (R.homeo (R.refined.midpointHomeomorph y)) ≤ d / 2
  rw [show R.refined.midpointHomeomorph x = R.refined.midpointEval x from
    R.refined.midpointHomeomorph_apply x]
  rw [show R.refined.midpointHomeomorph y = R.refined.midpointEval y from
    R.refined.midpointHomeomorph_apply y]
  obtain ⟨t, hst⟩ := R.refined.exists_parentFace_of_mem_midpointFaces hs
  obtain ⟨a, ha⟩ := R.affineOnFace t.1 t.2
  have hxParent : R.refined.midpointEval x ∈ R.refined.faceCarrier t.1 :=
    R.refined.midpointEval_mem_parentFace t hst x hx
  have hyParent : R.refined.midpointEval y ∈ R.refined.faceCarrier t.1 :=
    R.refined.midpointEval_mem_parentFace t hst y hy
  have hvertex : ∀ j k : ZMod 3,
      dist (a (Pi.single (R.refined.faceVertex t j) 1))
        (a (Pi.single (R.refined.faceVertex t k) 1)) ≤ d := by
    intro j k
    let v : t.1 := ⟨R.refined.faceVertex t j, R.refined.faceVertex_mem t j⟩
    let w : t.1 := ⟨R.refined.faceVertex t k, R.refined.faceVertex_mem t k⟩
    have h := hR t.1 t.2 (R.refined.facePoint t v)
      (R.refined.facePoint_mem_faceCarrier t v) (R.refined.facePoint t w)
      (R.refined.facePoint_mem_faceCarrier t w)
    change dist ((R.homeo (R.refined.facePoint t v)).1)
      ((R.homeo (R.refined.facePoint t w)).1) ≤ d at h
    rw [ha _ (R.refined.facePoint_mem_faceCarrier t v),
      ha _ (R.refined.facePoint_mem_faceCarrier t w)] at h
    simpa only [R.refined.facePoint_val, v, w] using h
  let b : (R.refined.midpointComplex.Vertex → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ) :=
    a.comp R.refined.midpointEvalAffine
  let S : R.refined.midpointComplex.Face := ⟨s, hs⟩
  obtain ⟨v, w, hvw⟩ :=
    R.refined.midpointComplex.exists_facePoints_dist_ge S b x y hx hy
  have hxy : dist (R.homeo (R.refined.midpointEval x))
      (R.homeo (R.refined.midpointEval y)) = dist (b x.1) (b y.1) := by
    change dist ((R.homeo (R.refined.midpointEval x)).1)
      ((R.homeo (R.refined.midpointEval y)).1) = _
    rw [ha _ hxParent, ha _ hyParent]
    rfl
  rw [hxy]
  refine hvw.trans ?_
  have hbv : b (R.refined.midpointComplex.facePoint S v).1 =
      a (R.refined.midpointPosition v.1) := by
    change a (R.refined.midpointEvalAffine
      (R.refined.midpointComplex.facePoint S v).1) = _
    rw [R.refined.midpointEvalAffine_facePoint S v]
  have hbw : b (R.refined.midpointComplex.facePoint S w).1 =
      a (R.refined.midpointPosition w.1) := by
    change a (R.refined.midpointEvalAffine
      (R.refined.midpointComplex.facePoint S w).1) = _
    rw [R.refined.midpointEvalAffine_facePoint S w]
  rw [hbv, hbw]
  have hd : 0 ≤ d := R.meshLE_nonneg hR t
  rcases Finset.mem_union.mp hst with hcorner | hcentral
  · obtain ⟨i, -, hsi⟩ := Finset.mem_image.mp hcorner
    have hv : v.1 ∈ R.refined.midpointCornerFace t i := by rw [hsi]; exact v.2
    have hw : w.1 ∈ R.refined.midpointCornerFace t i := by rw [hsi]; exact w.2
    exact R.refined.dist_midpointPosition_corner_le t i a hd hvertex hv hw
  · have hscentral : s = R.refined.midpointCentralFace t :=
      Finset.mem_singleton.mp hcentral
    have hv : v.1 ∈ R.refined.midpointCentralFace t := by rw [← hscentral]; exact v.2
    have hw : w.1 ∈ R.refined.midpointCentralFace t := by rw [← hscentral]; exact w.2
    exact R.refined.dist_midpointPosition_central_le t a hd hvertex hv hw

/-- The identity subdivision has mesh at most one in barycentric sup distance. -/
theorem Subdivision.refl_meshLE (K : IntrinsicTwoComplex) :
    (Subdivision.refl K).MeshLE 1 := by
  intro t ht x hx y hy
  change dist x.1 y.1 ≤ 1
  rw [dist_pi_le_iff zero_le_one]
  intro v
  rw [Real.dist_eq, abs_le]
  have hxv := mem_Icc_of_mem_stdSimplex x.2.1 v
  have hyv := mem_Icc_of_mem_stdSimplex y.2.1 v
  rcases hxv with ⟨hx0, hx1⟩
  rcases hyv with ⟨hy0, hy1⟩
  constructor <;> linarith

/-- The `n`-fold intrinsic midpoint subdivision. -/
noncomputable def iteratedMidpointSubdivision (K : IntrinsicTwoComplex) :
    (n : ℕ) → K.Subdivision
  | 0 => Subdivision.refl K
  | n + 1 =>
      let R := K.iteratedMidpointSubdivision n
      R.trans R.refined.midpointSubdivision

@[simp] theorem iteratedMidpointSubdivision_zero (K : IntrinsicTwoComplex) :
    K.iteratedMidpointSubdivision 0 = Subdivision.refl K := rfl

theorem iteratedMidpointSubdivision_succ (K : IntrinsicTwoComplex) (n : ℕ) :
    K.iteratedMidpointSubdivision (n + 1) =
      (K.iteratedMidpointSubdivision n).trans
        (K.iteratedMidpointSubdivision n).refined.midpointSubdivision := rfl

/-- Every iterated midpoint refinement preserves the surface edge-valence bound. -/
theorem hasSurfaceEdgeValence_iteratedMidpointSubdivision
    (K : IntrinsicTwoComplex) (hK : K.HasSurfaceEdgeValence) :
    ∀ n, (K.iteratedMidpointSubdivision n).refined.HasSurfaceEdgeValence := by
  intro n
  induction n with
  | zero =>
      simpa [iteratedMidpointSubdivision] using hK
  | succ n ih =>
      exact
        (K.iteratedMidpointSubdivision n).refined.hasSurfaceEdgeValence_midpointComplex ih

/-- Quantitative mesh estimate for iterated midpoint subdivision. -/
theorem iteratedMidpointSubdivision_meshLE (K : IntrinsicTwoComplex) (n : ℕ) :
    (K.iteratedMidpointSubdivision n).MeshLE ((1 / 2 : ℝ) ^ n) := by
  induction n with
  | zero => simpa using Subdivision.refl_meshLE K
  | succ n ih =>
      rw [K.iteratedMidpointSubdivision_succ n]
      have h := (K.iteratedMidpointSubdivision n).meshLE_trans_midpoint ih
      convert h using 1
      rw [pow_succ]
      ring

/-- Every intrinsic finite two-complex has a faithful subdivision of arbitrarily small mesh. -/
theorem exists_subdivision_mesh_lt (K : IntrinsicTwoComplex) {eps : ℝ} (heps : 0 < eps) :
    ∃ R : K.Subdivision, ∀ t ∈ R.refined.faces,
      ∀ x ∈ R.refined.faceCarrier t, ∀ y ∈ R.refined.faceCarrier t,
        dist (R.homeo x) (R.homeo y) < eps := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one heps (by norm_num : (1 / 2 : ℝ) < 1)
  let R := K.iteratedMidpointSubdivision n
  refine ⟨R, ?_⟩
  intro t ht x hx y hy
  exact (K.iteratedMidpointSubdivision_meshLE n t ht x hx y hy).trans_lt hn

/-- Heine--Cantor and faithful midpoint subdivision make the image of every refined face have
arbitrarily small diameter under a continuous map. -/
theorem exists_subdivision_image_dist_lt (K : IntrinsicTwoComplex)
    {h : K.realization → Plane} (hcont : Continuous h)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ R : K.Subdivision, ∀ t ∈ R.refined.faces,
      ∀ x ∈ R.refined.faceCarrier t, ∀ y ∈ R.refined.faceCarrier t,
        dist (h (R.homeo x)) (h (R.homeo y)) < eps := by
  have huniform : UniformContinuousOn h (Set.univ : Set K.realization) :=
    isCompact_univ.uniformContinuousOn_of_continuous hcont.continuousOn
  obtain ⟨delta, hdelta, hcontrol⟩ :=
    (Metric.uniformContinuousOn_iff.mp huniform) eps heps
  obtain ⟨R, hR⟩ := K.exists_subdivision_mesh_lt hdelta
  refine ⟨R, ?_⟩
  intro t ht x hx y hy
  exact hcontrol (R.homeo x) (Set.mem_univ _) (R.homeo y) (Set.mem_univ _)
    (hR t ht x hx y hy)

/-- A sufficiently fine intrinsic subdivision is subordinate to any open cover. -/
theorem exists_subdivision_subordinate_openCover (K : IntrinsicTwoComplex)
    {I : Type*} (U : I → Set K.realization) (hU : ∀ i, IsOpen (U i))
    (hcover : (Set.univ : Set K.realization) ⊆ ⋃ i, U i) :
    ∃ R : K.Subdivision, ∀ t ∈ R.refined.faces,
      ∃ i, ∀ x ∈ R.refined.faceCarrier t, R.homeo x ∈ U i := by
  obtain ⟨delta, hdelta, hLebesgue⟩ :=
    lebesgue_number_lemma_of_metric (s := (Set.univ : Set K.realization))
      isCompact_univ hU hcover
  obtain ⟨R, hR⟩ := K.exists_subdivision_mesh_lt hdelta
  refine ⟨R, ?_⟩
  intro t ht
  have htpos : 0 < t.card := by rw [R.refined.faces_card t ht]; decide
  obtain ⟨v, hv⟩ := Finset.card_pos.mp htpos
  let T : R.refined.Face := ⟨t, ht⟩
  let p := R.refined.facePoint T ⟨v, hv⟩
  obtain ⟨i, hi⟩ := hLebesgue (R.homeo p) (Set.mem_univ _)
  refine ⟨i, fun x hx => hi ?_⟩
  rw [Metric.mem_ball]
  rw [dist_comm]
  exact hR t ht p (R.refined.facePoint_mem_faceCarrier T _) x hx

/-! ## Finite subcomplexes between compact and open sets -/

/-- A finite subcomplex of a faithful subdivision of `K`, selected so that its carrier contains
the prescribed compact set `C` and remains inside the prescribed open set `U`.

This is the finite-complex form of the compact part of Moise Ch. 8, Thm. 2.  The full theorem in
Moise treats arbitrary open subsets by a locally finite exhaustion; the Radó step only needs a
finite collar around the compact part already constructed. -/
structure OpenSubcomplex (K : IntrinsicTwoComplex) (C U : Set K.realization) where
  /-- A faithful finite refinement of the original complex. -/
  subdivision : K.Subdivision
  /-- The maximal refined faces retained in the subcomplex. -/
  keptFaces : Finset (Finset subdivision.refined.Vertex)
  /-- Every retained face is a face of the refined complex. -/
  keptFaces_subset : keptFaces ⊆ subdivision.refined.faces
  /-- The selected subcomplex contains `C` after transport to the original realization. -/
  covers : C ⊆ Set.range (subdivision.homeo ∘
    subdivision.refined.restrictFacesInclusion (fun t => t ∈ keptFaces))
  /-- Its transported carrier is contained in `U`. -/
  contained : Set.range (subdivision.homeo ∘
    subdivision.refined.restrictFacesInclusion (fun t => t ∈ keptFaces)) ⊆ U

namespace OpenSubcomplex

variable {K : IntrinsicTwoComplex} {C U : Set K.realization}

/-- The selected finite intrinsic complex. -/
abbrev complex (L : K.OpenSubcomplex C U) : IntrinsicTwoComplex :=
  L.subdivision.refined.restrictFaces (fun t => t ∈ L.keptFaces)

/-- Its canonical map into the original realization. -/
def inclusion (L : K.OpenSubcomplex C U) : L.complex.realization → K.realization :=
  L.subdivision.homeo ∘
    L.subdivision.refined.restrictFacesInclusion (fun t => t ∈ L.keptFaces)

/-- The canonical inclusion of an open subcomplex is an embedding. -/
theorem isEmbedding_inclusion (L : K.OpenSubcomplex C U) :
    _root_.Topology.IsEmbedding L.inclusion :=
  L.subdivision.homeo.isEmbedding.comp
    (L.subdivision.refined.isEmbedding_restrictFacesInclusion
      (fun t => t ∈ L.keptFaces))

/-- The carrier of the selected subcomplex in the original realization. -/
def support (L : K.OpenSubcomplex C U) : Set K.realization :=
  Set.range L.inclusion

theorem covers_support (L : K.OpenSubcomplex C U) : C ⊆ L.support :=
  L.covers

theorem support_subset (L : K.OpenSubcomplex C U) : L.support ⊆ U :=
  L.contained

end OpenSubcomplex

/-- A compact subset of an open subset of a finite intrinsic complex is covered by a finite
subcomplex of a faithful subdivision which is still contained in that open set. -/
theorem exists_openSubcomplex (K : IntrinsicTwoComplex) {C U : Set K.realization}
    (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    Nonempty (K.OpenSubcomplex C U) := by
  classical
  let W : Bool → Set K.realization := fun b => if b then Cᶜ else U
  have hWopen : ∀ b, IsOpen (W b) := by
    intro b
    cases b <;> simp [W, hU, hC.isClosed]
  have hWcover : (Set.univ : Set K.realization) ⊆ ⋃ b, W b := by
    intro x _
    by_cases hx : x ∈ C
    · exact Set.mem_iUnion.mpr ⟨false, by simpa [W] using hCU hx⟩
    · exact Set.mem_iUnion.mpr ⟨true, by simpa [W] using hx⟩
  obtain ⟨R, hR⟩ := K.exists_subdivision_subordinate_openCover W hWopen hWcover
  let keep : Finset (Finset R.refined.Vertex) :=
    R.refined.faces.filter fun t =>
      ∀ x ∈ R.refined.faceCarrier t, R.homeo x ∈ U
  refine ⟨⟨R, keep, ?_, ?_, ?_⟩⟩
  · intro t ht
    exact (Finset.mem_filter.mp ht).1
  · intro z hz
    let x : R.refined.realization := R.homeo.symm z
    rcases x.2.2 with ⟨t, ht, hxt⟩
    obtain ⟨b, hb⟩ := hR t ht
    have htU : ∀ y ∈ R.refined.faceCarrier t, R.homeo y ∈ U := by
      cases b with
      | false => simpa [W] using hb
      | true =>
          exfalso
          have hxcomp : z ∈ Cᶜ := by
            have := hb x hxt
            simpa [W, x] using this
          exact hxcomp hz
    have htkeep : t ∈ keep := Finset.mem_filter.mpr ⟨ht, htU⟩
    let y : (@IntrinsicTwoComplex.restrictFaces R.refined (fun s => s ∈ keep)
        (fun s => Finset.decidableMem s keep)).realization :=
      ⟨x.1, x.2.1, ⟨t, (@Finset.mem_filter _ (fun s => s ∈ keep)
        (fun s => Finset.decidableMem s keep) _ _).mpr ⟨ht, htkeep⟩, hxt⟩⟩
    refine ⟨y, ?_⟩
    change R.homeo (@IntrinsicTwoComplex.restrictFacesInclusion R.refined
      (fun s => s ∈ keep) (fun s => Finset.decidableMem s keep) y) = z
    rw [← R.homeo.apply_symm_apply z]
    congr 1
  · rintro z ⟨y, rfl⟩
    rcases y.2.2 with ⟨t, ht, hyt⟩
    have htParts := (@Finset.mem_filter _ (fun s => s ∈ keep)
      (fun s => Finset.decidableMem s keep) _ _).mp ht
    have htkeep : t ∈ keep := htParts.2
    have htU := (Finset.mem_filter.mp htkeep).2
    exact htU ⟨y.1, y.2.1, ⟨t, htParts.1, hyt⟩⟩ hyt

/-! ## Compact stages exhausting a proper open subset -/

/-- Finite faithful subcomplex stages exhausting an open subset of a finite intrinsic complex.
Each stage contains a canonical compact distance core and lies in the interior of the next
distance core.  The stages are not yet a single conforming locally finite complex: reconciling
their boundary subdivisions is the remaining combinatorial part of Moise Ch. 8, Thm. 2. -/
structure OpenExhaustion (K : IntrinsicTwoComplex) (U : Set K.realization) where
  /-- The `stage` declaration. -/
  stage : ∀ n : ℕ,
    K.OpenSubcomplex (frontierCore U n) (interior (frontierCore U (n + 1)))

namespace OpenExhaustion

variable {K : IntrinsicTwoComplex} {U : Set K.realization}

/-- The carrier of one finite stage, viewed in the original realization. -/
def stageSupport (E : K.OpenExhaustion U) (n : ℕ) : Set K.realization :=
  (E.stage n).support

theorem stageSupport_subset (E : K.OpenExhaustion U) (hUc : Uᶜ.Nonempty) (n : ℕ) :
    E.stageSupport n ⊆ U := by
  exact (E.stage n).support_subset.trans interior_subset |>.trans
    (frontierCore_subset hUc (n + 1))

/-- The finite stage carriers cover exactly the prescribed open set. -/
theorem iUnion_stageSupport (E : K.OpenExhaustion U) (hU : IsOpen U)
    (hUc : Uᶜ.Nonempty) :
    (⋃ n : ℕ, E.stageSupport n) = U := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact E.stageSupport_subset hUc n hn
  · intro x hx
    have hxC : x ∈ ⋃ n : ℕ, frontierCore U n := by
      rw [iUnion_frontierCore hU hUc]
      exact hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxC
    exact Set.mem_iUnion.mpr ⟨n, (E.stage n).covers hn⟩

end OpenExhaustion

/-- Every proper open subset of a finite intrinsic complex has a compactly nested exhaustion by
finite subcomplexes of faithful subdivisions. -/
theorem exists_openExhaustion (K : IntrinsicTwoComplex) {U : Set K.realization}
    (_ : IsOpen U) (_ : Uᶜ.Nonempty) : Nonempty (K.OpenExhaustion U) := by
  refine ⟨⟨fun n => Classical.choice (K.exists_openSubcomplex
    (isCompact_frontierCore U n) isOpen_interior
    (frontierCore_subset_interior_succ U n))⟩⟩

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
