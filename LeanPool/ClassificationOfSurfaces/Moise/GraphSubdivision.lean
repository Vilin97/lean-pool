/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.PolygonalArc

/-!
# Finite line-arrangement subdivisions of plane graphs

This file supplies the source-side subdivision used in Moise Chapter 6, Theorem 2.  A finite
plane graph is encoded as one auxiliary broken line which traverses every edge (with harmless
connector segments between edges).  The line arrangement of that auxiliary chain resolves every
source edge.  Keeping only arrangement faces subordinate to an original face produces an honest
subdivision of the graph.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

theorem normalized_ge_of_line_nonneg {a b q t : ℝ}
    (hΔ : 0 < b - a) (hq : 0 ≤ q - ((1 - t) * a + t * b)) :
    t ≤ (b - a)⁻¹ * (q - a) := by
  have hbase : t * (b - a) ≤ q - a := by nlinarith
  have h := mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hΔ.le)
  calc
    t = (b - a)⁻¹ * (t * (b - a)) := by
      field_simp [hΔ.ne']
    _ ≤ (b - a)⁻¹ * (q - a) := h

theorem normalized_le_of_line_nonpos {a b q t : ℝ}
    (hΔ : 0 < b - a) (hq : q - ((1 - t) * a + t * b) ≤ 0) :
    (b - a)⁻¹ * (q - a) ≤ t := by
  have hbase : q - a ≤ t * (b - a) := by nlinarith
  have h := mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hΔ.le)
  calc
    (b - a)⁻¹ * (q - a) ≤ (b - a)⁻¹ * (t * (b - a)) := h
    _ = t := by field_simp [hΔ.ne']

theorem normalized_le_of_line_nonneg_of_neg {a b q t : ℝ}
    (hΔ : b - a < 0) (hq : 0 ≤ q - ((1 - t) * a + t * b)) :
    (b - a)⁻¹ * (q - a) ≤ t := by
  have hbase : t * (b - a) ≤ q - a := by nlinarith
  have h := mul_le_mul_of_nonpos_left hbase (inv_nonpos.mpr hΔ.le)
  calc
    (b - a)⁻¹ * (q - a) ≤ (b - a)⁻¹ * (t * (b - a)) := h
    _ = t := by field_simp [hΔ.ne]

theorem normalized_ge_of_line_nonpos_of_neg {a b q t : ℝ}
    (hΔ : b - a < 0) (hq : q - ((1 - t) * a + t * b) ≤ 0) :
    t ≤ (b - a)⁻¹ * (q - a) := by
  have hbase : q - a ≤ t * (b - a) := by nlinarith
  have h := mul_le_mul_of_nonpos_left hbase (inv_nonpos.mpr hΔ.le)
  calc
    t = (b - a)⁻¹ * (t * (b - a)) := by
      field_simp [hΔ.ne]
    _ ≤ (b - a)⁻¹ * (q - a) := h

private theorem abs_sub_le_inv_nat_of_same_grid_side {D : ℕ} (hD : 0 < D)
    {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hside : ∀ r : Fin (D + 1),
      (x ≤ r.val / (D : ℝ) ∧ y ≤ r.val / (D : ℝ)) ∨
        (r.val / (D : ℝ) ≤ x ∧ r.val / (D : ℝ) ≤ y)) :
    |x - y| ≤ 1 / (D : ℝ) := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  wlog hxy : x ≤ y generalizing x y
  · have h := this hy hx (fun r => by
      rcases hside r with h | h
      · exact Or.inl ⟨h.2, h.1⟩
      · exact Or.inr ⟨h.2, h.1⟩) (le_of_not_ge hxy)
    rw [abs_sub_comm]
    exact h
  rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
  by_cases hx1 : x = 1
  · have hy1 : y = 1 := le_antisymm hy.2 (hx1 ▸ hxy)
    rw [hx1, hy1]
    simp []
  · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    let z : ℝ := (D : ℝ) * x
    let k : ℕ := ⌊z⌋₊
    have hz0 : 0 ≤ z := mul_nonneg (Nat.cast_nonneg _) hx.1
    have hzD : z < D := by
      dsimp [z]
      nlinarith
    have hklt : k < D := (Nat.floor_lt hz0).mpr hzD
    let r : Fin (D + 1) := ⟨k + 1, by omega⟩
    have hxGrid : x < r.val / (D : ℝ) := by
      have hfloor : z < k + 1 := Nat.lt_floor_add_one z
      change (D : ℝ) * x < (k : ℝ) + 1 at hfloor
      dsimp [z, r]
      apply (lt_div_iff₀ hDreal).mpr
      simpa [mul_comm] using hfloor
    have hyGrid : y ≤ r.val / (D : ℝ) := by
      rcases hside r with h | h
      · exact h.2
      · exact (not_le_of_gt hxGrid h.1).elim
    have hk : (k : ℝ) ≤ z := Nat.floor_le hz0
    have hgridLe : r.val / (D : ℝ) ≤ x + 1 / (D : ℝ) := by
      dsimp [r, z] at hk ⊢
      apply (div_le_iff₀ hDreal).mpr
      calc
        ((k + 1 : ℕ) : ℝ) ≤ (D : ℝ) * x + 1 := by
          norm_num at hk ⊢
          linarith
        _ = (x + 1 / (D : ℝ)) * D := by
          field_simp [hDreal.ne']
    linarith

namespace PlaneComplex

variable (K : PlaneComplex)

/-- The `EdgeFace` declaration. -/
abbrev EdgeFace := {e : Finset K.Vertex // e ∈ K.edges}

/-- The `edgeEquiv` declaration. -/
noncomputable def edgeEquiv : K.EdgeFace ≃ Fin (Fintype.card K.EdgeFace) :=
  Fintype.equivFin K.EdgeFace

/-- The `edgeAt` declaration. -/
noncomputable def edgeAt (i : Fin (Fintype.card K.EdgeFace)) : K.EdgeFace :=
  K.edgeEquiv.symm i

/-- The `vertexEquiv` declaration. -/
noncomputable def vertexEquiv : K.Vertex ≃ Fin (Fintype.card K.Vertex) :=
  Fintype.equivFin K.Vertex

/-- The `vertexAt` declaration. -/
noncomputable def vertexAt (i : Fin (Fintype.card K.Vertex)) : K.Vertex :=
  K.vertexEquiv.symm i

theorem edgeAt_card (i : Fin (Fintype.card K.EdgeFace)) : (K.edgeAt i).1.card = 2 := by
  exact (Finset.mem_filter.mp (K.edgeAt i).2).2

/-- The `edgeFirst` declaration. -/
noncomputable def edgeFirst (i : Fin (Fintype.card K.EdgeFace)) : K.Vertex :=
  (Finset.card_eq_two.mp (K.edgeAt_card i)).choose

/-- The `edgeSecond` declaration. -/
noncomputable def edgeSecond (i : Fin (Fintype.card K.EdgeFace)) : K.Vertex :=
  (Finset.card_eq_two.mp (K.edgeAt_card i)).choose_spec.choose

theorem edgeFirst_ne_edgeSecond (i : Fin (Fintype.card K.EdgeFace)) :
    K.edgeFirst i ≠ K.edgeSecond i :=
  (Finset.card_eq_two.mp (K.edgeAt_card i)).choose_spec.choose_spec.1

theorem edgeAt_eq (i : Fin (Fintype.card K.EdgeFace)) :
    (K.edgeAt i).1 = {K.edgeFirst i, K.edgeSecond i} :=
  (Finset.card_eq_two.mp (K.edgeAt_card i)).choose_spec.choose_spec.2

theorem edgeAt_mem_simplexes (i : Fin (Fintype.card K.EdgeFace)) :
    (K.edgeAt i).1 ∈ K.simplexes :=
  (Finset.mem_filter.mp (K.edgeAt i).2).1

/-- Affine coordinate from `0` to `1` on an enumerated source edge. -/
noncomputable def edgeParameter (i : Fin (Fintype.card K.EdgeFace)) :
    Plane →ᵃ[ℝ] ℝ :=
  if _ : K.position (K.edgeFirst i) 0 ≠ K.position (K.edgeSecond i) 0 then
    (K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0)⁻¹ •
      (cartesianX - AffineMap.const ℝ Plane (K.position (K.edgeFirst i) 0))
  else
    (K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1)⁻¹ •
      (cartesianY - AffineMap.const ℝ Plane (K.position (K.edgeFirst i) 1))

theorem edgeParameter_apply_first (i : Fin (Fintype.card K.EdgeFace)) :
    K.edgeParameter i (K.position (K.edgeFirst i)) = 0 := by
  unfold edgeParameter
  split_ifs <;> simp

theorem edgeParameter_apply_second (i : Fin (Fintype.card K.EdgeFace)) :
    K.edgeParameter i (K.position (K.edgeSecond i)) = 1 := by
  unfold edgeParameter
  split_ifs with hx
  · change (K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0)⁻¹ *
      (K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0) = 1
    exact inv_mul_cancel₀ (sub_ne_zero.mpr hx.symm)
  · have hne : K.position (K.edgeFirst i) ≠ K.position (K.edgeSecond i) := by
      exact K.position_injective.ne (K.edgeFirst_ne_edgeSecond i)
    have hy : K.position (K.edgeFirst i) 1 ≠ K.position (K.edgeSecond i) 1 := by
      intro hy
      apply hne
      exact plane_ext (not_ne_iff.mp hx) hy
    change (K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1)⁻¹ *
      (K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1) = 1
    exact inv_mul_cancel₀ (sub_ne_zero.mpr hy.symm)

theorem edgeParameter_lineMap (i : Fin (Fintype.card K.EdgeFace)) (t : ℝ) :
    K.edgeParameter i
      (AffineMap.lineMap (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i)) t) = t := by
  rw [AffineMap.apply_lineMap, K.edgeParameter_apply_first,
    K.edgeParameter_apply_second]
  simp [AffineMap.lineMap_apply_module]

theorem edgeParameter_mem_Icc (i : Fin (Fintype.card K.EdgeFace)) {x : Plane}
    (hx : x ∈ K.cellCarrier (K.edgeAt i).1) : K.edgeParameter i x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [K.edgeAt_eq, PlaneComplex.cellCarrier] at hx
  have himage : K.position ''
      (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
      {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
    ext y
    simp [eq_comm]
  rw [himage, convexHull_pair] at hx
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  simpa [K.edgeParameter_lineMap]

theorem lineMap_edgeParameter_eq (i : Fin (Fintype.card K.EdgeFace)) {x : Plane}
    (hx : x ∈ K.cellCarrier (K.edgeAt i).1) :
    AffineMap.lineMap (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i))
      (K.edgeParameter i x) = x := by
  rw [K.edgeAt_eq, PlaneComplex.cellCarrier] at hx
  have himage : K.position ''
      (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
      {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
    ext y
    simp [eq_comm]
  rw [himage, convexHull_pair, segment_eq_image_lineMap] at hx
  obtain ⟨t, -, rfl⟩ := hx
  rw [K.edgeParameter_lineMap]

theorem exists_edgeAt (e : K.EdgeFace) : ∃ i, K.edgeAt i = e := by
  exact K.edgeEquiv.symm.surjective e

theorem exists_vertexAt (v : K.Vertex) : ∃ i, K.vertexAt i = v := by
  exact K.vertexEquiv.symm.surjective v

/-- The auxiliary chain has one genuine edge segment at every even index; odd segments merely
connect one enumerated edge to the next and are discarded by `subordinateTo`. -/
noncomputable def edgeChain : BrokenLineData (Set.univ : Set Plane) := by
  classical
  let m := Fintype.card K.EdgeFace
  let q := Fintype.card K.Vertex
  let vertex : Fin (2 * m + q + 1) → Plane := fun k =>
    if hk : k.val < 2 * m then
      let i : Fin m := ⟨k.val / 2, by omega⟩
      if k.val % 2 = 0 then K.position (K.edgeFirst i) else K.position (K.edgeSecond i)
    else if hv : k.val < 2 * m + q then
      K.position (K.vertexAt ⟨k.val - 2 * m, by omega⟩)
    else 0
  exact {
    n := 2 * m + q
    vertex := vertex
    segment_subset := fun _ _ _ => Set.mem_univ _ }

theorem edgeChain_vertex_even (i : Fin (Fintype.card K.EdgeFace)) :
    K.edgeChain.vertex ⟨2 * i.val, by
      change 2 * i.val <
        2 * Fintype.card K.EdgeFace + Fintype.card K.Vertex + 1
      omega⟩ = K.position (K.edgeFirst i) := by
  classical
  simp only [edgeChain]
  rw [dif_pos (by omega)]
  have hmod : (2 * i.val) % 2 = 0 := by omega
  rw [if_pos hmod]
  have hdiv : 2 * i.val / 2 = i.val := by omega
  congr 2
  exact Fin.ext hdiv

theorem edgeChain_vertex_odd (i : Fin (Fintype.card K.EdgeFace)) :
    K.edgeChain.vertex ⟨2 * i.val + 1, by
      change 2 * i.val + 1 <
        2 * Fintype.card K.EdgeFace + Fintype.card K.Vertex + 1
      omega⟩ = K.position (K.edgeSecond i) := by
  classical
  simp only [edgeChain]
  rw [dif_pos (by omega)]
  have hmod : (2 * i.val + 1) % 2 ≠ 0 := by omega
  rw [if_neg hmod]
  have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
  congr 2
  exact Fin.ext hdiv

theorem edgeChain_vertex_original (i : Fin (Fintype.card K.Vertex)) :
    K.edgeChain.vertex ⟨2 * Fintype.card K.EdgeFace + i.val, by
      change 2 * Fintype.card K.EdgeFace + i.val <
        2 * Fintype.card K.EdgeFace + Fintype.card K.Vertex + 1
      omega⟩ = K.position (K.vertexAt i) := by
  classical
  simp only [edgeChain]
  rw [dif_neg (by omega), dif_pos (by omega)]
  have hsub : 2 * Fintype.card K.EdgeFace + i.val -
      2 * Fintype.card K.EdgeFace = i.val := by omega
  congr 2
  exact Fin.ext hsub

/-- The `edgeChainIndex` declaration. -/
noncomputable def edgeChainIndex (i : Fin (Fintype.card K.EdgeFace)) :
    Fin K.edgeChain.n :=
  ⟨2 * i.val, by
    change 2 * i.val < 2 * Fintype.card K.EdgeFace + Fintype.card K.Vertex
    have hm : 0 < Fintype.card K.EdgeFace :=
      Fintype.card_pos_iff.mpr ⟨K.edgeAt i⟩
    omega⟩

theorem edgeChainIndex_castSucc (i : Fin (Fintype.card K.EdgeFace)) :
    (K.edgeChainIndex i).castSucc =
      ⟨2 * i.val, by
        change 2 * i.val <
          2 * Fintype.card K.EdgeFace + Fintype.card K.Vertex + 1
        omega⟩ := by
  rfl

theorem edgeChainIndex_succ (i : Fin (Fintype.card K.EdgeFace)) :
    (K.edgeChainIndex i).succ =
      ⟨2 * i.val + 1, by
        change 2 * i.val + 1 <
          2 * Fintype.card K.EdgeFace + Fintype.card K.Vertex + 1
        omega⟩ := by
  rfl

theorem edgeChain_segment (i : Fin (Fintype.card K.EdgeFace)) :
    segment ℝ
        (K.edgeChain.vertex (K.edgeChainIndex i).castSucc)
        (K.edgeChain.vertex (K.edgeChainIndex i).succ) =
      K.cellCarrier (K.edgeAt i).1 := by
  rw [K.edgeChainIndex_castSucc, K.edgeChainIndex_succ,
    K.edgeChain_vertex_even, K.edgeChain_vertex_odd, K.edgeAt_eq,
    PlaneComplex.cellCarrier]
  have himage : K.position ''
      (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
      {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
    ext x
    simp [eq_comm]
  rw [himage, convexHull_pair]

/-- The ambient arrangement generated by all graph edges. -/
noncomputable def edgeArrangement : PlaneComplex :=
  K.edgeChain.arrangementMesh.toPlaneComplex

/-- The arrangement faces subordinate to the original graph. -/
noncomputable def edgeSubdivision : PlaneComplex :=
  K.edgeArrangement.subordinateTo K

theorem edgeSubdivision_support_eq (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2) :
    K.edgeSubdivision.support = K.support := by
  unfold edgeSubdivision edgeArrangement
  apply Set.Subset.antisymm
  · exact K.edgeChain.arrangementMesh.toPlaneComplex.subordinateTo_support_subset K
  · intro x hx
    rw [PlaneComplex.support] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    have hsne := K.nonempty_of_mem s hs
    have hspos : 0 < s.card := Finset.card_pos.mpr hsne
    have hscard := hgraph s hs
    have hcases : s.card = 1 ∨ s.card = 2 := by omega
    rw [PlaneComplex.support]
    simp only [Set.mem_iUnion]
    rcases hcases with hsone | hstwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
      have hxv : x = K.position v := by
        simpa [PlaneComplex.cellCarrier] using hxs
      obtain ⟨i, hi⟩ := K.exists_vertexAt v
      let j : Fin (K.edgeChain.n + 1) :=
        ⟨2 * Fintype.card K.EdgeFace + i.val, by
          change 2 * Fintype.card K.EdgeFace + i.val <
            2 * Fintype.card K.EdgeFace + Fintype.card K.Vertex + 1
          omega⟩
      obtain ⟨w, hwpos, hwface⟩ := K.edgeChain.exists_arrangementVertex_position_eq j
      let u : Finset K.edgeChain.arrangementMesh.toPlaneComplex.Vertex := {w}
      refine ⟨u, ?_, ?_⟩
      · apply (K.edgeChain.arrangementMesh.toPlaneComplex.mem_subordinateTo_simplexes_iff K).mpr
        refine ⟨hwface, {v}, hs, ?_⟩
        intro y hy
        have hyw : y = K.edgeChain.arrangementMesh.toPlaneComplex.position w := by
          change y ∈ convexHull ℝ
            (K.edgeChain.arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset K.edgeChain.arrangementMesh.Vertex) :
                Set K.edgeChain.arrangementMesh.Vertex)) at hy
          have himage : K.edgeChain.arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset K.edgeChain.arrangementMesh.Vertex) :
                Set K.edgeChain.arrangementMesh.Vertex) =
              {K.edgeChain.arrangementMesh.toPlaneComplex.position w} := by
            ext z
            constructor
            · rintro ⟨q, hq, rfl⟩
              have hqw : q = w := Finset.mem_singleton.mp hq
              subst q
              rfl
            · intro hz
              have hz' : z = K.edgeChain.arrangementMesh.toPlaneComplex.position w :=
                Set.mem_singleton_iff.mp hz
              subst z
              exact ⟨w, Finset.mem_singleton_self _, rfl⟩
          rw [himage, convexHull_singleton] at hy
          exact hy
        rw [hyw, hwpos, show K.edgeChain.vertex j = K.position v by
          rw [K.edgeChain_vertex_original i, hi]]
        exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩
      · rw [hxv]
        rw [K.edgeChain.arrangementMesh.toPlaneComplex.subordinateTo_cellCarrier K]
        exact subset_convexHull ℝ _ ⟨w, Finset.mem_singleton_self _, by
          rw [hwpos, K.edgeChain_vertex_original i, hi]⟩
    · let e : K.EdgeFace := ⟨s, Finset.mem_filter.mpr ⟨hs, hstwo⟩⟩
      obtain ⟨i, hi⟩ := K.exists_edgeAt e
      have hsegment : segment ℝ
          (K.edgeChain.vertex (K.edgeChainIndex i).castSucc)
          (K.edgeChain.vertex (K.edgeChainIndex i).succ) = K.cellCarrier s := by
        rw [K.edgeChain_segment i, hi]
      obtain ⟨u, hu, hxu, huSegment⟩ :=
        K.edgeChain.exists_face_on_segment (K.edgeChainIndex i) (hsegment.symm ▸ hxs)
      refine ⟨u, ?_, hxu⟩
      apply (K.edgeChain.arrangementMesh.toPlaneComplex.mem_subordinateTo_simplexes_iff K).mpr
      refine ⟨hu, s, hs, ?_⟩
      rw [← hsegment]
      apply convexHull_min
      · rintro y ⟨w, hw, rfl⟩
        exact huSegment w hw
      · exact convex_segment _ _

theorem edgeSubdivision_subdivides (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2) :
    K.edgeSubdivision.Subdivides K :=
  K.edgeArrangement.subordinateTo_subdivides K (K.edgeSubdivision_support_eq hgraph)

/-! ## Arbitrarily fine marked arrangements -/

/-- The `EdgeSample` declaration. -/
abbrev EdgeSample (cuts : ℕ) :=
  Fin (Fintype.card K.EdgeFace) × Fin (cuts + 2)

/-- The `edgeSampleEquiv` declaration. -/
noncomputable def edgeSampleEquiv (cuts : ℕ) :
    K.EdgeSample cuts ≃ Fin (Fintype.card (K.EdgeSample cuts)) :=
  Fintype.equivFin (K.EdgeSample cuts)

/-- The `edgeSamplePoint` declaration. -/
noncomputable def edgeSamplePoint (cuts : ℕ) (s : K.EdgeSample cuts) : Plane :=
  AffineMap.lineMap (K.position (K.edgeFirst s.1))
    (K.position (K.edgeSecond s.1)) (s.2.val / (cuts + 1 : ℝ))

theorem edgeParameter_samplePoint (cuts : ℕ) (s : K.EdgeSample cuts) :
    K.edgeParameter s.1 (K.edgeSamplePoint cuts s) = s.2.val / (cuts + 1 : ℝ) := by
  exact K.edgeParameter_lineMap s.1 _

/-- The auxiliary edge chain enlarged by `cuts` equally spaced interior marks on every edge.
The marks need not occur consecutively: their two coordinate lines are what refine the ambient
arrangement. -/
noncomputable def sampledEdgeChain (cuts : ℕ) : BrokenLineData (Set.univ : Set Plane) := by
  classical
  let m := Fintype.card K.EdgeFace
  let r := Fintype.card (K.EdgeSample cuts)
  let q := Fintype.card K.Vertex
  let vertex : Fin (2 * m + r + q + 1) → Plane := fun k =>
    if hk : k.val < 2 * m then
      let i : Fin m := ⟨k.val / 2, by omega⟩
      if k.val % 2 = 0 then K.position (K.edgeFirst i) else K.position (K.edgeSecond i)
    else if hs : k.val < 2 * m + r then
      K.edgeSamplePoint cuts
        (K.edgeSampleEquiv cuts |>.symm ⟨k.val - 2 * m, by omega⟩)
    else if hv : k.val < 2 * m + r + q then
      K.position (K.vertexAt ⟨k.val - (2 * m + r), by omega⟩)
    else 0
  exact {
    n := 2 * m + r + q
    vertex := vertex
    segment_subset := fun _ _ _ => Set.mem_univ _ }

theorem sampledEdgeChain_vertex_even (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace)) :
    (K.sampledEdgeChain cuts).vertex ⟨2 * i.val, by
      change 2 * i.val < 2 * Fintype.card K.EdgeFace +
        Fintype.card (K.EdgeSample cuts) + Fintype.card K.Vertex + 1
      omega⟩ = K.position (K.edgeFirst i) := by
  classical
  simp only [sampledEdgeChain]
  rw [dif_pos (by omega)]
  have hmod : (2 * i.val) % 2 = 0 := by omega
  rw [if_pos hmod]
  have hdiv : 2 * i.val / 2 = i.val := by omega
  congr 2
  exact Fin.ext hdiv

theorem sampledEdgeChain_vertex_odd (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace)) :
    (K.sampledEdgeChain cuts).vertex ⟨2 * i.val + 1, by
      change 2 * i.val + 1 < 2 * Fintype.card K.EdgeFace +
        Fintype.card (K.EdgeSample cuts) + Fintype.card K.Vertex + 1
      omega⟩ = K.position (K.edgeSecond i) := by
  classical
  simp only [sampledEdgeChain]
  rw [dif_pos (by omega)]
  have hmod : (2 * i.val + 1) % 2 ≠ 0 := by omega
  rw [if_neg hmod]
  have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
  congr 2
  exact Fin.ext hdiv

theorem sampledEdgeChain_vertex_sample (cuts : ℕ) (s : K.EdgeSample cuts) :
    (K.sampledEdgeChain cuts).vertex
      ⟨2 * Fintype.card K.EdgeFace + (K.edgeSampleEquiv cuts s).val, by
        change 2 * Fintype.card K.EdgeFace + (K.edgeSampleEquiv cuts s).val <
          2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) +
            Fintype.card K.Vertex + 1
        omega⟩ = K.edgeSamplePoint cuts s := by
  classical
  simp only [sampledEdgeChain]
  rw [dif_neg (by omega), dif_pos (by omega)]
  have hsub : 2 * Fintype.card K.EdgeFace + (K.edgeSampleEquiv cuts s).val -
      2 * Fintype.card K.EdgeFace = (K.edgeSampleEquiv cuts s).val := by omega
  have hfin : (⟨2 * Fintype.card K.EdgeFace + (K.edgeSampleEquiv cuts s).val -
      2 * Fintype.card K.EdgeFace, by omega⟩ :
      Fin (Fintype.card (K.EdgeSample cuts))) = K.edgeSampleEquiv cuts s :=
    Fin.ext hsub
  rw [hfin, Equiv.symm_apply_apply]

/-- The `sampledEdgeChainSampleIndex` declaration. -/
noncomputable def sampledEdgeChainSampleIndex (cuts : ℕ) (s : K.EdgeSample cuts) :
    Fin ((K.sampledEdgeChain cuts).n + 1) :=
  ⟨2 * Fintype.card K.EdgeFace + (K.edgeSampleEquiv cuts s).val, by
    change 2 * Fintype.card K.EdgeFace + (K.edgeSampleEquiv cuts s).val <
      2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) +
        Fintype.card K.Vertex + 1
    omega⟩

theorem sampledEdgeArrangement_monochromatic_vertical (cuts : ℕ)
    (s : K.EdgeSample cuts) :
    (K.sampledEdgeChain cuts).arrangementMesh.IsMonochromatic
      (BrokenLineData.verticalLine (K.edgeSamplePoint cuts s)) := by
  have h := (K.sampledEdgeChain cuts).arrangementMesh_monochromatic_verticalLine
    (K.sampledEdgeChainSampleIndex cuts s)
  have hj : (K.sampledEdgeChain cuts).vertex (K.sampledEdgeChainSampleIndex cuts s) =
      K.edgeSamplePoint cuts s := by
    exact K.sampledEdgeChain_vertex_sample cuts s
  rw [hj] at h
  exact h

theorem sampledEdgeArrangement_monochromatic_horizontal (cuts : ℕ)
    (s : K.EdgeSample cuts) :
    (K.sampledEdgeChain cuts).arrangementMesh.IsMonochromatic
      (BrokenLineData.horizontalLine (K.edgeSamplePoint cuts s)) := by
  have h := (K.sampledEdgeChain cuts).arrangementMesh_monochromatic_horizontalLine
    (K.sampledEdgeChainSampleIndex cuts s)
  have hj : (K.sampledEdgeChain cuts).vertex (K.sampledEdgeChainSampleIndex cuts s) =
      K.edgeSamplePoint cuts s := by
    exact K.sampledEdgeChain_vertex_sample cuts s
  rw [hj] at h
  exact h

/-- Every arrangement face lies wholly on one side of every rational mark on an original edge,
when measured in that edge's affine coordinate. -/
theorem sampledFace_parameter_side (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace)) (r : Fin (cuts + 2))
    {u : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex}
    (hu : u ∈ (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.simplexes) :
    (∀ v ∈ u, K.edgeParameter i
        ((K.sampledEdgeChain cuts).arrangementMesh.position v) ≤
          r.val / (cuts + 1 : ℝ)) ∨
      (∀ v ∈ u, r.val / (cuts + 1 : ℝ) ≤ K.edgeParameter i
        ((K.sampledEdgeChain cuts).arrangementMesh.position v)) := by
  let M := (K.sampledEdgeChain cuts).arrangementMesh
  let sample : K.EdgeSample cuts := (i, r)
  obtain ⟨-, T, hT, huT⟩ := M.mem_faces_iff.mp hu
  unfold edgeParameter
  split_ifs with hx
  · have hmono := K.sampledEdgeArrangement_monochromatic_vertical cuts sample
    rcases hmono T hT with hnonneg | hnonpos
    · by_cases hΔ : 0 < K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0
      · right
        intro v hv
        apply normalized_ge_of_line_nonneg hΔ
        have hline := hnonneg v (huT hv)
        change 0 ≤ M.position v 0 - K.edgeSamplePoint cuts sample 0 at hline
        simpa [edgeSamplePoint, sample, M, AffineMap.lineMap_apply_module] using hline
      · have hΔ' : K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0 < 0 := by
          have hne : K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0 ≠ 0 :=
            sub_ne_zero.mpr hx.symm
          exact lt_of_le_of_ne (le_of_not_gt hΔ) hne
        left
        intro v hv
        apply normalized_le_of_line_nonneg_of_neg hΔ'
        have hline := hnonneg v (huT hv)
        change 0 ≤ M.position v 0 - K.edgeSamplePoint cuts sample 0 at hline
        simpa [edgeSamplePoint, sample, M, AffineMap.lineMap_apply_module] using hline
    · by_cases hΔ : 0 < K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0
      · left
        intro v hv
        apply normalized_le_of_line_nonpos hΔ
        have hline := hnonpos v (huT hv)
        change M.position v 0 - K.edgeSamplePoint cuts sample 0 ≤ 0 at hline
        simpa [edgeSamplePoint, sample, M, AffineMap.lineMap_apply_module] using hline
      · have hΔ' : K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0 < 0 := by
          have hne : K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0 ≠ 0 :=
            sub_ne_zero.mpr hx.symm
          exact lt_of_le_of_ne (le_of_not_gt hΔ) hne
        right
        intro v hv
        apply normalized_ge_of_line_nonpos_of_neg hΔ'
        have hline := hnonpos v (huT hv)
        change M.position v 0 - K.edgeSamplePoint cuts sample 0 ≤ 0 at hline
        simpa [edgeSamplePoint, sample, M, AffineMap.lineMap_apply_module] using hline
  · have hxy : K.position (K.edgeFirst i) 1 ≠ K.position (K.edgeSecond i) 1 := by
      intro hy
      apply K.position_injective.ne (K.edgeFirst_ne_edgeSecond i)
      exact plane_ext (not_ne_iff.mp hx) hy
    have hmono := K.sampledEdgeArrangement_monochromatic_horizontal cuts sample
    rcases hmono T hT with hnonneg | hnonpos
    · by_cases hΔ : 0 < K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1
      · right
        intro v hv
        apply normalized_ge_of_line_nonneg hΔ
        have hline := hnonneg v (huT hv)
        change 0 ≤ M.position v 1 - K.edgeSamplePoint cuts sample 1 at hline
        simpa [edgeSamplePoint, sample, M, AffineMap.lineMap_apply_module] using hline
      · have hΔ' : K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1 < 0 := by
          have hne : K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1 ≠ 0 :=
            sub_ne_zero.mpr hxy.symm
          exact lt_of_le_of_ne (le_of_not_gt hΔ) hne
        left
        intro v hv
        apply normalized_le_of_line_nonneg_of_neg hΔ'
        have hline := hnonneg v (huT hv)
        change 0 ≤ M.position v 1 - K.edgeSamplePoint cuts sample 1 at hline
        simpa [edgeSamplePoint, sample, M, AffineMap.lineMap_apply_module] using hline
    · by_cases hΔ : 0 < K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1
      · left
        intro v hv
        apply normalized_le_of_line_nonpos hΔ
        have hline := hnonpos v (huT hv)
        change M.position v 1 - K.edgeSamplePoint cuts sample 1 ≤ 0 at hline
        simpa [edgeSamplePoint, sample, M, AffineMap.lineMap_apply_module] using hline
      · have hΔ' : K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1 < 0 := by
          have hne : K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1 ≠ 0 :=
            sub_ne_zero.mpr hxy.symm
          exact lt_of_le_of_ne (le_of_not_gt hΔ) hne
        right
        intro v hv
        apply normalized_ge_of_line_nonpos_of_neg hΔ'
        have hline := hnonpos v (huT hv)
        change M.position v 1 - K.edgeSamplePoint cuts sample 1 ≤ 0 at hline
        simpa [edgeSamplePoint, sample, M, AffineMap.lineMap_apply_module] using hline

theorem sampledFaceCarrier_parameter_side (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace)) (r : Fin (cuts + 2))
    {u : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex}
    (hu : u ∈ (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.simplexes) :
    (∀ x ∈ (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.cellCarrier u,
        K.edgeParameter i x ≤ r.val / (cuts + 1 : ℝ)) ∨
      (∀ x ∈ (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.cellCarrier u,
        r.val / (cuts + 1 : ℝ) ≤ K.edgeParameter i x) := by
  rcases K.sampledFace_parameter_side cuts i r hu with hle | hge
  · left
    intro x hx
    apply convexHull_min ?_ ((convex_Iic (r.val / (cuts + 1 : ℝ))).affine_preimage
      (K.edgeParameter i)) hx
    rintro y ⟨v, hv, rfl⟩
    exact hle v hv
  · right
    intro x hx
    apply convexHull_min ?_ ((convex_Ici (r.val / (cuts + 1 : ℝ))).affine_preimage
      (K.edgeParameter i)) hx
    rintro y ⟨v, hv, rfl⟩
    exact hge v hv

theorem sampledFace_parameter_diameter (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace))
    {u : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex}
    (hu : u ∈ (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.simplexes)
    (hui : (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.cellCarrier u ⊆
      K.cellCarrier (K.edgeAt i).1)
    {x y : Plane}
    (hx : x ∈ (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.cellCarrier u)
    (hy : y ∈ (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.cellCarrier u) :
    |K.edgeParameter i x - K.edgeParameter i y| ≤ 1 / (cuts + 1 : ℝ) := by
  have hbound : |K.edgeParameter i x - K.edgeParameter i y| ≤
      1 / ((cuts + 1 : ℕ) : ℝ) := by
    apply abs_sub_le_inv_nat_of_same_grid_side (D := cuts + 1) (by omega)
      (K.edgeParameter_mem_Icc i (hui hx)) (K.edgeParameter_mem_Icc i (hui hy))
    intro r
    rcases K.sampledFaceCarrier_parameter_side cuts i r hu with hle | hge
    · left
      constructor
      · simpa only [Nat.cast_add, Nat.cast_one] using hle x hx
      · simpa only [Nat.cast_add, Nat.cast_one] using hle y hy
    · right
      constructor
      · simpa only [Nat.cast_add, Nat.cast_one] using hge x hx
      · simpa only [Nat.cast_add, Nat.cast_one] using hge y hy
  simpa only [Nat.cast_add, Nat.cast_one] using hbound

theorem sampledEdgeChain_vertex_original (cuts : ℕ)
    (i : Fin (Fintype.card K.Vertex)) :
    (K.sampledEdgeChain cuts).vertex
      ⟨2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val, by
        change 2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val <
          2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) +
            Fintype.card K.Vertex + 1
        omega⟩ = K.position (K.vertexAt i) := by
  classical
  simp only [sampledEdgeChain]
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  have hsub : 2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val -
      (2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts)) = i.val := by omega
  congr 2
  exact Fin.ext hsub

/-- The `sampledEdgeChainIndex` declaration. -/
noncomputable def sampledEdgeChainIndex (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace)) : Fin (K.sampledEdgeChain cuts).n :=
  ⟨2 * i.val, by
    change 2 * i.val < 2 * Fintype.card K.EdgeFace +
      Fintype.card (K.EdgeSample cuts) + Fintype.card K.Vertex
    have hm : 0 < Fintype.card K.EdgeFace :=
      Fintype.card_pos_iff.mpr ⟨K.edgeAt i⟩
    omega⟩

theorem sampledEdgeChainIndex_castSucc (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace)) :
    (K.sampledEdgeChainIndex cuts i).castSucc =
      ⟨2 * i.val, by
        change 2 * i.val < 2 * Fintype.card K.EdgeFace +
          Fintype.card (K.EdgeSample cuts) + Fintype.card K.Vertex + 1
        omega⟩ := by
  rfl

theorem sampledEdgeChainIndex_succ (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace)) :
    (K.sampledEdgeChainIndex cuts i).succ =
      ⟨2 * i.val + 1, by
        change 2 * i.val + 1 < 2 * Fintype.card K.EdgeFace +
          Fintype.card (K.EdgeSample cuts) + Fintype.card K.Vertex + 1
        omega⟩ := by
  rfl

theorem sampledEdgeChain_segment (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace)) :
    segment ℝ
        ((K.sampledEdgeChain cuts).vertex (K.sampledEdgeChainIndex cuts i).castSucc)
        ((K.sampledEdgeChain cuts).vertex (K.sampledEdgeChainIndex cuts i).succ) =
      K.cellCarrier (K.edgeAt i).1 := by
  rw [K.sampledEdgeChainIndex_castSucc, K.sampledEdgeChainIndex_succ,
    K.sampledEdgeChain_vertex_even, K.sampledEdgeChain_vertex_odd, K.edgeAt_eq,
    PlaneComplex.cellCarrier]
  have himage : K.position ''
      (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
      {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
    ext x
    simp [eq_comm]
  rw [himage, convexHull_pair]

/-- The `sampledEdgeArrangement` declaration. -/
noncomputable def sampledEdgeArrangement (cuts : ℕ) : PlaneComplex :=
  (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex

/-- The `sampledEdgeSubdivision` declaration. -/
noncomputable def sampledEdgeSubdivision (cuts : ℕ) : PlaneComplex :=
  (K.sampledEdgeArrangement cuts).subordinateTo K

/-- Every point of an original graph face lies in a sampled-subdivision face contained in that
same original face. -/
theorem exists_sampledEdgeSubdivision_face_at (cuts : ℕ)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    {s : Finset K.Vertex} (hs : s ∈ K.simplexes) {x : Plane}
    (hxs : x ∈ K.cellCarrier s) :
    ∃ u ∈ (K.sampledEdgeSubdivision cuts).simplexes,
      x ∈ (K.sampledEdgeSubdivision cuts).cellCarrier u ∧
        (K.sampledEdgeSubdivision cuts).cellCarrier u ⊆ K.cellCarrier s := by
  have hspos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem s hs)
  have hscard := hgraph s hs
  have hcases : s.card = 1 ∨ s.card = 2 := by omega
  rcases hcases with hsone | hstwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
    have hxv : x = K.position v := by
      simpa [PlaneComplex.cellCarrier] using hxs
    obtain ⟨i, hi⟩ := K.exists_vertexAt v
    let j : Fin ((K.sampledEdgeChain cuts).n + 1) :=
      ⟨2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val, by
        change 2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val <
          2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) +
            Fintype.card K.Vertex + 1
        omega⟩
    obtain ⟨w, hwpos, hwface⟩ :=
      (K.sampledEdgeChain cuts).exists_arrangementVertex_position_eq j
    let u : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex := {w}
    have huCarrier : (K.sampledEdgeSubdivision cuts).cellCarrier u ⊆
        K.cellCarrier ({v} : Finset K.Vertex) := by
      intro y hy
      have hyw : y =
          (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w := by
        change y ∈ convexHull ℝ
          ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position ''
            (({w} : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex) :
              Set (K.sampledEdgeChain cuts).arrangementMesh.Vertex)) at hy
        have himage :
            (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position ''
                (({w} : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex) :
                  Set (K.sampledEdgeChain cuts).arrangementMesh.Vertex) =
              {(K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w} := by
          ext z
          constructor
          · rintro ⟨q, hq, hz⟩
            rw [Finset.mem_singleton.mp hq] at hz
            exact hz.symm
          · intro hz
            exact ⟨w, Finset.mem_singleton_self w, hz.symm⟩
        rw [himage, convexHull_singleton] at hy
        exact hy
      rw [hyw, hwpos, K.sampledEdgeChain_vertex_original cuts i, hi]
      exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩
    have hu : u ∈ (K.sampledEdgeSubdivision cuts).simplexes := by
      apply ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex
        |>.mem_subordinateTo_simplexes_iff K).mpr
      exact ⟨hwface, {v}, hs, huCarrier⟩
    refine ⟨u, hu, ?_, huCarrier⟩
    rw [hxv]
    change K.position v ∈ convexHull ℝ
      ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position ''
        (u : Set (K.sampledEdgeChain cuts).arrangementMesh.Vertex))
    exact subset_convexHull ℝ _ ⟨w, Finset.mem_singleton_self _, by
      rw [hwpos, K.sampledEdgeChain_vertex_original cuts i, hi]⟩
  · let e : K.EdgeFace := ⟨s, Finset.mem_filter.mpr ⟨hs, hstwo⟩⟩
    obtain ⟨i, hi⟩ := K.exists_edgeAt e
    have hsegment : segment ℝ
        ((K.sampledEdgeChain cuts).vertex (K.sampledEdgeChainIndex cuts i).castSucc)
        ((K.sampledEdgeChain cuts).vertex (K.sampledEdgeChainIndex cuts i).succ) =
        K.cellCarrier s := by
      rw [K.sampledEdgeChain_segment cuts i, hi]
    obtain ⟨u, hu, hxu, huSegment⟩ :=
      (K.sampledEdgeChain cuts).exists_face_on_segment
        (K.sampledEdgeChainIndex cuts i) (hsegment.symm ▸ hxs)
    have huCarrier : (K.sampledEdgeSubdivision cuts).cellCarrier u ⊆
        K.cellCarrier s := by
      rw [← hsegment]
      apply convexHull_min
      · rintro y ⟨w, hw, rfl⟩
        exact huSegment w hw
      · exact convex_segment _ _
    refine ⟨u, ?_, hxu, huCarrier⟩
    apply ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex
      |>.mem_subordinateTo_simplexes_iff K).mpr
    exact ⟨hu, s, hs, huCarrier⟩

theorem sampledEdgeSubdivision_support_eq (cuts : ℕ)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2) :
    (K.sampledEdgeSubdivision cuts).support = K.support := by
  unfold sampledEdgeSubdivision sampledEdgeArrangement
  apply Set.Subset.antisymm
  · exact (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.subordinateTo_support_subset K
  · intro x hx
    rw [PlaneComplex.support] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    have hspos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem s hs)
    have hscard := hgraph s hs
    have hcases : s.card = 1 ∨ s.card = 2 := by omega
    rw [PlaneComplex.support]
    simp only [Set.mem_iUnion]
    rcases hcases with hsone | hstwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
      have hxv : x = K.position v := by
        simpa [PlaneComplex.cellCarrier] using hxs
      obtain ⟨i, hi⟩ := K.exists_vertexAt v
      let j : Fin ((K.sampledEdgeChain cuts).n + 1) :=
        ⟨2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val, by
          change 2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val <
            2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) +
              Fintype.card K.Vertex + 1
          omega⟩
      obtain ⟨w, hwpos, hwface⟩ :=
        (K.sampledEdgeChain cuts).exists_arrangementVertex_position_eq j
      let u : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex := {w}
      refine ⟨u, ?_, ?_⟩
      · apply ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex
          |>.mem_subordinateTo_simplexes_iff K).mpr
        refine ⟨hwface, {v}, hs, ?_⟩
        intro y hy
        have hyw : y = (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w := by
          change y ∈ convexHull ℝ
            ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex) :
                Set (K.sampledEdgeChain cuts).arrangementMesh.Vertex)) at hy
          have himage : (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex) :
                Set (K.sampledEdgeChain cuts).arrangementMesh.Vertex) =
              {(K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w} := by
            ext z
            constructor
            · rintro ⟨q, hq, rfl⟩
              have hqw : q = w := Finset.mem_singleton.mp hq
              subst q
              rfl
            · intro hz
              have hz' : z =
                  (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w :=
                Set.mem_singleton_iff.mp hz
              subst z
              exact ⟨w, Finset.mem_singleton_self _, rfl⟩
          rw [himage, convexHull_singleton] at hy
          exact hy
        rw [hyw, hwpos, show (K.sampledEdgeChain cuts).vertex j = K.position v by
          rw [K.sampledEdgeChain_vertex_original cuts i, hi]]
        exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩
      · rw [hxv]
        rw [show
          ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.subordinateTo K).cellCarrier u =
            (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.cellCarrier u from
          (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.subordinateTo_cellCarrier K u]
        exact subset_convexHull ℝ _ ⟨w, Finset.mem_singleton_self _, by
          rw [hwpos, K.sampledEdgeChain_vertex_original cuts i, hi]⟩
    · let e : K.EdgeFace := ⟨s, Finset.mem_filter.mpr ⟨hs, hstwo⟩⟩
      obtain ⟨i, hi⟩ := K.exists_edgeAt e
      have hsegment : segment ℝ
          ((K.sampledEdgeChain cuts).vertex (K.sampledEdgeChainIndex cuts i).castSucc)
          ((K.sampledEdgeChain cuts).vertex (K.sampledEdgeChainIndex cuts i).succ) =
          K.cellCarrier s := by
        rw [K.sampledEdgeChain_segment cuts i, hi]
      obtain ⟨u, hu, hxu, huSegment⟩ :=
        (K.sampledEdgeChain cuts).exists_face_on_segment
          (K.sampledEdgeChainIndex cuts i) (hsegment.symm ▸ hxs)
      refine ⟨u, ?_, hxu⟩
      apply ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex
        |>.mem_subordinateTo_simplexes_iff K).mpr
      refine ⟨hu, s, hs, ?_⟩
      rw [← hsegment]
      apply convexHull_min
      · rintro y ⟨w, hw, rfl⟩
        exact huSegment w hw
      · exact convex_segment _ _

/-- Every original vertex position which lies in the graph support becomes an actual zero-face
of the sampled subdivision.  The extra original-vertex marks in `sampledEdgeChain` ensure this
even when the original abstract vertex was not itself used by a face. -/
theorem exists_sampledEdgeSubdivision_vertex_position_eq (cuts : ℕ) (v : K.Vertex)
    (hv : K.position v ∈ K.support) :
    ∃ w : (K.sampledEdgeSubdivision cuts).Vertex,
      (K.sampledEdgeSubdivision cuts).position w = K.position v ∧
        ({w} : Finset (K.sampledEdgeSubdivision cuts).Vertex) ∈
          (K.sampledEdgeSubdivision cuts).simplexes := by
  obtain ⟨i, hi⟩ := K.exists_vertexAt v
  let j : Fin ((K.sampledEdgeChain cuts).n + 1) :=
    ⟨2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val, by
      change 2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val <
        2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) +
          Fintype.card K.Vertex + 1
      omega⟩
  obtain ⟨w, hwpos, hwface⟩ :=
    (K.sampledEdgeChain cuts).exists_arrangementVertex_position_eq j
  rw [PlaneComplex.support] at hv
  simp only [Set.mem_iUnion] at hv
  obtain ⟨s, hs, hvs⟩ := hv
  refine ⟨w, ?_, ?_⟩
  · change (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w = K.position v
    rw [hwpos, K.sampledEdgeChain_vertex_original cuts i, hi]
  · apply ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex
      |>.mem_subordinateTo_simplexes_iff K).mpr
    refine ⟨hwface, s, hs, ?_⟩
    intro y hy
    have hyw : y =
        (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w := by
      change y ∈ convexHull ℝ
        ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position ''
          (({w} : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex) :
            Set (K.sampledEdgeChain cuts).arrangementMesh.Vertex)) at hy
      have himage :
          (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex) :
                Set (K.sampledEdgeChain cuts).arrangementMesh.Vertex) =
            {(K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w} := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          rw [Finset.mem_singleton.mp hx]
          exact Set.mem_singleton _
        · intro hz
          have hz' : z =
              (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w :=
            Set.mem_singleton_iff.mp hz
          subst z
          exact ⟨w, Finset.mem_singleton_self w, rfl⟩
      rwa [himage, convexHull_singleton] at hy
    rw [hyw, hwpos, K.sampledEdgeChain_vertex_original cuts i, hi]
    exact hvs

theorem sampledEdgeSubdivision_subdivides (cuts : ℕ)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2) :
    (K.sampledEdgeSubdivision cuts).Subdivides K :=
  (K.sampledEdgeArrangement cuts).subordinateTo_subdivides K
    (K.sampledEdgeSubdivision_support_eq cuts hgraph)

/-- A positive common upper bound for the lengths of all enumerated edges. -/
noncomputable def edgeLengthBound : ℝ :=
  1 + ∑ i : Fin (Fintype.card K.EdgeFace),
    dist (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i))

theorem edgeLengthBound_pos : 0 < K.edgeLengthBound := by
  unfold edgeLengthBound
  have hsum : 0 ≤ ∑ i : Fin (Fintype.card K.EdgeFace),
      dist (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i)) :=
    Finset.sum_nonneg fun _ _ => dist_nonneg
  linarith

theorem edge_length_lt_bound (i : Fin (Fintype.card K.EdgeFace)) :
    dist (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i)) <
      K.edgeLengthBound := by
  unfold edgeLengthBound
  have hi : dist (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i)) ≤
      ∑ j : Fin (Fintype.card K.EdgeFace),
        dist (K.position (K.edgeFirst j)) (K.position (K.edgeSecond j)) :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin (Fintype.card K.EdgeFace) =>
        dist (K.position (K.edgeFirst j)) (K.position (K.edgeSecond j)))
      (fun _ _ => dist_nonneg) (Finset.mem_univ i)
  linarith

/-- Heine--Cantor plus the marked line arrangement: every finite embedded graph has a subordinate
subdivision whose faces have arbitrarily small image diameter under a continuous map. -/
theorem exists_sampledEdgeSubdivision_image_diameter_lt
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    {η : ℝ} (hη : 0 < η) :
    ∃ cuts : ℕ, ∀ u ∈ (K.sampledEdgeSubdivision cuts).simplexes,
      ∀ x ∈ (K.sampledEdgeSubdivision cuts).cellCarrier u,
        ∀ y ∈ (K.sampledEdgeSubdivision cuts).cellCarrier u,
          dist (h x) (h y) < η := by
  have huc := K.isCompact_support.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hmod⟩ := huc η hη
  obtain ⟨N, hN⟩ := exists_nat_gt (K.edgeLengthBound / δ)
  have hNreal : K.edgeLengthBound / δ < (N : ℝ) := hN
  have hratio : K.edgeLengthBound / (N + 1 : ℝ) < δ := by
    have hNpos : (0 : ℝ) < N + 1 := by positivity
    apply (div_lt_iff₀ hNpos).mpr
    have hmul : K.edgeLengthBound < δ * N := by
      have hmul' := (div_lt_iff₀ hδ).mp hNreal
      simpa [mul_comm] using hmul'
    nlinarith
  refine ⟨N, ?_⟩
  intro u hu x hx y hy
  obtain ⟨huA, s, hs, hus⟩ :=
    (K.sampledEdgeArrangement N |>.mem_subordinateTo_simplexes_iff K).mp hu
  have hspos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem s hs)
  have hscard := hgraph s hs
  have hcases : s.card = 1 ∨ s.card = 2 := by omega
  have hxK : x ∈ K.support := K.cellCarrier_subset_support hs (hus hx)
  have hyK : y ∈ K.support := K.cellCarrier_subset_support hs (hus hy)
  rcases hcases with hsone | hstwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
    have hxy : x = y := by
      have hxv : x = K.position v := by
        simpa [PlaneComplex.cellCarrier] using hus hx
      have hyv : y = K.position v := by
        simpa [PlaneComplex.cellCarrier] using hus hy
      exact hxv.trans hyv.symm
    subst y
    simpa using hη
  · let e : K.EdgeFace := ⟨s, Finset.mem_filter.mpr ⟨hs, hstwo⟩⟩
    obtain ⟨i, hi⟩ := K.exists_edgeAt e
    have husI : (K.sampledEdgeChain N).arrangementMesh.toPlaneComplex.cellCarrier u ⊆
        K.cellCarrier (K.edgeAt i).1 := by
      simpa [sampledEdgeArrangement, hi] using hus
    have hparam := K.sampledFace_parameter_diameter N i huA husI hx hy
    have hxline := K.lineMap_edgeParameter_eq i (husI hx)
    have hyline := K.lineMap_edgeParameter_eq i (husI hy)
    have hdistXY : dist x y < δ := by
      rw [← hxline, ← hyline, dist_lineMap_lineMap]
      have hparam' : dist (K.edgeParameter i x) (K.edgeParameter i y) ≤
          1 / (N + 1 : ℝ) := by
        simpa [Real.dist_eq] using hparam
      calc
        dist (K.edgeParameter i x) (K.edgeParameter i y) *
            dist (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i)) ≤
          (1 / (N + 1 : ℝ)) *
            dist (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i)) :=
              mul_le_mul_of_nonneg_right hparam' dist_nonneg
        _ < (1 / (N + 1 : ℝ)) * K.edgeLengthBound := by
          exact mul_lt_mul_of_pos_left (K.edge_length_lt_bound i) (by positivity)
        _ = K.edgeLengthBound / (N + 1 : ℝ) := by ring
        _ < δ := hratio
    exact hmod x hxK y hyK hdistXY

end PlaneComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
