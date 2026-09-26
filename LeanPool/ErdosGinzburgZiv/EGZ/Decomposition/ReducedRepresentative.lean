/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Pullback

/-!
# A reduced representative with the same cumulative weight

The face index of the whole polytope is the join of all proper bases below
the node. Every nonzero local summand has such a base, so passing to this
reduced node preserves the entire cumulative function.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f)

theorem localWeight_base_le_faceIndex_top (hp : Odd p) {y x : Φ.flag.Node}
    (h : y ≤ x) (v : FpCoord p d) (hv : Φ.localWeight y v ≠ 0) :
    y ≤ Φ.faceIndex x ⊤ := by
  classical
  let z := FpCoord.centeredLift (Φ.representation.map y v)
  have hz : Φ.localLift y z ≠ 0 := by
    exact (FlagDecompositionRaw.localLift_ne_zero_iff _ _ _ _).mpr
      ⟨FpCoord.isCenteredLift_centeredLift hp _, v,
        (FpCoord.mod_centeredLift _).symm, hv⟩
  have hzP : z.real ∈ (Φ.flag.polytope y).carrier :=
    Φ.originalWeights.mem_old_polytope
      (ne_of_gt ((Nat.pos_of_ne_zero hz).trans_le (Φ.localLift_le_hat y z)))
  let q : Φ.flag.Point := ⟨y, z.real, hzP⟩
  have hq : q ∈ Φ.omega := ConvexFlag.subset_convexHull Φ.flag _ ⟨z, rfl, hz⟩
  apply Finset.le_sup' (f := id)
  simp only [faceBases, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨q, ⟨hq, h, q.coord_mem h⟩, rfl⟩

theorem cumulativeWeight_faceIndex_top (hp : Odd p) (x : Φ.flag.Node) :
    Φ.cumulativeWeight (Φ.faceIndex x ⊤) = Φ.cumulativeWeight x := by
  classical
  funext v
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y ≤ Φ.faceIndex x ⊤
  · simp only [ite_eq_left hy, ite_eq_left (hy.trans (Φ.faceIndex_le x ⊤))]
  · by_cases hyx : y ≤ x
    · have hv : Φ.localWeight y v = 0 := by
        by_contra hv
        exact hy (Φ.localWeight_base_le_faceIndex_top hp hyx v hv)
      simp only [ite_eq_right hy, ite_eq_left hyx, hv]
    · simp only [ite_eq_right hy, ite_eq_right hyx]

/-- Every node has a reduced node below it carrying the same cumulative
function. In a minimal decomposition their finite-field spaces also agree. -/
theorem exists_reducedRepresentative (hp : Odd p) (x : Φ.flag.Node) :
    ∃ y, y ≤ x ∧ Φ.IsReducedElement y ∧ Φ.cumulativeWeight y = Φ.cumulativeWeight x :=
  ⟨Φ.faceIndex x ⊤, Φ.faceIndex_le x ⊤, Φ.isReducedElement_faceIndex x ⊤,
    Φ.cumulativeWeight_faceIndex_top hp x⟩

theorem space_faceIndex_top (hp : Odd p) (hminimal : Φ.IsMinimal) (x : Φ.flag.Node) :
    Φ.representation.space (Φ.faceIndex x ⊤) = Φ.representation.space x := by
  rw [(hminimal _).1, (hminimal _).1, Φ.cumulativeWeight_faceIndex_top hp x]

/-- With minimal spaces, completeness passes to the reduced representative:
its finer representation can only make the fibre condition weaker. -/
theorem isCompleteElement_faceIndex_top (hp : Odd p) (hminimal : Φ.IsMinimal)
    (x : Φ.flag.Node) {t : ℕ} {δ : ℝ} (hc : Φ.IsCompleteElement x t δ) :
    Φ.IsCompleteElement (Φ.faceIndex x ⊤) t δ := by
  intro ξ hξ
  rw [Φ.cumulativeWeight_faceIndex_top hp x]
  apply hc ξ
  obtain ⟨v, w, hv, hw, hmap, hξ⟩ := hξ
  refine ⟨v, w, ?_, ?_, ?_, hξ⟩
  · rwa [← Φ.space_faceIndex_top hp hminimal x]
  · rwa [← Φ.space_faceIndex_top hp hminimal x]
  · rw [Φ.representation.compatible (Φ.faceIndex_le x ⊤) hv,
      Φ.representation.compatible (Φ.faceIndex_le x ⊤) hw, hmap]

end EGZ.FlagDecomposition
