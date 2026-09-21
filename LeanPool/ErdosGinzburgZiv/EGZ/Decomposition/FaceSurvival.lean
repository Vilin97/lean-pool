/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceRefinement
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedDecomposition
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ReducedRepresentative

/-!
# Survival of the upper anchor in a proper-face refinement

An unselected cumulative atom supplies an upper-layer local generator. The
other generators witnessing old reducedness still have active copies, so
their join together with this upper generator is the old upper node.
-/

open Classical

namespace EGZ.FlagDecomposition.FaceRefinement

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node)
    (selected : FpCoord p d → Prop) (hp : Odd p)

/-- A reduced old node remains reduced upstairs when some cumulative atom
at that node is not moved to the lower layer. -/
theorem upper_isReducedElement_of_unselected (x : Φ.flag.Node)
    (hred : Φ.IsReducedElement x)
    (houtside : ∃ v, Φ.cumulativeWeight x v ≠ 0 ∧ ¬ selected v) :
    (decomposition Φ anchor selected hp).IsReducedElement (upper Φ anchor selected hp x) := by
  let Ψ := decomposition Φ anchor selected hp
  let b : Ψ.flag.Node := Ψ.faceIndex (upper Φ anchor selected hp x) ⊤
  have hlocal : ∀ y, y ≤ x → ∀ v, Φ.localWeight y v ≠ 0 → y ≤ b.val.val.1 := by
    intro y hyx v hv
    obtain ⟨a, hay, hav⟩ := TwoLayer.exists_splitWeight_eq anchor Φ.localWeight selected y v
    have hmass : (splitWeights Φ anchor selected).weight a v ≠ 0 := by
      change TwoLayer.splitWeight anchor Φ.localWeight selected a v ≠ 0
      rwa [hav]
    let a' : Ψ.flag.Node := ⟨a, ⟨a, le_rfl, v, hmass⟩⟩
    have ha'x : a' ≤ upper Φ anchor selected hp x := by
      change a.val.1 ≤ x ∧ a.val.2 ≤ 1
      refine ⟨?_, by have := a.val.2.isLt; omega⟩
      change TwoLayer.projection anchor a ≤ x
      rwa [hay]
    have hab := Ψ.localWeight_base_le_faceIndex_top hp ha'x v hmass
    change a.val.1 ≤ b.val.val.1 ∧ a.val.2 ≤ b.val.val.2 at hab
    exact hay ▸ hab.1
  have hproj : x ≤ b.val.val.1 := by
    obtain ⟨s, hs, hgen, hsup⟩ := (Φ.isReducedElement_iff_sup'_localWeight hp x).mp hred
    rw [← hsup]
    apply Finset.sup'_le _ _
    intro y hy
    obtain ⟨v, hv⟩ := hgen y hy
    apply hlocal y ?_ v hv
    rw [← hsup]
    exact Finset.le_sup' id hy
  obtain ⟨v, hv, hselected⟩ := houtside
  obtain ⟨y, hyx, hyv⟩ := (FlagDecompositionRaw.cumulative_ne_zero_iff Φ.localWeight x v).mp hv
  have hu : Ψ.localWeight (upper Φ anchor selected hp y) v ≠ 0 := by
    change TwoLayer.splitWeight anchor Φ.localWeight selected (TwoLayer.upper anchor y) v ≠ 0
    rw [TwoLayer.splitWeight_upper, ite_eq_right (by simp [hselected])]
    exact hyv
  have hupper : upper Φ anchor selected hp y ≤ upper Φ anchor selected hp x :=
    (upperOrderEmbedding Φ anchor selected hp).monotone hyx
  have hub := Ψ.localWeight_base_le_faceIndex_top hp hupper v hu
  have hlayer : b.val.val.2 = 1 := by
    change y ≤ b.val.val.1 ∧ (1 : Fin 2) ≤ b.val.val.2 at hub
    have := b.val.val.2.isLt
    have := hub.2
    omega
  have hbx := Ψ.faceIndex_le (upper Φ anchor selected hp x) ⊤
  have heq : b = upper Φ anchor selected hp x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact le_antisymm hbx.1 hproj
    · exact hlayer
  rw [← heq]
  exact Ψ.isReducedElement_faceIndex _ _

omit selected in
/-- A proper face leaves an unselected cumulative atom. -/
theorem exists_unselected_of_ne_top (Γ : (Φ.flag.polytope anchor).Face) (hΓ : Γ ≠ ⊤) :
    ∃ v, Φ.cumulativeWeight anchor v ≠ 0 ∧ ¬ Φ.faceSelector anchor Γ v := by
  have houtside : ∃ q ∈ Φ.liftedSupport anchor, q.real ∉ Γ.carrier := by
    by_contra! h
    apply hΓ
    apply RationalPolytope.Face.ext
    apply Set.Subset.antisymm Γ.subset_polytope
    rw [Φ.polytope_eq_liftedSupport]
    apply convexHull_min _ Γ.convex
    rintro _ ⟨q, hq, rfl⟩
    exact h q hq
  obtain ⟨q, hq, hqface⟩ := houtside
  obtain ⟨hc, v, hmap, hv⟩ := (Φ.originalWeights.hat_ne_zero_iff anchor q).mp
    ((Φ.liftedSupport_spec anchor q).mp hq)
  refine ⟨v, hv, ?_⟩
  change (FpCoord.centeredLift (Φ.representation.map anchor v)).real ∉ Γ.carrier
  rwa [hmap, FpCoord.centeredLift_mod hc]

omit selected in
/-- The upper anchor of a proper-face refinement survives restriction to
the reduced nodes. -/
theorem face_upperAnchor_isReduced (Γ : (Φ.flag.polytope anchor).Face) (hΓ : Γ ≠ ⊤)
    (hred : Φ.IsReducedElement anchor) :
    (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).IsReducedElement
      (upper Φ anchor (Φ.faceSelector anchor Γ) hp anchor) :=
  upper_isReducedElement_of_unselected Φ anchor (Φ.faceSelector anchor Γ) hp anchor hred
    (exists_unselected_of_ne_top Φ anchor Γ hΓ)

end EGZ.FlagDecomposition.FaceRefinement
