/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CenteredLift

/-!
# Reduced nodes of a flag decomposition

A base occurs in a flag convex hull precisely when it is a nonempty finite
join of bases of generating points.  In particular the reduced nodes are
closed under joins.  These are the order-theoretic facts used when removing
inactive nodes in the reduced-decomposition lemma.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ.ConvexFlag

/-- Every nonempty finite join of generator bases occurs in the flag hull.
The witnesses are combined with equal, strictly positive coefficients. -/
theorem exists_mem_convexHull_base_sup' {F : ConvexFlag} {S : Set F.Point}
    (s : Finset F.Node) (hs : s.Nonempty)
    (hS : ∀ x ∈ s, ∃ q ∈ S, q.base = x) :
    ∃ q ∈ F.convexHull S, q.base = s.sup' hs id := by
  classical
  let I := {x // x ∈ s}
  let : Nonempty I := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  have hpoints (i : I) : ∃ q ∈ S, q.base = i.1 := hS i.1 i.2
  choose points hmem hbase using hpoints
  let weight : I → ℝ := fun _ ↦ (Fintype.card I : ℝ)⁻¹
  have hcard : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  have hweight (i : I) : 0 < weight i := inv_pos.mpr hcard
  have hsum : (∑ i, weight i) = 1 := by
    simp [weight, ne_of_gt hcard]
  obtain ⟨q, hq⟩ := exists_convexCombination points weight
    (fun i ↦ (hweight i).le) hsum
  refine ⟨q, ?_, le_antisymm ?_ ?_⟩
  · let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
    exact ⟨Fintype.card I, points ∘ e, weight ∘ e,
      fun i ↦ hmem (e i), hq.reindex e⟩
  · apply hq.base_isLUB.2
    intro i _
    rw [hbase i]
    exact Finset.le_sup' id i.2
  · apply Finset.sup'_le
    intro x hx
    exact (hbase ⟨x, hx⟩).symm.trans_le
      (hq.base_isLUB.1 ⟨x, hx⟩ (hweight ⟨x, hx⟩))

/-- The bases occurring in a flag convex hull are exactly the nonempty
finite joins of bases occurring in its generating set. -/
theorem exists_mem_convexHull_base_iff {F : ConvexFlag} {S : Set F.Point}
    (x : F.Node) :
    (∃ q ∈ F.convexHull S, q.base = x) ↔
      ∃ (s : Finset F.Node) (hs : s.Nonempty),
        (∀ y ∈ s, ∃ q ∈ S, q.base = y) ∧ s.sup' hs id = x := by
  classical
  constructor
  · rintro ⟨q, ⟨n, points, weight, hmem, hcomb⟩, rfl⟩
    have hpos : ∃ i, 0 < weight i := by
      by_contra! h
      have hz : ∀ i, weight i = 0 := fun i ↦
        le_antisymm (h i) (hcomb.nonnegative i)
      have hsum := hcomb.sum_eq_one
      simp [hz] at hsum
    let active := Finset.univ.filter (fun i ↦ 0 < weight i)
    let s := active.image (fun i ↦ (points i).base)
    have hs : s.Nonempty := by
      obtain ⟨i, hi⟩ := hpos
      exact ⟨(points i).base, Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩⟩
    refine ⟨s, hs, ?_, le_antisymm ?_ ?_⟩
    · intro y hy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨points i, hmem i, rfl⟩
    · apply Finset.sup'_le
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact hcomb.base_isLUB.1 i (Finset.mem_filter.mp hi).2
    · apply hcomb.base_isLUB.2
      intro i hi
      exact Finset.le_sup' id (show (points i).base ∈ s from
        Finset.mem_image.mpr
          ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩)
  · rintro ⟨s, hs, hS, rfl⟩
    exact exists_mem_convexHull_base_sup' s hs hS

/-- Bases of proper points are closed under every nonempty finite join. -/
theorem ProperPointSet.exists_mem_base_sup' {F : ConvexFlag}
    (Ω : F.ProperPointSet) (s : Finset F.Node) (hs : s.Nonempty)
    (hS : ∀ x ∈ s, ∃ q ∈ Ω.carrier, q.base = x) :
    ∃ q ∈ Ω.carrier, q.base = s.sup' hs id := by
  obtain ⟨q, hq, hbase⟩ := exists_mem_convexHull_base_sup' s hs hS
  exact ⟨q, Ω.convex_closed hq, hbase⟩

end EGZ.ConvexFlag

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

/-- A local weight is bounded by the cumulative weight at its own node. -/
theorem localWeight_le_cumulativeWeight (Φ : FlagDecomposition p d f)
    (x : Φ.flag.Node) (v : FpCoord p d) :
    Φ.localWeight x v ≤ Φ.cumulativeWeight x v := by
  classical
  unfold cumulativeWeight FlagDecompositionRaw.cumulativeWeight
  simpa using Finset.single_le_sum
    (f := fun y ↦ if y ≤ x then Φ.localWeight y v else 0)
    (fun y _ ↦ Nat.zero_le _) (Finset.mem_univ x)

/-- The local centered lift is bounded by the cumulative centered lift. -/
theorem localLift_le_hat (Φ : FlagDecomposition p d f)
    (x : Φ.flag.Node) (z : IntCoord (Φ.flag.rank x)) :
    Φ.localLift x z ≤ Φ.hat x z := by
  classical
  unfold localLift hat FlagDecompositionRaw.localLift FlagDecompositionRaw.hat
  split_ifs with hz
  · unfold FlagDecompositionRaw.affineFibreMass
    apply Finset.sum_le_sum
    intro v _
    split_ifs
    · exact Φ.localWeight_le_cumulativeWeight x v
    · exact le_rfl
  · exact le_rfl

/-- Every nonzero local lifted point belongs to its node polytope. -/
theorem mem_polytope_of_localLift_ne_zero (Φ : FlagDecomposition p d f)
    (x : Φ.flag.Node) (z : IntCoord (Φ.flag.rank x))
    (hz : Φ.localLift x z ≠ 0) : z.real ∈ (Φ.flag.polytope x).carrier := by
  rw [Φ.polytope_eq_liftedSupport]
  apply _root_.subset_convexHull ℝ
  exact ⟨z, (Φ.liftedSupport_spec x z).mpr
    (ne_of_gt ((Nat.pos_of_ne_zero hz).trans_le (Φ.localLift_le_hat x z))), rfl⟩

/-- A nonzero local lift supplies a generating point based at its node. -/
theorem isReducedElement_of_localLift_ne_zero (Φ : FlagDecomposition p d f)
    (x : Φ.flag.Node) (z : IntCoord (Φ.flag.rank x))
    (hz : Φ.localLift x z ≠ 0) : Φ.IsReducedElement x := by
  let q : Φ.flag.Point := ⟨x, z.real, Φ.mem_polytope_of_localLift_ne_zero x z hz⟩
  refine ⟨q, ConvexFlag.subset_convexHull Φ.flag Φ.omegaZero ?_, rfl⟩
  exact ⟨z, rfl, hz⟩

/-- Over an odd modulus every nonzero local weight is detected by its
centered lift, and therefore its node is reduced. -/
theorem isReducedElement_of_localWeight_ne_zero (Φ : FlagDecomposition p d f)
    (hp : Odd p) (x : Φ.flag.Node) (v : FpCoord p d)
    (hv : Φ.localWeight x v ≠ 0) : Φ.IsReducedElement x := by
  classical
  let z := FpCoord.centeredLift (Φ.representation.map x v)
  apply Φ.isReducedElement_of_localLift_ne_zero x z
  have hz : IsCenteredLift p z := FpCoord.isCenteredLift_centeredLift hp _
  have hmod : z.mod p = Φ.representation.map x v := FpCoord.mod_centeredLift _
  change (if IsCenteredLift p z then
    FlagDecompositionRaw.affineFibreMass (Φ.localWeight x)
      (Φ.representation.map x) (z.mod p) else 0) ≠ 0
  rw [ite_eq_left hz, hmod]
  have hle : Φ.localWeight x v ≤ FlagDecompositionRaw.affineFibreMass
      (Φ.localWeight x) (Φ.representation.map x) (Φ.representation.map x v) := by
    unfold FlagDecompositionRaw.affineFibreMass
    simpa using Finset.single_le_sum
      (f := fun w ↦ if Φ.representation.map x w = Φ.representation.map x v
        then Φ.localWeight x w else 0)
      (fun w _ ↦ Nat.zero_le _) (Finset.mem_univ v)
  exact ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le hle)

/-- Deleting a non-reduced node deletes no local mass. -/
theorem localWeight_eq_zero_of_not_isReducedElement
    (Φ : FlagDecomposition p d f) (hp : Odd p)
    {x : Φ.flag.Node} (hx : ¬ Φ.IsReducedElement x) (v : FpCoord p d) :
    Φ.localWeight x v = 0 := by
  by_contra hv
  exact hx (Φ.isReducedElement_of_localWeight_ne_zero hp x v hv)

/-- Reduced nodes are exactly the nonempty finite joins of local generator
bases, as in the paragraph preceding the reduced-decomposition lemma. -/
theorem isReducedElement_iff_sup'_omegaZero (Φ : FlagDecomposition p d f)
    (x : Φ.flag.Node) :
    Φ.IsReducedElement x ↔
      ∃ (s : Finset Φ.flag.Node) (hs : s.Nonempty),
        (∀ y ∈ s, ∃ q ∈ Φ.omegaZero, q.base = y) ∧ s.sup' hs id = x :=
  ConvexFlag.exists_mem_convexHull_base_iff x

/-- The description of reduced nodes directly in terms of nonzero local
lifts, matching the set displayed in the paper. -/
theorem isReducedElement_iff_sup'_localLift (Φ : FlagDecomposition p d f)
    (x : Φ.flag.Node) :
    Φ.IsReducedElement x ↔
      ∃ (s : Finset Φ.flag.Node) (hs : s.Nonempty),
        (∀ y ∈ s, ∃ z, Φ.localLift y z ≠ 0) ∧ s.sup' hs id = x := by
  rw [Φ.isReducedElement_iff_sup'_omegaZero]
  constructor
  · rintro ⟨s, hs, hgen, hsup⟩
    refine ⟨s, hs, ?_, hsup⟩
    intro y hy
    obtain ⟨q, ⟨z, _, hz⟩, rfl⟩ := hgen y hy
    exact ⟨z, hz⟩
  · rintro ⟨s, hs, hgen, hsup⟩
    refine ⟨s, hs, ?_, hsup⟩
    intro y hy
    obtain ⟨z, hz⟩ := hgen y hy
    let q : Φ.flag.Point := ⟨y, z.real, Φ.mem_polytope_of_localLift_ne_zero y z hz⟩
    exact ⟨q, ⟨z, rfl, hz⟩, rfl⟩

/-- The reduced nodes form a set closed under nonempty finite joins. -/
theorem isReducedElement_sup' (Φ : FlagDecomposition p d f)
    (s : Finset Φ.flag.Node) (hs : s.Nonempty)
    (hred : ∀ x ∈ s, Φ.IsReducedElement x) :
    Φ.IsReducedElement (s.sup' hs id) :=
  Φ.properPoints.exists_mem_base_sup' s hs hred

/-- In particular the join of two reduced nodes is reduced. -/
theorem isReducedElement_sup (Φ : FlagDecomposition p d f)
    {x y : Φ.flag.Node} (hx : Φ.IsReducedElement x)
    (hy : Φ.IsReducedElement y) : Φ.IsReducedElement (x ⊔ y) := by
  classical
  have h := Φ.isReducedElement_sup' {x, y} (by simp)
    (by intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption)
  simpa using h

/-- The index of any visible face is reduced, because it is a nonempty
finite join of bases of proper points on that face. -/
theorem isReducedElement_faceIndex (Φ : FlagDecomposition p d f)
    (x : Φ.flag.Node) (Γ : (Φ.flag.polytope x).Face) :
    Φ.IsReducedElement (Φ.faceIndex x Γ) := by
  classical
  unfold faceIndex
  apply Φ.isReducedElement_sup'
  intro y hy
  simp only [faceBases, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  obtain ⟨q, hq, hbase⟩ := hy
  exact ⟨q, hq.1, hbase⟩

end EGZ.FlagDecomposition
