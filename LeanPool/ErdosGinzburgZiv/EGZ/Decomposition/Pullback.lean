/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Rebuild
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartFlag
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FacePreservation

/-!
# Splitting local weights over a new node poset

An order-preserving map to the old nodes pulls back the old flag and its
representation. Local pieces dominated by the corresponding old summands
can then be rebuilt on their active nodes. This construction permits the
two-layer face refinement before the subsequent minimalization.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ

namespace ConvexFlag

variable (F : ConvexFlag) {N : Type*} [Fintype N] [SemilatticeSup N] [OrderTop N]

/-- Reindex all fibres along an order-preserving node map. -/
noncomputable abbrev reindex (node : N →o F.Node) : ConvexFlag where
  Node := N
  rank x := F.rank (node x)
  polytope x := F.polytope (node x)
  lattice x := F.lattice (node x)
  transition h := F.transition (node.monotone h)
  transition_mem h := F.transition_mem (node.monotone h)
  transition_lattice h := F.transition_lattice (node.monotone h)
  transition_refl x := F.transition_refl (node x)
  transition_trans hxy hyz := F.transition_trans (node.monotone hxy) (node.monotone hyz)

end ConvexFlag

namespace FpRepresentation

variable {p d : ℕ} {F : ConvexFlag} {N : Type*}
    [Fintype N] [SemilatticeSup N] [OrderTop N]

/-- Reindex the finite-field representation with the same node map. -/
noncomputable def reindex (R : FpRepresentation p d F) (node : N →o F.Node) :
    FpRepresentation p d (F.reindex node) where
  space x := R.space (node x)
  map x := R.map (node x)
  space_mono h := R.space_mono (node.monotone h)
  map_surjective x := R.map_surjective (node x)
  compatible h := R.compatible (node.monotone h)
  lattice_eq_standard x := R.lattice_eq_standard (node x)

end FpRepresentation

namespace FlagDecompositionRaw

variable {p d : ℕ} [NeZero p] {F : ConvexFlag}

omit [NeZero p] in
theorem cumulative_ne_zero_iff (pieces : F.Node → FpCoord p d → ℕ)
    (x : F.Node) (v : FpCoord p d) :
    cumulativeWeight pieces x v ≠ 0 ↔ ∃ y, y ≤ x ∧ pieces y v ≠ 0 := by
  classical
  constructor
  · intro hv
    obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
    by_cases hyx : y ≤ x
    · exact ⟨y, hyx, by simpa only [ite_eq_left hyx] using hy⟩
    · exact (hy (ite_eq_right hyx)).elim
  · rintro ⟨y, hyx, hy⟩
    have hle : pieces y v ≤ cumulativeWeight pieces x v := by
      simpa only [cumulativeWeight, ite_eq_left hyx] using Finset.single_le_sum
        (f := fun z ↦ if z ≤ x then pieces z v else 0)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ y)
    exact ne_of_gt ((Nat.pos_of_ne_zero hy).trans_le hle)

theorem affineFibreMass_ne_zero_iff {n : ℕ} (w : FpCoord p d → ℕ)
    (φ : FpCoord p d → FpCoord p n) (c : FpCoord p n) :
    affineFibreMass w φ c ≠ 0 ↔ ∃ v, φ v = c ∧ w v ≠ 0 := by
  classical
  constructor
  · intro h
    obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    by_cases heq : φ v = c
    · exact ⟨v, heq, by simpa only [ite_eq_left heq] using hv⟩
    · exact (hv (ite_eq_right heq)).elim
  · rintro ⟨v, heq, hv⟩
    apply ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le _)
    simpa only [affineFibreMass, ite_eq_left heq] using Finset.single_le_sum
      (f := fun v ↦ if φ v = c then w v else 0)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ v)

theorem hat_ne_zero_iff (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (x : F.Node) (q : IntCoord (F.rank x)) :
    hat R pieces x q ≠ 0 ↔ IsCenteredLift p q ∧
      ∃ v, R.map x v = q.mod p ∧ cumulativeWeight pieces x v ≠ 0 := by
  classical
  unfold hat
  by_cases hc : IsCenteredLift p q
  · rw [ite_eq_left hc, affineFibreMass_ne_zero_iff]
    exact (and_iff_right hc).symm
  · rw [ite_eq_right hc]
    simp only [ne_eq, not_true_eq_false, false_iff, not_and]
    exact fun h ↦ (hc h).elim

theorem localLift_ne_zero_iff (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (x : F.Node) (q : IntCoord (F.rank x)) :
    localLift R pieces x q ≠ 0 ↔ IsCenteredLift p q ∧
      ∃ v, R.map x v = q.mod p ∧ pieces x v ≠ 0 := by
  classical
  unfold localLift
  by_cases hc : IsCenteredLift p q
  · rw [ite_eq_left hc, affineFibreMass_ne_zero_iff]
    exact (and_iff_right hc).symm
  · rw [ite_eq_right hc]
    simp only [ne_eq, not_true_eq_false, false_iff, not_and]
    exact fun h ↦ (hc h).elim

end FlagDecompositionRaw

namespace FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f) {N : Type}
    [Fintype N] [SemilatticeSup N] [OrderTop N]

/-- Local weights distributed over a new poset with their old bases recorded. -/
structure SplitWeights (node : N →o Φ.flag.Node) where
  /-- The local multiplicities assigned to the new nodes, bounded by their original node
  weights. -/
  weight : N → FpCoord p d → ℕ
  weight_le : ∀ x v, weight x v ≤ Φ.localWeight (node x) v
  nonzero : ∃ x v, weight x v ≠ 0
  retained_le : ∀ v, (∑ x, weight x v) ≤ f v

namespace SplitWeights

variable {Φ} {node : N →o Φ.flag.Node} (D : Φ.SplitWeights node)

/-- The original finite-field representation reindexed by the split-node map. -/
noncomputable abbrev representation (_D : Φ.SplitWeights node) := Φ.representation.reindex node
/-- The split weights accumulated over the lower nodes of the reindexed flag. -/
noncomputable abbrev cumulative :=
  FlagDecompositionRaw.cumulativeWeight (F := Φ.flag.reindex node) D.weight
/-- The cumulative centered lift for the split weights and their reindexed representation. -/
noncomputable abbrev hat := FlagDecompositionRaw.hat D.representation D.weight
/-- The centered lift of each split node's local weight. -/
noncomputable abbrev localLift := FlagDecompositionRaw.localLift D.representation D.weight

theorem weight_supported (x : N) (v : FpCoord p d) (hv : D.weight x v ≠ 0) :
    v ∈ D.representation.space x :=
  Φ.local_supported (node x) v (ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le (D.weight_le x v)))

theorem cumulative_old_nonzero (x : N) (v : FpCoord p d)
    (hv : D.cumulative x v ≠ 0) : Φ.cumulativeWeight (node x) v ≠ 0 := by
  obtain ⟨y, hyx, hy⟩ := (FlagDecompositionRaw.cumulative_ne_zero_iff
    (F := Φ.flag.reindex node) D.weight x v).mp hv
  exact (Φ.originalWeights.cumulative_ne_zero_iff (node x) v).mpr
    ⟨node y, node.monotone hyx, ne_of_gt ((Nat.pos_of_ne_zero hy).trans_le (D.weight_le y v))⟩

theorem cumulative_supported (x : N) (v : FpCoord p d) (hv : D.cumulative x v ≠ 0) :
    v ∈ D.representation.space x :=
  Φ.originalWeights.cumulative_supported (node x) v (D.cumulative_old_nonzero x v hv)

theorem hat_old_nonzero (x : N) (q : IntCoord (Φ.flag.rank (node x)))
    (hq : D.hat x q ≠ 0) : Φ.hat (node x) q ≠ 0 := by
  obtain ⟨hc, v, hmap, hv⟩ := (FlagDecompositionRaw.hat_ne_zero_iff _ _ _ _).mp hq
  exact (Φ.originalWeights.hat_ne_zero_iff (node x) q).mpr
    ⟨hc, v, hmap, D.cumulative_old_nonzero x v hv⟩

theorem localLift_old_nonzero (x : N) (q : IntCoord (Φ.flag.rank (node x)))
    (hq : D.localLift x q ≠ 0) : Φ.localLift (node x) q ≠ 0 := by
  obtain ⟨hc, v, hmap, hv⟩ := (FlagDecompositionRaw.localLift_ne_zero_iff _ _ _ _).mp hq
  exact (FlagDecompositionRaw.localLift_ne_zero_iff _ _ _ _).mpr
    ⟨hc, v, hmap, ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le (D.weight_le x v))⟩

/-- Centered support compatibility and visibility survive splitting the old
local atoms among new bases. -/
theorem rebuildData (hp : Odd p) :
    FlagDecompositionRaw.RebuildData D.representation D.weight f where
  odd := hp
  nonzero := D.nonzero
  local_supported := D.weight_supported
  retained_le := D.retained_le
  transition_hat_nonzero := by
    intro x y h q hq
    obtain ⟨_, v, hmap, hv⟩ := (FlagDecompositionRaw.hat_ne_zero_iff _ _ _ _).mp hq
    refine (FlagDecompositionRaw.hat_ne_zero_iff _ _ _ _).mpr ⟨?_, v, ?_, ?_⟩
    · exact Φ.originalWeights.transition_centered (node.monotone h) (D.hat_old_nonzero x q hq)
    · rw [D.representation.compatible h (D.cumulative_supported x v hv), hmap,
        (Φ.flag.reindex node).transition h |>.mod_integer]
    · obtain ⟨z, hzx, hz⟩ := (FlagDecompositionRaw.cumulative_ne_zero_iff
        (F := Φ.flag.reindex node) D.weight x v).mp hv
      exact (FlagDecompositionRaw.cumulative_ne_zero_iff
        (F := Φ.flag.reindex node) D.weight y v).mpr ⟨z, hzx.trans h, hz⟩
  hat_exists_local := by
    classical
    intro x q hq
    have heq := FlagDecompositionRaw.hat_eq_localIntegerMassBelow hp
      D.representation D.weight D.weight_supported x q
      (fun y h z hz ↦ Φ.isCenteredLift_transition_of_localLift (node.monotone h) z
        (D.localLift_old_nonzero y z hz))
    rw [heq] at hq
    obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    by_cases hyx : y ≤ x
    · rw [dite_eq_left hyx] at hy
      obtain ⟨z, _, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
      by_cases heq : ((Φ.flag.reindex node).transition hyx).integer z = q
      · exact ⟨y, hyx, z, by simpa only [ite_eq_left heq] using hz, heq⟩
      · exact (hz (ite_eq_right heq)).elim
    · exact (hy (dite_eq_right hyx)).elim

/-- The flag decomposition rebuilt from the split weights when the characteristic is odd. -/
noncomputable abbrev decomposition (hp : Odd p) : FlagDecomposition p d f :=
  (D.rebuildData hp).decomposition

@[simp]
theorem decomposition_retainedWeight (hp : Odd p) (v : FpCoord p d) :
    (D.decomposition hp).retainedWeight v = ∑ x, D.weight x v :=
  congrFun (D.rebuildData hp).decomposition_retainedWeight v

theorem decomposition_cumulativeWeight (hp : Odd p)
    (x : (D.decomposition hp).flag.Node) :
    (D.decomposition hp).cumulativeWeight x = D.cumulative x.1 :=
  (D.rebuildData hp).decomposition_cumulativeWeight x

theorem decomposition_hat (hp : Odd p) (x : (D.decomposition hp).flag.Node) :
    (D.decomposition hp).hat x = D.hat x.1 :=
  (D.rebuildData hp).decomposition_hat x

theorem decomposition_polytope_subset (hp : Odd p)
    (x : (D.decomposition hp).flag.Node) :
    ((D.decomposition hp).flag.polytope x).carrier ⊆
      (Φ.flag.polytope (node x.1)).carrier := by
  change ((D.rebuildData hp).polytope x).carrier ⊆ _
  rw [(D.rebuildData hp).polytope_carrier]
  apply convexHull_min _ (Φ.flag.polytope (node x.1)).convex
  rintro _ ⟨q, hq, rfl⟩
  exact Φ.originalWeights.mem_old_polytope (D.hat_old_nonzero x.1 q
    ((FlagDecompositionRaw.mem_hatSupport _ _ _ _).mp hq))

theorem decomposition_isKBounded (hp : Odd p) {K : Φ.flag.Node → ℕ}
    (hK : Φ.IsKBounded K) :
    (D.decomposition hp).IsKBounded (fun x ↦ K (node x.1)) := by
  intro x q hq
  exact hK (node x.1) q (D.decomposition_polytope_subset hp x hq)

theorem decomposition_card_le (hp : Odd p) :
    @Fintype.card (D.decomposition hp).flag.Node (D.decomposition hp).flag.nodeFintype ≤
      Fintype.card N :=
  (D.rebuildData hp).card_decomposition_le

/-- Every surviving split generator is an old local generator. -/
noncomputable def subdivisionMap (hp : Odd p)
    (hsup : ∀ x y, node (x ⊔ y) = node x ⊔ node y) :
    SubdivisionMap Φ (D.decomposition hp) := by
  letI : SemilatticeSup (D.decomposition hp).flag.Node :=
    (D.decomposition hp).flag.nodeSemilatticeSup
  exact SubdivisionMap.ofLocalGenerators
    { toFun := fun x ↦ node x.1, map_sup' := fun x y ↦ hsup x.1 y.1 }
    (fun _ ↦ AffineMap.id ℝ _)
    (fun x ↦ D.decomposition_polytope_subset hp x)
    (fun _ _ ↦ rfl)
    (by
      rintro q ⟨z, hz, hmass⟩
      exact ⟨z, hz, D.localLift_old_nonzero q.base.1 z hmass⟩)

end SplitWeights

end FlagDecomposition

end EGZ
