/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Cleanup
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LocalToCumulative
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CenteredPolytope

/-!
# Surviving weights and their lifted supports

The support lemmas here prepare the geometric rebuilding after numerical
pruning. A surviving collection is pointwise below the old local weights and
has at least one nonzero atom.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

/-- A nonzero family of local weights obtained by decreasing the weights of a flag
decomposition. -/
structure PrunedWeights (Φ : FlagDecomposition p d f) where
  /-- The retained local multiplicity at each node and ambient point. -/
  weight : Φ.flag.Node → FpCoord p d → ℕ
  weight_le : ∀ x v, weight x v ≤ Φ.localWeight x v
  nonzero : ∃ x v, weight x v ≠ 0

namespace PrunedWeights

variable {Φ : FlagDecomposition p d f} (D : PrunedWeights Φ)

/-- The pruned weight accumulated over all nodes below a given node. -/
noncomputable abbrev cumulative := FlagDecompositionRaw.cumulativeWeight D.weight
/-- The centered integral lift of the cumulative pruned weight. -/
noncomputable abbrev hat := FlagDecompositionRaw.hat Φ.representation D.weight
/-- The centered integral lift of the pruned weight at a single node. -/
noncomputable abbrev localLift := FlagDecompositionRaw.localLift Φ.representation D.weight
/-- The finite support of the cumulative centered lift of the pruned weights. -/
noncomputable abbrev support := FlagDecompositionRaw.hatSupport Φ.representation D.weight

theorem mem_support (x : Φ.flag.Node) (q : IntCoord (Φ.flag.rank x)) :
    q ∈ D.support x ↔ D.hat x q ≠ 0 := FlagDecompositionRaw.mem_hatSupport _ _ _ _

theorem weight_supported (x : Φ.flag.Node) (v : FpCoord p d)
    (hv : D.weight x v ≠ 0) : v ∈ Φ.representation.space x :=
  Φ.local_supported x v (ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le (D.weight_le x v)))

theorem cumulative_ne_zero_iff (x : Φ.flag.Node) (v : FpCoord p d) :
    D.cumulative x v ≠ 0 ↔ ∃ y, y ≤ x ∧ D.weight y v ≠ 0 := by
  classical
  constructor
  · intro hv
    obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
    by_cases hyx : y ≤ x
    · exact ⟨y, hyx, by simpa only [ite_eq_left hyx] using hy⟩
    · exact (hy (ite_eq_right hyx)).elim
  · rintro ⟨y, hyx, hy⟩
    have hle : D.weight y v ≤ D.cumulative x v := by
      simpa only [cumulative, FlagDecompositionRaw.cumulativeWeight, ite_eq_left hyx] using
        Finset.single_le_sum
        (f := fun z ↦ if z ≤ x then D.weight z v else 0)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ y)
    exact ne_of_gt ((Nat.pos_of_ne_zero hy).trans_le hle)

theorem cumulative_supported (x : Φ.flag.Node) (v : FpCoord p d)
    (hv : D.cumulative x v ≠ 0) : v ∈ Φ.representation.space x := by
  obtain ⟨y, hyx, hy⟩ := (D.cumulative_ne_zero_iff x v).mp hv
  exact Φ.representation.space_mono hyx (D.weight_supported y v hy)

theorem cumulative_ne_zero_of_le {y x : Φ.flag.Node} (h : y ≤ x)
    {v : FpCoord p d} (hv : D.cumulative y v ≠ 0) : D.cumulative x v ≠ 0 := by
  obtain ⟨z, hzy, hz⟩ := (D.cumulative_ne_zero_iff y v).mp hv
  exact (D.cumulative_ne_zero_iff x v).mpr ⟨z, hzy.trans h, hz⟩

theorem hat_le_old (x : Φ.flag.Node) (q : IntCoord (Φ.flag.rank x)) :
    D.hat x q ≤ Φ.hat x q := FlagDecompositionRaw.hat_mono _ D.weight_le _ _

theorem localLift_le_old (x : Φ.flag.Node) (q : IntCoord (Φ.flag.rank x)) :
    D.localLift x q ≤ Φ.localLift x q := by
  classical
  unfold localLift FlagDecomposition.localLift FlagDecompositionRaw.localLift
  split_ifs
  · apply Finset.sum_le_sum
    intro v _
    split_ifs
    · exact D.weight_le x v
    · exact le_rfl
  · exact le_rfl

theorem mem_old_polytope {x : Φ.flag.Node} {q : IntCoord (Φ.flag.rank x)}
    (hq : D.hat x q ≠ 0) : q.real ∈ (Φ.flag.polytope x).carrier := by
  rw [Φ.polytope_eq_liftedSupport]
  exact _root_.subset_convexHull ℝ _ ⟨q, (Φ.liftedSupport_spec x q).mpr
    (ne_of_gt ((Nat.pos_of_ne_zero hq).trans_le (D.hat_le_old x q))), rfl⟩

theorem hat_ne_zero_iff (x : Φ.flag.Node) (q : IntCoord (Φ.flag.rank x)) :
    D.hat x q ≠ 0 ↔ IsCenteredLift p q ∧
      ∃ v, Φ.representation.map x v = q.mod p ∧ D.cumulative x v ≠ 0 := by
  classical
  unfold hat FlagDecompositionRaw.hat
  by_cases hc : IsCenteredLift p q
  · rw [ite_eq_left hc]
    constructor
    · intro hmass
      obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hmass
      by_cases heq : Φ.representation.map x v = q.mod p
      · exact ⟨hc, v, heq, by simpa only [ite_eq_left heq] using hv⟩
      · exact (hv (ite_eq_right heq)).elim
    · rintro ⟨_, v, heq, hv⟩
      have hle : D.cumulative x v ≤
          FlagDecompositionRaw.affineFibreMass (D.cumulative x) (Φ.representation.map x)
            (q.mod p) := by
        simpa only [FlagDecompositionRaw.affineFibreMass, ite_eq_left heq] using
        Finset.single_le_sum
          (f := fun w ↦ if Φ.representation.map x w = q.mod p then D.cumulative x w else 0)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ v)
      exact ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le hle)
  · rw [ite_eq_right hc]
    simp only [ne_eq, not_true_eq_false, false_iff, not_and]
    exact fun h ↦ (hc h).elim

theorem support_nonempty_iff (hp : Odd p) (x : Φ.flag.Node) :
    (D.support x).Nonempty ↔ ∃ v, D.cumulative x v ≠ 0 := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨_, v, _, hv⟩ := (D.hat_ne_zero_iff x q).mp ((D.mem_support x q).mp hq)
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    refine ⟨FpCoord.centeredLift (Φ.representation.map x v), ?_⟩
    rw [D.mem_support, D.hat_ne_zero_iff]
    exact ⟨FpCoord.isCenteredLift_centeredLift hp _, v,
      (FpCoord.mod_centeredLift _).symm, hv⟩

/-- Upper transitions of surviving support points remain centered because
they lie in the old, bounded upper polytope. -/
theorem transition_centered {y x : Φ.flag.Node} (h : y ≤ x)
    {q : IntCoord (Φ.flag.rank y)} (hq : D.hat y q ≠ 0) :
    IsCenteredLift p ((Φ.flag.transition h).integer q) := by
  exact Φ.isCenteredLift_transition_of_mem_polytope h q (D.mem_old_polytope hq)

theorem transition_mem_support {y x : Φ.flag.Node} (h : y ≤ x)
    {q : IntCoord (Φ.flag.rank y)} (hq : q ∈ D.support y) :
    (Φ.flag.transition h).integer q ∈ D.support x := by
  rw [D.mem_support] at hq ⊢
  obtain ⟨_, v, hmap, hv⟩ := (D.hat_ne_zero_iff y q).mp hq
  refine (D.hat_ne_zero_iff x _).mpr ⟨D.transition_centered h hq, v, ?_,
    D.cumulative_ne_zero_of_le h hv⟩
  rw [Φ.representation.compatible h (D.cumulative_supported y v hv), hmap,
    (Φ.flag.transition h).mod_integer]

/-- Every surviving cumulative atom comes from a surviving local atom at
a lower node. This is the visibility input for the rebuilt support hulls. -/
theorem exists_localLift_of_hat_ne_zero (hp : Odd p)
    (x : Φ.flag.Node) (q : IntCoord (Φ.flag.rank x)) (hq : D.hat x q ≠ 0) :
    ∃ (y : Φ.flag.Node) (h : y ≤ x) (z : IntCoord (Φ.flag.rank y)),
      D.localLift y z ≠ 0 ∧ (Φ.flag.transition h).integer z = q := by
  classical
  have heq := FlagDecompositionRaw.hat_eq_localIntegerMassBelow hp
    Φ.representation D.weight D.weight_supported x q
    (fun y h z hz ↦ Φ.isCenteredLift_transition_of_localLift h z
      (ne_of_gt ((Nat.pos_of_ne_zero hz).trans_le (D.localLift_le_old y z))))
  rw [show D.hat x q = _ from heq] at hq
  obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
  by_cases hyx : y ≤ x
  · rw [dite_eq_left hyx] at hy
    obtain ⟨z, _, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    by_cases heq : (Φ.flag.transition hyx).integer z = q
    · exact ⟨y, hyx, z, by simpa only [ite_eq_left heq] using hz, heq⟩
    · exact (hz (ite_eq_right heq)).elim
  · exact (hy (dite_eq_right hyx)).elim

end PrunedWeights

end EGZ.FlagDecomposition
