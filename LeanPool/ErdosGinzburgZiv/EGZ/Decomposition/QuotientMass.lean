/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Basic

/-!
# Local-to-cumulative mass over residue classes

The correction in Section 4 distinguishes the local summands `f_x` from the
cumulative function `f_{≤ x}`.  This file proves the first, purely finite-sum
part of equation `local-to-cumulative`: a cumulative fibre mass is exactly the
sum of the contributions of the local summands below the node.

The statement deliberately keeps every local contribution in the coordinate
fibre of the upper representation map.  Passing from this quotient-level
identity to the paper's sum over local flag points additionally uses uniqueness
of centered representatives for odd `p`.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ.FlagDecompositionRaw

variable {p d : ℕ} [NeZero p] {F : ConvexFlag}

/-- Sum of the local masses below `x`, grouped using the fibre of the upper
representation map. -/
noncomputable def localFibreMassBelow
    (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (x : F.Node)
    (c : FpCoord p (F.rank x)) : ℕ := by
  classical
  exact ∑ y, if y ≤ x then affineFibreMass (pieces y) (R.map x) c else 0

/-- Quotient-level local-to-cumulative expression for a lattice coordinate.
-/
noncomputable def localToCumulativeMass
    (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (x : F.Node)
    (q : IntCoord (F.rank x)) : ℕ := by
  classical
  exact if IsCenteredLift p q then
    localFibreMassBelow R pieces x (q.mod p) else 0

/-- The same local mass sum, now partitioned by residue classes in the
source lattice fibre and transported along the flag map. -/
noncomputable def localTransitionMassBelow
    (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (x : F.Node)
    (c : FpCoord p (F.rank x)) : ℕ := by
  classical
  exact ∑ y, if h : y ≤ x then
    ∑ a : FpCoord p (F.rank y),
      if (F.transition h).modp p a = c then
        affineFibreMass (pieces y) (R.map y) a else 0
    else 0

/-- The fibre mass of a cumulative weight is the sum of the corresponding
fibre masses of the local pieces below the node.

This is the finite-sum core of equation `local-to-cumulative`; importantly,
the right-hand side uses `pieces y`, not the cumulative weight at `y`. -/
theorem affineFibreMass_cumulativeWeight
    (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (x : F.Node)
    (c : FpCoord p (F.rank x)) :
    affineFibreMass (cumulativeWeight pieces x) (R.map x) c =
      localFibreMassBelow R pieces x c := by
  classical
  unfold affineFibreMass cumulativeWeight localFibreMassBelow
  calc
    (∑ v, if R.map x v = c then ∑ y, if y ≤ x then pieces y v else 0 else 0) =
        ∑ v, ∑ y,
          if y ≤ x then (if R.map x v = c then pieces y v else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : R.map x v = c <;> simp [hv]
    _ = ∑ y, ∑ v,
          if y ≤ x then (if R.map x v = c then pieces y v else 0) else 0 := by
      exact Finset.sum_comm
    _ = ∑ y, if y ≤ x then
          ∑ v, if R.map x v = c then pieces y v else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y ≤ x <;> simp [hy]

/-- On a local summand supported in `space y`, an upper fibre is the disjoint
union of the lower fibres whose residue classes map to it.  This is where
compatibility of the finite-field representation enters the
local-to-cumulative calculation. -/
theorem affineFibreMass_eq_sum_transitionFibres
    (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ)
    {y x : F.Node} (h : y ≤ x)
    (hsupported : ∀ v, pieces y v ≠ 0 → v ∈ R.space y)
    (c : FpCoord p (F.rank x)) :
    affineFibreMass (pieces y) (R.map x) c =
      ∑ a : FpCoord p (F.rank y),
        if (F.transition h).modp p a = c then
          affineFibreMass (pieces y) (R.map y) a else 0 := by
  classical
  unfold affineFibreMass
  rw [show
      (∑ a : FpCoord p (F.rank y),
          if (F.transition h).modp p a = c then
            ∑ v, if R.map y v = a then pieces y v else 0 else 0) =
        ∑ v, ∑ a : FpCoord p (F.rank y),
          if (F.transition h).modp p a = c then
            (if R.map y v = a then pieces y v else 0) else 0 by
    calc
      _ = ∑ a : FpCoord p (F.rank y), ∑ v,
          if (F.transition h).modp p a = c then
            (if R.map y v = a then pieces y v else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : (F.transition h).modp p a = c <;> simp [ha]
      _ = _ := Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : pieces y v = 0
  · simp [hv]
  · have hcompat := R.compatible h (hsupported v hv)
    rw [hcompat]
    by_cases hc : (F.transition h).modp p (R.map y v) = c
    · rw [ite_eq_left hc]
      rw [Finset.sum_eq_single (R.map y v)]
      · simp [hc]
      · intro a _ ha
        simp [Ne.symm ha]
      · simp
    · rw [ite_eq_right hc]
      symm
      apply Finset.sum_eq_zero
      intro a _
      by_cases ha : R.map y v = a
      · subst a
        simp [hc]
      · simp [ha]

/-- Fully quotient-level local-to-cumulative identity.  It partitions each
local summand by its own lattice residue and then applies the transition map
to the upper residue. -/
theorem localFibreMassBelow_eq_localTransitionMassBelow
    (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ)
    (hsupported : ∀ y v, pieces y v ≠ 0 → v ∈ R.space y)
    (x : F.Node) (c : FpCoord p (F.rank x)) :
    localFibreMassBelow R pieces x c =
      localTransitionMassBelow R pieces x c := by
  classical
  unfold localFibreMassBelow localTransitionMassBelow
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : y ≤ x
  · simp only [h, dite_eq_left, ite_eq_left]
    exact affineFibreMass_eq_sum_transitionFibres R pieces h
      (hsupported y) c
  · simp [h]

/-- The cumulative centered lift is obtained from the same local fibre-mass
sum whenever the displayed lattice coordinate is centered. -/
theorem hat_eq_sum_localFibreMass
    (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (x : F.Node)
    (q : IntCoord (F.rank x)) :
    hat R pieces x q = localToCumulativeMass R pieces x q := by
  classical
  unfold hat localToCumulativeMass
  split_ifs with hq
  · exact affineFibreMass_cumulativeWeight R pieces x (q.mod p)
  · rfl

/-- For a centered upper coordinate, cumulative lifted mass is the sum of
the local quotient masses below it, partitioned through the transition maps.
This is the strongest form of the local-to-cumulative identity that does not
yet choose centered representatives in every lower lattice fibre. -/
theorem hat_eq_localTransitionMassBelow_of_centered
    (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ)
    (hsupported : ∀ y v, pieces y v ≠ 0 → v ∈ R.space y)
    (x : F.Node) (q : IntCoord (F.rank x))
    (hq : IsCenteredLift p q) :
    hat R pieces x q =
      localTransitionMassBelow R pieces x (q.mod p) := by
  rw [hat_eq_sum_localFibreMass]
  unfold localToCumulativeMass
  rw [ite_eq_left hq]
  exact localFibreMassBelow_eq_localTransitionMassBelow R pieces
    hsupported x (q.mod p)

end EGZ.FlagDecompositionRaw
