/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeights
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeightCellRigidity
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeightMaxUnion
/-!
# `NRR.EMP.EqualAreaWeightsUniqueness` — uniqueness of equal-area power weights

Equal-area power weights for fixed pairwise-distinct sites are unique up to a global additive
constant.  The proof is internal to the repository: for two solutions, take the indices on which
`w' - w` is maximal.  Cell rigidity identifies their restricted power cells in the two diagrams;
the union of those cells is relatively clopen in the convex body, hence all of the body.  Positive
cell area and null pairwise overlap force every index to be maximal.  Normalization then removes
the common additive constant.
-/

open NRR NRR.Geometry NRR.Geometry.ConvexBody

namespace NRR

variable {n : ℕ}

/-- Two equal-area weight vectors differ by a global additive constant.  No positivity
hypothesis on `n` is needed: the statement is vacuous when `n = 0`. -/
theorem EMP.powerDiagram_equalArea_weights_unique_core
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hs : Function.Injective s)
    {w w' : Fin n → ℝ}
    (hw : EMP.IsEqualAreaWeight K s w)
    (hw' : EMP.IsEqualAreaWeight K s w') :
    ∃ c : ℝ, ∀ i, w' i = w i + c := by
  by_cases hn0 : n = 0
  · subst n
    exact ⟨0, fun i => Fin.elim0 i⟩
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    let i0 : Fin n := ⟨0, hn⟩
    refine ⟨w' i0 - w i0, ?_⟩
    intro i
    have hdiff := EMP.weightDifference_eq_of_equalArea K s hn hs hw hw' i i0
    linarith

/-- **Uniqueness up to additive constants.** For a planar convex body `K` and pairwise‑distinct
sites `s`, any two equal‑area weight vectors differ by a global additive constant.

Derived directly from the isolated uniqueness core
`EMP.powerDiagram_equalArea_weights_unique_core`.

The conclusion also holds for an empty site set, with additive constant `c = 0`. -/
theorem EMP.equalArea_weights_unique
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hs : Function.Injective s)
    {w w' : Fin n → ℝ}
    (hw : EMP.IsEqualAreaWeight K s w)
    (hw' : EMP.IsEqualAreaWeight K s w') :
    ∃ c : ℝ, ∀ i, w' i = w i + c :=
  EMP.powerDiagram_equalArea_weights_unique_core K s hs hw hw'

/-- **Normalization uniqueness.** For a planar convex body `K` and pairwise‑distinct sites `s`,
two equal‑area weight vectors that are both *normalized* (`∑ i, w i = 0`) are equal.

proved from `EMP.equalArea_weights_unique`: writing `w' i = w i + c` and summing over all
`i`, normalization gives `0 = 0 + (Fintype.card (Fin n)) • c`, and over a nonempty index set
this forces `c = 0`; over an empty index set the weight vectors are trivially equal. -/
theorem EMP.equalArea_weights_unique_normalized
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s)
    {w w' : Fin n → ℝ}
    (hw : EMP.IsEqualAreaWeight K s w)
    (hw' : EMP.IsEqualAreaWeight K s w')
    (hnorm : EMP.WeightNormalized w)
    (hnorm' : EMP.WeightNormalized w') :
    w = w' := by
  obtain ⟨c, hc⟩ := EMP.equalArea_weights_unique K s hs hw hw'
  have hsum : (0 : ℝ) = ∑ i, w i + (n : ℝ) * c := by
    have : ∑ i, w' i = ∑ i, (w i + c) := Finset.sum_congr rfl (fun i _ => hc i)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at this
    simp only [EMP.WeightNormalized, EMP.weightSum] at hnorm'
    rw [hnorm'] at this
    linarith [this]
  simp only [EMP.WeightNormalized, EMP.weightSum] at hnorm
  rw [hnorm, zero_add] at hsum
  funext i
  have hnc : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hc0 : c = 0 := by
    have hprod : (n : ℝ) * c = 0 := hsum.symm
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h hnc
    · exact h
  rw [hc i, hc0, add_zero]

end NRR
