/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RefinedAffineMap
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.IteratedSubdivisionSmallSimplex
/-!
# Staircase prism charts and their barycentric refinements

For a refined `(p-1)`-simplex, its product with the unit interval is triangulated by the standard
`p` staircase simplices.  Each staircase simplex is then allowed an independent iterated
barycentric refinement.  These charts are the finite domain on which the S6 PL homotopy is sampled.
-/

namespace NRR

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision

namespace FoxNeuwirthOrderComplex
namespace SubdivisionPrismCharts

variable {p : Nat}

/-- The interval coordinate attached to a staircase vertex. -/
def staircaseTime (k : Fin p) (j : Fin (p + 1)) : Fin 2 :=
  if j.1 ≤ k.1 then 0 else 1

/-- Spatial vertex attached to a staircase vertex.  Vertices `k` and `k+1` project to the same
spatial vertex and lie at the two interval endpoints. -/
def staircaseSpatial (hp : Nat.Prime p) (k : Fin p) (j : Fin (p + 1)) : Fin p :=
  if h : j.1 ≤ k.1 then
    ⟨j.1, lt_of_le_of_lt h k.2⟩
  else
    ⟨j.1 - 1, by
      have hj := j.2
      have hk : k.1 < j.1 := Nat.lt_of_not_ge h
      omega⟩

@[simp] theorem staircaseTime_lower
    (k : Fin p) (j : Fin (p + 1)) (h : j.1 ≤ k.1) :
    staircaseTime k j = 0 := by simp [staircaseTime, h]

@[simp] theorem staircaseTime_upper
    (k : Fin p) (j : Fin (p + 1)) (h : k.1 < j.1) :
    staircaseTime k j = 1 := by simp [staircaseTime, Nat.not_le.mpr h]

/-- Spatial barycentric coordinate induced by one staircase simplex. -/
noncomputable def spatialWeight
    (hp : Nat.Prime p) (k : Fin p) (w : StandardSimplex p)
    (i : Fin (p - 1 + 1)) : Real :=
  ∑ j : Fin (p + 1),
    if Fin.cast (Nat.sub_add_cancel hp.pos).symm (staircaseSpatial hp k j) = i then w j else 0

/-- The staircase interval coordinate. -/
noncomputable def intervalWeight
    (k : Fin p) (w : StandardSimplex p) : Real :=
  ∑ j : Fin (p + 1), if staircaseTime k j = 1 then w j else 0

/-- The spatial weights form a standard `(p-1)`-simplex. -/
noncomputable def spatialPoint
    (hp : Nat.Prime p) (k : Fin p) (w : StandardSimplex p) :
    StandardSimplex (p - 1) :=
  ⟨spatialWeight hp k w, by
    constructor
    · intro i
      exact Finset.sum_nonneg fun j _ => by
        split_ifs
        · exact w.nonneg j
        · exact le_rfl
    · unfold spatialWeight
      rw [Finset.sum_comm]
      simp [w.sum_eq_one]⟩

/-- The interval weight lies in the unit interval. -/
noncomputable def intervalPoint
    (k : Fin p) (w : StandardSimplex p) : Set.Icc (0 : Real) 1 :=
  ⟨intervalWeight k w, by
    constructor
    · exact Finset.sum_nonneg fun j _ => by
        split_ifs
        · exact w.nonneg j
        · exact le_rfl
    · calc
        intervalWeight k w
            ≤ ∑ j : Fin (p + 1), w j := by
              apply Finset.sum_le_sum
              intro j hj
              split_ifs
              · exact le_rfl
              · exact w.nonneg j
        _ = 1 := w.sum_eq_one⟩

/-- One staircase chart from the `p`-simplex to `Δ^(p-1) × I`. -/
noncomputable def staircasePoint
    (hp : Nat.Prime p) (k : Fin p) (w : StandardSimplex p) :
    StandardSimplex (p - 1) × Set.Icc (0 : Real) 1 :=
  (spatialPoint hp k w, intervalPoint k w)

/-- A base prism cell over one spatial refined top simplex. -/
abbrev BasePrismCell (hp : Nat.Prime p) (N : Nat) :=
  RefinedAffineMap.TopCell hp N × Fin p

/-- A word indexing a further barycentric refinement of a `p`-dimensional prism simplex. -/
abbrev PrismRefinementWord (p L : Nat) :=
  Fin L → Equiv.Perm (Fin (p + 1))

/-- A fully refined prism cell. -/
abbrev PrismCell (hp : Nat.Prime p) (N L : Nat) :=
  BasePrismCell hp N × PrismRefinementWord p L

noncomputable instance (hp : Nat.Prime p) (N L : Nat) : Fintype (PrismCell hp N L) :=
  inferInstance
noncomputable instance (hp : Nat.Prime p) (N L : Nat) : DecidableEq (PrismCell hp N L) :=
  inferInstance

/-- Refined prism chart into the realization cylinder. -/
noncomputable def chart
    (hp : Nat.Prime p) (N L : Nat) (q : PrismCell hp N L) :
    C(Delta p, Realization p × Set.Icc (0 : Real) 1) where
  toFun w :=
    let u : StandardSimplex p :=
      StandardSimplex.ofDelta (affineCompMap p L q.2 w)
    let st := staircasePoint hp q.1.2 u
    (RefinedAffineMap.chart hp N q.1.1 (StandardSimplex.toDelta st.1), st.2)
  continuous_toFun := by
    have hspatial : Continuous fun w : Delta p =>
        StandardSimplex.toDelta
          (spatialPoint hp q.1.2
            (StandardSimplex.ofDelta (affineCompMap p L q.2 w))) := by
      apply Continuous.subtype_mk
      change Continuous fun w : Delta p => fun i =>
        ∑ j : Fin (p + 1),
          if Fin.cast (Nat.sub_add_cancel hp.pos).symm (staircaseSpatial hp q.1.2 j) = i then
            StandardSimplex.ofDelta (affineCompMap p L q.2 w) j else 0
      apply continuous_pi
      intro i
      apply continuous_finsetSum
      intro j hj
      split_ifs
      · change Continuous fun w : Delta p => ((affineCompMap p L q.2) w : Fin (p + 1) → Real) j
        exact (continuous_apply j).comp
          (continuous_subtype_val.comp (affineCompMap p L q.2).continuous)
      · fun_prop
    have hinterval : Continuous fun w : Delta p =>
        intervalPoint q.1.2
          (StandardSimplex.ofDelta (affineCompMap p L q.2 w)) := by
      apply Continuous.subtype_mk
      change Continuous fun w : Delta p =>
        ∑ j : Fin (p + 1), if staircaseTime q.1.2 j = 1 then
          StandardSimplex.ofDelta (affineCompMap p L q.2 w) j else 0
      apply continuous_finsetSum
      intro j hj
      split_ifs
      · change Continuous fun w : Delta p => ((affineCompMap p L q.2) w : Fin (p + 1) → Real) j
        exact (continuous_apply j).comp
          (continuous_subtype_val.comp (affineCompMap p L q.2).continuous)
      · fun_prop
    apply Continuous.prodMk
    · exact (RefinedAffineMap.chart hp N q.1.1).continuous.comp hspatial
    · exact hinterval

/-- Vertices of a refined prism cell. -/
noncomputable def vertex
    (hp : Nat.Prime p) (N L : Nat) (q : PrismCell hp N L) (i : Fin (p + 1)) :
    Realization p × Set.Icc (0 : Real) 1 :=
  chart hp N L q (stdSimplex.vertex (S := Real) i)

/-- Orientation sign of a staircase simplex. -/
noncomputable def staircaseSign (k : Fin p) : Int := (-1 : Int) ^ k.1

/-- Orientation sign of a fully refined prism simplex. -/
noncomputable def prismSign {hp : Nat.Prime p} (q : PrismCell hp N L) : Int :=
  staircaseSign q.1.2 *
    (∏ r : Fin L, (Equiv.Perm.sign (q.2 r) : Int))

end SubdivisionPrismCharts
end FoxNeuwirthOrderComplex
end NRR
