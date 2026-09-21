/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Partition.ConvexPartition
import LeanPool.NandakumarRamanaRao.NRR.AreaPerimeter
import LeanPool.NandakumarRamanaRao.NRR.Representation.ZeroSum

/-!
# `NRR.Partition.PerimeterVector` — perimeter vector of a convex partition

For a convex partition `P : ConvexPartition K n` this module records the elementary
**perimeter data** of `P`:

* `ConvexPartition.perimeterVec` — the `Fin n → ℝ` vector of piece perimeters;
* `ConvexPartition.totalPerimeter` — the sum of the piece perimeters;
* `ConvexPartition.averagePerimeter` — the total perimeter divided by `(n : ℝ)`.

The underlying perimeter is the public planar Cauchy perimeter
`NRR.Geometry.ConvexBody.perimeter` from `NRR.AreaPerimeter`. The pieces of a
`ConvexPartition` have type `Body = Geometry.ConvexBody Plane`, so this perimeter applies
directly to each piece.

No equal-area assumption, test map, or continuity statement is introduced here: this module is
purely the definitional perimeter API.
-/

namespace NRR

open NRR.Geometry.ConvexBody

namespace ConvexPartition

variable {K : Body} {n : ℕ}

/-- The **perimeter vector** of a convex partition: the `i`-th entry is the perimeter of the
`i`-th piece. -/
noncomputable def perimeterVec (P : ConvexPartition K n) : Fin n → ℝ :=
  fun i => perimeter (P.piece i)

/-- The **total perimeter** of a convex partition: the sum of the piece perimeters. -/
noncomputable def totalPerimeter (P : ConvexPartition K n) : ℝ :=
  ∑ i, P.perimeterVec i

/-- The **average perimeter** of a convex partition: the total perimeter divided by `(n : ℝ)`.
The division is explicitly by the real cast `(n : ℝ)`. -/
noncomputable def averagePerimeter (P : ConvexPartition K n) : ℝ :=
  P.totalPerimeter / (n : ℝ)

@[simp] theorem perimeterVec_apply (P : ConvexPartition K n) (i : Fin n) :
    P.perimeterVec i = perimeter (P.piece i) := rfl

theorem totalPerimeter_eq_sum (P : ConvexPartition K n) :
    P.totalPerimeter = ∑ i, P.perimeterVec i := rfl

theorem averagePerimeter_eq (P : ConvexPartition K n) :
    P.averagePerimeter = P.totalPerimeter / (n : ℝ) := rfl

/-- The **perimeter-deviation vector** of a convex partition: the `i`-th entry is the
deviation of the `i`-th piece perimeter from the average perimeter. -/
noncomputable def perimeterDeviation (P : ConvexPartition K n) : Fin n → ℝ :=
  fun i => P.perimeterVec i - P.averagePerimeter

/-- All pieces have equal perimeter. -/
def HasEqualPerimeter (P : ConvexPartition K n) : Prop :=
  ∀ i j, perimeter (P.piece i) = perimeter (P.piece j)

@[simp] theorem perimeterDeviation_apply (P : ConvexPartition K n) (i : Fin n) :
    P.perimeterDeviation i = P.perimeterVec i - P.averagePerimeter := rfl

/-- The perimeter-deviation vector sums to zero. -/
theorem sum_perimeterDeviation_eq_zero (P : ConvexPartition K n) (hn : 0 < n) :
    ∑ i, P.perimeterDeviation i = 0 := by
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  simp only [perimeterDeviation_apply, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← totalPerimeter_eq_sum, averagePerimeter_eq]
  field_simp
  ring

/-- The perimeter-deviation vector, packaged as an element of the zero-sum target type. -/
noncomputable def perimeterDeviationZeroSum (P : ConvexPartition K n) (hn : 0 < n) : ZeroSum n :=
  ⟨P.perimeterDeviation, P.sum_perimeterDeviation_eq_zero hn⟩

/-- The perimeter deviation vanishes pointwise iff all pieces have equal perimeter. -/
theorem perimeterDeviation_pointwise_zero_iff (P : ConvexPartition K n) (hn : 0 < n) :
    (∀ i, P.perimeterDeviation i = 0) ↔ P.HasEqualPerimeter := by
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  constructor
  · intro h i j
    have hi := h i
    have hj := h j
    simp only [perimeterDeviation_apply, perimeterVec_apply, sub_eq_zero] at hi hj
    rw [hi, hj]
  · intro h i
    simp only [perimeterDeviation_apply, perimeterVec_apply, averagePerimeter_eq,
      totalPerimeter_eq_sum, perimeterVec_apply, sub_eq_zero]
    have hsum : ∑ j, perimeter (P.piece j) = (n : ℝ) * perimeter (P.piece i) := by
      rw [Finset.sum_congr rfl (fun j _ => h j i)]
      simp [Finset.card_univ]
    rw [hsum]
    field_simp

/-- The perimeter deviation is the zero function iff all pieces have equal perimeter. -/
theorem perimeterDeviation_eq_zero_iff (P : ConvexPartition K n) (hn : 0 < n) :
    P.perimeterDeviation = 0 ↔ P.HasEqualPerimeter := by
  rw [← perimeterDeviation_pointwise_zero_iff P hn, funext_iff]
  simp

end ConvexPartition

end NRR
