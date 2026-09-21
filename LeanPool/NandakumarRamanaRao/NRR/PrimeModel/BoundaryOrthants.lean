/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.ChildTestMap

/-!
# Endpoint orthants

The strict endpoint signs of a nice multivalued function place the child test map in the negative
orthant at `-1` and the positive orthant at `1`.
-/

namespace NRR

open Geometry

variable {p : ℕ}

/-- Strictly negative coordinate orthant. -/
def negativeOrthant (p : ℕ) : Set (Fin p → ℝ) :=
  {v | ∀ i, v i < 0}

/-- Strictly positive coordinate orthant. -/
def positiveOrthant (p : ℕ) : Set (Fin p → ℝ) :=
  {v | ∀ i, 0 < v i}

 theorem isOpen_negativeOrthant : IsOpen (negativeOrthant p) := by
  rw [show negativeOrthant p = ⋂ i : Fin p, {v | v i < 0} by
    ext v
    simp [negativeOrthant]]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (continuous_apply i) continuous_const

 theorem isOpen_positiveOrthant : IsOpen (positiveOrthant p) := by
  rw [show positiveOrthant p = ⋂ i : Fin p, {v | 0 < v i} by
    ext v
    simp [positiveOrthant]]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (continuous_apply i)

 theorem negativeOrthant_invariant (p : Nat) :
    IsPrimeInvariant (p := p) (negativeOrthant p) := by
  intro g v hv i
  exact hv _

 theorem positiveOrthant_invariant (p : Nat) :
    IsPrimeInvariant (p := p) (positiveOrthant p) := by
  intro g v hv i
  exact hv _

 theorem zero_not_mem_negativeOrthant (hp : Nat.Prime p) :
    (0 : Fin p → ℝ) ∉ negativeOrthant p := by
  intro h
  exact (lt_irrefl (0 : ℝ)) (h ⟨0, hp.pos⟩)

 theorem zero_not_mem_positiveOrthant (hp : Nat.Prime p) :
    (0 : Fin p → ℝ) ∉ positiveOrthant p := by
  intro h
  exact (lt_irrefl (0 : ℝ)) (h ⟨0, hp.pos⟩)

variable {hp : Nat.Prime p}
variable {K : Geometry.ConvexBody Plane} {A : ℝ}

namespace PrimeConfigurationModel

 theorem childTestMap_left_mem_negative
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ))))
    (C : BodySpace K A) (x : M.Point) :
    M.childTestMap hA φ ((C, x), SignedInterval.left) ∈ negativeOrthant p := by
  intro i
  exact φ.eval_left_neg _

 theorem childTestMap_right_mem_positive
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ))))
    (C : BodySpace K A) (x : M.Point) :
    M.childTestMap hA φ ((C, x), SignedInterval.right) ∈ positiveOrthant p := by
  intro i
  exact φ.eval_right_pos _

/-- Left endpoint boundary. -/
def leftBoundary
    (M : PrimeConfigurationModel hp)
    (K : Geometry.ConvexBody Plane) (A : ℝ) :
    Set ((BodySpace K A × M.Point) × SignedInterval) :=
  {z | z.2 = SignedInterval.left}

/-- Right endpoint boundary. -/
def rightBoundary
    (M : PrimeConfigurationModel hp)
    (K : Geometry.ConvexBody Plane) (A : ℝ) :
    Set ((BodySpace K A × M.Point) × SignedInterval) :=
  {z | z.2 = SignedInterval.right}

 theorem allChildrenZeroSet_disjoint_left
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ)))) :
    Disjoint (M.allChildrenZeroSet hA φ) (M.leftBoundary K A) := by
  rw [Set.disjoint_left]
  rintro ⟨⟨C, x⟩, t⟩ hz hleft
  change t = SignedInterval.left at hleft
  subst t
  have hzero : M.childTestMap hA φ ((C, x), SignedInterval.left) = 0 := hz
  have hneg := M.childTestMap_left_mem_negative hA φ C x
  exact zero_not_mem_negativeOrthant hp (hzero ▸ hneg)

 theorem allChildrenZeroSet_disjoint_right
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ)))) :
    Disjoint (M.allChildrenZeroSet hA φ) (M.rightBoundary K A) := by
  rw [Set.disjoint_left]
  rintro ⟨⟨C, x⟩, t⟩ hz hright
  change t = SignedInterval.right at hright
  subst t
  have hzero : M.childTestMap hA φ ((C, x), SignedInterval.right) = 0 := hz
  have hpos := M.childTestMap_right_mem_positive hA φ C x
  exact zero_not_mem_positiveOrthant hp (hzero ▸ hpos)

end PrimeConfigurationModel

end NRR
