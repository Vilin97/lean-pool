/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaLattice

/-! # Theta Moment -/

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-! Interior path moments in normalized strand coordinates.  Endpoints are
omitted; this is the coordinate part of the theta Jacobian invariant. -/
def interiorMoment (B : Banana 2) (α : Fin 3) (D : CFDiv B.graph) : ℤ :=
  Finset.sum (Finset.range (B.length α - 1))
    (fun r => if h : r + 1 < B.length α then
      ((r + 1 : ℕ) : ℤ) * D (strandVertex B α ⟨r + 1, by omega⟩)
    else 0)

def thetaMoment (B : Banana 2) (D : CFDiv B.graph) : ℤ × ℤ :=
  (interiorMoment B 1 D - interiorMoment B 0 D,
   interiorMoment B 2 D - interiorMoment B 0 D)

/-! The raw difference of the three interior moments is useful for evaluating
marked divisors, but it is not itself the Jacobian coordinate: a principal
divisor can have nonzero endpoint contribution.  The following asymmetric
coordinate is the one compatible with the paper's presentation, taking
`v_{0,0}` as basepoint. -/
def thetaCoordinate (B : Banana 2) (D : CFDiv B.graph) : ℤ × ℤ × ℤ :=
  (interiorMoment B 0 D + (B.length 0 : ℤ) * D (rightEndpoint B),
    interiorMoment B 1 D, interiorMoment B 2 D)

/-! The two-coordinate projection used by the paper's theta presentation. -/
def thetaJacobianMoment (B : Banana 2) (D : CFDiv B.graph) : ℤ × ℤ :=
  (interiorMoment B 0 D + (B.length 0 : ℤ) * D (rightEndpoint B) -
      interiorMoment B 2 D,
    interiorMoment B 1 D - interiorMoment B 2 D)

private theorem interior_position_eq_of_vertex_eq
    (B : Banana 2) (α β : Fin 3)
    (r : ℕ) (hr : r < B.length α - 1)
    (j : B.PathPosition β) (hj : B.IsInteriorPosition β j) :
    strandVertex B α ⟨r + 1, by omega⟩ = strandVertex B β j ↔
      α = β ∧ r + 1 = j.val := by
  constructor
  · intro h
    have hαβ := strand_eq_of_interior_vertex_eq B α β
      ⟨r + 1, by have hlen := B.length_pos α; omega⟩ j
        (by
          have hr' : r + 1 < B.length α := by omega
          exact ⟨Nat.zero_lt_succ r, hr'⟩) hj h
    refine ⟨hαβ, ?_⟩
    subst hαβ
    exact congrArg Fin.val (strandVertex_injective B α h)
  · rintro ⟨hαβ, hval⟩
    subst β
    exact congrArg (strandVertex B α) (Fin.ext hval)

theorem interiorMoment_one_chip
    (B : Banana 2) (α β : Fin 3)
    (j : B.PathPosition β) (hj : B.IsInteriorPosition β j) :
    interiorMoment B α (oneChip (strandVertex B β j)) =
      if α = β then (j.val : ℤ) else 0 := by
  classical
  unfold interiorMoment
  have hlen : 0 < B.length α := B.length_pos α
  by_cases hαβ : α = β
  · subst β
    have hterm : ∀ r ∈ Finset.range (B.length α - 1),
        (if h : r + 1 < B.length α then
          ((r + 1 : ℕ) : ℤ) *
            (oneChip (strandVertex B α j)
              (strandVertex B α ⟨r + 1, by omega⟩))
        else 0) =
          if r = j.val - 1 then (j.val : ℤ) else 0 := by
      intro r hrange
      have hr_lt : r + 1 < B.length α := by
        have hr := Finset.mem_range.mp hrange
        omega
      simp only [oneChip]
      by_cases hrj : r = j.val - 1
      · subst r
        have hjpos : 1 ≤ j.val := hj.1
        have hjlt : j.val < B.length α := hj.2
        have hsub : j.val - 1 + 1 = j.val := Nat.sub_add_cancel hjpos
        have hsel : j.val - 1 + 1 < B.length α := by rw [hsub]; exact hjlt
        rw [dif_pos hsel]
        simp [Nat.sub_add_cancel hjpos]
      · have hne : strandVertex B α ⟨r + 1, by omega⟩ ≠
            strandVertex B α j := by
          intro h
          have hv := congrArg Fin.val (strandVertex_injective B α h)
          have hlen := B.length_pos α
          have hEq : r + 1 = j.val := hv
          omega
        simp [hr_lt, hne, hrj]
    have hselmem : j.val - 1 ∈ Finset.range (B.length α - 1) := by
      simp only [Finset.mem_range]
      have hjlt : j.val < B.length α := hj.2
      have hjpos : 1 ≤ j.val := hj.1
      omega
    rw [Finset.sum_eq_single (j.val - 1) (by
      intro b hb hbj
      simpa [hbj] using hterm b hb) (by
      intro hnot
      exact False.elim (hnot hselmem))]
    have hjpos : 1 ≤ j.val := hj.1
    have hsel : j.val - 1 + 1 < B.length α := by
      rw [Nat.sub_add_cancel hjpos]
      exact hj.2
    rw [dif_pos hsel]
    simp [Nat.sub_add_cancel hjpos]
  · simp only [hαβ, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro r hrange
    have hr_lt : r + 1 < B.length α := by
      have hr := Finset.mem_range.mp hrange
      omega
    have hne : strandVertex B α ⟨r + 1, by omega⟩ ≠
        strandVertex B β j := by
      intro h
      exact hαβ (strand_eq_of_interior_vertex_eq B α β
        ⟨r + 1, by omega⟩ j
          (by exact ⟨Nat.zero_lt_succ r, hr_lt⟩)
          hj h)
    simp [hr_lt, oneChip, hne]

private theorem interiorMoment_sub
    (B : Banana 2) (α : Fin 3) (D E : CFDiv B.graph) :
    interiorMoment B α (D - E) =
      interiorMoment B α D - interiorMoment B α E := by
  unfold interiorMoment
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hvalid : r + 1 < B.length α
  · simp [hvalid, Pi.sub_apply] ; ring
  · simp [hvalid]

/- TeX label: `prop-JacBanana` (marked-point moment calculation). -/
theorem thetaMoment_marked_difference
    (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i)
    (hj : B.IsInteriorPosition β j) :
    thetaMoment B
      (oneChip (strandVertex B α i) -
        oneChip (strandVertex B β j)) =
      ((if α = 1 then (i.val : ℤ) else 0) -
          (if β = 1 then (j.val : ℤ) else 0) -
        ((if α = 0 then (i.val : ℤ) else 0) -
          (if β = 0 then (j.val : ℤ) else 0)),
       (if α = 2 then (i.val : ℤ) else 0) -
          (if β = 2 then (j.val : ℤ) else 0) -
        ((if α = 0 then (i.val : ℤ) else 0) -
          (if β = 0 then (j.val : ℤ) else 0))) := by
  unfold thetaMoment
  repeat' rw [interiorMoment_sub]
  repeat' rw [interiorMoment_one_chip B _ _ _ hi]
  repeat' rw [interiorMoment_one_chip B _ _ _ hj]
  simp [eq_comm]

/- TeX label: `prop-JacBanana` (the marked divisor's Jacobian coordinates). -/
theorem thetaCoordinate_marked_difference
    (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i)
    (hj : B.IsInteriorPosition β j) :
    thetaCoordinate B
      (oneChip (strandVertex B α i) -
        oneChip (strandVertex B β j)) =
      ((if α = 0 then (i.val : ℤ) else 0) -
          (if β = 0 then (j.val : ℤ) else 0) -
          (B.length 0 : ℤ) *
            ((if strandVertex B α i = rightEndpoint B then (1 : ℤ) else 0) -
              (if strandVertex B β j = rightEndpoint B then (1 : ℤ) else 0)),
       (if α = 1 then (i.val : ℤ) else 0) -
          (if β = 1 then (j.val : ℤ) else 0),
       (if α = 2 then (i.val : ℤ) else 0) -
          (if β = 2 then (j.val : ℤ) else 0)) := by
  unfold thetaCoordinate
  rw [interiorMoment_sub, interiorMoment_sub, interiorMoment_sub]
  repeat' rw [interiorMoment_one_chip B _ _ _ hi]
  repeat' rw [interiorMoment_one_chip B _ _ _ hj]
  have hiRight : strandVertex B α i ≠ rightEndpoint B := by
    exact strandVertex_ne_rightEndpoint B α i hi.2
  have hjRight : strandVertex B β j ≠ rightEndpoint B := by
    exact strandVertex_ne_rightEndpoint B β j hj.2
  simp [oneChip, hiRight, hjRight, Ne.symm hiRight, Ne.symm hjRight, eq_comm]

/- TeX labels: `prop-JacBanana`, `eq:multDiffMarkedPts` (the paper's
two-coordinate marked-point representative). -/
theorem thetaJacobianMoment_marked_difference_01
    (B : Banana 2) (i : B.PathPosition 0) (j : B.PathPosition 1)
    (hi : B.IsInteriorPosition 0 i)
    (hj : B.IsInteriorPosition 1 j) :
    thetaJacobianMoment B
      (oneChip (strandVertex B 0 i) -
        oneChip (strandVertex B 1 j)) =
      ((i.val : ℤ), -(j.val : ℤ)) := by
  unfold thetaJacobianMoment
  rw [interiorMoment_sub, interiorMoment_sub, interiorMoment_sub]
  rw [interiorMoment_one_chip B 0 0 i hi,
    interiorMoment_one_chip B 0 1 j hj,
    interiorMoment_one_chip B 1 0 i hi,
    interiorMoment_one_chip B 1 1 j hj,
    interiorMoment_one_chip B 2 0 i hi,
    interiorMoment_one_chip B 2 1 j hj]
  have hiRight : strandVertex B 0 i ≠ rightEndpoint B :=
    strandVertex_ne_rightEndpoint B 0 i hi.2
  have hjRight : strandVertex B 1 j ≠ rightEndpoint B :=
    strandVertex_ne_rightEndpoint B 1 j hj.2
  simp [oneChip, Ne.symm hiRight, Ne.symm hjRight, eq_comm]


end Bananas
