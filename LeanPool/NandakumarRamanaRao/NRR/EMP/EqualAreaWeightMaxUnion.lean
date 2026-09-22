/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.CategoryTheory.Countable
import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeightCellRigidity
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.BodyCellPartition

/-!
# `NRR.EMP.EqualAreaWeightMaxUnion` — the maximal-difference clopen argument

For two equal-area power diagrams, let `d i = w' i - w i` and let `M` be the nonempty set
of indices where `d` is maximal.  Every `M`-cell for `w` equals the corresponding cell for
`w'`.  Their union inside the convex body is closed because it is a finite union of closed
cells.  It is also relatively open: after passing from `w` to `w'`, every maximal cell beats
all nonmaximal sites by a strict amount.  Connectedness of the convex body therefore forces
that union to be the whole body.  Positive area and null overlap then force every index to be
maximal.

This supplies the global propagation step needed for uniqueness of equal-area weights without
introducing a separate adjacency graph for the power diagram.
-/

open NRR NRR.Geometry MeasureTheory

namespace NRR

variable {n : ℕ}

namespace EMP

/-- For two equal-area weight vectors, all coordinate differences `w' i - w i` are equal. -/
theorem weightDifference_eq_of_equalArea
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s)
    {w w' : Fin n → ℝ}
    (hw : EMP.IsEqualAreaWeight K s w)
    (hw' : EMP.IsEqualAreaWeight K s w') :
    ∀ i j, w' i - w i = w' j - w j := by
  let d : Fin n → ℝ := fun i => w' i - w i
  obtain ⟨i0, _, hi0⟩ :=
    Finset.exists_max_image Finset.univ d
      ⟨(⟨0, hn⟩ : Fin n), Finset.mem_univ _⟩
  have hdmax : ∀ j, d j ≤ d i0 := fun j => hi0 j (Finset.mem_univ j)
  let I := {i : Fin n // d i = d i0}
  let J := {j : Fin n // d j < d i0}
  let X := {x : Plane // x ∈ (K : Set Plane)}
  let U : Set X := ⋃ i : I, {x : X | x.1 ∈ PowerDiagram.cell s w i.1}
  let O : Set X := ⋃ i : I, ⋂ j : J,
    {x : X | PowerDiagram.powerDist s w' i.1 x.1 <
      PowerDiagram.powerDist s w' j.1 x.1}
  have hcellEq (i : I) :
      PowerDiagram.bodyCellSet K s w i.1 =
        PowerDiagram.bodyCellSet K s w' i.1 := by
    apply PowerDiagram.bodyCellSet_eq_of_equalArea_of_weightDifference_max K s hn hw hw' i.1
    intro j
    rw [show w' i.1 - w i.1 = d i.1 by rfl, i.2]
    simpa [d] using hdmax j
  have hcellMemEq (i : I) (x : X) :
      x.1 ∈ PowerDiagram.cell s w i.1 ↔
        x.1 ∈ PowerDiagram.cell s w' i.1 := by
    have hx := Set.ext_iff.mp (hcellEq i) x.1
    simpa [PowerDiagram.bodyCellSet, x.2] using hx
  have hUO : U = O := by
    ext x
    constructor
    · intro hx
      simp only [U, Set.mem_iUnion, Set.mem_ofPred_eq] at hx
      obtain ⟨i, hxi⟩ := hx
      simp only [O, Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq]
      refine ⟨i, ?_⟩
      intro j
      have hle := (PowerDiagram.mem_cell s w i.1 x.1).mp hxi j.1
      have hi : d i.1 = d i0 := i.2
      have hj : d j.1 < d i0 := j.2
      simp only [PowerDiagram.powerDist] at hle ⊢
      dsimp [d] at hi hj
      linarith
    · intro hx
      simp only [O, Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq] at hx
      obtain ⟨i, hstrict⟩ := hx
      obtain ⟨k, _, hk⟩ :=
        Finset.exists_min_image Finset.univ
          (fun q : I => PowerDiagram.powerDist s w' q.1 x.1)
          ⟨i, Finset.mem_univ i⟩
      have hxk' : x.1 ∈ PowerDiagram.cell s w' k.1 := by
        rw [PowerDiagram.mem_cell]
        intro j
        by_cases hj : d j = d i0
        · let jI : I := ⟨j, hj⟩
          exact hk jI (Finset.mem_univ jI)
        · have hjlt : d j < d i0 := lt_of_le_of_ne (hdmax j) hj
          let jJ : J := ⟨j, hjlt⟩
          exact (lt_of_le_of_lt
            (hk i (Finset.mem_univ i))
            (hstrict jJ)).le
      have hxk : x.1 ∈ PowerDiagram.cell s w k.1 :=
        (hcellMemEq k x).mpr hxk'
      simp only [U, Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨k, hxk⟩
  have hpowerDist_cont (q : Fin n) :
      Continuous fun x : X => PowerDiagram.powerDist s w' q x.1 := by
    unfold PowerDiagram.powerDist
    exact (((continuous_subtype_val.sub continuous_const).norm.pow 2).sub
      continuous_const)
  have hUopen : IsOpen U := by
    rw [hUO]
    exact isOpen_iUnion fun i =>
      isOpen_iInter_of_finite fun j =>
        isOpen_lt (hpowerDist_cont i.1) (hpowerDist_cont j.1)
  have hUclosed : IsClosed U := by
    exact isClosed_iUnion_of_finite fun i =>
      (PowerDiagram.cell_isClosed s w i.1).preimage continuous_subtype_val
  have hUnonempty : U.Nonempty := by
    have hK : 0 < K.area :=
      (NRR.SolidConvexBody.ofConvexBody K).area_pos
    have hInt := PowerDiagram.bodyCellSet_interior_nonempty_of_equalArea
      K s w hn hK hw i0
    obtain ⟨x, hx⟩ := hInt
    have hxbody : x ∈ PowerDiagram.bodyCellSet K s w i0 := interior_subset hx
    let xi : I := ⟨i0, rfl⟩
    let xK : X := ⟨x, hxbody.1⟩
    refine ⟨xK, ?_⟩
    simp only [U, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨xi, hxbody.2⟩
  let : PreconnectedSpace X :=
    Subtype.preconnectedSpace K.convex.isPreconnected
  have hUuniv : U = Set.univ :=
    (show IsClopen U from ⟨hUclosed, hUopen⟩).eq_univ hUnonempty
  have hUbody :
      (⋃ i : I, PowerDiagram.bodyCellSet K s w i.1) = (K : Set Plane) := by
    ext x
    constructor
    · intro hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hxi⟩ := hx
      exact hxi.1
    · intro hxK
      let xK : X := ⟨x, hxK⟩
      have hxU : xK ∈ U := by rw [hUuniv]; trivial
      simp only [U, Set.mem_iUnion, Set.mem_ofPred_eq] at hxU
      obtain ⟨i, hxi⟩ := hxU
      simp only [Set.mem_iUnion]
      exact ⟨i, hxK, hxi⟩
  have hallMax : ∀ j, d j = d i0 := by
    intro j
    by_contra hj
    have hjlt : d j < d i0 := lt_of_le_of_ne (hdmax j) hj
    have hsub :
        PowerDiagram.bodyCellSet K s w j ⊆
          ⋃ i : I, PowerDiagram.bodyCellSet K s w i.1 := by
      rw [hUbody]
      exact PowerDiagram.bodyCellSet_subset_body K s w j
    have hnullUnion :
        volume (⋃ i : I,
          (PowerDiagram.bodyCellSet K s w j ∩
            PowerDiagram.bodyCellSet K s w i.1)) = 0 := by
      apply MeasureTheory.measure_iUnion_null
      intro i
      apply PowerDiagram.bodyCellSet_inter_null K s w hs
      intro hji
      have : d j = d i.1 := congrArg d hji
      rw [i.2] at this
      exact (ne_of_lt hjlt) this
    have hcellNull : volume (PowerDiagram.bodyCellSet K s w j) = 0 := by
      apply MeasureTheory.measure_mono_null
      · intro x hx
        have hxU := hsub hx
        simp only [Set.mem_iUnion] at hxU
        obtain ⟨i, hxi⟩ := hxU
        apply Set.mem_iUnion.mpr
        exact ⟨i, Set.mem_inter hx hxi⟩
      · exact hnullUnion
    have hK : 0 < K.area :=
      (NRR.SolidConvexBody.ofConvexBody K).area_pos
    have hpos := PowerDiagram.bodyCellArea_pos_of_equalArea K s w hn hK hw j
    have hareaZero : PowerDiagram.bodyCellArea K s w j = 0 := by
      unfold PowerDiagram.bodyCellArea
      rw [hcellNull]
      simp
    rw [hareaZero] at hpos
    exact (lt_irrefl (0 : Real)) hpos
  intro i j
  exact (hallMax i).trans (hallMax j).symm

end EMP

end NRR
