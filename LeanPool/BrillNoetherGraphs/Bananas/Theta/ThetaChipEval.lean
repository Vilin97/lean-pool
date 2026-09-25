/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Basics.BananaGeometry

/-!
# Chip evaluations for the theta ramp

The endpoint and first-interior evaluations support the firing identity
`eq:multDiffMarkedPts` and the evenly-marked conclusion `cor:evenlyMarkedKGT`
in the paper source.

The theta ramp uses the path positions `0`, `1`, and `length`.  Position `1`
needs a length split: on a strand of length one it is the head core vertex,
whereas on a longer strand it is the first interior vertex.
-/

namespace Bananas

open Utilities

open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

@[simp] theorem one_chip_pathVertex_zero_eq_core
    {g : ℕ} (B : Banana g) (α : Fin (g + 1)) :
    oneChip (G := B.graph) (B.pathVertex α ⟨0, by omega⟩) =
      oneChip (G := B.graph) (B.coreVertex (B.core.tail α)) := by
  rw [B.pathVertex_zero]

@[simp] theorem one_chip_pathVertex_length_eq_core
    {g : ℕ} (B : Banana g) (α : Fin (g + 1)) :
    oneChip (G := B.graph) (B.pathVertex α ⟨B.length α, by omega⟩) =
      oneChip (G := B.graph) (B.coreVertex (B.core.head α)) := by
  rw [B.pathVertex_length]

theorem one_chip_pathVertex_one_eq_core_of_length_eq_one
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (hLength : B.length α = 1) :
    oneChip (G := B.graph)
        (B.pathVertex α ⟨1, by have := B.length_pos α; omega⟩) =
      oneChip (G := B.graph) (B.coreVertex (B.core.head α)) := by
  have hPosition :
      (⟨1, by have := B.length_pos α; omega⟩ : B.PathPosition α) =
        ⟨B.length α, by omega⟩ := by
    apply Fin.ext
    simp [hLength]
  rw [hPosition, B.pathVertex_length]

theorem one_chip_pathVertex_one_eq_interior_of_one_lt_length
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (hLength : 1 < B.length α) :
    oneChip (G := B.graph)
        (B.pathVertex α ⟨1, by have := B.length_pos α; omega⟩) =
      oneChip (G := B.graph) (B.interiorVertex α
        ⟨0, by have := B.length_pos α; omega⟩) := by
  let position : B.PathPosition α :=
    ⟨1, by have := B.length_pos α; omega⟩
  have hInterior : B.IsInteriorPosition α position := by
    constructor
    · simp [position]
    · simp [position, hLength]
  have hVertex := B.pathVertex_eq_interiorVertex α position hInterior
  rw [show (⟨1, by have := B.length_pos α; omega⟩ : B.PathPosition α) = position by
    rfl, hVertex]
  congr 2

@[simp] theorem one_chip_pathVertex_zero_apply_core
    {g : ℕ} (B : Banana g) (α : Fin (g + 1)) (v : Fin 2) :
    (oneChip (G := B.graph) (B.pathVertex α ⟨0, by omega⟩))
        (B.coreVertex v) =
      if B.core.tail α = v then (1 : ℤ) else 0 := by
  rw [one_chip_pathVertex_zero_eq_core]
  simp [oneChip, SubdivisionGraph.Spec.coreVertex, eq_comm]

@[simp] theorem one_chip_pathVertex_length_apply_core
    {g : ℕ} (B : Banana g) (α : Fin (g + 1)) (v : Fin 2) :
    (oneChip (G := B.graph) (B.pathVertex α ⟨B.length α, by omega⟩))
        (B.coreVertex v) =
      if B.core.head α = v then (1 : ℤ) else 0 := by
  rw [one_chip_pathVertex_length_eq_core]
  simp [oneChip, SubdivisionGraph.Spec.coreVertex, eq_comm]

@[simp] theorem one_chip_pathVertex_zero_apply_interior
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (edge : Fin (g + 1)) (offset : Fin (B.length edge - 1)) :
    (oneChip (G := B.graph) (B.pathVertex α ⟨0, by omega⟩))
        (B.interiorVertex edge offset) = 0 := by
  rw [one_chip_pathVertex_zero_eq_core]
  simp [oneChip, SubdivisionGraph.Spec.coreVertex,
    SubdivisionGraph.Spec.interiorVertex]

@[simp] theorem one_chip_pathVertex_length_apply_interior
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (edge : Fin (g + 1)) (offset : Fin (B.length edge - 1)) :
    (oneChip (G := B.graph) (B.pathVertex α ⟨B.length α, by omega⟩))
        (B.interiorVertex edge offset) = 0 := by
  rw [one_chip_pathVertex_length_eq_core]
  simp [oneChip, SubdivisionGraph.Spec.coreVertex,
    SubdivisionGraph.Spec.interiorVertex]

@[simp] theorem one_chip_pathVertex_one_apply_core_of_one_lt_length
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (hLength : 1 < B.length α) (v : Fin 2) :
    (oneChip (G := B.graph)
        (B.pathVertex α ⟨1, by have := B.length_pos α; omega⟩))
        (B.coreVertex v) = 0 := by
  rw [one_chip_pathVertex_one_eq_interior_of_one_lt_length B α hLength]
  simp [oneChip, SubdivisionGraph.Spec.interiorVertex,
    SubdivisionGraph.Spec.coreVertex]

@[simp] theorem one_chip_pathVertex_one_apply_interior_of_one_lt_length
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (hLength : 1 < B.length α) (edge : Fin (g + 1))
    (offset : Fin (B.length edge - 1)) :
    (oneChip (G := B.graph)
        (B.pathVertex α ⟨1, by have := B.length_pos α; omega⟩))
        (B.interiorVertex edge offset) =
      if edge = α ∧ offset.val = 0 then (1 : ℤ) else 0 := by
  rw [one_chip_pathVertex_one_eq_interior_of_one_lt_length B α hLength]
  by_cases hEdge : edge = α
  · subst edge
    by_cases hOffset : offset.val = 0
    · have hOffsetEq : offset = ⟨0, by have := offset.isLt; omega⟩ :=
        Fin.ext hOffset
      simp [oneChip, SubdivisionGraph.Spec.interiorVertex, hOffsetEq]
    · have hOffsetEq : offset ≠ ⟨0, by have := offset.isLt; omega⟩ := by
        intro h
        apply hOffset
        exact congrArg Fin.val h
      simp [oneChip, SubdivisionGraph.Spec.interiorVertex, hOffset,
        hOffsetEq]
  · simp [oneChip, SubdivisionGraph.Spec.interiorVertex, hEdge]

@[simp] theorem one_chip_pathVertex_one_apply_core_of_length_eq_one
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (hLength : B.length α = 1) (v : Fin 2) :
    (oneChip (G := B.graph)
        (B.pathVertex α ⟨1, by have := B.length_pos α; omega⟩))
        (B.coreVertex v) =
      if B.core.head α = v then (1 : ℤ) else 0 := by
  rw [one_chip_pathVertex_one_eq_core_of_length_eq_one B α hLength]
  simp [oneChip, SubdivisionGraph.Spec.coreVertex, eq_comm]

@[simp] theorem one_chip_pathVertex_one_apply_interior_of_length_eq_one
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (hLength : B.length α = 1) (edge : Fin (g + 1))
    (offset : Fin (B.length edge - 1)) :
    (oneChip (G := B.graph)
        (B.pathVertex α ⟨1, by have := B.length_pos α; omega⟩))
        (B.interiorVertex edge offset) = 0 := by
  rw [one_chip_pathVertex_one_eq_core_of_length_eq_one B α hLength]
  simp [oneChip, SubdivisionGraph.Spec.coreVertex,
    SubdivisionGraph.Spec.interiorVertex]

end Bananas
