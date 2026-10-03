/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.HadwigerNelsonBounds.PartsPermutations
public import LeanPool.HadwigerNelsonBounds.PartsCertificateData0
public import LeanPool.HadwigerNelsonBounds.PartsCertificateData1
public import LeanPool.HadwigerNelsonBounds.PartsCertificateData2
public import LeanPool.HadwigerNelsonBounds.PartsCertificateData3
public import LeanPool.HadwigerNelsonBounds.PartsCertificateData4
public import LeanPool.HadwigerNelsonBounds.PartsCertificateData5
public import LeanPool.HadwigerNelsonBounds.PartsCertificateData6
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# The Parts obstruction to a monochromatic sqrt-three triangle

This module expands the 36 normalized coloring trees through the six exact
root symmetries and the remaining color swap. The resulting 432 certificates
cover every proper normalized coloring of the 13-vertex 2-Golomb root.
-/

public section

namespace HadwigerNelsonBounds

/-- Swap the two colors not fixed by the normalized root. -/
@[expose] def partsSwapMiddleColor (color : Fin 4) : Fin 4 := ![0, 2, 1, 3] color

/-- The color renaming used by a certificate variant. -/
@[expose] def partsTransformColor (swap : Bool) (color : Fin 4) : Fin 4 :=
  if swap then partsSwapMiddleColor color else color

/-- Rename the vertices and optionally the two free colors of an assignment. -/
@[expose] def partsTransformAssignment (symmetry : Fin 6) (swap : Bool)
    (assignment : PartsAssignment) : PartsAssignment :=
  { vertex := partsPermuteVertex symmetry assignment.vertex
    color := partsTransformColor swap assignment.color }

/-- Transform a root path without materializing a second copy of its tree. -/
@[expose] def partsTransformPath (symmetry : Fin 6) (swap : Bool) :
    List PartsAssignment → List PartsAssignment
  | [] => []
  | assignment :: path =>
      partsTransformAssignment symmetry swap assignment ::
        partsTransformPath symmetry swap path

private lemma partsTransformColor_involutive (swap : Bool) (color : Fin 4) :
    partsTransformColor swap (partsTransformColor swap color) = color := by
  cases swap <;> fin_cases color <;> rfl

private lemma partsTransformColor_beq (swap : Bool) (left right : Fin 4) :
    (partsTransformColor swap left == partsTransformColor swap right) = (left == right) := by
  cases swap <;> fin_cases left <;> fin_cases right <;> decide

private lemma partsColors_all_transformColor (swap : Bool) (predicate : Fin 4 → Bool) :
    partsColors.all (fun color ↦ predicate (partsTransformColor swap color)) =
      partsColors.all predicate := by
  cases swap <;>
    simp [partsColors, partsTransformColor, partsSwapMiddleColor,
      Bool.and_left_comm, Bool.and_comm]

namespace PartsPoint

/-- Exact coordinate relation induced by one of the six stored root symmetries. -/
private def IsTransform (symmetry : Fin 6) (point image : PartsPoint) : Prop :=
  match symmetry.val with
  | 0 => image = point
  | 1 =>
      2 * image.a = -point.a - 3 * point.c ∧
      2 * image.b = -point.b - point.d ∧
      2 * image.c = point.a - point.c ∧
      2 * image.d = 3 * point.b - point.d
  | 2 =>
      2 * image.a = -point.a + 3 * point.c ∧
      2 * image.b = -point.b + point.d ∧
      2 * image.c = -point.a - point.c ∧
      2 * image.d = -3 * point.b - point.d
  | 3 =>
      image.a = point.a ∧ image.b = -point.b ∧
      image.c = -point.c ∧ image.d = point.d
  | 4 =>
      2 * image.a = -point.a - 3 * point.c ∧
      2 * image.b = point.b + point.d ∧
      2 * image.c = -point.a + point.c ∧
      2 * image.d = 3 * point.b - point.d
  | 5 =>
      2 * image.a = -point.a + 3 * point.c ∧
      2 * image.b = point.b - point.d ∧
      2 * image.c = point.a + point.c ∧
      2 * image.d = -3 * point.b - point.d
  | _ => False

private lemma IsTransform.sub {symmetry : Fin 6} {point image point' image' : PartsPoint}
    (left : IsTransform symmetry point image)
    (right : IsTransform symmetry point' image') :
    IsTransform symmetry (point.sub point') (image.sub image') := by
  fin_cases symmetry
  · simpa [IsTransform] using congrArg₂ PartsPoint.sub left right
  all_goals
    simp [IsTransform, PartsPoint.sub] at left right ⊢
    omega

private lemma IsTransform.isUnit_eq {symmetry : Fin 6} {point image : PartsPoint}
    (transform : IsTransform symmetry point image) : image.IsUnit = point.IsUnit := by
  fin_cases symmetry
  · simpa [IsTransform] using congrArg PartsPoint.IsUnit transform
  · rcases transform with ⟨ha, hb, hc, hd⟩
    have hnorm : 4 * image.normNumerator = 4 * point.normNumerator := by
      simp only [normNumerator]
      linear_combination
        (2 * image.a + (-point.a - 3 * point.c)) * ha +
        33 * (2 * image.b + (-point.b - point.d)) * hb +
        3 * (2 * image.c + (point.a - point.c)) * hc +
        11 * (2 * image.d + (3 * point.b - point.d)) * hd
    have hradical : 4 * image.radicalCoefficient = 4 * point.radicalCoefficient := by
      simp only [radicalCoefficient]
      linear_combination
        (2 * image.b) * ha + (-point.a - 3 * point.c) * hb +
        (2 * image.d) * hc + (point.a - point.c) * hd
    have hnorm' : image.normNumerator = point.normNumerator := by omega
    have hradical' : image.radicalCoefficient = point.radicalCoefficient := by omega
    simp [IsUnit, hnorm', hradical']
  · rcases transform with ⟨ha, hb, hc, hd⟩
    have hnorm : 4 * image.normNumerator = 4 * point.normNumerator := by
      simp only [normNumerator]
      linear_combination
        (2 * image.a + (-point.a + 3 * point.c)) * ha +
        33 * (2 * image.b + (-point.b + point.d)) * hb +
        3 * (2 * image.c + (-point.a - point.c)) * hc +
        11 * (2 * image.d + (-3 * point.b - point.d)) * hd
    have hradical : 4 * image.radicalCoefficient = 4 * point.radicalCoefficient := by
      simp only [radicalCoefficient]
      linear_combination
        (2 * image.b) * ha + (-point.a + 3 * point.c) * hb +
        (2 * image.d) * hc + (-point.a - point.c) * hd
    have hnorm' : image.normNumerator = point.normNumerator := by omega
    have hradical' : image.radicalCoefficient = point.radicalCoefficient := by omega
    simp [IsUnit, hnorm', hradical']
  · rcases transform with ⟨ha, hb, hc, hd⟩
    have hnorm : image.normNumerator = point.normNumerator := by
      simp only [normNumerator]
      linear_combination
        (image.a + point.a) * ha +
        33 * (image.b - point.b) * hb +
        3 * (image.c - point.c) * hc +
        11 * (image.d + point.d) * hd
    have hradical : image.radicalCoefficient = -point.radicalCoefficient := by
      simp only [radicalCoefficient]
      linear_combination
        image.b * ha + point.a * hb + image.d * hc + (-point.c) * hd
    simp [IsUnit, hnorm, hradical]
  · rcases transform with ⟨ha, hb, hc, hd⟩
    have hnorm : 4 * image.normNumerator = 4 * point.normNumerator := by
      simp only [normNumerator]
      linear_combination
        (2 * image.a + (-point.a - 3 * point.c)) * ha +
        33 * (2 * image.b + (point.b + point.d)) * hb +
        3 * (2 * image.c + (-point.a + point.c)) * hc +
        11 * (2 * image.d + (3 * point.b - point.d)) * hd
    have hradical : 4 * image.radicalCoefficient = -4 * point.radicalCoefficient := by
      simp only [radicalCoefficient]
      linear_combination
        (2 * image.b) * ha + (-point.a - 3 * point.c) * hb +
        (2 * image.d) * hc + (-point.a + point.c) * hd
    have hnorm' : image.normNumerator = point.normNumerator := by omega
    have hzero : image.radicalCoefficient = 0 ↔ point.radicalCoefficient = 0 := by
      omega
    simp [IsUnit, hnorm', hzero]
  · rcases transform with ⟨ha, hb, hc, hd⟩
    have hnorm : 4 * image.normNumerator = 4 * point.normNumerator := by
      simp only [normNumerator]
      linear_combination
        (2 * image.a + (-point.a + 3 * point.c)) * ha +
        33 * (2 * image.b + (point.b - point.d)) * hb +
        3 * (2 * image.c + (point.a + point.c)) * hc +
        11 * (2 * image.d + (-3 * point.b - point.d)) * hd
    have hradical : 4 * image.radicalCoefficient = -4 * point.radicalCoefficient := by
      simp only [radicalCoefficient]
      linear_combination
        (2 * image.b) * ha + (-point.a + 3 * point.c) * hb +
        (2 * image.d) * hc + (point.a + point.c) * hd
    have hnorm' : image.normNumerator = point.normNumerator := by omega
    have hzero : image.radicalCoefficient = 0 ↔ point.radicalCoefficient = 0 := by
      omega
    simp [IsUnit, hnorm', hzero]

end PartsPoint

/-- The stored vertex tables implement the exact isometries described above. -/
private lemma partsPoint_permuteVertex_isTransform_case0 :
    ∀ vertex, PartsPoint.IsTransform (0 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (0 : Fin 6) vertex)) := by
  rintro ⟨vertex, bound⟩
  have hsplit :
      vertex < 120 ∨
        (120 ≤ vertex ∧ vertex < 240) ∨
        (240 ≤ vertex ∧ vertex < 360) ∨
        360 ≤ vertex := by omega
  rcases hsplit with upper | ⟨lower, upper⟩ | ⟨lower, upper⟩ | lower
  all_goals
    interval_cases vertex <;> simp only [PartsPoint.IsTransform]
    all_goals
      have hbound : bound = (by decide) := Subsingleton.elim _ _
      rw [hbound]
      rfl

private lemma partsPoint_permuteVertex_isTransform_case1_chunk0
    (vertex : Fin 481) (range : vertex.val < 8) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  interval_cases vertex
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk0,
      partsPointChunk0]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk1
    (vertex : Fin 481) (range : 8 ≤ vertex.val ∧ vertex.val < 16) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk0,
      partsPointChunk0]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk2
    (vertex : Fin 481) (range : 16 ≤ vertex.val ∧ vertex.val < 24) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk0,
      partsPointChunk0]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk3
    (vertex : Fin 481) (range : 24 ≤ vertex.val ∧ vertex.val < 32) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk0,
      partsPointChunk0]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk4
    (vertex : Fin 481) (range : 32 ≤ vertex.val ∧ vertex.val < 40) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk0,
      partsPointChunk0]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk5
    (vertex : Fin 481) (range : 40 ≤ vertex.val ∧ vertex.val < 48) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk0,
      partsPointChunk0]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk6
    (vertex : Fin 481) (range : 48 ≤ vertex.val ∧ vertex.val < 56) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk0,
      partsPointChunk0, partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk7
    (vertex : Fin 481) (range : 56 ≤ vertex.val ∧ vertex.val < 64) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk0,
      partsPointChunk0]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk8
    (vertex : Fin 481) (range : 64 ≤ vertex.val ∧ vertex.val < 72) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk1,
      partsPointChunk0, partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk9
    (vertex : Fin 481) (range : 72 ≤ vertex.val ∧ vertex.val < 80) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk1,
      partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk10
    (vertex : Fin 481) (range : 80 ≤ vertex.val ∧ vertex.val < 88) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk1,
      partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk11
    (vertex : Fin 481) (range : 88 ≤ vertex.val ∧ vertex.val < 96) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk1,
      partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk12
    (vertex : Fin 481) (range : 96 ≤ vertex.val ∧ vertex.val < 104) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk1,
      partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk13
    (vertex : Fin 481) (range : 104 ≤ vertex.val ∧ vertex.val < 112) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk1,
      partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk14
    (vertex : Fin 481) (range : 112 ≤ vertex.val ∧ vertex.val < 120) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk1,
      partsPointChunk1, partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk15
    (vertex : Fin 481) (range : 120 ≤ vertex.val ∧ vertex.val < 128) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk1,
      partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk16
    (vertex : Fin 481) (range : 128 ≤ vertex.val ∧ vertex.val < 136) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk2,
      partsPointChunk1, partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk17
    (vertex : Fin 481) (range : 136 ≤ vertex.val ∧ vertex.val < 144) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk2,
      partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk18
    (vertex : Fin 481) (range : 144 ≤ vertex.val ∧ vertex.val < 152) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk2,
      partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk19
    (vertex : Fin 481) (range : 152 ≤ vertex.val ∧ vertex.val < 160) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk2,
      partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk20
    (vertex : Fin 481) (range : 160 ≤ vertex.val ∧ vertex.val < 168) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk2,
      partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk21
    (vertex : Fin 481) (range : 168 ≤ vertex.val ∧ vertex.val < 176) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk2,
      partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk22
    (vertex : Fin 481) (range : 176 ≤ vertex.val ∧ vertex.val < 184) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk2,
      partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk23
    (vertex : Fin 481) (range : 184 ≤ vertex.val ∧ vertex.val < 192) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk2,
      partsPointChunk2, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk24
    (vertex : Fin 481) (range : 192 ≤ vertex.val ∧ vertex.val < 200) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk3,
      partsPointChunk2, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk25
    (vertex : Fin 481) (range : 200 ≤ vertex.val ∧ vertex.val < 208) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk3,
      partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk26
    (vertex : Fin 481) (range : 208 ≤ vertex.val ∧ vertex.val < 216) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk3,
      partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk27
    (vertex : Fin 481) (range : 216 ≤ vertex.val ∧ vertex.val < 224) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk3,
      partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk28
    (vertex : Fin 481) (range : 224 ≤ vertex.val ∧ vertex.val < 232) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk3,
      partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk29
    (vertex : Fin 481) (range : 232 ≤ vertex.val ∧ vertex.val < 240) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk3,
      partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk30
    (vertex : Fin 481) (range : 240 ≤ vertex.val ∧ vertex.val < 248) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk3,
      partsPointChunk3, partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk31
    (vertex : Fin 481) (range : 248 ≤ vertex.val ∧ vertex.val < 256) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk3,
      partsPointChunk3, partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk32
    (vertex : Fin 481) (range : 256 ≤ vertex.val ∧ vertex.val < 264) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk4,
      partsPointChunk3, partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk33
    (vertex : Fin 481) (range : 264 ≤ vertex.val ∧ vertex.val < 272) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk34
    (vertex : Fin 481) (range : 272 ≤ vertex.val ∧ vertex.val < 280) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk35
    (vertex : Fin 481) (range : 280 ≤ vertex.val ∧ vertex.val < 288) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk36
    (vertex : Fin 481) (range : 288 ≤ vertex.val ∧ vertex.val < 296) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk37
    (vertex : Fin 481) (range : 296 ≤ vertex.val ∧ vertex.val < 304) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk38
    (vertex : Fin 481) (range : 304 ≤ vertex.val ∧ vertex.val < 312) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk39
    (vertex : Fin 481) (range : 312 ≤ vertex.val ∧ vertex.val < 320) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk4,
      partsPointChunk4, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk40
    (vertex : Fin 481) (range : 320 ≤ vertex.val ∧ vertex.val < 328) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk5,
      partsPointChunk4, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk41
    (vertex : Fin 481) (range : 328 ≤ vertex.val ∧ vertex.val < 336) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk5,
      partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk42
    (vertex : Fin 481) (range : 336 ≤ vertex.val ∧ vertex.val < 344) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk5,
      partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk43
    (vertex : Fin 481) (range : 344 ≤ vertex.val ∧ vertex.val < 352) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk5,
      partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk44
    (vertex : Fin 481) (range : 352 ≤ vertex.val ∧ vertex.val < 360) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk5,
      partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk45
    (vertex : Fin 481) (range : 360 ≤ vertex.val ∧ vertex.val < 368) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk5,
      partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk46
    (vertex : Fin 481) (range : 368 ≤ vertex.val ∧ vertex.val < 376) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk5,
      partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk47
    (vertex : Fin 481) (range : 376 ≤ vertex.val ∧ vertex.val < 384) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk5,
      partsPointChunk5, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk48
    (vertex : Fin 481) (range : 384 ≤ vertex.val ∧ vertex.val < 392) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk6,
      partsPointChunk5, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk49
    (vertex : Fin 481) (range : 392 ≤ vertex.val ∧ vertex.val < 400) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk50
    (vertex : Fin 481) (range : 400 ≤ vertex.val ∧ vertex.val < 408) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk51
    (vertex : Fin 481) (range : 408 ≤ vertex.val ∧ vertex.val < 416) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk52
    (vertex : Fin 481) (range : 416 ≤ vertex.val ∧ vertex.val < 424) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk53
    (vertex : Fin 481) (range : 424 ≤ vertex.val ∧ vertex.val < 432) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk54
    (vertex : Fin 481) (range : 432 ≤ vertex.val ∧ vertex.val < 440) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk55
    (vertex : Fin 481) (range : 440 ≤ vertex.val ∧ vertex.val < 448) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk6,
      partsPointChunk6, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk56
    (vertex : Fin 481) (range : 448 ≤ vertex.val ∧ vertex.val < 456) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk7,
      partsPointChunk6, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk57
    (vertex : Fin 481) (range : 456 ≤ vertex.val ∧ vertex.val < 464) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk7,
      partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk58
    (vertex : Fin 481) (range : 464 ≤ vertex.val ∧ vertex.val < 472) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk7,
      partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk59
    (vertex : Fin 481) (range : 472 ≤ vertex.val ∧ vertex.val < 480) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk7,
      partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case1_chunk60
    (vertex : Fin 481) (range : 480 ≤ vertex.val ∧ vertex.val < 481) :
    PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation1, partsVertexPermutation1Chunk7,
      partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case1 :
    ∀ vertex, PartsPoint.IsTransform (1 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (1 : Fin 6) vertex)) := by
  intro vertex
  by_cases h0 : vertex.val < 8
  · exact partsPoint_permuteVertex_isTransform_case1_chunk0 vertex h0
  by_cases h1 : vertex.val < 16
  · exact partsPoint_permuteVertex_isTransform_case1_chunk1 vertex ⟨by omega, h1⟩
  by_cases h2 : vertex.val < 24
  · exact partsPoint_permuteVertex_isTransform_case1_chunk2 vertex ⟨by omega, h2⟩
  by_cases h3 : vertex.val < 32
  · exact partsPoint_permuteVertex_isTransform_case1_chunk3 vertex ⟨by omega, h3⟩
  by_cases h4 : vertex.val < 40
  · exact partsPoint_permuteVertex_isTransform_case1_chunk4 vertex ⟨by omega, h4⟩
  by_cases h5 : vertex.val < 48
  · exact partsPoint_permuteVertex_isTransform_case1_chunk5 vertex ⟨by omega, h5⟩
  by_cases h6 : vertex.val < 56
  · exact partsPoint_permuteVertex_isTransform_case1_chunk6 vertex ⟨by omega, h6⟩
  by_cases h7 : vertex.val < 64
  · exact partsPoint_permuteVertex_isTransform_case1_chunk7 vertex ⟨by omega, h7⟩
  by_cases h8 : vertex.val < 72
  · exact partsPoint_permuteVertex_isTransform_case1_chunk8 vertex ⟨by omega, h8⟩
  by_cases h9 : vertex.val < 80
  · exact partsPoint_permuteVertex_isTransform_case1_chunk9 vertex ⟨by omega, h9⟩
  by_cases h10 : vertex.val < 88
  · exact partsPoint_permuteVertex_isTransform_case1_chunk10 vertex ⟨by omega, h10⟩
  by_cases h11 : vertex.val < 96
  · exact partsPoint_permuteVertex_isTransform_case1_chunk11 vertex ⟨by omega, h11⟩
  by_cases h12 : vertex.val < 104
  · exact partsPoint_permuteVertex_isTransform_case1_chunk12 vertex ⟨by omega, h12⟩
  by_cases h13 : vertex.val < 112
  · exact partsPoint_permuteVertex_isTransform_case1_chunk13 vertex ⟨by omega, h13⟩
  by_cases h14 : vertex.val < 120
  · exact partsPoint_permuteVertex_isTransform_case1_chunk14 vertex ⟨by omega, h14⟩
  by_cases h15 : vertex.val < 128
  · exact partsPoint_permuteVertex_isTransform_case1_chunk15 vertex ⟨by omega, h15⟩
  by_cases h16 : vertex.val < 136
  · exact partsPoint_permuteVertex_isTransform_case1_chunk16 vertex ⟨by omega, h16⟩
  by_cases h17 : vertex.val < 144
  · exact partsPoint_permuteVertex_isTransform_case1_chunk17 vertex ⟨by omega, h17⟩
  by_cases h18 : vertex.val < 152
  · exact partsPoint_permuteVertex_isTransform_case1_chunk18 vertex ⟨by omega, h18⟩
  by_cases h19 : vertex.val < 160
  · exact partsPoint_permuteVertex_isTransform_case1_chunk19 vertex ⟨by omega, h19⟩
  by_cases h20 : vertex.val < 168
  · exact partsPoint_permuteVertex_isTransform_case1_chunk20 vertex ⟨by omega, h20⟩
  by_cases h21 : vertex.val < 176
  · exact partsPoint_permuteVertex_isTransform_case1_chunk21 vertex ⟨by omega, h21⟩
  by_cases h22 : vertex.val < 184
  · exact partsPoint_permuteVertex_isTransform_case1_chunk22 vertex ⟨by omega, h22⟩
  by_cases h23 : vertex.val < 192
  · exact partsPoint_permuteVertex_isTransform_case1_chunk23 vertex ⟨by omega, h23⟩
  by_cases h24 : vertex.val < 200
  · exact partsPoint_permuteVertex_isTransform_case1_chunk24 vertex ⟨by omega, h24⟩
  by_cases h25 : vertex.val < 208
  · exact partsPoint_permuteVertex_isTransform_case1_chunk25 vertex ⟨by omega, h25⟩
  by_cases h26 : vertex.val < 216
  · exact partsPoint_permuteVertex_isTransform_case1_chunk26 vertex ⟨by omega, h26⟩
  by_cases h27 : vertex.val < 224
  · exact partsPoint_permuteVertex_isTransform_case1_chunk27 vertex ⟨by omega, h27⟩
  by_cases h28 : vertex.val < 232
  · exact partsPoint_permuteVertex_isTransform_case1_chunk28 vertex ⟨by omega, h28⟩
  by_cases h29 : vertex.val < 240
  · exact partsPoint_permuteVertex_isTransform_case1_chunk29 vertex ⟨by omega, h29⟩
  by_cases h30 : vertex.val < 248
  · exact partsPoint_permuteVertex_isTransform_case1_chunk30 vertex ⟨by omega, h30⟩
  by_cases h31 : vertex.val < 256
  · exact partsPoint_permuteVertex_isTransform_case1_chunk31 vertex ⟨by omega, h31⟩
  by_cases h32 : vertex.val < 264
  · exact partsPoint_permuteVertex_isTransform_case1_chunk32 vertex ⟨by omega, h32⟩
  by_cases h33 : vertex.val < 272
  · exact partsPoint_permuteVertex_isTransform_case1_chunk33 vertex ⟨by omega, h33⟩
  by_cases h34 : vertex.val < 280
  · exact partsPoint_permuteVertex_isTransform_case1_chunk34 vertex ⟨by omega, h34⟩
  by_cases h35 : vertex.val < 288
  · exact partsPoint_permuteVertex_isTransform_case1_chunk35 vertex ⟨by omega, h35⟩
  by_cases h36 : vertex.val < 296
  · exact partsPoint_permuteVertex_isTransform_case1_chunk36 vertex ⟨by omega, h36⟩
  by_cases h37 : vertex.val < 304
  · exact partsPoint_permuteVertex_isTransform_case1_chunk37 vertex ⟨by omega, h37⟩
  by_cases h38 : vertex.val < 312
  · exact partsPoint_permuteVertex_isTransform_case1_chunk38 vertex ⟨by omega, h38⟩
  by_cases h39 : vertex.val < 320
  · exact partsPoint_permuteVertex_isTransform_case1_chunk39 vertex ⟨by omega, h39⟩
  by_cases h40 : vertex.val < 328
  · exact partsPoint_permuteVertex_isTransform_case1_chunk40 vertex ⟨by omega, h40⟩
  by_cases h41 : vertex.val < 336
  · exact partsPoint_permuteVertex_isTransform_case1_chunk41 vertex ⟨by omega, h41⟩
  by_cases h42 : vertex.val < 344
  · exact partsPoint_permuteVertex_isTransform_case1_chunk42 vertex ⟨by omega, h42⟩
  by_cases h43 : vertex.val < 352
  · exact partsPoint_permuteVertex_isTransform_case1_chunk43 vertex ⟨by omega, h43⟩
  by_cases h44 : vertex.val < 360
  · exact partsPoint_permuteVertex_isTransform_case1_chunk44 vertex ⟨by omega, h44⟩
  by_cases h45 : vertex.val < 368
  · exact partsPoint_permuteVertex_isTransform_case1_chunk45 vertex ⟨by omega, h45⟩
  by_cases h46 : vertex.val < 376
  · exact partsPoint_permuteVertex_isTransform_case1_chunk46 vertex ⟨by omega, h46⟩
  by_cases h47 : vertex.val < 384
  · exact partsPoint_permuteVertex_isTransform_case1_chunk47 vertex ⟨by omega, h47⟩
  by_cases h48 : vertex.val < 392
  · exact partsPoint_permuteVertex_isTransform_case1_chunk48 vertex ⟨by omega, h48⟩
  by_cases h49 : vertex.val < 400
  · exact partsPoint_permuteVertex_isTransform_case1_chunk49 vertex ⟨by omega, h49⟩
  by_cases h50 : vertex.val < 408
  · exact partsPoint_permuteVertex_isTransform_case1_chunk50 vertex ⟨by omega, h50⟩
  by_cases h51 : vertex.val < 416
  · exact partsPoint_permuteVertex_isTransform_case1_chunk51 vertex ⟨by omega, h51⟩
  by_cases h52 : vertex.val < 424
  · exact partsPoint_permuteVertex_isTransform_case1_chunk52 vertex ⟨by omega, h52⟩
  by_cases h53 : vertex.val < 432
  · exact partsPoint_permuteVertex_isTransform_case1_chunk53 vertex ⟨by omega, h53⟩
  by_cases h54 : vertex.val < 440
  · exact partsPoint_permuteVertex_isTransform_case1_chunk54 vertex ⟨by omega, h54⟩
  by_cases h55 : vertex.val < 448
  · exact partsPoint_permuteVertex_isTransform_case1_chunk55 vertex ⟨by omega, h55⟩
  by_cases h56 : vertex.val < 456
  · exact partsPoint_permuteVertex_isTransform_case1_chunk56 vertex ⟨by omega, h56⟩
  by_cases h57 : vertex.val < 464
  · exact partsPoint_permuteVertex_isTransform_case1_chunk57 vertex ⟨by omega, h57⟩
  by_cases h58 : vertex.val < 472
  · exact partsPoint_permuteVertex_isTransform_case1_chunk58 vertex ⟨by omega, h58⟩
  by_cases h59 : vertex.val < 480
  · exact partsPoint_permuteVertex_isTransform_case1_chunk59 vertex ⟨by omega, h59⟩
  exact partsPoint_permuteVertex_isTransform_case1_chunk60 vertex ⟨by omega, by omega⟩

private lemma partsPoint_permuteVertex_isTransform_case2_chunk0
    (vertex : Fin 481) (range : vertex.val < 8) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  interval_cases vertex
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk0,
      partsPointChunk0]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk1
    (vertex : Fin 481) (range : 8 ≤ vertex.val ∧ vertex.val < 16) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk0,
      partsPointChunk0]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk2
    (vertex : Fin 481) (range : 16 ≤ vertex.val ∧ vertex.val < 24) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk0,
      partsPointChunk0]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk3
    (vertex : Fin 481) (range : 24 ≤ vertex.val ∧ vertex.val < 32) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk0,
      partsPointChunk0]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk4
    (vertex : Fin 481) (range : 32 ≤ vertex.val ∧ vertex.val < 40) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk0,
      partsPointChunk0]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk5
    (vertex : Fin 481) (range : 40 ≤ vertex.val ∧ vertex.val < 48) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk0,
      partsPointChunk0]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk6
    (vertex : Fin 481) (range : 48 ≤ vertex.val ∧ vertex.val < 56) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk0,
      partsPointChunk0]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk7
    (vertex : Fin 481) (range : 56 ≤ vertex.val ∧ vertex.val < 64) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk0,
      partsPointChunk0, partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk8
    (vertex : Fin 481) (range : 64 ≤ vertex.val ∧ vertex.val < 72) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk1,
      partsPointChunk0, partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk9
    (vertex : Fin 481) (range : 72 ≤ vertex.val ∧ vertex.val < 80) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk1,
      partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk10
    (vertex : Fin 481) (range : 80 ≤ vertex.val ∧ vertex.val < 88) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk1,
      partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk11
    (vertex : Fin 481) (range : 88 ≤ vertex.val ∧ vertex.val < 96) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk1,
      partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk12
    (vertex : Fin 481) (range : 96 ≤ vertex.val ∧ vertex.val < 104) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk1,
      partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk13
    (vertex : Fin 481) (range : 104 ≤ vertex.val ∧ vertex.val < 112) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk1,
      partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk14
    (vertex : Fin 481) (range : 112 ≤ vertex.val ∧ vertex.val < 120) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk1,
      partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk15
    (vertex : Fin 481) (range : 120 ≤ vertex.val ∧ vertex.val < 128) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk1,
      partsPointChunk1, partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk16
    (vertex : Fin 481) (range : 128 ≤ vertex.val ∧ vertex.val < 136) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk2,
      partsPointChunk1, partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk17
    (vertex : Fin 481) (range : 136 ≤ vertex.val ∧ vertex.val < 144) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk2,
      partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk18
    (vertex : Fin 481) (range : 144 ≤ vertex.val ∧ vertex.val < 152) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk2,
      partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk19
    (vertex : Fin 481) (range : 152 ≤ vertex.val ∧ vertex.val < 160) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk2,
      partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk20
    (vertex : Fin 481) (range : 160 ≤ vertex.val ∧ vertex.val < 168) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk2,
      partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk21
    (vertex : Fin 481) (range : 168 ≤ vertex.val ∧ vertex.val < 176) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk2,
      partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk22
    (vertex : Fin 481) (range : 176 ≤ vertex.val ∧ vertex.val < 184) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk2,
      partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk23
    (vertex : Fin 481) (range : 184 ≤ vertex.val ∧ vertex.val < 192) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk2,
      partsPointChunk2, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk24
    (vertex : Fin 481) (range : 192 ≤ vertex.val ∧ vertex.val < 200) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk3,
      partsPointChunk2, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk25
    (vertex : Fin 481) (range : 200 ≤ vertex.val ∧ vertex.val < 208) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk3,
      partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk26
    (vertex : Fin 481) (range : 208 ≤ vertex.val ∧ vertex.val < 216) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk3,
      partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk27
    (vertex : Fin 481) (range : 216 ≤ vertex.val ∧ vertex.val < 224) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk3,
      partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk28
    (vertex : Fin 481) (range : 224 ≤ vertex.val ∧ vertex.val < 232) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk3,
      partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk29
    (vertex : Fin 481) (range : 232 ≤ vertex.val ∧ vertex.val < 240) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk3,
      partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk30
    (vertex : Fin 481) (range : 240 ≤ vertex.val ∧ vertex.val < 248) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk3,
      partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk31
    (vertex : Fin 481) (range : 248 ≤ vertex.val ∧ vertex.val < 256) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk3,
      partsPointChunk3, partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk32
    (vertex : Fin 481) (range : 256 ≤ vertex.val ∧ vertex.val < 264) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk4,
      partsPointChunk3, partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk33
    (vertex : Fin 481) (range : 264 ≤ vertex.val ∧ vertex.val < 272) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk4,
      partsPointChunk3, partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk34
    (vertex : Fin 481) (range : 272 ≤ vertex.val ∧ vertex.val < 280) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk35
    (vertex : Fin 481) (range : 280 ≤ vertex.val ∧ vertex.val < 288) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk36
    (vertex : Fin 481) (range : 288 ≤ vertex.val ∧ vertex.val < 296) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk37
    (vertex : Fin 481) (range : 296 ≤ vertex.val ∧ vertex.val < 304) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk38
    (vertex : Fin 481) (range : 304 ≤ vertex.val ∧ vertex.val < 312) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk39
    (vertex : Fin 481) (range : 312 ≤ vertex.val ∧ vertex.val < 320) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk4,
      partsPointChunk4, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk40
    (vertex : Fin 481) (range : 320 ≤ vertex.val ∧ vertex.val < 328) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk5,
      partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk41
    (vertex : Fin 481) (range : 328 ≤ vertex.val ∧ vertex.val < 336) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk5,
      partsPointChunk4, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk42
    (vertex : Fin 481) (range : 336 ≤ vertex.val ∧ vertex.val < 344) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk5,
      partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk43
    (vertex : Fin 481) (range : 344 ≤ vertex.val ∧ vertex.val < 352) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk5,
      partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk44
    (vertex : Fin 481) (range : 352 ≤ vertex.val ∧ vertex.val < 360) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk5,
      partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk45
    (vertex : Fin 481) (range : 360 ≤ vertex.val ∧ vertex.val < 368) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk5,
      partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk46
    (vertex : Fin 481) (range : 368 ≤ vertex.val ∧ vertex.val < 376) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk5,
      partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk47
    (vertex : Fin 481) (range : 376 ≤ vertex.val ∧ vertex.val < 384) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk5,
      partsPointChunk5, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk48
    (vertex : Fin 481) (range : 384 ≤ vertex.val ∧ vertex.val < 392) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk6,
      partsPointChunk5, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk49
    (vertex : Fin 481) (range : 392 ≤ vertex.val ∧ vertex.val < 400) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk50
    (vertex : Fin 481) (range : 400 ≤ vertex.val ∧ vertex.val < 408) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk51
    (vertex : Fin 481) (range : 408 ≤ vertex.val ∧ vertex.val < 416) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk52
    (vertex : Fin 481) (range : 416 ≤ vertex.val ∧ vertex.val < 424) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk53
    (vertex : Fin 481) (range : 424 ≤ vertex.val ∧ vertex.val < 432) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk54
    (vertex : Fin 481) (range : 432 ≤ vertex.val ∧ vertex.val < 440) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk55
    (vertex : Fin 481) (range : 440 ≤ vertex.val ∧ vertex.val < 448) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk6,
      partsPointChunk6, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk56
    (vertex : Fin 481) (range : 448 ≤ vertex.val ∧ vertex.val < 456) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk7,
      partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk57
    (vertex : Fin 481) (range : 456 ≤ vertex.val ∧ vertex.val < 464) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk7,
      partsPointChunk6, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk58
    (vertex : Fin 481) (range : 464 ≤ vertex.val ∧ vertex.val < 472) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk7,
      partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk59
    (vertex : Fin 481) (range : 472 ≤ vertex.val ∧ vertex.val < 480) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk7,
      partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case2_chunk60
    (vertex : Fin 481) (range : 480 ≤ vertex.val ∧ vertex.val < 481) :
    PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation2, partsVertexPermutation2Chunk7,
      partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case2 :
    ∀ vertex, PartsPoint.IsTransform (2 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (2 : Fin 6) vertex)) := by
  intro vertex
  by_cases h0 : vertex.val < 8
  · exact partsPoint_permuteVertex_isTransform_case2_chunk0 vertex h0
  by_cases h1 : vertex.val < 16
  · exact partsPoint_permuteVertex_isTransform_case2_chunk1 vertex ⟨by omega, h1⟩
  by_cases h2 : vertex.val < 24
  · exact partsPoint_permuteVertex_isTransform_case2_chunk2 vertex ⟨by omega, h2⟩
  by_cases h3 : vertex.val < 32
  · exact partsPoint_permuteVertex_isTransform_case2_chunk3 vertex ⟨by omega, h3⟩
  by_cases h4 : vertex.val < 40
  · exact partsPoint_permuteVertex_isTransform_case2_chunk4 vertex ⟨by omega, h4⟩
  by_cases h5 : vertex.val < 48
  · exact partsPoint_permuteVertex_isTransform_case2_chunk5 vertex ⟨by omega, h5⟩
  by_cases h6 : vertex.val < 56
  · exact partsPoint_permuteVertex_isTransform_case2_chunk6 vertex ⟨by omega, h6⟩
  by_cases h7 : vertex.val < 64
  · exact partsPoint_permuteVertex_isTransform_case2_chunk7 vertex ⟨by omega, h7⟩
  by_cases h8 : vertex.val < 72
  · exact partsPoint_permuteVertex_isTransform_case2_chunk8 vertex ⟨by omega, h8⟩
  by_cases h9 : vertex.val < 80
  · exact partsPoint_permuteVertex_isTransform_case2_chunk9 vertex ⟨by omega, h9⟩
  by_cases h10 : vertex.val < 88
  · exact partsPoint_permuteVertex_isTransform_case2_chunk10 vertex ⟨by omega, h10⟩
  by_cases h11 : vertex.val < 96
  · exact partsPoint_permuteVertex_isTransform_case2_chunk11 vertex ⟨by omega, h11⟩
  by_cases h12 : vertex.val < 104
  · exact partsPoint_permuteVertex_isTransform_case2_chunk12 vertex ⟨by omega, h12⟩
  by_cases h13 : vertex.val < 112
  · exact partsPoint_permuteVertex_isTransform_case2_chunk13 vertex ⟨by omega, h13⟩
  by_cases h14 : vertex.val < 120
  · exact partsPoint_permuteVertex_isTransform_case2_chunk14 vertex ⟨by omega, h14⟩
  by_cases h15 : vertex.val < 128
  · exact partsPoint_permuteVertex_isTransform_case2_chunk15 vertex ⟨by omega, h15⟩
  by_cases h16 : vertex.val < 136
  · exact partsPoint_permuteVertex_isTransform_case2_chunk16 vertex ⟨by omega, h16⟩
  by_cases h17 : vertex.val < 144
  · exact partsPoint_permuteVertex_isTransform_case2_chunk17 vertex ⟨by omega, h17⟩
  by_cases h18 : vertex.val < 152
  · exact partsPoint_permuteVertex_isTransform_case2_chunk18 vertex ⟨by omega, h18⟩
  by_cases h19 : vertex.val < 160
  · exact partsPoint_permuteVertex_isTransform_case2_chunk19 vertex ⟨by omega, h19⟩
  by_cases h20 : vertex.val < 168
  · exact partsPoint_permuteVertex_isTransform_case2_chunk20 vertex ⟨by omega, h20⟩
  by_cases h21 : vertex.val < 176
  · exact partsPoint_permuteVertex_isTransform_case2_chunk21 vertex ⟨by omega, h21⟩
  by_cases h22 : vertex.val < 184
  · exact partsPoint_permuteVertex_isTransform_case2_chunk22 vertex ⟨by omega, h22⟩
  by_cases h23 : vertex.val < 192
  · exact partsPoint_permuteVertex_isTransform_case2_chunk23 vertex ⟨by omega, h23⟩
  by_cases h24 : vertex.val < 200
  · exact partsPoint_permuteVertex_isTransform_case2_chunk24 vertex ⟨by omega, h24⟩
  by_cases h25 : vertex.val < 208
  · exact partsPoint_permuteVertex_isTransform_case2_chunk25 vertex ⟨by omega, h25⟩
  by_cases h26 : vertex.val < 216
  · exact partsPoint_permuteVertex_isTransform_case2_chunk26 vertex ⟨by omega, h26⟩
  by_cases h27 : vertex.val < 224
  · exact partsPoint_permuteVertex_isTransform_case2_chunk27 vertex ⟨by omega, h27⟩
  by_cases h28 : vertex.val < 232
  · exact partsPoint_permuteVertex_isTransform_case2_chunk28 vertex ⟨by omega, h28⟩
  by_cases h29 : vertex.val < 240
  · exact partsPoint_permuteVertex_isTransform_case2_chunk29 vertex ⟨by omega, h29⟩
  by_cases h30 : vertex.val < 248
  · exact partsPoint_permuteVertex_isTransform_case2_chunk30 vertex ⟨by omega, h30⟩
  by_cases h31 : vertex.val < 256
  · exact partsPoint_permuteVertex_isTransform_case2_chunk31 vertex ⟨by omega, h31⟩
  by_cases h32 : vertex.val < 264
  · exact partsPoint_permuteVertex_isTransform_case2_chunk32 vertex ⟨by omega, h32⟩
  by_cases h33 : vertex.val < 272
  · exact partsPoint_permuteVertex_isTransform_case2_chunk33 vertex ⟨by omega, h33⟩
  by_cases h34 : vertex.val < 280
  · exact partsPoint_permuteVertex_isTransform_case2_chunk34 vertex ⟨by omega, h34⟩
  by_cases h35 : vertex.val < 288
  · exact partsPoint_permuteVertex_isTransform_case2_chunk35 vertex ⟨by omega, h35⟩
  by_cases h36 : vertex.val < 296
  · exact partsPoint_permuteVertex_isTransform_case2_chunk36 vertex ⟨by omega, h36⟩
  by_cases h37 : vertex.val < 304
  · exact partsPoint_permuteVertex_isTransform_case2_chunk37 vertex ⟨by omega, h37⟩
  by_cases h38 : vertex.val < 312
  · exact partsPoint_permuteVertex_isTransform_case2_chunk38 vertex ⟨by omega, h38⟩
  by_cases h39 : vertex.val < 320
  · exact partsPoint_permuteVertex_isTransform_case2_chunk39 vertex ⟨by omega, h39⟩
  by_cases h40 : vertex.val < 328
  · exact partsPoint_permuteVertex_isTransform_case2_chunk40 vertex ⟨by omega, h40⟩
  by_cases h41 : vertex.val < 336
  · exact partsPoint_permuteVertex_isTransform_case2_chunk41 vertex ⟨by omega, h41⟩
  by_cases h42 : vertex.val < 344
  · exact partsPoint_permuteVertex_isTransform_case2_chunk42 vertex ⟨by omega, h42⟩
  by_cases h43 : vertex.val < 352
  · exact partsPoint_permuteVertex_isTransform_case2_chunk43 vertex ⟨by omega, h43⟩
  by_cases h44 : vertex.val < 360
  · exact partsPoint_permuteVertex_isTransform_case2_chunk44 vertex ⟨by omega, h44⟩
  by_cases h45 : vertex.val < 368
  · exact partsPoint_permuteVertex_isTransform_case2_chunk45 vertex ⟨by omega, h45⟩
  by_cases h46 : vertex.val < 376
  · exact partsPoint_permuteVertex_isTransform_case2_chunk46 vertex ⟨by omega, h46⟩
  by_cases h47 : vertex.val < 384
  · exact partsPoint_permuteVertex_isTransform_case2_chunk47 vertex ⟨by omega, h47⟩
  by_cases h48 : vertex.val < 392
  · exact partsPoint_permuteVertex_isTransform_case2_chunk48 vertex ⟨by omega, h48⟩
  by_cases h49 : vertex.val < 400
  · exact partsPoint_permuteVertex_isTransform_case2_chunk49 vertex ⟨by omega, h49⟩
  by_cases h50 : vertex.val < 408
  · exact partsPoint_permuteVertex_isTransform_case2_chunk50 vertex ⟨by omega, h50⟩
  by_cases h51 : vertex.val < 416
  · exact partsPoint_permuteVertex_isTransform_case2_chunk51 vertex ⟨by omega, h51⟩
  by_cases h52 : vertex.val < 424
  · exact partsPoint_permuteVertex_isTransform_case2_chunk52 vertex ⟨by omega, h52⟩
  by_cases h53 : vertex.val < 432
  · exact partsPoint_permuteVertex_isTransform_case2_chunk53 vertex ⟨by omega, h53⟩
  by_cases h54 : vertex.val < 440
  · exact partsPoint_permuteVertex_isTransform_case2_chunk54 vertex ⟨by omega, h54⟩
  by_cases h55 : vertex.val < 448
  · exact partsPoint_permuteVertex_isTransform_case2_chunk55 vertex ⟨by omega, h55⟩
  by_cases h56 : vertex.val < 456
  · exact partsPoint_permuteVertex_isTransform_case2_chunk56 vertex ⟨by omega, h56⟩
  by_cases h57 : vertex.val < 464
  · exact partsPoint_permuteVertex_isTransform_case2_chunk57 vertex ⟨by omega, h57⟩
  by_cases h58 : vertex.val < 472
  · exact partsPoint_permuteVertex_isTransform_case2_chunk58 vertex ⟨by omega, h58⟩
  by_cases h59 : vertex.val < 480
  · exact partsPoint_permuteVertex_isTransform_case2_chunk59 vertex ⟨by omega, h59⟩
  exact partsPoint_permuteVertex_isTransform_case2_chunk60 vertex ⟨by omega, by omega⟩

private lemma partsPoint_permuteVertex_isTransform_case3_chunk0
    (vertex : Fin 481) (range : vertex.val < 8) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  interval_cases vertex
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk0,
      partsPointChunk0, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk1
    (vertex : Fin 481) (range : 8 ≤ vertex.val ∧ vertex.val < 16) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk0,
      partsPointChunk0, partsPointChunk3, partsPointChunk6, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk2
    (vertex : Fin 481) (range : 16 ≤ vertex.val ∧ vertex.val < 24) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk0,
      partsPointChunk0, partsPointChunk6, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk3
    (vertex : Fin 481) (range : 24 ≤ vertex.val ∧ vertex.val < 32) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk0,
      partsPointChunk0, partsPointChunk6, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk4
    (vertex : Fin 481) (range : 32 ≤ vertex.val ∧ vertex.val < 40) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk0,
      partsPointChunk0, partsPointChunk2, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk5
    (vertex : Fin 481) (range : 40 ≤ vertex.val ∧ vertex.val < 48) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk0,
      partsPointChunk0, partsPointChunk2, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk6
    (vertex : Fin 481) (range : 48 ≤ vertex.val ∧ vertex.val < 56) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk0,
      partsPointChunk0, partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk7
    (vertex : Fin 481) (range : 56 ≤ vertex.val ∧ vertex.val < 64) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk0,
      partsPointChunk0, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk8
    (vertex : Fin 481) (range : 64 ≤ vertex.val ∧ vertex.val < 72) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk1,
      partsPointChunk1, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk9
    (vertex : Fin 481) (range : 72 ≤ vertex.val ∧ vertex.val < 80) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk1,
      partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk10
    (vertex : Fin 481) (range : 80 ≤ vertex.val ∧ vertex.val < 88) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk1,
      partsPointChunk1, partsPointChunk5, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk11
    (vertex : Fin 481) (range : 88 ≤ vertex.val ∧ vertex.val < 96) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk1,
      partsPointChunk1, partsPointChunk5, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk12
    (vertex : Fin 481) (range : 96 ≤ vertex.val ∧ vertex.val < 104) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk1,
      partsPointChunk1, partsPointChunk3, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk13
    (vertex : Fin 481) (range : 104 ≤ vertex.val ∧ vertex.val < 112) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk1,
      partsPointChunk1, partsPointChunk3, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk14
    (vertex : Fin 481) (range : 112 ≤ vertex.val ∧ vertex.val < 120) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk1,
      partsPointChunk1, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk15
    (vertex : Fin 481) (range : 120 ≤ vertex.val ∧ vertex.val < 128) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk1,
      partsPointChunk1, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk16
    (vertex : Fin 481) (range : 128 ≤ vertex.val ∧ vertex.val < 136) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk2,
      partsPointChunk2, partsPointChunk4, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk17
    (vertex : Fin 481) (range : 136 ≤ vertex.val ∧ vertex.val < 144) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk2,
      partsPointChunk2, partsPointChunk4, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk18
    (vertex : Fin 481) (range : 144 ≤ vertex.val ∧ vertex.val < 152) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk2,
      partsPointChunk2, partsPointChunk4, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk19
    (vertex : Fin 481) (range : 152 ≤ vertex.val ∧ vertex.val < 160) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk2,
      partsPointChunk2, partsPointChunk4, partsPointChunk5, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk20
    (vertex : Fin 481) (range : 160 ≤ vertex.val ∧ vertex.val < 168) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk2,
      partsPointChunk2, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk21
    (vertex : Fin 481) (range : 168 ≤ vertex.val ∧ vertex.val < 176) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk2,
      partsPointChunk2, partsPointChunk6, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk22
    (vertex : Fin 481) (range : 176 ≤ vertex.val ∧ vertex.val < 184) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk2,
      partsPointChunk0, partsPointChunk2, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk23
    (vertex : Fin 481) (range : 184 ≤ vertex.val ∧ vertex.val < 192) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk2,
      partsPointChunk0, partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk24
    (vertex : Fin 481) (range : 192 ≤ vertex.val ∧ vertex.val < 200) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk3,
      partsPointChunk0, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk25
    (vertex : Fin 481) (range : 200 ≤ vertex.val ∧ vertex.val < 208) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk3,
      partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk26
    (vertex : Fin 481) (range : 208 ≤ vertex.val ∧ vertex.val < 216) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk3,
      partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk27
    (vertex : Fin 481) (range : 216 ≤ vertex.val ∧ vertex.val < 224) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk3,
      partsPointChunk1, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk28
    (vertex : Fin 481) (range : 224 ≤ vertex.val ∧ vertex.val < 232) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk3,
      partsPointChunk1, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk29
    (vertex : Fin 481) (range : 232 ≤ vertex.val ∧ vertex.val < 240) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk3,
      partsPointChunk0, partsPointChunk1, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk30
    (vertex : Fin 481) (range : 240 ≤ vertex.val ∧ vertex.val < 248) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk3,
      partsPointChunk0, partsPointChunk3, partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk31
    (vertex : Fin 481) (range : 248 ≤ vertex.val ∧ vertex.val < 256) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk3,
      partsPointChunk3, partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk32
    (vertex : Fin 481) (range : 256 ≤ vertex.val ∧ vertex.val < 264) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk4,
      partsPointChunk3, partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk33
    (vertex : Fin 481) (range : 264 ≤ vertex.val ∧ vertex.val < 272) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk4,
      partsPointChunk4, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk34
    (vertex : Fin 481) (range : 272 ≤ vertex.val ∧ vertex.val < 280) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk4,
      partsPointChunk4, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk35
    (vertex : Fin 481) (range : 280 ≤ vertex.val ∧ vertex.val < 288) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk36
    (vertex : Fin 481) (range : 288 ≤ vertex.val ∧ vertex.val < 296) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk37
    (vertex : Fin 481) (range : 296 ≤ vertex.val ∧ vertex.val < 304) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk38
    (vertex : Fin 481) (range : 304 ≤ vertex.val ∧ vertex.val < 312) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk39
    (vertex : Fin 481) (range : 312 ≤ vertex.val ∧ vertex.val < 320) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk4,
      partsPointChunk2, partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk40
    (vertex : Fin 481) (range : 320 ≤ vertex.val ∧ vertex.val < 328) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk5,
      partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk41
    (vertex : Fin 481) (range : 328 ≤ vertex.val ∧ vertex.val < 336) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk5,
      partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk42
    (vertex : Fin 481) (range : 336 ≤ vertex.val ∧ vertex.val < 344) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk5,
      partsPointChunk0, partsPointChunk1, partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk43
    (vertex : Fin 481) (range : 344 ≤ vertex.val ∧ vertex.val < 352) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk5,
      partsPointChunk0, partsPointChunk1, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk44
    (vertex : Fin 481) (range : 352 ≤ vertex.val ∧ vertex.val < 360) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk5,
      partsPointChunk0, partsPointChunk1, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk45
    (vertex : Fin 481) (range : 360 ≤ vertex.val ∧ vertex.val < 368) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk5,
      partsPointChunk1, partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk46
    (vertex : Fin 481) (range : 368 ≤ vertex.val ∧ vertex.val < 376) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk5,
      partsPointChunk1, partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk47
    (vertex : Fin 481) (range : 376 ≤ vertex.val ∧ vertex.val < 384) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk5,
      partsPointChunk1, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk48
    (vertex : Fin 481) (range : 384 ≤ vertex.val ∧ vertex.val < 392) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk6,
      partsPointChunk1, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk49
    (vertex : Fin 481) (range : 392 ≤ vertex.val ∧ vertex.val < 400) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk50
    (vertex : Fin 481) (range : 400 ≤ vertex.val ∧ vertex.val < 408) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk51
    (vertex : Fin 481) (range : 408 ≤ vertex.val ∧ vertex.val < 416) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk52
    (vertex : Fin 481) (range : 416 ≤ vertex.val ∧ vertex.val < 424) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk6,
      partsPointChunk2, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk53
    (vertex : Fin 481) (range : 424 ≤ vertex.val ∧ vertex.val < 432) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk6,
      partsPointChunk2, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk54
    (vertex : Fin 481) (range : 432 ≤ vertex.val ∧ vertex.val < 440) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk6,
      partsPointChunk2, partsPointChunk4, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk55
    (vertex : Fin 481) (range : 440 ≤ vertex.val ∧ vertex.val < 448) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk6,
      partsPointChunk0, partsPointChunk4, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk56
    (vertex : Fin 481) (range : 448 ≤ vertex.val ∧ vertex.val < 456) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk7,
      partsPointChunk0, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk57
    (vertex : Fin 481) (range : 456 ≤ vertex.val ∧ vertex.val < 464) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk7,
      partsPointChunk0, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk58
    (vertex : Fin 481) (range : 464 ≤ vertex.val ∧ vertex.val < 472) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk7,
      partsPointChunk0, partsPointChunk2, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk59
    (vertex : Fin 481) (range : 472 ≤ vertex.val ∧ vertex.val < 480) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk7,
      partsPointChunk2, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case3_chunk60
    (vertex : Fin 481) (range : 480 ≤ vertex.val ∧ vertex.val < 481) :
    PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation3, partsVertexPermutation3Chunk7,
      partsPointChunk2, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case3 :
    ∀ vertex, PartsPoint.IsTransform (3 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (3 : Fin 6) vertex)) := by
  intro vertex
  by_cases h0 : vertex.val < 8
  · exact partsPoint_permuteVertex_isTransform_case3_chunk0 vertex h0
  by_cases h1 : vertex.val < 16
  · exact partsPoint_permuteVertex_isTransform_case3_chunk1 vertex ⟨by omega, h1⟩
  by_cases h2 : vertex.val < 24
  · exact partsPoint_permuteVertex_isTransform_case3_chunk2 vertex ⟨by omega, h2⟩
  by_cases h3 : vertex.val < 32
  · exact partsPoint_permuteVertex_isTransform_case3_chunk3 vertex ⟨by omega, h3⟩
  by_cases h4 : vertex.val < 40
  · exact partsPoint_permuteVertex_isTransform_case3_chunk4 vertex ⟨by omega, h4⟩
  by_cases h5 : vertex.val < 48
  · exact partsPoint_permuteVertex_isTransform_case3_chunk5 vertex ⟨by omega, h5⟩
  by_cases h6 : vertex.val < 56
  · exact partsPoint_permuteVertex_isTransform_case3_chunk6 vertex ⟨by omega, h6⟩
  by_cases h7 : vertex.val < 64
  · exact partsPoint_permuteVertex_isTransform_case3_chunk7 vertex ⟨by omega, h7⟩
  by_cases h8 : vertex.val < 72
  · exact partsPoint_permuteVertex_isTransform_case3_chunk8 vertex ⟨by omega, h8⟩
  by_cases h9 : vertex.val < 80
  · exact partsPoint_permuteVertex_isTransform_case3_chunk9 vertex ⟨by omega, h9⟩
  by_cases h10 : vertex.val < 88
  · exact partsPoint_permuteVertex_isTransform_case3_chunk10 vertex ⟨by omega, h10⟩
  by_cases h11 : vertex.val < 96
  · exact partsPoint_permuteVertex_isTransform_case3_chunk11 vertex ⟨by omega, h11⟩
  by_cases h12 : vertex.val < 104
  · exact partsPoint_permuteVertex_isTransform_case3_chunk12 vertex ⟨by omega, h12⟩
  by_cases h13 : vertex.val < 112
  · exact partsPoint_permuteVertex_isTransform_case3_chunk13 vertex ⟨by omega, h13⟩
  by_cases h14 : vertex.val < 120
  · exact partsPoint_permuteVertex_isTransform_case3_chunk14 vertex ⟨by omega, h14⟩
  by_cases h15 : vertex.val < 128
  · exact partsPoint_permuteVertex_isTransform_case3_chunk15 vertex ⟨by omega, h15⟩
  by_cases h16 : vertex.val < 136
  · exact partsPoint_permuteVertex_isTransform_case3_chunk16 vertex ⟨by omega, h16⟩
  by_cases h17 : vertex.val < 144
  · exact partsPoint_permuteVertex_isTransform_case3_chunk17 vertex ⟨by omega, h17⟩
  by_cases h18 : vertex.val < 152
  · exact partsPoint_permuteVertex_isTransform_case3_chunk18 vertex ⟨by omega, h18⟩
  by_cases h19 : vertex.val < 160
  · exact partsPoint_permuteVertex_isTransform_case3_chunk19 vertex ⟨by omega, h19⟩
  by_cases h20 : vertex.val < 168
  · exact partsPoint_permuteVertex_isTransform_case3_chunk20 vertex ⟨by omega, h20⟩
  by_cases h21 : vertex.val < 176
  · exact partsPoint_permuteVertex_isTransform_case3_chunk21 vertex ⟨by omega, h21⟩
  by_cases h22 : vertex.val < 184
  · exact partsPoint_permuteVertex_isTransform_case3_chunk22 vertex ⟨by omega, h22⟩
  by_cases h23 : vertex.val < 192
  · exact partsPoint_permuteVertex_isTransform_case3_chunk23 vertex ⟨by omega, h23⟩
  by_cases h24 : vertex.val < 200
  · exact partsPoint_permuteVertex_isTransform_case3_chunk24 vertex ⟨by omega, h24⟩
  by_cases h25 : vertex.val < 208
  · exact partsPoint_permuteVertex_isTransform_case3_chunk25 vertex ⟨by omega, h25⟩
  by_cases h26 : vertex.val < 216
  · exact partsPoint_permuteVertex_isTransform_case3_chunk26 vertex ⟨by omega, h26⟩
  by_cases h27 : vertex.val < 224
  · exact partsPoint_permuteVertex_isTransform_case3_chunk27 vertex ⟨by omega, h27⟩
  by_cases h28 : vertex.val < 232
  · exact partsPoint_permuteVertex_isTransform_case3_chunk28 vertex ⟨by omega, h28⟩
  by_cases h29 : vertex.val < 240
  · exact partsPoint_permuteVertex_isTransform_case3_chunk29 vertex ⟨by omega, h29⟩
  by_cases h30 : vertex.val < 248
  · exact partsPoint_permuteVertex_isTransform_case3_chunk30 vertex ⟨by omega, h30⟩
  by_cases h31 : vertex.val < 256
  · exact partsPoint_permuteVertex_isTransform_case3_chunk31 vertex ⟨by omega, h31⟩
  by_cases h32 : vertex.val < 264
  · exact partsPoint_permuteVertex_isTransform_case3_chunk32 vertex ⟨by omega, h32⟩
  by_cases h33 : vertex.val < 272
  · exact partsPoint_permuteVertex_isTransform_case3_chunk33 vertex ⟨by omega, h33⟩
  by_cases h34 : vertex.val < 280
  · exact partsPoint_permuteVertex_isTransform_case3_chunk34 vertex ⟨by omega, h34⟩
  by_cases h35 : vertex.val < 288
  · exact partsPoint_permuteVertex_isTransform_case3_chunk35 vertex ⟨by omega, h35⟩
  by_cases h36 : vertex.val < 296
  · exact partsPoint_permuteVertex_isTransform_case3_chunk36 vertex ⟨by omega, h36⟩
  by_cases h37 : vertex.val < 304
  · exact partsPoint_permuteVertex_isTransform_case3_chunk37 vertex ⟨by omega, h37⟩
  by_cases h38 : vertex.val < 312
  · exact partsPoint_permuteVertex_isTransform_case3_chunk38 vertex ⟨by omega, h38⟩
  by_cases h39 : vertex.val < 320
  · exact partsPoint_permuteVertex_isTransform_case3_chunk39 vertex ⟨by omega, h39⟩
  by_cases h40 : vertex.val < 328
  · exact partsPoint_permuteVertex_isTransform_case3_chunk40 vertex ⟨by omega, h40⟩
  by_cases h41 : vertex.val < 336
  · exact partsPoint_permuteVertex_isTransform_case3_chunk41 vertex ⟨by omega, h41⟩
  by_cases h42 : vertex.val < 344
  · exact partsPoint_permuteVertex_isTransform_case3_chunk42 vertex ⟨by omega, h42⟩
  by_cases h43 : vertex.val < 352
  · exact partsPoint_permuteVertex_isTransform_case3_chunk43 vertex ⟨by omega, h43⟩
  by_cases h44 : vertex.val < 360
  · exact partsPoint_permuteVertex_isTransform_case3_chunk44 vertex ⟨by omega, h44⟩
  by_cases h45 : vertex.val < 368
  · exact partsPoint_permuteVertex_isTransform_case3_chunk45 vertex ⟨by omega, h45⟩
  by_cases h46 : vertex.val < 376
  · exact partsPoint_permuteVertex_isTransform_case3_chunk46 vertex ⟨by omega, h46⟩
  by_cases h47 : vertex.val < 384
  · exact partsPoint_permuteVertex_isTransform_case3_chunk47 vertex ⟨by omega, h47⟩
  by_cases h48 : vertex.val < 392
  · exact partsPoint_permuteVertex_isTransform_case3_chunk48 vertex ⟨by omega, h48⟩
  by_cases h49 : vertex.val < 400
  · exact partsPoint_permuteVertex_isTransform_case3_chunk49 vertex ⟨by omega, h49⟩
  by_cases h50 : vertex.val < 408
  · exact partsPoint_permuteVertex_isTransform_case3_chunk50 vertex ⟨by omega, h50⟩
  by_cases h51 : vertex.val < 416
  · exact partsPoint_permuteVertex_isTransform_case3_chunk51 vertex ⟨by omega, h51⟩
  by_cases h52 : vertex.val < 424
  · exact partsPoint_permuteVertex_isTransform_case3_chunk52 vertex ⟨by omega, h52⟩
  by_cases h53 : vertex.val < 432
  · exact partsPoint_permuteVertex_isTransform_case3_chunk53 vertex ⟨by omega, h53⟩
  by_cases h54 : vertex.val < 440
  · exact partsPoint_permuteVertex_isTransform_case3_chunk54 vertex ⟨by omega, h54⟩
  by_cases h55 : vertex.val < 448
  · exact partsPoint_permuteVertex_isTransform_case3_chunk55 vertex ⟨by omega, h55⟩
  by_cases h56 : vertex.val < 456
  · exact partsPoint_permuteVertex_isTransform_case3_chunk56 vertex ⟨by omega, h56⟩
  by_cases h57 : vertex.val < 464
  · exact partsPoint_permuteVertex_isTransform_case3_chunk57 vertex ⟨by omega, h57⟩
  by_cases h58 : vertex.val < 472
  · exact partsPoint_permuteVertex_isTransform_case3_chunk58 vertex ⟨by omega, h58⟩
  by_cases h59 : vertex.val < 480
  · exact partsPoint_permuteVertex_isTransform_case3_chunk59 vertex ⟨by omega, h59⟩
  exact partsPoint_permuteVertex_isTransform_case3_chunk60 vertex ⟨by omega, by omega⟩

private lemma partsPoint_permuteVertex_isTransform_case4_chunk0
    (vertex : Fin 481) (range : vertex.val < 8) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  interval_cases vertex
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk0,
      partsPointChunk0, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk1
    (vertex : Fin 481) (range : 8 ≤ vertex.val ∧ vertex.val < 16) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk0,
      partsPointChunk0, partsPointChunk3, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk2
    (vertex : Fin 481) (range : 16 ≤ vertex.val ∧ vertex.val < 24) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk0,
      partsPointChunk0, partsPointChunk6, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk3
    (vertex : Fin 481) (range : 24 ≤ vertex.val ∧ vertex.val < 32) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk0,
      partsPointChunk0, partsPointChunk6, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk4
    (vertex : Fin 481) (range : 32 ≤ vertex.val ∧ vertex.val < 40) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk0,
      partsPointChunk0, partsPointChunk2, partsPointChunk3, partsPointChunk6,
      partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk5
    (vertex : Fin 481) (range : 40 ≤ vertex.val ∧ vertex.val < 48) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk0,
      partsPointChunk0, partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk6
    (vertex : Fin 481) (range : 48 ≤ vertex.val ∧ vertex.val < 56) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk0,
      partsPointChunk0, partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk7
    (vertex : Fin 481) (range : 56 ≤ vertex.val ∧ vertex.val < 64) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk0,
      partsPointChunk0, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk8
    (vertex : Fin 481) (range : 64 ≤ vertex.val ∧ vertex.val < 72) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk1,
      partsPointChunk1, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk9
    (vertex : Fin 481) (range : 72 ≤ vertex.val ∧ vertex.val < 80) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk1,
      partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk10
    (vertex : Fin 481) (range : 80 ≤ vertex.val ∧ vertex.val < 88) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk1,
      partsPointChunk1, partsPointChunk5, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk11
    (vertex : Fin 481) (range : 88 ≤ vertex.val ∧ vertex.val < 96) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk1,
      partsPointChunk1, partsPointChunk5, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk12
    (vertex : Fin 481) (range : 96 ≤ vertex.val ∧ vertex.val < 104) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk1,
      partsPointChunk1, partsPointChunk3, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk13
    (vertex : Fin 481) (range : 104 ≤ vertex.val ∧ vertex.val < 112) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk1,
      partsPointChunk1, partsPointChunk3, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk14
    (vertex : Fin 481) (range : 112 ≤ vertex.val ∧ vertex.val < 120) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk1,
      partsPointChunk1, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk15
    (vertex : Fin 481) (range : 120 ≤ vertex.val ∧ vertex.val < 128) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk1,
      partsPointChunk1, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk16
    (vertex : Fin 481) (range : 128 ≤ vertex.val ∧ vertex.val < 136) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk2,
      partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk17
    (vertex : Fin 481) (range : 136 ≤ vertex.val ∧ vertex.val < 144) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk2,
      partsPointChunk2, partsPointChunk4, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk18
    (vertex : Fin 481) (range : 144 ≤ vertex.val ∧ vertex.val < 152) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk2,
      partsPointChunk2, partsPointChunk4, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk19
    (vertex : Fin 481) (range : 152 ≤ vertex.val ∧ vertex.val < 160) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk2,
      partsPointChunk2, partsPointChunk4, partsPointChunk5, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk20
    (vertex : Fin 481) (range : 160 ≤ vertex.val ∧ vertex.val < 168) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk2,
      partsPointChunk2, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk21
    (vertex : Fin 481) (range : 168 ≤ vertex.val ∧ vertex.val < 176) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk2,
      partsPointChunk2, partsPointChunk6, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk22
    (vertex : Fin 481) (range : 176 ≤ vertex.val ∧ vertex.val < 184) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk2,
      partsPointChunk0, partsPointChunk2, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk23
    (vertex : Fin 481) (range : 184 ≤ vertex.val ∧ vertex.val < 192) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk2,
      partsPointChunk0, partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk24
    (vertex : Fin 481) (range : 192 ≤ vertex.val ∧ vertex.val < 200) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk3,
      partsPointChunk0, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk25
    (vertex : Fin 481) (range : 200 ≤ vertex.val ∧ vertex.val < 208) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk3,
      partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk26
    (vertex : Fin 481) (range : 208 ≤ vertex.val ∧ vertex.val < 216) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk3,
      partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk27
    (vertex : Fin 481) (range : 216 ≤ vertex.val ∧ vertex.val < 224) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk3,
      partsPointChunk1, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk28
    (vertex : Fin 481) (range : 224 ≤ vertex.val ∧ vertex.val < 232) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk3,
      partsPointChunk1, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk29
    (vertex : Fin 481) (range : 232 ≤ vertex.val ∧ vertex.val < 240) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk3,
      partsPointChunk0, partsPointChunk1, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk30
    (vertex : Fin 481) (range : 240 ≤ vertex.val ∧ vertex.val < 248) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk3,
      partsPointChunk0, partsPointChunk3, partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk31
    (vertex : Fin 481) (range : 248 ≤ vertex.val ∧ vertex.val < 256) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk3,
      partsPointChunk3, partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk32
    (vertex : Fin 481) (range : 256 ≤ vertex.val ∧ vertex.val < 264) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk4,
      partsPointChunk3, partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk33
    (vertex : Fin 481) (range : 264 ≤ vertex.val ∧ vertex.val < 272) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk4,
      partsPointChunk3, partsPointChunk4, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk34
    (vertex : Fin 481) (range : 272 ≤ vertex.val ∧ vertex.val < 280) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk4,
      partsPointChunk4, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk35
    (vertex : Fin 481) (range : 280 ≤ vertex.val ∧ vertex.val < 288) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk36
    (vertex : Fin 481) (range : 288 ≤ vertex.val ∧ vertex.val < 296) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk37
    (vertex : Fin 481) (range : 296 ≤ vertex.val ∧ vertex.val < 304) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk38
    (vertex : Fin 481) (range : 304 ≤ vertex.val ∧ vertex.val < 312) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk39
    (vertex : Fin 481) (range : 312 ≤ vertex.val ∧ vertex.val < 320) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk4,
      partsPointChunk2, partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk40
    (vertex : Fin 481) (range : 320 ≤ vertex.val ∧ vertex.val < 328) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk5,
      partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk41
    (vertex : Fin 481) (range : 328 ≤ vertex.val ∧ vertex.val < 336) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk5,
      partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk42
    (vertex : Fin 481) (range : 336 ≤ vertex.val ∧ vertex.val < 344) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk5,
      partsPointChunk0, partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk43
    (vertex : Fin 481) (range : 344 ≤ vertex.val ∧ vertex.val < 352) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk5,
      partsPointChunk0, partsPointChunk1, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk44
    (vertex : Fin 481) (range : 352 ≤ vertex.val ∧ vertex.val < 360) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk5,
      partsPointChunk0, partsPointChunk1, partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk45
    (vertex : Fin 481) (range : 360 ≤ vertex.val ∧ vertex.val < 368) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk5,
      partsPointChunk1, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk46
    (vertex : Fin 481) (range : 368 ≤ vertex.val ∧ vertex.val < 376) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk5,
      partsPointChunk1, partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk47
    (vertex : Fin 481) (range : 376 ≤ vertex.val ∧ vertex.val < 384) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk5,
      partsPointChunk1, partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk48
    (vertex : Fin 481) (range : 384 ≤ vertex.val ∧ vertex.val < 392) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk6,
      partsPointChunk1, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk49
    (vertex : Fin 481) (range : 392 ≤ vertex.val ∧ vertex.val < 400) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk50
    (vertex : Fin 481) (range : 400 ≤ vertex.val ∧ vertex.val < 408) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk51
    (vertex : Fin 481) (range : 408 ≤ vertex.val ∧ vertex.val < 416) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk52
    (vertex : Fin 481) (range : 416 ≤ vertex.val ∧ vertex.val < 424) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk6,
      partsPointChunk2, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk53
    (vertex : Fin 481) (range : 424 ≤ vertex.val ∧ vertex.val < 432) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk6,
      partsPointChunk2, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk54
    (vertex : Fin 481) (range : 432 ≤ vertex.val ∧ vertex.val < 440) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk6,
      partsPointChunk2, partsPointChunk4, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk55
    (vertex : Fin 481) (range : 440 ≤ vertex.val ∧ vertex.val < 448) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk6,
      partsPointChunk0, partsPointChunk4, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk56
    (vertex : Fin 481) (range : 448 ≤ vertex.val ∧ vertex.val < 456) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk7,
      partsPointChunk0, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk57
    (vertex : Fin 481) (range : 456 ≤ vertex.val ∧ vertex.val < 464) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk7,
      partsPointChunk0, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk58
    (vertex : Fin 481) (range : 464 ≤ vertex.val ∧ vertex.val < 472) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk7,
      partsPointChunk0, partsPointChunk2, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk59
    (vertex : Fin 481) (range : 472 ≤ vertex.val ∧ vertex.val < 480) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk7,
      partsPointChunk2, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case4_chunk60
    (vertex : Fin 481) (range : 480 ≤ vertex.val ∧ vertex.val < 481) :
    PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation4, partsVertexPermutation4Chunk7,
      partsPointChunk2, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case4 :
    ∀ vertex, PartsPoint.IsTransform (4 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (4 : Fin 6) vertex)) := by
  intro vertex
  by_cases h0 : vertex.val < 8
  · exact partsPoint_permuteVertex_isTransform_case4_chunk0 vertex h0
  by_cases h1 : vertex.val < 16
  · exact partsPoint_permuteVertex_isTransform_case4_chunk1 vertex ⟨by omega, h1⟩
  by_cases h2 : vertex.val < 24
  · exact partsPoint_permuteVertex_isTransform_case4_chunk2 vertex ⟨by omega, h2⟩
  by_cases h3 : vertex.val < 32
  · exact partsPoint_permuteVertex_isTransform_case4_chunk3 vertex ⟨by omega, h3⟩
  by_cases h4 : vertex.val < 40
  · exact partsPoint_permuteVertex_isTransform_case4_chunk4 vertex ⟨by omega, h4⟩
  by_cases h5 : vertex.val < 48
  · exact partsPoint_permuteVertex_isTransform_case4_chunk5 vertex ⟨by omega, h5⟩
  by_cases h6 : vertex.val < 56
  · exact partsPoint_permuteVertex_isTransform_case4_chunk6 vertex ⟨by omega, h6⟩
  by_cases h7 : vertex.val < 64
  · exact partsPoint_permuteVertex_isTransform_case4_chunk7 vertex ⟨by omega, h7⟩
  by_cases h8 : vertex.val < 72
  · exact partsPoint_permuteVertex_isTransform_case4_chunk8 vertex ⟨by omega, h8⟩
  by_cases h9 : vertex.val < 80
  · exact partsPoint_permuteVertex_isTransform_case4_chunk9 vertex ⟨by omega, h9⟩
  by_cases h10 : vertex.val < 88
  · exact partsPoint_permuteVertex_isTransform_case4_chunk10 vertex ⟨by omega, h10⟩
  by_cases h11 : vertex.val < 96
  · exact partsPoint_permuteVertex_isTransform_case4_chunk11 vertex ⟨by omega, h11⟩
  by_cases h12 : vertex.val < 104
  · exact partsPoint_permuteVertex_isTransform_case4_chunk12 vertex ⟨by omega, h12⟩
  by_cases h13 : vertex.val < 112
  · exact partsPoint_permuteVertex_isTransform_case4_chunk13 vertex ⟨by omega, h13⟩
  by_cases h14 : vertex.val < 120
  · exact partsPoint_permuteVertex_isTransform_case4_chunk14 vertex ⟨by omega, h14⟩
  by_cases h15 : vertex.val < 128
  · exact partsPoint_permuteVertex_isTransform_case4_chunk15 vertex ⟨by omega, h15⟩
  by_cases h16 : vertex.val < 136
  · exact partsPoint_permuteVertex_isTransform_case4_chunk16 vertex ⟨by omega, h16⟩
  by_cases h17 : vertex.val < 144
  · exact partsPoint_permuteVertex_isTransform_case4_chunk17 vertex ⟨by omega, h17⟩
  by_cases h18 : vertex.val < 152
  · exact partsPoint_permuteVertex_isTransform_case4_chunk18 vertex ⟨by omega, h18⟩
  by_cases h19 : vertex.val < 160
  · exact partsPoint_permuteVertex_isTransform_case4_chunk19 vertex ⟨by omega, h19⟩
  by_cases h20 : vertex.val < 168
  · exact partsPoint_permuteVertex_isTransform_case4_chunk20 vertex ⟨by omega, h20⟩
  by_cases h21 : vertex.val < 176
  · exact partsPoint_permuteVertex_isTransform_case4_chunk21 vertex ⟨by omega, h21⟩
  by_cases h22 : vertex.val < 184
  · exact partsPoint_permuteVertex_isTransform_case4_chunk22 vertex ⟨by omega, h22⟩
  by_cases h23 : vertex.val < 192
  · exact partsPoint_permuteVertex_isTransform_case4_chunk23 vertex ⟨by omega, h23⟩
  by_cases h24 : vertex.val < 200
  · exact partsPoint_permuteVertex_isTransform_case4_chunk24 vertex ⟨by omega, h24⟩
  by_cases h25 : vertex.val < 208
  · exact partsPoint_permuteVertex_isTransform_case4_chunk25 vertex ⟨by omega, h25⟩
  by_cases h26 : vertex.val < 216
  · exact partsPoint_permuteVertex_isTransform_case4_chunk26 vertex ⟨by omega, h26⟩
  by_cases h27 : vertex.val < 224
  · exact partsPoint_permuteVertex_isTransform_case4_chunk27 vertex ⟨by omega, h27⟩
  by_cases h28 : vertex.val < 232
  · exact partsPoint_permuteVertex_isTransform_case4_chunk28 vertex ⟨by omega, h28⟩
  by_cases h29 : vertex.val < 240
  · exact partsPoint_permuteVertex_isTransform_case4_chunk29 vertex ⟨by omega, h29⟩
  by_cases h30 : vertex.val < 248
  · exact partsPoint_permuteVertex_isTransform_case4_chunk30 vertex ⟨by omega, h30⟩
  by_cases h31 : vertex.val < 256
  · exact partsPoint_permuteVertex_isTransform_case4_chunk31 vertex ⟨by omega, h31⟩
  by_cases h32 : vertex.val < 264
  · exact partsPoint_permuteVertex_isTransform_case4_chunk32 vertex ⟨by omega, h32⟩
  by_cases h33 : vertex.val < 272
  · exact partsPoint_permuteVertex_isTransform_case4_chunk33 vertex ⟨by omega, h33⟩
  by_cases h34 : vertex.val < 280
  · exact partsPoint_permuteVertex_isTransform_case4_chunk34 vertex ⟨by omega, h34⟩
  by_cases h35 : vertex.val < 288
  · exact partsPoint_permuteVertex_isTransform_case4_chunk35 vertex ⟨by omega, h35⟩
  by_cases h36 : vertex.val < 296
  · exact partsPoint_permuteVertex_isTransform_case4_chunk36 vertex ⟨by omega, h36⟩
  by_cases h37 : vertex.val < 304
  · exact partsPoint_permuteVertex_isTransform_case4_chunk37 vertex ⟨by omega, h37⟩
  by_cases h38 : vertex.val < 312
  · exact partsPoint_permuteVertex_isTransform_case4_chunk38 vertex ⟨by omega, h38⟩
  by_cases h39 : vertex.val < 320
  · exact partsPoint_permuteVertex_isTransform_case4_chunk39 vertex ⟨by omega, h39⟩
  by_cases h40 : vertex.val < 328
  · exact partsPoint_permuteVertex_isTransform_case4_chunk40 vertex ⟨by omega, h40⟩
  by_cases h41 : vertex.val < 336
  · exact partsPoint_permuteVertex_isTransform_case4_chunk41 vertex ⟨by omega, h41⟩
  by_cases h42 : vertex.val < 344
  · exact partsPoint_permuteVertex_isTransform_case4_chunk42 vertex ⟨by omega, h42⟩
  by_cases h43 : vertex.val < 352
  · exact partsPoint_permuteVertex_isTransform_case4_chunk43 vertex ⟨by omega, h43⟩
  by_cases h44 : vertex.val < 360
  · exact partsPoint_permuteVertex_isTransform_case4_chunk44 vertex ⟨by omega, h44⟩
  by_cases h45 : vertex.val < 368
  · exact partsPoint_permuteVertex_isTransform_case4_chunk45 vertex ⟨by omega, h45⟩
  by_cases h46 : vertex.val < 376
  · exact partsPoint_permuteVertex_isTransform_case4_chunk46 vertex ⟨by omega, h46⟩
  by_cases h47 : vertex.val < 384
  · exact partsPoint_permuteVertex_isTransform_case4_chunk47 vertex ⟨by omega, h47⟩
  by_cases h48 : vertex.val < 392
  · exact partsPoint_permuteVertex_isTransform_case4_chunk48 vertex ⟨by omega, h48⟩
  by_cases h49 : vertex.val < 400
  · exact partsPoint_permuteVertex_isTransform_case4_chunk49 vertex ⟨by omega, h49⟩
  by_cases h50 : vertex.val < 408
  · exact partsPoint_permuteVertex_isTransform_case4_chunk50 vertex ⟨by omega, h50⟩
  by_cases h51 : vertex.val < 416
  · exact partsPoint_permuteVertex_isTransform_case4_chunk51 vertex ⟨by omega, h51⟩
  by_cases h52 : vertex.val < 424
  · exact partsPoint_permuteVertex_isTransform_case4_chunk52 vertex ⟨by omega, h52⟩
  by_cases h53 : vertex.val < 432
  · exact partsPoint_permuteVertex_isTransform_case4_chunk53 vertex ⟨by omega, h53⟩
  by_cases h54 : vertex.val < 440
  · exact partsPoint_permuteVertex_isTransform_case4_chunk54 vertex ⟨by omega, h54⟩
  by_cases h55 : vertex.val < 448
  · exact partsPoint_permuteVertex_isTransform_case4_chunk55 vertex ⟨by omega, h55⟩
  by_cases h56 : vertex.val < 456
  · exact partsPoint_permuteVertex_isTransform_case4_chunk56 vertex ⟨by omega, h56⟩
  by_cases h57 : vertex.val < 464
  · exact partsPoint_permuteVertex_isTransform_case4_chunk57 vertex ⟨by omega, h57⟩
  by_cases h58 : vertex.val < 472
  · exact partsPoint_permuteVertex_isTransform_case4_chunk58 vertex ⟨by omega, h58⟩
  by_cases h59 : vertex.val < 480
  · exact partsPoint_permuteVertex_isTransform_case4_chunk59 vertex ⟨by omega, h59⟩
  exact partsPoint_permuteVertex_isTransform_case4_chunk60 vertex ⟨by omega, by omega⟩

private lemma partsPoint_permuteVertex_isTransform_case5_chunk0
    (vertex : Fin 481) (range : vertex.val < 8) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  interval_cases vertex
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk0,
      partsPointChunk0, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk1
    (vertex : Fin 481) (range : 8 ≤ vertex.val ∧ vertex.val < 16) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk0,
      partsPointChunk0, partsPointChunk3, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk2
    (vertex : Fin 481) (range : 16 ≤ vertex.val ∧ vertex.val < 24) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk0,
      partsPointChunk0, partsPointChunk6, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk3
    (vertex : Fin 481) (range : 24 ≤ vertex.val ∧ vertex.val < 32) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk0,
      partsPointChunk0, partsPointChunk6, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk4
    (vertex : Fin 481) (range : 32 ≤ vertex.val ∧ vertex.val < 40) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk0,
      partsPointChunk0, partsPointChunk2, partsPointChunk6, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk5
    (vertex : Fin 481) (range : 40 ≤ vertex.val ∧ vertex.val < 48) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk0,
      partsPointChunk0, partsPointChunk2, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk6
    (vertex : Fin 481) (range : 48 ≤ vertex.val ∧ vertex.val < 56) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk0,
      partsPointChunk0, partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk7
    (vertex : Fin 481) (range : 56 ≤ vertex.val ∧ vertex.val < 64) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk0,
      partsPointChunk0, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk8
    (vertex : Fin 481) (range : 64 ≤ vertex.val ∧ vertex.val < 72) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk1,
      partsPointChunk1, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk9
    (vertex : Fin 481) (range : 72 ≤ vertex.val ∧ vertex.val < 80) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk1,
      partsPointChunk1]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk10
    (vertex : Fin 481) (range : 80 ≤ vertex.val ∧ vertex.val < 88) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk1,
      partsPointChunk1, partsPointChunk5, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk11
    (vertex : Fin 481) (range : 88 ≤ vertex.val ∧ vertex.val < 96) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk1,
      partsPointChunk1, partsPointChunk5, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk12
    (vertex : Fin 481) (range : 96 ≤ vertex.val ∧ vertex.val < 104) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk1,
      partsPointChunk1, partsPointChunk3, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk13
    (vertex : Fin 481) (range : 104 ≤ vertex.val ∧ vertex.val < 112) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk1,
      partsPointChunk1, partsPointChunk3, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk14
    (vertex : Fin 481) (range : 112 ≤ vertex.val ∧ vertex.val < 120) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk1,
      partsPointChunk1, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk15
    (vertex : Fin 481) (range : 120 ≤ vertex.val ∧ vertex.val < 128) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk1,
      partsPointChunk1, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk16
    (vertex : Fin 481) (range : 128 ≤ vertex.val ∧ vertex.val < 136) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk2,
      partsPointChunk2, partsPointChunk4, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk17
    (vertex : Fin 481) (range : 136 ≤ vertex.val ∧ vertex.val < 144) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk2,
      partsPointChunk2, partsPointChunk4, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk18
    (vertex : Fin 481) (range : 144 ≤ vertex.val ∧ vertex.val < 152) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk2,
      partsPointChunk2, partsPointChunk4, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk19
    (vertex : Fin 481) (range : 152 ≤ vertex.val ∧ vertex.val < 160) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk2,
      partsPointChunk2, partsPointChunk4, partsPointChunk5, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk20
    (vertex : Fin 481) (range : 160 ≤ vertex.val ∧ vertex.val < 168) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk2,
      partsPointChunk2, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk21
    (vertex : Fin 481) (range : 168 ≤ vertex.val ∧ vertex.val < 176) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk2,
      partsPointChunk2, partsPointChunk6, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk22
    (vertex : Fin 481) (range : 176 ≤ vertex.val ∧ vertex.val < 184) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk2,
      partsPointChunk0, partsPointChunk2, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk23
    (vertex : Fin 481) (range : 184 ≤ vertex.val ∧ vertex.val < 192) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk2,
      partsPointChunk0, partsPointChunk2]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk24
    (vertex : Fin 481) (range : 192 ≤ vertex.val ∧ vertex.val < 200) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk3,
      partsPointChunk0, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk25
    (vertex : Fin 481) (range : 200 ≤ vertex.val ∧ vertex.val < 208) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk3,
      partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk26
    (vertex : Fin 481) (range : 208 ≤ vertex.val ∧ vertex.val < 216) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk3,
      partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk27
    (vertex : Fin 481) (range : 216 ≤ vertex.val ∧ vertex.val < 224) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk3,
      partsPointChunk1, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk28
    (vertex : Fin 481) (range : 224 ≤ vertex.val ∧ vertex.val < 232) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk3,
      partsPointChunk1, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk29
    (vertex : Fin 481) (range : 232 ≤ vertex.val ∧ vertex.val < 240) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk3,
      partsPointChunk0, partsPointChunk1, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk30
    (vertex : Fin 481) (range : 240 ≤ vertex.val ∧ vertex.val < 248) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk3,
      partsPointChunk0, partsPointChunk3]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk31
    (vertex : Fin 481) (range : 248 ≤ vertex.val ∧ vertex.val < 256) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk3,
      partsPointChunk3, partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk32
    (vertex : Fin 481) (range : 256 ≤ vertex.val ∧ vertex.val < 264) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk4,
      partsPointChunk3, partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk33
    (vertex : Fin 481) (range : 264 ≤ vertex.val ∧ vertex.val < 272) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk4,
      partsPointChunk4, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk34
    (vertex : Fin 481) (range : 272 ≤ vertex.val ∧ vertex.val < 280) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk4,
      partsPointChunk4, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk35
    (vertex : Fin 481) (range : 280 ≤ vertex.val ∧ vertex.val < 288) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk36
    (vertex : Fin 481) (range : 288 ≤ vertex.val ∧ vertex.val < 296) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk37
    (vertex : Fin 481) (range : 296 ≤ vertex.val ∧ vertex.val < 304) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk38
    (vertex : Fin 481) (range : 304 ≤ vertex.val ∧ vertex.val < 312) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk4,
      partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk39
    (vertex : Fin 481) (range : 312 ≤ vertex.val ∧ vertex.val < 320) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk4,
      partsPointChunk2, partsPointChunk4]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk40
    (vertex : Fin 481) (range : 320 ≤ vertex.val ∧ vertex.val < 328) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk5,
      partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk41
    (vertex : Fin 481) (range : 328 ≤ vertex.val ∧ vertex.val < 336) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk5,
      partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk42
    (vertex : Fin 481) (range : 336 ≤ vertex.val ∧ vertex.val < 344) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk5,
      partsPointChunk0, partsPointChunk1, partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk43
    (vertex : Fin 481) (range : 344 ≤ vertex.val ∧ vertex.val < 352) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk5,
      partsPointChunk0, partsPointChunk1, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk44
    (vertex : Fin 481) (range : 352 ≤ vertex.val ∧ vertex.val < 360) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk5,
      partsPointChunk0, partsPointChunk1, partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk45
    (vertex : Fin 481) (range : 360 ≤ vertex.val ∧ vertex.val < 368) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk5,
      partsPointChunk1, partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk46
    (vertex : Fin 481) (range : 368 ≤ vertex.val ∧ vertex.val < 376) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk5,
      partsPointChunk1, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk47
    (vertex : Fin 481) (range : 376 ≤ vertex.val ∧ vertex.val < 384) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk5,
      partsPointChunk1, partsPointChunk2, partsPointChunk5]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk48
    (vertex : Fin 481) (range : 384 ≤ vertex.val ∧ vertex.val < 392) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk6,
      partsPointChunk1, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk49
    (vertex : Fin 481) (range : 392 ≤ vertex.val ∧ vertex.val < 400) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk50
    (vertex : Fin 481) (range : 400 ≤ vertex.val ∧ vertex.val < 408) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk51
    (vertex : Fin 481) (range : 408 ≤ vertex.val ∧ vertex.val < 416) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk6,
      partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk52
    (vertex : Fin 481) (range : 416 ≤ vertex.val ∧ vertex.val < 424) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk6,
      partsPointChunk2, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk53
    (vertex : Fin 481) (range : 424 ≤ vertex.val ∧ vertex.val < 432) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk6,
      partsPointChunk2, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk54
    (vertex : Fin 481) (range : 432 ≤ vertex.val ∧ vertex.val < 440) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk6,
      partsPointChunk2, partsPointChunk4, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk55
    (vertex : Fin 481) (range : 440 ≤ vertex.val ∧ vertex.val < 448) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk6,
      partsPointChunk0, partsPointChunk4, partsPointChunk6]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk56
    (vertex : Fin 481) (range : 448 ≤ vertex.val ∧ vertex.val < 456) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk7,
      partsPointChunk0, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk57
    (vertex : Fin 481) (range : 456 ≤ vertex.val ∧ vertex.val < 464) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk7,
      partsPointChunk0, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk58
    (vertex : Fin 481) (range : 464 ≤ vertex.val ∧ vertex.val < 472) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk7,
      partsPointChunk0, partsPointChunk2, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk59
    (vertex : Fin 481) (range : 472 ≤ vertex.val ∧ vertex.val < 480) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk7,
      partsPointChunk2, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case5_chunk60
    (vertex : Fin 481) (range : 480 ≤ vertex.val ∧ vertex.val < 481) :
    PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  rcases vertex with ⟨vertex, bound⟩
  rcases range with ⟨lower, upper⟩
  interval_cases vertex using lower, upper
  all_goals
    have hbound : bound = (by decide) := Subsingleton.elim _ _
    rw [hbound]
    norm_num [PartsPoint.IsTransform, partsPoint, partsPermuteVertex,
      partsVertexPermutation5, partsVertexPermutation5Chunk7,
      partsPointChunk2, partsPointChunk7]

private lemma partsPoint_permuteVertex_isTransform_case5 :
    ∀ vertex, PartsPoint.IsTransform (5 : Fin 6) (partsPoint vertex)
      (partsPoint (partsPermuteVertex (5 : Fin 6) vertex)) := by
  intro vertex
  by_cases h0 : vertex.val < 8
  · exact partsPoint_permuteVertex_isTransform_case5_chunk0 vertex h0
  by_cases h1 : vertex.val < 16
  · exact partsPoint_permuteVertex_isTransform_case5_chunk1 vertex ⟨by omega, h1⟩
  by_cases h2 : vertex.val < 24
  · exact partsPoint_permuteVertex_isTransform_case5_chunk2 vertex ⟨by omega, h2⟩
  by_cases h3 : vertex.val < 32
  · exact partsPoint_permuteVertex_isTransform_case5_chunk3 vertex ⟨by omega, h3⟩
  by_cases h4 : vertex.val < 40
  · exact partsPoint_permuteVertex_isTransform_case5_chunk4 vertex ⟨by omega, h4⟩
  by_cases h5 : vertex.val < 48
  · exact partsPoint_permuteVertex_isTransform_case5_chunk5 vertex ⟨by omega, h5⟩
  by_cases h6 : vertex.val < 56
  · exact partsPoint_permuteVertex_isTransform_case5_chunk6 vertex ⟨by omega, h6⟩
  by_cases h7 : vertex.val < 64
  · exact partsPoint_permuteVertex_isTransform_case5_chunk7 vertex ⟨by omega, h7⟩
  by_cases h8 : vertex.val < 72
  · exact partsPoint_permuteVertex_isTransform_case5_chunk8 vertex ⟨by omega, h8⟩
  by_cases h9 : vertex.val < 80
  · exact partsPoint_permuteVertex_isTransform_case5_chunk9 vertex ⟨by omega, h9⟩
  by_cases h10 : vertex.val < 88
  · exact partsPoint_permuteVertex_isTransform_case5_chunk10 vertex ⟨by omega, h10⟩
  by_cases h11 : vertex.val < 96
  · exact partsPoint_permuteVertex_isTransform_case5_chunk11 vertex ⟨by omega, h11⟩
  by_cases h12 : vertex.val < 104
  · exact partsPoint_permuteVertex_isTransform_case5_chunk12 vertex ⟨by omega, h12⟩
  by_cases h13 : vertex.val < 112
  · exact partsPoint_permuteVertex_isTransform_case5_chunk13 vertex ⟨by omega, h13⟩
  by_cases h14 : vertex.val < 120
  · exact partsPoint_permuteVertex_isTransform_case5_chunk14 vertex ⟨by omega, h14⟩
  by_cases h15 : vertex.val < 128
  · exact partsPoint_permuteVertex_isTransform_case5_chunk15 vertex ⟨by omega, h15⟩
  by_cases h16 : vertex.val < 136
  · exact partsPoint_permuteVertex_isTransform_case5_chunk16 vertex ⟨by omega, h16⟩
  by_cases h17 : vertex.val < 144
  · exact partsPoint_permuteVertex_isTransform_case5_chunk17 vertex ⟨by omega, h17⟩
  by_cases h18 : vertex.val < 152
  · exact partsPoint_permuteVertex_isTransform_case5_chunk18 vertex ⟨by omega, h18⟩
  by_cases h19 : vertex.val < 160
  · exact partsPoint_permuteVertex_isTransform_case5_chunk19 vertex ⟨by omega, h19⟩
  by_cases h20 : vertex.val < 168
  · exact partsPoint_permuteVertex_isTransform_case5_chunk20 vertex ⟨by omega, h20⟩
  by_cases h21 : vertex.val < 176
  · exact partsPoint_permuteVertex_isTransform_case5_chunk21 vertex ⟨by omega, h21⟩
  by_cases h22 : vertex.val < 184
  · exact partsPoint_permuteVertex_isTransform_case5_chunk22 vertex ⟨by omega, h22⟩
  by_cases h23 : vertex.val < 192
  · exact partsPoint_permuteVertex_isTransform_case5_chunk23 vertex ⟨by omega, h23⟩
  by_cases h24 : vertex.val < 200
  · exact partsPoint_permuteVertex_isTransform_case5_chunk24 vertex ⟨by omega, h24⟩
  by_cases h25 : vertex.val < 208
  · exact partsPoint_permuteVertex_isTransform_case5_chunk25 vertex ⟨by omega, h25⟩
  by_cases h26 : vertex.val < 216
  · exact partsPoint_permuteVertex_isTransform_case5_chunk26 vertex ⟨by omega, h26⟩
  by_cases h27 : vertex.val < 224
  · exact partsPoint_permuteVertex_isTransform_case5_chunk27 vertex ⟨by omega, h27⟩
  by_cases h28 : vertex.val < 232
  · exact partsPoint_permuteVertex_isTransform_case5_chunk28 vertex ⟨by omega, h28⟩
  by_cases h29 : vertex.val < 240
  · exact partsPoint_permuteVertex_isTransform_case5_chunk29 vertex ⟨by omega, h29⟩
  by_cases h30 : vertex.val < 248
  · exact partsPoint_permuteVertex_isTransform_case5_chunk30 vertex ⟨by omega, h30⟩
  by_cases h31 : vertex.val < 256
  · exact partsPoint_permuteVertex_isTransform_case5_chunk31 vertex ⟨by omega, h31⟩
  by_cases h32 : vertex.val < 264
  · exact partsPoint_permuteVertex_isTransform_case5_chunk32 vertex ⟨by omega, h32⟩
  by_cases h33 : vertex.val < 272
  · exact partsPoint_permuteVertex_isTransform_case5_chunk33 vertex ⟨by omega, h33⟩
  by_cases h34 : vertex.val < 280
  · exact partsPoint_permuteVertex_isTransform_case5_chunk34 vertex ⟨by omega, h34⟩
  by_cases h35 : vertex.val < 288
  · exact partsPoint_permuteVertex_isTransform_case5_chunk35 vertex ⟨by omega, h35⟩
  by_cases h36 : vertex.val < 296
  · exact partsPoint_permuteVertex_isTransform_case5_chunk36 vertex ⟨by omega, h36⟩
  by_cases h37 : vertex.val < 304
  · exact partsPoint_permuteVertex_isTransform_case5_chunk37 vertex ⟨by omega, h37⟩
  by_cases h38 : vertex.val < 312
  · exact partsPoint_permuteVertex_isTransform_case5_chunk38 vertex ⟨by omega, h38⟩
  by_cases h39 : vertex.val < 320
  · exact partsPoint_permuteVertex_isTransform_case5_chunk39 vertex ⟨by omega, h39⟩
  by_cases h40 : vertex.val < 328
  · exact partsPoint_permuteVertex_isTransform_case5_chunk40 vertex ⟨by omega, h40⟩
  by_cases h41 : vertex.val < 336
  · exact partsPoint_permuteVertex_isTransform_case5_chunk41 vertex ⟨by omega, h41⟩
  by_cases h42 : vertex.val < 344
  · exact partsPoint_permuteVertex_isTransform_case5_chunk42 vertex ⟨by omega, h42⟩
  by_cases h43 : vertex.val < 352
  · exact partsPoint_permuteVertex_isTransform_case5_chunk43 vertex ⟨by omega, h43⟩
  by_cases h44 : vertex.val < 360
  · exact partsPoint_permuteVertex_isTransform_case5_chunk44 vertex ⟨by omega, h44⟩
  by_cases h45 : vertex.val < 368
  · exact partsPoint_permuteVertex_isTransform_case5_chunk45 vertex ⟨by omega, h45⟩
  by_cases h46 : vertex.val < 376
  · exact partsPoint_permuteVertex_isTransform_case5_chunk46 vertex ⟨by omega, h46⟩
  by_cases h47 : vertex.val < 384
  · exact partsPoint_permuteVertex_isTransform_case5_chunk47 vertex ⟨by omega, h47⟩
  by_cases h48 : vertex.val < 392
  · exact partsPoint_permuteVertex_isTransform_case5_chunk48 vertex ⟨by omega, h48⟩
  by_cases h49 : vertex.val < 400
  · exact partsPoint_permuteVertex_isTransform_case5_chunk49 vertex ⟨by omega, h49⟩
  by_cases h50 : vertex.val < 408
  · exact partsPoint_permuteVertex_isTransform_case5_chunk50 vertex ⟨by omega, h50⟩
  by_cases h51 : vertex.val < 416
  · exact partsPoint_permuteVertex_isTransform_case5_chunk51 vertex ⟨by omega, h51⟩
  by_cases h52 : vertex.val < 424
  · exact partsPoint_permuteVertex_isTransform_case5_chunk52 vertex ⟨by omega, h52⟩
  by_cases h53 : vertex.val < 432
  · exact partsPoint_permuteVertex_isTransform_case5_chunk53 vertex ⟨by omega, h53⟩
  by_cases h54 : vertex.val < 440
  · exact partsPoint_permuteVertex_isTransform_case5_chunk54 vertex ⟨by omega, h54⟩
  by_cases h55 : vertex.val < 448
  · exact partsPoint_permuteVertex_isTransform_case5_chunk55 vertex ⟨by omega, h55⟩
  by_cases h56 : vertex.val < 456
  · exact partsPoint_permuteVertex_isTransform_case5_chunk56 vertex ⟨by omega, h56⟩
  by_cases h57 : vertex.val < 464
  · exact partsPoint_permuteVertex_isTransform_case5_chunk57 vertex ⟨by omega, h57⟩
  by_cases h58 : vertex.val < 472
  · exact partsPoint_permuteVertex_isTransform_case5_chunk58 vertex ⟨by omega, h58⟩
  by_cases h59 : vertex.val < 480
  · exact partsPoint_permuteVertex_isTransform_case5_chunk59 vertex ⟨by omega, h59⟩
  exact partsPoint_permuteVertex_isTransform_case5_chunk60 vertex ⟨by omega, by omega⟩

private lemma partsPoint_permuteVertex_isTransform (symmetry : Fin 6) :
    ∀ vertex, PartsPoint.IsTransform symmetry (partsPoint vertex)
      (partsPoint (partsPermuteVertex symmetry vertex)) := by
  fin_cases symmetry
  · simpa using partsPoint_permuteVertex_isTransform_case0
  · simpa using partsPoint_permuteVertex_isTransform_case1
  · simpa using partsPoint_permuteVertex_isTransform_case2
  · simpa using partsPoint_permuteVertex_isTransform_case3
  · simpa using partsPoint_permuteVertex_isTransform_case4
  · simpa using partsPoint_permuteVertex_isTransform_case5

private lemma partsAdjacent_permuteVertex (symmetry : Fin 6) (left right : Fin 481) :
    partsAdjacent (partsPermuteVertex symmetry left) (partsPermuteVertex symmetry right) =
      partsAdjacent left right := by
  exact PartsPoint.IsTransform.isUnit_eq
    ((partsPoint_permuteVertex_isTransform symmetry left).sub
      (partsPoint_permuteVertex_isTransform symmetry right))

private lemma partsBlocksB_transform (symmetry : Fin 6) (swap : Bool)
    (path : List PartsAssignment) (vertex : Fin 481) (color : Fin 4) :
    PartsBlocksB (partsTransformPath symmetry swap path)
      (partsPermuteVertex symmetry vertex) (partsTransformColor swap color) =
        PartsBlocksB path vertex color := by
  induction path with
  | nil => rfl
  | cons assignment path induction =>
      simp only [partsTransformPath]
      change
        ((partsTransformColor swap assignment.color == partsTransformColor swap color) &&
            partsAdjacent (partsPermuteVertex symmetry vertex)
              (partsPermuteVertex symmetry assignment.vertex) ||
          PartsBlocksB (partsTransformPath symmetry swap path)
            (partsPermuteVertex symmetry vertex) (partsTransformColor swap color)) =
          (assignment.color == color && partsAdjacent vertex assignment.vertex ||
            PartsBlocksB path vertex color)
      rw [partsTransformColor_beq, partsAdjacent_permuteVertex, induction]

private lemma partsForcedB_transform (symmetry : Fin 6) (swap : Bool)
    (path : List PartsAssignment) (assignment : PartsAssignment) :
    PartsForcedB (partsTransformPath symmetry swap path)
      (partsTransformAssignment symmetry swap assignment) =
        PartsForcedB path assignment := by
  unfold PartsForcedB
  rw [← partsColors_all_transformColor swap]
  apply congrArg (List.all partsColors)
  funext color
  simp only [partsTransformAssignment, partsTransformColor_beq,
    partsBlocksB_transform]

private lemma partsRunStemB_transform (symmetry : Fin 6) (swap : Bool) :
    ∀ stem path,
      PartsRunStemB (partsTransformPath symmetry swap stem)
          (partsTransformPath symmetry swap path) =
        Option.map (partsTransformPath symmetry swap) (PartsRunStemB stem path) := by
  intro stem
  induction stem with
  | nil => intro path; rfl
  | cons assignment stem induction =>
      intro path
      simp only [partsTransformPath, PartsRunStemB]
      rw [partsForcedB_transform]
      split
      · exact induction (assignment :: path)
      · rfl

/-- Select one of the 36 normalized root-orbit certificates. -/
@[expose] def partsBaseCertificate (base : Fin 36) : PartsCertificate :=
  match base.val with
  | 0 => partsBaseCertificate0
  | 1 => partsBaseCertificate1
  | 2 => partsBaseCertificate2
  | 3 => partsBaseCertificate3
  | 4 => partsBaseCertificate4
  | 5 => partsBaseCertificate5
  | 6 => partsBaseCertificate6
  | 7 => partsBaseCertificate7
  | 8 => partsBaseCertificate8
  | 9 => partsBaseCertificate9
  | 10 => partsBaseCertificate10
  | 11 => partsBaseCertificate11
  | 12 => partsBaseCertificate12
  | 13 => partsBaseCertificate13
  | 14 => partsBaseCertificate14
  | 15 => partsBaseCertificate15
  | 16 => partsBaseCertificate16
  | 17 => partsBaseCertificate17
  | 18 => partsBaseCertificate18
  | 19 => partsBaseCertificate19
  | 20 => partsBaseCertificate20
  | 21 => partsBaseCertificate21
  | 22 => partsBaseCertificate22
  | 23 => partsBaseCertificate23
  | 24 => partsBaseCertificate24
  | 25 => partsBaseCertificate25
  | 26 => partsBaseCertificate26
  | 27 => partsBaseCertificate27
  | 28 => partsBaseCertificate28
  | 29 => partsBaseCertificate29
  | 30 => partsBaseCertificate30
  | 31 => partsBaseCertificate31
  | 32 => partsBaseCertificate32
  | 33 => partsBaseCertificate33
  | 34 => partsBaseCertificate34
  | 35 => partsBaseCertificate35
  | _ => ⟨[], 0, #[]⟩

/-- Executable checker for a symmetry/color variant of a stored base tree. -/
def PartsVerifiesVariantNodeB (symmetry : Fin 6) (swap : Bool)
    (nodes : Array (Array PartsTreeNode)) : Nat → List PartsAssignment → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, path, index =>
      match partsTreeNodeAt nodes index with
      | none => false
      | some node =>
          match PartsRunStemB (partsTransformPath symmetry swap node.stem) path with
          | none => false
          | some extended =>
              let vertex := partsPermuteVertex symmetry node.vertex
              partsColors.all fun color =>
                PartsBlocksB extended vertex color ||
                  match node.child
                      (if swap then partsSwapMiddleColor color else color) with
                  | none => false
                  | some child =>
                      PartsVerifiesVariantNodeB symmetry swap nodes fuel
                        (⟨vertex, color⟩ :: extended) child

private lemma partsVerifiesVariantNodeB_transform (symmetry : Fin 6) (swap : Bool)
    (nodes : Array (Array PartsTreeNode)) :
    ∀ fuel path index,
      PartsVerifiesVariantNodeB symmetry swap nodes fuel
          (partsTransformPath symmetry swap path) index =
        PartsVerifiesNodeB nodes fuel path index := by
  intro fuel
  induction fuel with
  | zero => intro path index; rfl
  | succ fuel induction =>
      intro path index
      cases hnode : partsTreeNodeAt nodes index with
      | none => simp [PartsVerifiesVariantNodeB, PartsVerifiesNodeB, hnode]
      | some node =>
        simp only [PartsVerifiesVariantNodeB, PartsVerifiesNodeB, hnode]
        rw [partsRunStemB_transform]
        cases hrun : PartsRunStemB node.stem path with
        | none => simp
        | some extended =>
          simp only [Option.map_some]
          let variantPredicate : Fin 4 → Bool := fun color =>
            PartsBlocksB (partsTransformPath symmetry swap extended)
                (partsPermuteVertex symmetry node.vertex) color ||
              match node.child (partsTransformColor swap color) with
              | none => false
              | some child =>
                  PartsVerifiesVariantNodeB symmetry swap nodes fuel
                    (⟨partsPermuteVertex symmetry node.vertex, color⟩ ::
                      partsTransformPath symmetry swap extended) child
          change partsColors.all variantPredicate = _
          calc
            partsColors.all variantPredicate =
                partsColors.all fun color =>
                  variantPredicate (partsTransformColor swap color) :=
              (partsColors_all_transformColor swap variantPredicate).symm
            _ = partsColors.all fun color =>
                PartsBlocksB extended node.vertex color ||
                  match node.child color with
                  | none => false
                  | some child =>
                      PartsVerifiesNodeB nodes fuel
                        (⟨node.vertex, color⟩ :: extended) child := by
              apply congrArg (List.all partsColors)
              funext color
              cases hchild : node.child color with
              | none =>
                simp [variantPredicate, hchild, partsBlocksB_transform,
                  partsTransformColor_involutive]
              | some child =>
                have hrecursive :
                    PartsVerifiesVariantNodeB symmetry swap nodes fuel
                        (⟨partsPermuteVertex symmetry node.vertex,
                            partsTransformColor swap color⟩ ::
                          partsTransformPath symmetry swap extended) child =
                      PartsVerifiesNodeB nodes fuel
                        (⟨node.vertex, color⟩ :: extended) child := by
                  simpa only [partsTransformPath, partsTransformAssignment] using
                    induction (⟨node.vertex, color⟩ :: extended) child
                simp [variantPredicate, hchild, hrecursive, partsBlocksB_transform,
                  partsTransformColor_involutive]

/-- One of the 432 symmetry-expanded certificates passes the checker. -/
@[expose] def PartsCertificateVariantVerifies (base : Fin 36) (symmetry : Fin 6)
    (swap : Bool) : Prop :=
  let certificate := partsBaseCertificate base
  PartsVerifiesVariantNodeB symmetry swap certificate.nodes
    (certificate.nodeCount + 1)
    (partsTransformPath symmetry swap certificate.roots) 0 = true

private lemma partsCertificateVariantVerifies_of_base
    (base : Fin 36) (symmetry : Fin 6) (swap : Bool)
    (verified : (partsBaseCertificate base).Verifies) :
    PartsCertificateVariantVerifies base symmetry swap := by
  unfold PartsCertificate.Verifies at verified
  unfold PartsCertificateVariantVerifies
  dsimp only
  rw [partsVerifiesVariantNodeB_transform]
  exact verified

private theorem partsBaseCertificate0_verify :
    (partsBaseCertificate 0).Verifies := by decide +kernel

private theorem partsBaseCertificate1_verify :
    (partsBaseCertificate 1).Verifies := by decide +kernel

private theorem partsBaseCertificate2_verify :
    (partsBaseCertificate 2).Verifies := by decide +kernel

private theorem partsBaseCertificate3_verify :
    (partsBaseCertificate 3).Verifies := by decide +kernel

private theorem partsBaseCertificate4_verify :
    (partsBaseCertificate 4).Verifies := by decide +kernel

private theorem partsBaseCertificate5_verify :
    (partsBaseCertificate 5).Verifies := by decide +kernel

private theorem partsBaseCertificate6_verify :
    (partsBaseCertificate 6).Verifies := by decide +kernel

private theorem partsBaseCertificate7_verify :
    (partsBaseCertificate 7).Verifies := by decide +kernel

private theorem partsBaseCertificate8_verify :
    (partsBaseCertificate 8).Verifies := by decide +kernel

private theorem partsBaseCertificate9_verify :
    (partsBaseCertificate 9).Verifies := by decide +kernel

private theorem partsBaseCertificate10_verify :
    (partsBaseCertificate 10).Verifies := by decide +kernel

private theorem partsBaseCertificate11_verify :
    (partsBaseCertificate 11).Verifies := by decide +kernel

private theorem partsBaseCertificate12_verify :
    (partsBaseCertificate 12).Verifies := by decide +kernel

private theorem partsBaseCertificate13_verify :
    (partsBaseCertificate 13).Verifies := by decide +kernel

private theorem partsBaseCertificate14_verify :
    (partsBaseCertificate 14).Verifies := by decide +kernel

private theorem partsBaseCertificate15_verify :
    (partsBaseCertificate 15).Verifies := by decide +kernel

private theorem partsBaseCertificate16_verify :
    (partsBaseCertificate 16).Verifies := by decide +kernel

private theorem partsBaseCertificate17_verify :
    (partsBaseCertificate 17).Verifies := by decide +kernel

private theorem partsBaseCertificate18_verify :
    (partsBaseCertificate 18).Verifies := by decide +kernel

private theorem partsBaseCertificate19_verify :
    (partsBaseCertificate 19).Verifies := by decide +kernel

private theorem partsBaseCertificate20_verify :
    (partsBaseCertificate 20).Verifies := by decide +kernel

private theorem partsBaseCertificate21_verify :
    (partsBaseCertificate 21).Verifies := by decide +kernel

private theorem partsBaseCertificate22_verify :
    (partsBaseCertificate 22).Verifies := by decide +kernel

private theorem partsBaseCertificate23_verify :
    (partsBaseCertificate 23).Verifies := by decide +kernel

private theorem partsBaseCertificate24_verify :
    (partsBaseCertificate 24).Verifies := by decide +kernel

private theorem partsBaseCertificate25_verify :
    (partsBaseCertificate 25).Verifies := by decide +kernel

private theorem partsBaseCertificate26_verify :
    (partsBaseCertificate 26).Verifies := by decide +kernel

private theorem partsBaseCertificate27_verify :
    (partsBaseCertificate 27).Verifies := by decide +kernel

private theorem partsBaseCertificate28_verify :
    (partsBaseCertificate 28).Verifies := by decide +kernel

private theorem partsBaseCertificate29_verify :
    (partsBaseCertificate 29).Verifies := by decide +kernel

private theorem partsBaseCertificate30_verify :
    (partsBaseCertificate 30).Verifies := by decide +kernel

private theorem partsBaseCertificate31_verify :
    (partsBaseCertificate 31).Verifies := by decide +kernel

private theorem partsBaseCertificate32_verify :
    (partsBaseCertificate 32).Verifies := by decide +kernel

private theorem partsBaseCertificate33_verify :
    (partsBaseCertificate 33).Verifies := by decide +kernel

private theorem partsBaseCertificate34_verify :
    (partsBaseCertificate 34).Verifies := by decide +kernel

private theorem partsBaseCertificate35_verify :
    (partsBaseCertificate 35).Verifies := by decide +kernel

/-- Every stored base tree passes the checker before applying root symmetries. -/
theorem partsBaseCertificate_verifies (base : Fin 36) :
    (partsBaseCertificate base).Verifies := by
  fin_cases base
  · exact partsBaseCertificate0_verify
  · exact partsBaseCertificate1_verify
  · exact partsBaseCertificate2_verify
  · exact partsBaseCertificate3_verify
  · exact partsBaseCertificate4_verify
  · exact partsBaseCertificate5_verify
  · exact partsBaseCertificate6_verify
  · exact partsBaseCertificate7_verify
  · exact partsBaseCertificate8_verify
  · exact partsBaseCertificate9_verify
  · exact partsBaseCertificate10_verify
  · exact partsBaseCertificate11_verify
  · exact partsBaseCertificate12_verify
  · exact partsBaseCertificate13_verify
  · exact partsBaseCertificate14_verify
  · exact partsBaseCertificate15_verify
  · exact partsBaseCertificate16_verify
  · exact partsBaseCertificate17_verify
  · exact partsBaseCertificate18_verify
  · exact partsBaseCertificate19_verify
  · exact partsBaseCertificate20_verify
  · exact partsBaseCertificate21_verify
  · exact partsBaseCertificate22_verify
  · exact partsBaseCertificate23_verify
  · exact partsBaseCertificate24_verify
  · exact partsBaseCertificate25_verify
  · exact partsBaseCertificate26_verify
  · exact partsBaseCertificate27_verify
  · exact partsBaseCertificate28_verify
  · exact partsBaseCertificate29_verify
  · exact partsBaseCertificate30_verify
  · exact partsBaseCertificate31_verify
  · exact partsBaseCertificate32_verify
  · exact partsBaseCertificate33_verify
  · exact partsBaseCertificate34_verify
  · exact partsBaseCertificate35_verify

private theorem partsCertificateVariant_verifies_core
    (base : Fin 36) (symmetry : Fin 6) (swap : Bool) :
    PartsCertificateVariantVerifies base symmetry swap :=
  partsCertificateVariantVerifies_of_base base symmetry swap
    (partsBaseCertificate_verifies base)

instance (base : Fin 36) (symmetry : Fin 6) (swap : Bool) :
    Decidable (PartsCertificateVariantVerifies base symmetry swap) := by
  unfold PartsCertificateVariantVerifies
  infer_instance

lemma partsVerifiesVariantNodeB_unsat {symmetry : Fin 6} {swap : Bool}
    {nodes : Array (Array PartsTreeNode)} {coloring : Fin 481 → Fin 4}
    (hproper : PartsProper coloring) :
    ∀ {fuel path index},
      PartsVerifiesVariantNodeB symmetry swap nodes fuel path index = true →
      PartsExtends coloring path → False := by
  intro fuel
  induction fuel with
  | zero =>
      intro path index hverify _
      simp [PartsVerifiesVariantNodeB] at hverify
  | succ fuel ih =>
      intro path index hverify hextends
      simp only [PartsVerifiesVariantNodeB] at hverify
      split at hverify
      · contradiction
      · rename_i node hnode
        split at hverify
        · contradiction
        · rename_i extended hrun
          have hextended := partsRunStemB_sound hproper hrun hextends
          rw [List.all_eq_true] at hverify
          let vertex := partsPermuteVertex symmetry node.vertex
          have hcolor := hverify (coloring vertex) (mem_partsColors (coloring vertex))
          rw [Bool.or_eq_true] at hcolor
          rcases hcolor with hblocked | hnext
          · exact (not_partsBlocks_of_proper hproper extended hextended vertex)
              (partsBlocksB_eq_true.mp hblocked)
          · simp only [PartsTreeNode.child] at hnext
            split at hnext
            · contradiction
            · rename_i child hchild
              apply ih hnext
              intro assignment hin
              simp only [List.mem_cons] at hin
              rcases hin with rfl | hin
              · rfl
              · exact hextended assignment hin

/-- Soundness of any checked symmetry-expanded Parts tree. -/
theorem partsCertificateVariant_not_colorable {base : Fin 36}
    {symmetry : Fin 6} {swap : Bool}
    (hverify : PartsCertificateVariantVerifies base symmetry swap)
    {coloring : Fin 481 → Fin 4} (hproper : PartsProper coloring)
    (hroots : PartsExtends coloring
      (partsTransformPath symmetry swap (partsBaseCertificate base).roots)) : False := by
  exact partsVerifiesVariantNodeB_unsat hproper hverify hroots

theorem partsCertificateVariants0_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 0 symmetry swap := by
  exact partsCertificateVariant_verifies_core 0

theorem partsCertificateVariant1_0_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 1 0 swap := by
  exact partsCertificateVariant_verifies_core 1 0

theorem partsCertificateVariant1_1_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 1 1 swap := by
  exact partsCertificateVariant_verifies_core 1 1

theorem partsCertificateVariant1_2_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 1 2 swap := by
  exact partsCertificateVariant_verifies_core 1 2

theorem partsCertificateVariant1_3_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 1 3 swap := by
  exact partsCertificateVariant_verifies_core 1 3

theorem partsCertificateVariant1_4_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 1 4 swap := by
  exact partsCertificateVariant_verifies_core 1 4

theorem partsCertificateVariant1_5_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 1 5 swap := by
  exact partsCertificateVariant_verifies_core 1 5

theorem partsCertificateVariants1_verify (symmetry : Fin 6) (swap : Bool) :
    PartsCertificateVariantVerifies 1 symmetry swap := by
  exact partsCertificateVariant_verifies_core 1 symmetry swap

theorem partsCertificateVariants2_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 2 symmetry swap := by
  exact partsCertificateVariant_verifies_core 2

theorem partsCertificateVariants3_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 3 symmetry swap := by
  exact partsCertificateVariant_verifies_core 3

theorem partsCertificateVariants4_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 4 symmetry swap := by
  exact partsCertificateVariant_verifies_core 4

theorem partsCertificateVariants5_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 5 symmetry swap := by
  exact partsCertificateVariant_verifies_core 5

theorem partsCertificateVariants6_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 6 symmetry swap := by
  exact partsCertificateVariant_verifies_core 6

theorem partsCertificateVariants7_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 7 symmetry swap := by
  exact partsCertificateVariant_verifies_core 7

theorem partsCertificateVariant8_0_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 8 0 swap := by
  exact partsCertificateVariant_verifies_core 8 0

theorem partsCertificateVariant8_1_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 8 1 swap := by
  exact partsCertificateVariant_verifies_core 8 1

theorem partsCertificateVariant8_2_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 8 2 swap := by
  exact partsCertificateVariant_verifies_core 8 2

theorem partsCertificateVariant8_3_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 8 3 swap := by
  exact partsCertificateVariant_verifies_core 8 3

theorem partsCertificateVariant8_4_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 8 4 swap := by
  exact partsCertificateVariant_verifies_core 8 4

theorem partsCertificateVariant8_5_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 8 5 swap := by
  exact partsCertificateVariant_verifies_core 8 5

theorem partsCertificateVariants8_verify (symmetry : Fin 6) (swap : Bool) :
    PartsCertificateVariantVerifies 8 symmetry swap := by
  exact partsCertificateVariant_verifies_core 8 symmetry swap

theorem partsCertificateVariants9_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 9 symmetry swap := by
  exact partsCertificateVariant_verifies_core 9

theorem partsCertificateVariants10_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 10 symmetry swap := by
  exact partsCertificateVariant_verifies_core 10

theorem partsCertificateVariants11_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 11 symmetry swap := by
  exact partsCertificateVariant_verifies_core 11

theorem partsCertificateVariants12_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 12 symmetry swap := by
  exact partsCertificateVariant_verifies_core 12

theorem partsCertificateVariants13_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 13 symmetry swap := by
  exact partsCertificateVariant_verifies_core 13

theorem partsCertificateVariants14_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 14 symmetry swap := by
  exact partsCertificateVariant_verifies_core 14

theorem partsCertificateVariants15_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 15 symmetry swap := by
  exact partsCertificateVariant_verifies_core 15

theorem partsCertificateVariant16_0_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 16 0 swap := by
  exact partsCertificateVariant_verifies_core 16 0

theorem partsCertificateVariant16_1_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 16 1 swap := by
  exact partsCertificateVariant_verifies_core 16 1

theorem partsCertificateVariant16_2_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 16 2 swap := by
  exact partsCertificateVariant_verifies_core 16 2

theorem partsCertificateVariant16_3_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 16 3 swap := by
  exact partsCertificateVariant_verifies_core 16 3

theorem partsCertificateVariant16_4_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 16 4 swap := by
  exact partsCertificateVariant_verifies_core 16 4

theorem partsCertificateVariant16_5_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 16 5 swap := by
  exact partsCertificateVariant_verifies_core 16 5

theorem partsCertificateVariants16_verify (symmetry : Fin 6) (swap : Bool) :
    PartsCertificateVariantVerifies 16 symmetry swap := by
  exact partsCertificateVariant_verifies_core 16 symmetry swap

theorem partsCertificateVariant17_0_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 17 0 swap := by
  exact partsCertificateVariant_verifies_core 17 0

theorem partsCertificateVariant17_1_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 17 1 swap := by
  exact partsCertificateVariant_verifies_core 17 1

theorem partsCertificateVariant17_2_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 17 2 swap := by
  exact partsCertificateVariant_verifies_core 17 2

theorem partsCertificateVariant17_3_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 17 3 swap := by
  exact partsCertificateVariant_verifies_core 17 3

theorem partsCertificateVariant17_4_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 17 4 swap := by
  exact partsCertificateVariant_verifies_core 17 4

theorem partsCertificateVariant17_5_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 17 5 swap := by
  exact partsCertificateVariant_verifies_core 17 5

theorem partsCertificateVariants17_verify (symmetry : Fin 6) (swap : Bool) :
    PartsCertificateVariantVerifies 17 symmetry swap := by
  exact partsCertificateVariant_verifies_core 17 symmetry swap

theorem partsCertificateVariants18_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 18 symmetry swap := by
  exact partsCertificateVariant_verifies_core 18

theorem partsCertificateVariants19_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 19 symmetry swap := by
  exact partsCertificateVariant_verifies_core 19

theorem partsCertificateVariants20_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 20 symmetry swap := by
  exact partsCertificateVariant_verifies_core 20

theorem partsCertificateVariants21_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 21 symmetry swap := by
  exact partsCertificateVariant_verifies_core 21

theorem partsCertificateVariants22_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 22 symmetry swap := by
  exact partsCertificateVariant_verifies_core 22

theorem partsCertificateVariants23_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 23 symmetry swap := by
  exact partsCertificateVariant_verifies_core 23

theorem partsCertificateVariant24_0_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 24 0 swap := by
  exact partsCertificateVariant_verifies_core 24 0

theorem partsCertificateVariant24_1_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 24 1 swap := by
  exact partsCertificateVariant_verifies_core 24 1

theorem partsCertificateVariant24_2_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 24 2 swap := by
  exact partsCertificateVariant_verifies_core 24 2

theorem partsCertificateVariant24_3_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 24 3 swap := by
  exact partsCertificateVariant_verifies_core 24 3

theorem partsCertificateVariant24_4_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 24 4 swap := by
  exact partsCertificateVariant_verifies_core 24 4

theorem partsCertificateVariant24_5_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 24 5 swap := by
  exact partsCertificateVariant_verifies_core 24 5

theorem partsCertificateVariants24_verify (symmetry : Fin 6) (swap : Bool) :
    PartsCertificateVariantVerifies 24 symmetry swap := by
  exact partsCertificateVariant_verifies_core 24 symmetry swap

theorem partsCertificateVariant25_0_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 25 0 swap := by
  exact partsCertificateVariant_verifies_core 25 0

theorem partsCertificateVariant25_1_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 25 1 swap := by
  exact partsCertificateVariant_verifies_core 25 1

theorem partsCertificateVariant25_2_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 25 2 swap := by
  exact partsCertificateVariant_verifies_core 25 2

theorem partsCertificateVariant25_3_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 25 3 swap := by
  exact partsCertificateVariant_verifies_core 25 3

theorem partsCertificateVariant25_4_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 25 4 swap := by
  exact partsCertificateVariant_verifies_core 25 4

theorem partsCertificateVariant25_5_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 25 5 swap := by
  exact partsCertificateVariant_verifies_core 25 5

theorem partsCertificateVariants25_verify (symmetry : Fin 6) (swap : Bool) :
    PartsCertificateVariantVerifies 25 symmetry swap := by
  exact partsCertificateVariant_verifies_core 25 symmetry swap

theorem partsCertificateVariants26_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 26 symmetry swap := by
  exact partsCertificateVariant_verifies_core 26

theorem partsCertificateVariants27_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 27 symmetry swap := by
  exact partsCertificateVariant_verifies_core 27

theorem partsCertificateVariants28_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 28 symmetry swap := by
  exact partsCertificateVariant_verifies_core 28

theorem partsCertificateVariants29_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 29 symmetry swap := by
  exact partsCertificateVariant_verifies_core 29

theorem partsCertificateVariants30_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 30 symmetry swap := by
  exact partsCertificateVariant_verifies_core 30

theorem partsCertificateVariants31_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 31 symmetry swap := by
  exact partsCertificateVariant_verifies_core 31

theorem partsCertificateVariants32_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 32 symmetry swap := by
  exact partsCertificateVariant_verifies_core 32

theorem partsCertificateVariants33_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 33 symmetry swap := by
  exact partsCertificateVariant_verifies_core 33

theorem partsCertificateVariant34_0_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 34 0 swap := by
  exact partsCertificateVariant_verifies_core 34 0

theorem partsCertificateVariant34_1_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 34 1 swap := by
  exact partsCertificateVariant_verifies_core 34 1

theorem partsCertificateVariant34_2_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 34 2 swap := by
  exact partsCertificateVariant_verifies_core 34 2

theorem partsCertificateVariant34_3_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 34 3 swap := by
  exact partsCertificateVariant_verifies_core 34 3

theorem partsCertificateVariant34_4_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 34 4 swap := by
  exact partsCertificateVariant_verifies_core 34 4

theorem partsCertificateVariant34_5_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 34 5 swap := by
  exact partsCertificateVariant_verifies_core 34 5

theorem partsCertificateVariants34_verify (symmetry : Fin 6) (swap : Bool) :
    PartsCertificateVariantVerifies 34 symmetry swap := by
  exact partsCertificateVariant_verifies_core 34 symmetry swap

theorem partsCertificateVariants35_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 35 symmetry swap := by
  exact partsCertificateVariant_verifies_core 35

theorem partsCertificateVariant_verifies (base : Fin 36)
    (symmetry : Fin 6) (swap : Bool) :
    PartsCertificateVariantVerifies base symmetry swap := by
  exact partsCertificateVariant_verifies_core base symmetry swap

end HadwigerNelsonBounds
