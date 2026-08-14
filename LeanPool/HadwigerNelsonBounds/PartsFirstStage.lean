/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsCertificateData
import LeanPool.HadwigerNelsonBounds.PartsPermutations

/-!
# The Parts obstruction to a monochromatic sqrt-three triangle

This module expands the 36 normalized coloring trees through the six exact
root symmetries and the remaining color swap. The resulting 432 certificates
cover every proper normalized coloring of the 13-vertex 2-Golomb root.
-/

namespace HadwigerNelsonBounds

/-- Swap the two colors not fixed by the normalized root. -/
def partsSwapMiddleColor (color : Fin 4) : Fin 4 := ![0, 2, 1, 3] color

/-- The color renaming used by a certificate variant. -/
def partsTransformColor (swap : Bool) (color : Fin 4) : Fin 4 :=
  if swap then partsSwapMiddleColor color else color

/-- Rename the vertices and optionally the two free colors of an assignment. -/
def partsTransformAssignment (symmetry : Fin 6) (swap : Bool)
    (assignment : PartsAssignment) : PartsAssignment :=
  { vertex := partsPermuteVertex symmetry assignment.vertex
    color := partsTransformColor swap assignment.color }

/-- Transform a root path without materializing a second copy of its tree. -/
def partsTransformPath (symmetry : Fin 6) (swap : Bool) :
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

private def partsSymmetryOfNat (value : Nat) : Fin 6 :=
  ⟨value % 6, Nat.mod_lt value (by decide)⟩

private def partsVertexOfNat (value : Nat) : Fin 481 :=
  ⟨value % 481, Nat.mod_lt value (by decide)⟩

private lemma partsPoint_permuteVertex_isTransform0 (symmetryValue : Nat)
    (hsymmetry : symmetryValue < 6)
    (value : Nat) (hupper : value < 64) :
    PartsPoint.IsTransform (partsSymmetryOfNat symmetryValue)
      (partsPoint (partsVertexOfNat value))
      (partsPoint (partsPermuteVertex (partsSymmetryOfNat symmetryValue)
        (partsVertexOfNat value))) := by
  interval_cases symmetryValue <;> interval_cases value <;>
    simp only [PartsPoint.IsTransform, partsSymmetryOfNat] <;> decide

private lemma partsPoint_permuteVertex_isTransform1 (symmetryValue : Nat)
    (hsymmetry : symmetryValue < 6)
    (value : Nat) (hlower : 64 ≤ value) (hupper : value < 128) :
    PartsPoint.IsTransform (partsSymmetryOfNat symmetryValue)
      (partsPoint (partsVertexOfNat value))
      (partsPoint (partsPermuteVertex (partsSymmetryOfNat symmetryValue)
        (partsVertexOfNat value))) := by
  interval_cases symmetryValue <;> interval_cases value <;>
    simp only [PartsPoint.IsTransform, partsSymmetryOfNat] <;> decide

private lemma partsPoint_permuteVertex_isTransform2 (symmetryValue : Nat)
    (hsymmetry : symmetryValue < 6)
    (value : Nat) (hlower : 128 ≤ value) (hupper : value < 192) :
    PartsPoint.IsTransform (partsSymmetryOfNat symmetryValue)
      (partsPoint (partsVertexOfNat value))
      (partsPoint (partsPermuteVertex (partsSymmetryOfNat symmetryValue)
        (partsVertexOfNat value))) := by
  interval_cases symmetryValue <;> interval_cases value <;>
    simp only [PartsPoint.IsTransform, partsSymmetryOfNat] <;> decide

private lemma partsPoint_permuteVertex_isTransform3 (symmetryValue : Nat)
    (hsymmetry : symmetryValue < 6)
    (value : Nat) (hlower : 192 ≤ value) (hupper : value < 256) :
    PartsPoint.IsTransform (partsSymmetryOfNat symmetryValue)
      (partsPoint (partsVertexOfNat value))
      (partsPoint (partsPermuteVertex (partsSymmetryOfNat symmetryValue)
        (partsVertexOfNat value))) := by
  interval_cases symmetryValue <;> interval_cases value <;>
    simp only [PartsPoint.IsTransform, partsSymmetryOfNat] <;> decide

private lemma partsPoint_permuteVertex_isTransform4 (symmetryValue : Nat)
    (hsymmetry : symmetryValue < 6)
    (value : Nat) (hlower : 256 ≤ value) (hupper : value < 320) :
    PartsPoint.IsTransform (partsSymmetryOfNat symmetryValue)
      (partsPoint (partsVertexOfNat value))
      (partsPoint (partsPermuteVertex (partsSymmetryOfNat symmetryValue)
        (partsVertexOfNat value))) := by
  interval_cases symmetryValue <;> interval_cases value <;>
    simp only [PartsPoint.IsTransform, partsSymmetryOfNat] <;> decide

private lemma partsPoint_permuteVertex_isTransform5 (symmetryValue : Nat)
    (hsymmetry : symmetryValue < 6)
    (value : Nat) (hlower : 320 ≤ value) (hupper : value < 384) :
    PartsPoint.IsTransform (partsSymmetryOfNat symmetryValue)
      (partsPoint (partsVertexOfNat value))
      (partsPoint (partsPermuteVertex (partsSymmetryOfNat symmetryValue)
        (partsVertexOfNat value))) := by
  interval_cases symmetryValue <;> interval_cases value <;>
    simp only [PartsPoint.IsTransform, partsSymmetryOfNat] <;> decide

private lemma partsPoint_permuteVertex_isTransform6 (symmetryValue : Nat)
    (hsymmetry : symmetryValue < 6)
    (value : Nat) (hlower : 384 ≤ value) (hupper : value < 448) :
    PartsPoint.IsTransform (partsSymmetryOfNat symmetryValue)
      (partsPoint (partsVertexOfNat value))
      (partsPoint (partsPermuteVertex (partsSymmetryOfNat symmetryValue)
        (partsVertexOfNat value))) := by
  interval_cases symmetryValue <;> interval_cases value <;>
    simp only [PartsPoint.IsTransform, partsSymmetryOfNat] <;> decide

private lemma partsPoint_permuteVertex_isTransform7 (symmetryValue : Nat)
    (hsymmetry : symmetryValue < 6)
    (value : Nat) (hupper : value < 481) (hlower : 448 ≤ value) :
    PartsPoint.IsTransform (partsSymmetryOfNat symmetryValue)
      (partsPoint (partsVertexOfNat value))
      (partsPoint (partsPermuteVertex (partsSymmetryOfNat symmetryValue)
        (partsVertexOfNat value))) := by
  interval_cases symmetryValue <;> interval_cases value <;>
    simp only [PartsPoint.IsTransform, partsSymmetryOfNat] <;> decide

/-- The stored vertex tables implement the exact isometries described above. -/
private lemma partsPoint_permuteVertex_isTransform (symmetry : Fin 6) :
    ∀ vertex, PartsPoint.IsTransform symmetry (partsPoint vertex)
      (partsPoint (partsPermuteVertex symmetry vertex)) := by
  intro vertex
  have hsymmetry : partsSymmetryOfNat symmetry.val = symmetry := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt symmetry.isLt
  have hvertex : partsVertexOfNat vertex.val = vertex := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt vertex.isLt
  rw [← hsymmetry, ← hvertex]
  by_cases h64 : vertex.val < 64
  · exact partsPoint_permuteVertex_isTransform0 symmetry.val symmetry.isLt vertex.val h64
  by_cases h128 : vertex.val < 128
  · exact partsPoint_permuteVertex_isTransform1 symmetry.val symmetry.isLt vertex.val
      (Nat.le_of_not_gt h64) h128
  by_cases h192 : vertex.val < 192
  · exact partsPoint_permuteVertex_isTransform2 symmetry.val symmetry.isLt vertex.val
      (Nat.le_of_not_gt h128) h192
  by_cases h256 : vertex.val < 256
  · exact partsPoint_permuteVertex_isTransform3 symmetry.val symmetry.isLt vertex.val
      (Nat.le_of_not_gt h192) h256
  by_cases h320 : vertex.val < 320
  · exact partsPoint_permuteVertex_isTransform4 symmetry.val symmetry.isLt vertex.val
      (Nat.le_of_not_gt h256) h320
  by_cases h384 : vertex.val < 384
  · exact partsPoint_permuteVertex_isTransform5 symmetry.val symmetry.isLt vertex.val
      (Nat.le_of_not_gt h320) h384
  by_cases h448 : vertex.val < 448
  · exact partsPoint_permuteVertex_isTransform6 symmetry.val symmetry.isLt vertex.val
      (Nat.le_of_not_gt h384) h448
  · exact partsPoint_permuteVertex_isTransform7 symmetry.val symmetry.isLt vertex.val
      vertex.isLt (Nat.le_of_not_gt h448)

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
def partsBaseCertificate (base : Fin 36) : PartsCertificate :=
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
def PartsCertificateVariantVerifies (base : Fin 36) (symmetry : Fin 6)
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
    (partsBaseCertificate 0).Verifies := by decide

private theorem partsBaseCertificate1_verify :
    (partsBaseCertificate 1).Verifies := by decide

private theorem partsBaseCertificate2_verify :
    (partsBaseCertificate 2).Verifies := by decide

private theorem partsBaseCertificate3_verify :
    (partsBaseCertificate 3).Verifies := by decide

private theorem partsBaseCertificate4_verify :
    (partsBaseCertificate 4).Verifies := by decide

private theorem partsBaseCertificate5_verify :
    (partsBaseCertificate 5).Verifies := by decide

private theorem partsBaseCertificate6_verify :
    (partsBaseCertificate 6).Verifies := by decide

private theorem partsBaseCertificate7_verify :
    (partsBaseCertificate 7).Verifies := by decide

private theorem partsBaseCertificate8_verify :
    (partsBaseCertificate 8).Verifies := by decide

private theorem partsBaseCertificate9_verify :
    (partsBaseCertificate 9).Verifies := by decide

private theorem partsBaseCertificate10_verify :
    (partsBaseCertificate 10).Verifies := by decide

private theorem partsBaseCertificate11_verify :
    (partsBaseCertificate 11).Verifies := by decide

private theorem partsBaseCertificate12_verify :
    (partsBaseCertificate 12).Verifies := by decide

private theorem partsBaseCertificate13_verify :
    (partsBaseCertificate 13).Verifies := by decide

private theorem partsBaseCertificate14_verify :
    (partsBaseCertificate 14).Verifies := by decide

private theorem partsBaseCertificate15_verify :
    (partsBaseCertificate 15).Verifies := by decide

private theorem partsBaseCertificate16_verify :
    (partsBaseCertificate 16).Verifies := by decide

private theorem partsBaseCertificate17_verify :
    (partsBaseCertificate 17).Verifies := by decide

private theorem partsBaseCertificate18_verify :
    (partsBaseCertificate 18).Verifies := by decide

private theorem partsBaseCertificate19_verify :
    (partsBaseCertificate 19).Verifies := by decide

private theorem partsBaseCertificate20_verify :
    (partsBaseCertificate 20).Verifies := by decide

private theorem partsBaseCertificate21_verify :
    (partsBaseCertificate 21).Verifies := by decide

private theorem partsBaseCertificate22_verify :
    (partsBaseCertificate 22).Verifies := by decide

private theorem partsBaseCertificate23_verify :
    (partsBaseCertificate 23).Verifies := by decide

private theorem partsBaseCertificate24_verify :
    (partsBaseCertificate 24).Verifies := by decide

private theorem partsBaseCertificate25_verify :
    (partsBaseCertificate 25).Verifies := by decide

private theorem partsBaseCertificate26_verify :
    (partsBaseCertificate 26).Verifies := by decide

private theorem partsBaseCertificate27_verify :
    (partsBaseCertificate 27).Verifies := by decide

private theorem partsBaseCertificate28_verify :
    (partsBaseCertificate 28).Verifies := by decide

private theorem partsBaseCertificate29_verify :
    (partsBaseCertificate 29).Verifies := by decide

private theorem partsBaseCertificate30_verify :
    (partsBaseCertificate 30).Verifies := by decide

private theorem partsBaseCertificate31_verify :
    (partsBaseCertificate 31).Verifies := by decide

private theorem partsBaseCertificate32_verify :
    (partsBaseCertificate 32).Verifies := by decide

private theorem partsBaseCertificate33_verify :
    (partsBaseCertificate 33).Verifies := by decide

private theorem partsBaseCertificate34_verify :
    (partsBaseCertificate 34).Verifies := by decide

private theorem partsBaseCertificate35_verify :
    (partsBaseCertificate 35).Verifies := by decide

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
