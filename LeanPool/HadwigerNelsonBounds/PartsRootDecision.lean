/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.HadwigerNelsonBounds.PartsRootDecisionData0
public import LeanPool.HadwigerNelsonBounds.PartsRootDecisionData1
public import LeanPool.HadwigerNelsonBounds.PartsRootDecisionData2
public import LeanPool.HadwigerNelsonBounds.PartsRootDecisionData3

/-!
# Complete normalized root dispatch

The 1,023-node trie has 432 leaves, one for each proper normalized coloring of
the 13-vertex 2-Golomb root. Every leaf names a separately checked Parts tree.
-/

public section

namespace HadwigerNelsonBounds

/-- All chunks of the complete normalized root-decision trie. -/
def partsRootDecisionNodes : Array (Array PartsRootNode) := #[
  partsRootDecisionChunk0,
  partsRootDecisionChunk1,
  partsRootDecisionChunk2,
  partsRootDecisionChunk3,
  partsRootDecisionChunk4,
  partsRootDecisionChunk5,
  partsRootDecisionChunk6,
  partsRootDecisionChunk7,
  partsRootDecisionChunk8,
  partsRootDecisionChunk9,
  partsRootDecisionChunk10,
  partsRootDecisionChunk11,
  partsRootDecisionChunk12,
  partsRootDecisionChunk13,
  partsRootDecisionChunk14,
  partsRootDecisionChunk15,
]

private def partsAssignmentFieldsEq (left right : PartsAssignment) : Bool :=
  (left.vertex == right.vertex) && (left.color == right.color)

private theorem partsAssignmentFieldsEq_eq (left right : PartsAssignment) :
    partsAssignmentFieldsEq left right = (left == right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [partsAssignmentFieldsEq, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hvertex, hcolor⟩
    cases left with
    | mk leftVertex leftColor =>
      cases right with
      | mk rightVertex rightColor =>
        cases hvertex
        cases hcolor
        rfl
  · intro h
    cases h
    exact ⟨rfl, rfl⟩

private def partsAssignmentInPathBExplicit (path : List PartsAssignment)
    (assignment : PartsAssignment) : Bool :=
  path.any fun current => partsAssignmentFieldsEq current assignment

private theorem partsAssignmentInPathBExplicit_eq (path : List PartsAssignment)
    (assignment : PartsAssignment) :
    partsAssignmentInPathBExplicit path assignment =
      PartsAssignmentInPathB path assignment := by
  simp only [partsAssignmentInPathBExplicit, PartsAssignmentInPathB,
    partsAssignmentFieldsEq_eq]

private def partsRootsInPathBExplicit (path roots : List PartsAssignment) : Bool :=
  roots.all (partsAssignmentInPathBExplicit path)

private theorem partsRootsInPathBExplicit_eq (path roots : List PartsAssignment) :
    partsRootsInPathBExplicit path roots = PartsRootsInPathB path roots := by
  simp only [partsRootsInPathBExplicit, PartsRootsInPathB]
  congr 1
  funext assignment
  exact partsAssignmentInPathBExplicit_eq path assignment

private def partsRootVerifiesNodeBExplicit (nodes : Array (Array PartsRootNode)) :
    Nat → List PartsAssignment → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, path, index =>
      match partsRootNodeAt nodes index with
      | none => false
      | some (.leaf base symmetry swap) =>
          partsRootsInPathBExplicit path
            (partsTransformPath symmetry swap (partsBaseCertificate base).roots)
      | some (.branch vertex children) =>
          partsColors.all fun color =>
            PartsBlocksB path vertex color ||
              match partsRootChild children color with
              | none => false
              | some child =>
                  partsRootVerifiesNodeBExplicit nodes fuel
                    (⟨vertex, color⟩ :: path) child

private theorem partsRootVerifiesNodeBExplicit_eq (nodes : Array (Array PartsRootNode)) :
    ∀ fuel path index,
      partsRootVerifiesNodeBExplicit nodes fuel path index =
        PartsRootVerifiesNodeB nodes fuel path index := by
  intro fuel
  induction fuel with
  | zero =>
      intro path index
      rfl
  | succ fuel ih =>
      intro path index
      simp only [partsRootVerifiesNodeBExplicit, PartsRootVerifiesNodeB,
        partsRootsInPathBExplicit_eq, ih]
      rfl

theorem partsRootDecision_verifies :
    PartsRootVerifiesNodeB partsRootDecisionNodes 1024
      partsNormalizedRootPath 0 = true := by
  rw [← partsRootVerifiesNodeBExplicit_eq]
  decide +kernel

/-- No proper coloring of the Parts graph extends the normalized fixed root. -/
theorem no_parts_coloring_of_normalized_root {coloring : Fin 481 → Fin 4}
    (hproper : PartsProper coloring)
    (hroots : PartsExtends coloring partsNormalizedRootPath) : False := by
  exact partsRootDecision_not_colorable partsRootDecisionNodes 1023
    partsRootDecision_verifies hproper hroots

end HadwigerNelsonBounds
