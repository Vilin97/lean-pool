/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsCoordinates

/-!
# A sound checker for Parts coloring trees

Unary stretches of a coloring tree are stored as forced-color stems. A tree
node therefore ends at either a genuine branch or an uncolorable leaf. This is
the same certificate as the source coloring diagram, but avoids artificial
recursion depth from long chains of forced assignments.
-/

namespace HadwigerNelsonBounds

/-- A vertex-color assignment on the finite Parts graph. -/
structure PartsAssignment where
  /-- Assigned graph vertex. -/
  vertex : Fin 481
  /-- Assigned color. -/
  color : Fin 4
deriving DecidableEq

/-- A compressed coloring-tree node: a forced stem followed by a branch/leaf. -/
structure PartsTreeNode where
  /-- Unary forced assignments preceding the branch. -/
  stem : List PartsAssignment
  /-- Vertex branched on after the forced stem. -/
  vertex : Fin 481
  /-- Encoded child index for each color, with zero meaning absent. -/
  children : Fin 4 → Nat

namespace PartsTreeNode

/-- Decode zero as no child and `n + 1` as child index `n`. -/
def child (node : PartsTreeNode) (color : Fin 4) : Option Nat :=
  match node.children color with
  | 0 => none
  | n + 1 => some n

end PartsTreeNode

/-- A root coloring together with its compressed contradiction tree. -/
structure PartsCertificate where
  /-- Fixed root assignments. -/
  roots : List PartsAssignment
  /-- Number of nodes addressable in the chunked array. -/
  nodeCount : Nat
  /-- Coloring-tree nodes stored in 64-node chunks. -/
  nodes : Array (Array PartsTreeNode)

/-- Constant-depth lookup in a tree stored as 64-node chunks. -/
def partsTreeNodeAt (nodes : Array (Array PartsTreeNode)) (index : Nat) :
    Option PartsTreeNode :=
  match nodes[index / 64]? with
  | none => none
  | some chunk => chunk[index % 64]?

/-- A path assignment blocks `color` at `vertex` through a unit edge. -/
def PartsBlocks (path : List PartsAssignment) (vertex : Fin 481) (color : Fin 4) : Prop :=
  ∃ assignment ∈ path,
    assignment.color = color ∧ partsAdjacent vertex assignment.vertex = true

/-- A coloring agrees with every assignment on a certificate path. -/
def PartsExtends (coloring : Fin 481 → Fin 4) (path : List PartsAssignment) : Prop :=
  ∀ assignment ∈ path, coloring assignment.vertex = assignment.color

/-- Properness for the exact unit edges recognized by the certificate. -/
def PartsProper (coloring : Fin 481 → Fin 4) : Prop :=
  ∀ ⦃v w : Fin 481⦄, partsAdjacent v w = true → coloring v ≠ coloring w

/-- The four colors, as data for the executable checker. -/
def partsColors : List (Fin 4) := [0, 1, 2, 3]

lemma mem_partsColors (color : Fin 4) : color ∈ partsColors := by
  fin_cases color <;> simp [partsColors]

/-- Executable counterpart of `PartsBlocks`. -/
def PartsBlocksB (path : List PartsAssignment) (vertex : Fin 481) (color : Fin 4) : Bool :=
  path.any fun assignment =>
    assignment.color == color && partsAdjacent vertex assignment.vertex

lemma partsBlocksB_eq_true {path : List PartsAssignment} {vertex : Fin 481}
    {color : Fin 4} : PartsBlocksB path vertex color = true ↔
      PartsBlocks path vertex color := by
  rw [PartsBlocksB, List.any_eq_true]
  constructor
  · rintro ⟨assignment, hin, hcheck⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hcheck
    exact ⟨assignment, hin, hcheck⟩
  · rintro ⟨assignment, hin, hcolor, hadj⟩
    exact ⟨assignment, hin, by simp [hcolor, hadj]⟩

/-- A forced assignment is the only color not blocked by the current path. -/
def PartsForcedB (path : List PartsAssignment) (assignment : PartsAssignment) : Bool :=
  partsColors.all fun color =>
    color == assignment.color || PartsBlocksB path assignment.vertex color

/-- Execute a sequence of forced assignments, returning the extended path. -/
def PartsRunStemB : List PartsAssignment → List PartsAssignment →
    Option (List PartsAssignment)
  | [], path => some path
  | assignment :: stem, path =>
      if PartsForcedB path assignment then
        PartsRunStemB stem (assignment :: path)
      else
        none

/-- Executable checker for a compressed coloring tree. -/
def PartsVerifiesNodeB (nodes : Array (Array PartsTreeNode)) :
    Nat → List PartsAssignment → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, path, index =>
      match partsTreeNodeAt nodes index with
      | none => false
      | some node =>
          match PartsRunStemB node.stem path with
          | none => false
          | some extended =>
              partsColors.all fun color =>
                PartsBlocksB extended node.vertex color ||
                  match node.child color with
                  | none => false
                  | some child =>
                      PartsVerifiesNodeB nodes fuel
                        (⟨node.vertex, color⟩ :: extended) child

/-- Check a certificate from node zero with enough fuel for an acyclic tree. -/
def PartsCertificate.Verifies (certificate : PartsCertificate) : Prop :=
  PartsVerifiesNodeB certificate.nodes (certificate.nodeCount + 1)
    certificate.roots 0 = true

instance (certificate : PartsCertificate) : Decidable certificate.Verifies := by
  unfold PartsCertificate.Verifies
  infer_instance

lemma not_partsBlocks_of_proper {coloring : Fin 481 → Fin 4}
    (hproper : PartsProper coloring) (path : List PartsAssignment)
    (hextends : PartsExtends coloring path) (vertex : Fin 481) :
    ¬PartsBlocks path vertex (coloring vertex) := by
  rintro ⟨assignment, hin, hcolor, hadj⟩
  have hpath := hextends assignment hin
  have hne := hproper hadj
  apply hne
  rw [hpath, hcolor]

lemma partsForcedB_sound {coloring : Fin 481 → Fin 4}
    (hproper : PartsProper coloring) {path : List PartsAssignment}
    (hextends : PartsExtends coloring path) {assignment : PartsAssignment}
    (hforced : PartsForcedB path assignment = true) :
    coloring assignment.vertex = assignment.color := by
  rw [PartsForcedB, List.all_eq_true] at hforced
  have hcolor := hforced (coloring assignment.vertex)
    (mem_partsColors (coloring assignment.vertex))
  rw [Bool.or_eq_true] at hcolor
  rcases hcolor with hsame | hblocked
  · exact beq_iff_eq.mp hsame
  · exact False.elim ((not_partsBlocks_of_proper hproper path hextends assignment.vertex)
      (partsBlocksB_eq_true.mp hblocked))

lemma partsRunStemB_sound {coloring : Fin 481 → Fin 4}
    (hproper : PartsProper coloring) :
    ∀ {stem path extended}, PartsRunStemB stem path = some extended →
      PartsExtends coloring path → PartsExtends coloring extended := by
  intro stem
  induction stem with
  | nil =>
      intro path extended hrun hextends
      simp only [PartsRunStemB, Option.some.injEq] at hrun
      subst extended
      exact hextends
  | cons assignment stem ih =>
      intro path extended hrun hextends
      simp only [PartsRunStemB] at hrun
      split at hrun
      · rename_i hforced
        apply ih hrun
        intro current hin
        simp only [List.mem_cons] at hin
        rcases hin with rfl | hin
        · exact partsForcedB_sound hproper hextends hforced
        · exact hextends current hin
      · contradiction

lemma partsVerifiesNodeB_unsat {nodes : Array (Array PartsTreeNode)}
    {coloring : Fin 481 → Fin 4} (hproper : PartsProper coloring) :
    ∀ {fuel path index}, PartsVerifiesNodeB nodes fuel path index = true →
      PartsExtends coloring path → False := by
  intro fuel
  induction fuel with
  | zero =>
      intro path index hverify _
      simp [PartsVerifiesNodeB] at hverify
  | succ fuel ih =>
      intro path index hverify hextends
      simp only [PartsVerifiesNodeB] at hverify
      split at hverify
      · contradiction
      · rename_i node hnode
        split at hverify
        · contradiction
        · rename_i extended hrun
          have hextended := partsRunStemB_sound hproper hrun hextends
          rw [List.all_eq_true] at hverify
          have hcolor := hverify (coloring node.vertex)
            (mem_partsColors (coloring node.vertex))
          rw [Bool.or_eq_true] at hcolor
          rcases hcolor with hblocked | hnext
          · exact (not_partsBlocks_of_proper hproper extended hextended node.vertex)
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

/-- Soundness of a checked Parts coloring tree. -/
theorem PartsCertificate.not_colorable (certificate : PartsCertificate)
    (hverify : certificate.Verifies) {coloring : Fin 481 → Fin 4}
    (hproper : PartsProper coloring)
    (hroots : PartsExtends coloring certificate.roots) : False := by
  exact partsVerifiesNodeB_unsat hproper hverify hroots

end HadwigerNelsonBounds
