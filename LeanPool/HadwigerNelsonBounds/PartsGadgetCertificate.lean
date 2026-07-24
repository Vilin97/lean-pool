/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsGadgetData

/-!
# A sound checker for the second-stage Parts gadget

The finite constraint system has unit-edge inequalities and non-monochromatic
sqrt-three triples.  Unary stretches of its coloring trees are stored as
forced stems, exactly as in the first-stage Parts certificate.
-/

namespace HadwigerNelsonBounds

/-- A vertex-color assignment in the 73-vertex second-stage gadget. -/
structure PartsGadgetAssignment where
  /-- Assigned gadget vertex. -/
  vertex : Fin 73
  /-- Assigned color. -/
  color : Fin 4
deriving DecidableEq

/-- A compressed coloring-tree node. -/
structure PartsGadgetTreeNode where
  /-- Unary forced assignments preceding the branch. -/
  stem : List PartsGadgetAssignment
  /-- Vertex branched on after the forced stem. -/
  vertex : Fin 73
  /-- Encoded child index for each color, with zero meaning absent. -/
  children : Fin 4 → Nat

namespace PartsGadgetTreeNode

/-- Decode zero as no child and `n + 1` as child index `n`. -/
def child (node : PartsGadgetTreeNode) (color : Fin 4) : Option Nat :=
  match node.children color with
  | 0 => none
  | index + 1 => some index

end PartsGadgetTreeNode

/-- A normalized root coloring and its compressed contradiction tree. -/
structure PartsGadgetCertificate where
  /-- Fixed root assignments. -/
  roots : List PartsGadgetAssignment
  /-- Number of nodes addressable in the chunked array. -/
  nodeCount : Nat
  /-- Coloring-tree nodes stored in 64-node chunks. -/
  nodes : Array (Array PartsGadgetTreeNode)

/-- Constant-depth lookup in a tree stored as 64-node chunks. -/
def partsGadgetTreeNodeAt (nodes : Array (Array PartsGadgetTreeNode))
    (index : Nat) : Option PartsGadgetTreeNode :=
  match nodes[index / 64]? with
  | none => none
  | some chunk => chunk[index % 64]?

/-- Properness on every listed unit edge. -/
def PartsGadgetProper (coloring : Fin 73 → Fin 4) : Prop :=
  ∀ vertex neighbor, neighbor ∈ partsGadgetNeighbors vertex →
    coloring vertex ≠ coloring neighbor

/-- Every listed sqrt-three triangle is non-monochromatic. -/
def PartsGadgetNoMono (coloring : Fin 73 → Fin 4) : Prop :=
  ∀ vertex pair, pair ∈ partsGadgetTriplePairs vertex →
    ¬(coloring vertex = coloring pair.1 ∧ coloring pair.1 = coloring pair.2)

/-- The two constraints used by the second-stage checker. -/
def PartsGadgetValid (coloring : Fin 73 → Fin 4) : Prop :=
  PartsGadgetProper coloring ∧ PartsGadgetNoMono coloring

/-- A coloring agrees with every assignment on a certificate path. -/
def PartsGadgetExtends (coloring : Fin 73 → Fin 4)
    (path : List PartsGadgetAssignment) : Prop :=
  ∀ assignment ∈ path, coloring assignment.vertex = assignment.color

/-- The path already assigns a given color to a vertex. -/
def PartsGadgetHasColor (path : List PartsGadgetAssignment)
    (vertex : Fin 73) (color : Fin 4) : Prop :=
  ∃ assignment ∈ path,
    assignment.vertex = vertex ∧ assignment.color = color

/-- A path blocks a color through an edge or a monochromatic triple. -/
def PartsGadgetBlocks (path : List PartsGadgetAssignment)
    (vertex : Fin 73) (color : Fin 4) : Prop :=
  (∃ assignment ∈ path,
      assignment.color = color ∧
        assignment.vertex ∈ partsGadgetNeighbors vertex) ∨
    ∃ pair ∈ partsGadgetTriplePairs vertex,
      PartsGadgetHasColor path pair.1 color ∧
        PartsGadgetHasColor path pair.2 color

/-- The four colors, as executable data. -/
def partsGadgetColors : List (Fin 4) := [0, 1, 2, 3]

lemma mem_partsGadgetColors (color : Fin 4) : color ∈ partsGadgetColors := by
  fin_cases color <;> simp [partsGadgetColors]

/-- Executable path-color lookup. -/
def PartsGadgetHasColorB (path : List PartsGadgetAssignment)
    (vertex : Fin 73) (color : Fin 4) : Bool :=
  path.any fun assignment =>
    assignment.vertex == vertex && assignment.color == color

lemma partsGadgetHasColorB_eq_true {path : List PartsGadgetAssignment}
    {vertex : Fin 73} {color : Fin 4} :
    PartsGadgetHasColorB path vertex color = true ↔
      PartsGadgetHasColor path vertex color := by
  rw [PartsGadgetHasColorB, List.any_eq_true]
  constructor
  · rintro ⟨assignment, hin, hcheck⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hcheck
    exact ⟨assignment, hin, hcheck⟩
  · rintro ⟨assignment, hin, rfl, rfl⟩
    exact ⟨assignment, hin, by simp⟩

/-- Executable counterpart of `PartsGadgetBlocks`. -/
def PartsGadgetBlocksB (path : List PartsGadgetAssignment)
    (vertex : Fin 73) (color : Fin 4) : Bool :=
  path.any (fun assignment =>
      assignment.color == color &&
        decide (assignment.vertex ∈ partsGadgetNeighbors vertex)) ||
    (partsGadgetTriplePairs vertex).any fun pair =>
      PartsGadgetHasColorB path pair.1 color &&
        PartsGadgetHasColorB path pair.2 color

lemma partsGadgetBlocksB_eq_true {path : List PartsGadgetAssignment}
    {vertex : Fin 73} {color : Fin 4} :
    PartsGadgetBlocksB path vertex color = true ↔
      PartsGadgetBlocks path vertex color := by
  rw [PartsGadgetBlocksB, Bool.or_eq_true]
  constructor
  · rintro (hedge | htriple)
    · left
      rw [List.any_eq_true] at hedge
      rcases hedge with ⟨assignment, hin, hcheck⟩
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcheck
      exact ⟨assignment, hin, hcheck⟩
    · right
      rw [List.any_eq_true] at htriple
      rcases htriple with ⟨pair, hin, hcheck⟩
      simp only [Bool.and_eq_true] at hcheck
      exact ⟨pair, hin, partsGadgetHasColorB_eq_true.mp hcheck.1,
        partsGadgetHasColorB_eq_true.mp hcheck.2⟩
  · rintro (hedge | htriple)
    · left
      rcases hedge with ⟨assignment, hin, hcolor, hadj⟩
      rw [List.any_eq_true]
      exact ⟨assignment, hin, by simp [hcolor, hadj]⟩
    · right
      rcases htriple with ⟨pair, hin, hleft, hright⟩
      rw [List.any_eq_true]
      exact ⟨pair, hin, by
        simp only [Bool.and_eq_true]
        exact ⟨partsGadgetHasColorB_eq_true.mpr hleft,
          partsGadgetHasColorB_eq_true.mpr hright⟩⟩

/-- A forced assignment is the only color not blocked by the path. -/
def PartsGadgetForcedB (path : List PartsGadgetAssignment)
    (assignment : PartsGadgetAssignment) : Bool :=
  partsGadgetColors.all fun color =>
    color == assignment.color ||
      PartsGadgetBlocksB path assignment.vertex color

/-- Execute a sequence of forced assignments. -/
def PartsGadgetRunStemB : List PartsGadgetAssignment →
    List PartsGadgetAssignment → Option (List PartsGadgetAssignment)
  | [], path => some path
  | assignment :: stem, path =>
      if PartsGadgetForcedB path assignment then
        PartsGadgetRunStemB stem (assignment :: path)
      else
        none

/-- Executable checker for a compressed contradiction tree. -/
def PartsGadgetVerifiesNodeB (nodes : Array (Array PartsGadgetTreeNode)) :
    Nat → List PartsGadgetAssignment → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, path, index =>
      match partsGadgetTreeNodeAt nodes index with
      | none => false
      | some node =>
          match PartsGadgetRunStemB node.stem path with
          | none => false
          | some extended =>
              partsGadgetColors.all fun color =>
                PartsGadgetBlocksB extended node.vertex color ||
                  match node.child color with
                  | none => false
                  | some child =>
                      PartsGadgetVerifiesNodeB nodes fuel
                        (⟨node.vertex, color⟩ :: extended) child

/-- Check a certificate from node zero with enough acyclic-tree fuel. -/
def PartsGadgetCertificate.Verifies
    (certificate : PartsGadgetCertificate) : Prop :=
  PartsGadgetVerifiesNodeB certificate.nodes (certificate.nodeCount + 1)
    certificate.roots 0 = true

instance (certificate : PartsGadgetCertificate) :
    Decidable certificate.Verifies := by
  unfold PartsGadgetCertificate.Verifies
  infer_instance

lemma not_partsGadgetBlocks_of_valid {coloring : Fin 73 → Fin 4}
    (hvalid : PartsGadgetValid coloring) (path : List PartsGadgetAssignment)
    (hextends : PartsGadgetExtends coloring path) (vertex : Fin 73) :
    ¬PartsGadgetBlocks path vertex (coloring vertex) := by
  rintro (hedge | htriple)
  · rcases hedge with ⟨assignment, hin, hcolor, hadj⟩
    apply hvalid.1 vertex assignment.vertex hadj
    rw [hextends assignment hin, hcolor]
  · rcases htriple with ⟨pair, hin, hleft, hright⟩
    apply hvalid.2 vertex pair hin
    rcases hleft with ⟨left, hleft, hleftVertex, hleftColor⟩
    rcases hright with ⟨right, hright, hrightVertex, hrightColor⟩
    constructor
    · rw [← hleftVertex, hextends left hleft, hleftColor]
    · rw [← hleftVertex, hextends left hleft, hleftColor,
        ← hrightVertex, hextends right hright, hrightColor]

lemma partsGadgetForcedB_sound {coloring : Fin 73 → Fin 4}
    (hvalid : PartsGadgetValid coloring) {path : List PartsGadgetAssignment}
    (hextends : PartsGadgetExtends coloring path)
    {assignment : PartsGadgetAssignment}
    (hforced : PartsGadgetForcedB path assignment = true) :
    coloring assignment.vertex = assignment.color := by
  rw [PartsGadgetForcedB, List.all_eq_true] at hforced
  have hcolor := hforced (coloring assignment.vertex)
    (mem_partsGadgetColors (coloring assignment.vertex))
  rw [Bool.or_eq_true] at hcolor
  rcases hcolor with hsame | hblocked
  · exact beq_iff_eq.mp hsame
  · exact False.elim ((not_partsGadgetBlocks_of_valid hvalid path hextends
      assignment.vertex) (partsGadgetBlocksB_eq_true.mp hblocked))

lemma partsGadgetRunStemB_sound {coloring : Fin 73 → Fin 4}
    (hvalid : PartsGadgetValid coloring) :
    ∀ {stem path extended}, PartsGadgetRunStemB stem path = some extended →
      PartsGadgetExtends coloring path →
        PartsGadgetExtends coloring extended := by
  intro stem
  induction stem with
  | nil =>
      intro path extended hrun hextends
      simp only [PartsGadgetRunStemB, Option.some.injEq] at hrun
      subst extended
      exact hextends
  | cons assignment stem ih =>
      intro path extended hrun hextends
      simp only [PartsGadgetRunStemB] at hrun
      split at hrun
      · rename_i hforced
        apply ih hrun
        intro current hin
        simp only [List.mem_cons] at hin
        rcases hin with rfl | hin
        · exact partsGadgetForcedB_sound hvalid hextends hforced
        · exact hextends current hin
      · contradiction

lemma partsGadgetVerifiesNodeB_unsat
    {nodes : Array (Array PartsGadgetTreeNode)}
    {coloring : Fin 73 → Fin 4} (hvalid : PartsGadgetValid coloring) :
    ∀ {fuel path index}, PartsGadgetVerifiesNodeB nodes fuel path index = true →
      PartsGadgetExtends coloring path → False := by
  intro fuel
  induction fuel with
  | zero =>
      intro path index hverify _
      simp [PartsGadgetVerifiesNodeB] at hverify
  | succ fuel ih =>
      intro path index hverify hextends
      simp only [PartsGadgetVerifiesNodeB] at hverify
      split at hverify
      · contradiction
      · rename_i node hnode
        split at hverify
        · contradiction
        · rename_i extended hrun
          have hextended := partsGadgetRunStemB_sound hvalid hrun hextends
          rw [List.all_eq_true] at hverify
          have hcolor := hverify (coloring node.vertex)
            (mem_partsGadgetColors (coloring node.vertex))
          rw [Bool.or_eq_true] at hcolor
          rcases hcolor with hblocked | hnext
          · exact (not_partsGadgetBlocks_of_valid hvalid extended hextended
              node.vertex) (partsGadgetBlocksB_eq_true.mp hblocked)
          · simp only [PartsGadgetTreeNode.child] at hnext
            split at hnext
            · contradiction
            · rename_i child hchild
              apply ih hnext
              intro assignment hin
              simp only [List.mem_cons] at hin
              rcases hin with rfl | hin
              · rfl
              · exact hextended assignment hin

/-- A verified coloring tree rules out every valid coloring extending its roots. -/
theorem PartsGadgetCertificate.not_colorable
    (certificate : PartsGadgetCertificate) (hverify : certificate.Verifies)
    {coloring : Fin 73 → Fin 4} (hvalid : PartsGadgetValid coloring)
    (hroots : PartsGadgetExtends coloring certificate.roots) : False := by
  exact partsGadgetVerifiesNodeB_unsat hvalid hverify hroots

end HadwigerNelsonBounds
