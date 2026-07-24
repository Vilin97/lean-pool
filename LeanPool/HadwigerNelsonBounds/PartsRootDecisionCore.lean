/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsFirstStage

/-!
# Root-case dispatcher for the Parts certificate

The dispatcher colors the nine unfixed vertices of the 13-vertex 2-Golomb
root. Its leaves point to the appropriate one of the 432 checked symmetry and
color variants from `PartsFirstStage`.
-/

namespace HadwigerNelsonBounds

/-- A branch in the root trie, or a leaf selecting a checked Parts tree. -/
inductive PartsRootNode where
  | branch (vertex : Fin 481) (children : Fin 4 → Nat)
  | leaf (base : Fin 36) (symmetry : Fin 6) (swap : Bool)

/-- Decode a branch's zero-sentinel child table. -/
def partsRootChild (children : Fin 4 → Nat) (color : Fin 4) : Option Nat :=
  match children color with
  | 0 => none
  | n + 1 => some n

/-- Constant-depth lookup in 64-node root-trie chunks. -/
def partsRootNodeAt (nodes : Array (Array PartsRootNode)) (index : Nat) :
    Option PartsRootNode :=
  match nodes[index / 64]? with
  | none => none
  | some chunk => chunk[index % 64]?

/-- Executable membership of an exact assignment in a current path. -/
def PartsAssignmentInPathB (path : List PartsAssignment)
    (assignment : PartsAssignment) : Bool :=
  path.any fun current => current == assignment

/-- Every selected certificate root already occurs in the root-trie path. -/
def PartsRootsInPathB (path roots : List PartsAssignment) : Bool :=
  roots.all (PartsAssignmentInPathB path)

lemma partsRootsInPathB_sound {coloring : Fin 481 → Fin 4} {path roots}
    (hcheck : PartsRootsInPathB path roots = true)
    (hextends : PartsExtends coloring path) : PartsExtends coloring roots := by
  rw [PartsRootsInPathB, List.all_eq_true] at hcheck
  intro assignment hin
  have hmember := hcheck assignment hin
  rw [PartsAssignmentInPathB, List.any_eq_true] at hmember
  rcases hmember with ⟨current, hcurrent, heq⟩
  rw [beq_iff_eq] at heq
  subst current
  exact hextends assignment hcurrent

/-- Executable checker for the finite root-case trie. -/
def PartsRootVerifiesNodeB (nodes : Array (Array PartsRootNode)) :
    Nat → List PartsAssignment → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, path, index =>
      match partsRootNodeAt nodes index with
      | none => false
      | some (.leaf base symmetry swap) =>
          PartsRootsInPathB path
            (partsTransformPath symmetry swap (partsBaseCertificate base).roots)
      | some (.branch vertex children) =>
          partsColors.all fun color =>
            PartsBlocksB path vertex color ||
              match partsRootChild children color with
              | none => false
              | some child =>
                  PartsRootVerifiesNodeB nodes fuel
                    (⟨vertex, color⟩ :: path) child

lemma partsRootVerifiesNodeB_unsat {nodes : Array (Array PartsRootNode)}
    {coloring : Fin 481 → Fin 4} (hproper : PartsProper coloring) :
    ∀ {fuel path index}, PartsRootVerifiesNodeB nodes fuel path index = true →
      PartsExtends coloring path → False := by
  intro fuel
  induction fuel with
  | zero =>
      intro path index hverify _
      simp [PartsRootVerifiesNodeB] at hverify
  | succ fuel ih =>
      intro path index hverify hextends
      simp only [PartsRootVerifiesNodeB] at hverify
      split at hverify
      · contradiction
      · rename_i base symmetry swap hnode
        have hroots := partsRootsInPathB_sound hverify hextends
        exact partsCertificateVariant_not_colorable
          (partsCertificateVariant_verifies base symmetry swap) hproper hroots
      · rename_i vertex children hnode
        rw [List.all_eq_true] at hverify
        have hcolor := hverify (coloring vertex)
          (mem_partsColors (coloring vertex))
        rw [Bool.or_eq_true] at hcolor
        rcases hcolor with hblocked | hnext
        · exact (not_partsBlocks_of_proper hproper path hextends vertex)
            (partsBlocksB_eq_true.mp hblocked)
        · simp only [partsRootChild] at hnext
          split at hnext
          · contradiction
          · rename_i child hchild
            apply ih hnext
            intro assignment hin
            simp only [List.mem_cons] at hin
            rcases hin with rfl | hin
            · rfl
            · exact hextends assignment hin

/-- The four fixed assignments after color normalization. -/
def partsNormalizedRootPath : List PartsAssignment :=
  [⟨0, 3⟩, ⟨195, 0⟩, ⟨205, 0⟩, ⟨215, 0⟩]

/-- A checked root trie eliminates every proper coloring extending the fixed root. -/
theorem partsRootDecision_not_colorable (nodes : Array (Array PartsRootNode))
    (nodeCount : Nat)
    (hverify : PartsRootVerifiesNodeB nodes (nodeCount + 1)
      partsNormalizedRootPath 0 = true)
    {coloring : Fin 481 → Fin 4} (hproper : PartsProper coloring)
    (hroots : PartsExtends coloring partsNormalizedRootPath) : False := by
  exact partsRootVerifiesNodeB_unsat hproper hverify hroots

end HadwigerNelsonBounds
