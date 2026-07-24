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

/-- Rename the vertices and optionally the two free colors of an assignment. -/
def partsTransformAssignment (symmetry : Fin 6) (swap : Bool)
    (assignment : PartsAssignment) : PartsAssignment :=
  { vertex := partsPermuteVertex symmetry assignment.vertex
    color := if swap then partsSwapMiddleColor assignment.color else assignment.color }

/-- Transform a root path without materializing a second copy of its tree. -/
def partsTransformPath (symmetry : Fin 6) (swap : Bool) :
    List PartsAssignment → List PartsAssignment
  | [] => []
  | assignment :: path =>
      partsTransformAssignment symmetry swap assignment ::
        partsTransformPath symmetry swap path

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

/-- One of the 432 symmetry-expanded certificates passes the checker. -/
def PartsCertificateVariantVerifies (base : Fin 36) (symmetry : Fin 6)
    (swap : Bool) : Prop :=
  let certificate := partsBaseCertificate base
  PartsVerifiesVariantNodeB symmetry swap certificate.nodes
    (certificate.nodeCount + 1)
    (partsTransformPath symmetry swap certificate.roots) 0 = true

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
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariant1_0_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 1 0 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant1_1_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 1 1 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant1_2_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 1 2 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant1_3_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 1 3 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant1_4_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 1 4 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant1_5_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 1 5 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariants1_verify (symmetry : Fin 6) (swap : Bool) :
    PartsCertificateVariantVerifies 1 symmetry swap := by
  fin_cases symmetry
  · exact partsCertificateVariant1_0_verify swap
  · exact partsCertificateVariant1_1_verify swap
  · exact partsCertificateVariant1_2_verify swap
  · exact partsCertificateVariant1_3_verify swap
  · exact partsCertificateVariant1_4_verify swap
  · exact partsCertificateVariant1_5_verify swap

theorem partsCertificateVariants2_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 2 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants3_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 3 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants4_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 4 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants5_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 5 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants6_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 6 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants7_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 7 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariant8_0_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 8 0 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant8_1_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 8 1 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant8_2_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 8 2 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant8_3_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 8 3 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant8_4_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 8 4 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant8_5_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 8 5 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariants8_verify (symmetry : Fin 6) (swap : Bool) :
    PartsCertificateVariantVerifies 8 symmetry swap := by
  fin_cases symmetry
  · exact partsCertificateVariant8_0_verify swap
  · exact partsCertificateVariant8_1_verify swap
  · exact partsCertificateVariant8_2_verify swap
  · exact partsCertificateVariant8_3_verify swap
  · exact partsCertificateVariant8_4_verify swap
  · exact partsCertificateVariant8_5_verify swap

theorem partsCertificateVariants9_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 9 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants10_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 10 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants11_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 11 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants12_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 12 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants13_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 13 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants14_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 14 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants15_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 15 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariant16_0_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 16 0 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant16_1_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 16 1 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant16_2_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 16 2 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant16_3_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 16 3 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant16_4_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 16 4 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant16_5_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 16 5 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariants16_verify (symmetry : Fin 6) (swap : Bool) :
    PartsCertificateVariantVerifies 16 symmetry swap := by
  fin_cases symmetry
  · exact partsCertificateVariant16_0_verify swap
  · exact partsCertificateVariant16_1_verify swap
  · exact partsCertificateVariant16_2_verify swap
  · exact partsCertificateVariant16_3_verify swap
  · exact partsCertificateVariant16_4_verify swap
  · exact partsCertificateVariant16_5_verify swap

theorem partsCertificateVariant17_0_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 17 0 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant17_1_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 17 1 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant17_2_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 17 2 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant17_3_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 17 3 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant17_4_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 17 4 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant17_5_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 17 5 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariants17_verify (symmetry : Fin 6) (swap : Bool) :
    PartsCertificateVariantVerifies 17 symmetry swap := by
  fin_cases symmetry
  · exact partsCertificateVariant17_0_verify swap
  · exact partsCertificateVariant17_1_verify swap
  · exact partsCertificateVariant17_2_verify swap
  · exact partsCertificateVariant17_3_verify swap
  · exact partsCertificateVariant17_4_verify swap
  · exact partsCertificateVariant17_5_verify swap

theorem partsCertificateVariants18_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 18 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants19_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 19 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants20_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 20 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants21_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 21 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants22_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 22 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants23_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 23 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariant24_0_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 24 0 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant24_1_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 24 1 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant24_2_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 24 2 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant24_3_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 24 3 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant24_4_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 24 4 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant24_5_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 24 5 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariants24_verify (symmetry : Fin 6) (swap : Bool) :
    PartsCertificateVariantVerifies 24 symmetry swap := by
  fin_cases symmetry
  · exact partsCertificateVariant24_0_verify swap
  · exact partsCertificateVariant24_1_verify swap
  · exact partsCertificateVariant24_2_verify swap
  · exact partsCertificateVariant24_3_verify swap
  · exact partsCertificateVariant24_4_verify swap
  · exact partsCertificateVariant24_5_verify swap

theorem partsCertificateVariant25_0_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 25 0 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant25_1_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 25 1 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant25_2_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 25 2 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant25_3_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 25 3 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant25_4_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 25 4 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant25_5_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 25 5 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariants25_verify (symmetry : Fin 6) (swap : Bool) :
    PartsCertificateVariantVerifies 25 symmetry swap := by
  fin_cases symmetry
  · exact partsCertificateVariant25_0_verify swap
  · exact partsCertificateVariant25_1_verify swap
  · exact partsCertificateVariant25_2_verify swap
  · exact partsCertificateVariant25_3_verify swap
  · exact partsCertificateVariant25_4_verify swap
  · exact partsCertificateVariant25_5_verify swap

theorem partsCertificateVariants26_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 26 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants27_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 27 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants28_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 28 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants29_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 29 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants30_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 30 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants31_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 31 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants32_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 32 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariants33_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 33 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariant34_0_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 34 0 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant34_1_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 34 1 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant34_2_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 34 2 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant34_3_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 34 3 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant34_4_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 34 4 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariant34_5_verify :
    ∀ swap : Bool, PartsCertificateVariantVerifies 34 5 swap := by
  intro swap
  cases swap <;> decide

theorem partsCertificateVariants34_verify (symmetry : Fin 6) (swap : Bool) :
    PartsCertificateVariantVerifies 34 symmetry swap := by
  fin_cases symmetry
  · exact partsCertificateVariant34_0_verify swap
  · exact partsCertificateVariant34_1_verify swap
  · exact partsCertificateVariant34_2_verify swap
  · exact partsCertificateVariant34_3_verify swap
  · exact partsCertificateVariant34_4_verify swap
  · exact partsCertificateVariant34_5_verify swap

theorem partsCertificateVariants35_verify :
    ∀ symmetry : Fin 6, ∀ swap : Bool,
      PartsCertificateVariantVerifies 35 symmetry swap := by
  intro symmetry swap
  fin_cases symmetry <;> cases swap <;> decide

theorem partsCertificateVariant_verifies (base : Fin 36)
    (symmetry : Fin 6) (swap : Bool) :
    PartsCertificateVariantVerifies base symmetry swap := by
  fin_cases base
  · exact partsCertificateVariants0_verify symmetry swap
  · exact partsCertificateVariants1_verify symmetry swap
  · exact partsCertificateVariants2_verify symmetry swap
  · exact partsCertificateVariants3_verify symmetry swap
  · exact partsCertificateVariants4_verify symmetry swap
  · exact partsCertificateVariants5_verify symmetry swap
  · exact partsCertificateVariants6_verify symmetry swap
  · exact partsCertificateVariants7_verify symmetry swap
  · exact partsCertificateVariants8_verify symmetry swap
  · exact partsCertificateVariants9_verify symmetry swap
  · exact partsCertificateVariants10_verify symmetry swap
  · exact partsCertificateVariants11_verify symmetry swap
  · exact partsCertificateVariants12_verify symmetry swap
  · exact partsCertificateVariants13_verify symmetry swap
  · exact partsCertificateVariants14_verify symmetry swap
  · exact partsCertificateVariants15_verify symmetry swap
  · exact partsCertificateVariants16_verify symmetry swap
  · exact partsCertificateVariants17_verify symmetry swap
  · exact partsCertificateVariants18_verify symmetry swap
  · exact partsCertificateVariants19_verify symmetry swap
  · exact partsCertificateVariants20_verify symmetry swap
  · exact partsCertificateVariants21_verify symmetry swap
  · exact partsCertificateVariants22_verify symmetry swap
  · exact partsCertificateVariants23_verify symmetry swap
  · exact partsCertificateVariants24_verify symmetry swap
  · exact partsCertificateVariants25_verify symmetry swap
  · exact partsCertificateVariants26_verify symmetry swap
  · exact partsCertificateVariants27_verify symmetry swap
  · exact partsCertificateVariants28_verify symmetry swap
  · exact partsCertificateVariants29_verify symmetry swap
  · exact partsCertificateVariants30_verify symmetry swap
  · exact partsCertificateVariants31_verify symmetry swap
  · exact partsCertificateVariants32_verify symmetry swap
  · exact partsCertificateVariants33_verify symmetry swap
  · exact partsCertificateVariants34_verify symmetry swap
  · exact partsCertificateVariants35_verify symmetry swap

end HadwigerNelsonBounds
