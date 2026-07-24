/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsGadgetCertificate

/-!
# Routing between independently checked gadget certificates

Large coloring trees are split into small, default-heartbeat certificates.
This checker verifies that the roots of those certificates cover every
unblocked color branch.  Certificate soundness remains a theorem of Lean,
while each small tree is independently reduced by the kernel.
-/

namespace HadwigerNelsonBounds

/-- A routing node either selects a checked certificate or branches on a color. -/
inductive PartsGadgetCaseNode (certificateCount : Nat) where
  | leaf (certificate : Fin certificateCount)
  | branch (vertex : Fin 73) (children : Fin 4 → Nat)

namespace PartsGadgetCaseNode

/-- Decode zero as no child and `n + 1` as child index `n`. -/
def child {certificateCount : Nat}
    (node : PartsGadgetCaseNode certificateCount)
    (color : Fin 4) : Option Nat :=
  match node with
  | leaf _ => none
  | branch _ children =>
      match children color with
      | 0 => none
      | index + 1 => some index

end PartsGadgetCaseNode

/-- A finite router covering a normalized root path by small certificates. -/
structure PartsGadgetCaseTree (certificateCount : Nat) where
  /-- Fixed normalized assignments shared by every routed case. -/
  roots : List PartsGadgetAssignment
  /-- Number of routing nodes. -/
  nodeCount : Nat
  /-- Branch and certificate-leaf nodes. -/
  nodes : Array (PartsGadgetCaseNode certificateCount)

/-- Check routing, but leave each selected certificate proof as a separate fact. -/
def PartsGadgetCaseVerifiesNodeB {certificateCount : Nat}
    (certificates : Fin certificateCount → PartsGadgetCertificate)
    (nodes : Array (PartsGadgetCaseNode certificateCount)) :
    Nat → List PartsGadgetAssignment → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, path, index =>
      match nodes[index]? with
      | none => false
      | some (PartsGadgetCaseNode.leaf certificate) =>
          decide ((certificates certificate).roots = path)
      | some node@(PartsGadgetCaseNode.branch vertex _) =>
          partsGadgetColors.all fun color =>
            PartsGadgetBlocksB path vertex color ||
              match node.child color with
              | none => false
              | some child =>
                  PartsGadgetCaseVerifiesNodeB certificates nodes fuel
                    (path ++ [⟨vertex, color⟩]) child

/-- The root-routing check for a case tree. -/
def PartsGadgetCaseTree.VerifiesRouting {certificateCount : Nat}
    (tree : PartsGadgetCaseTree certificateCount)
    (certificates : Fin certificateCount → PartsGadgetCertificate) : Prop :=
  PartsGadgetCaseVerifiesNodeB certificates tree.nodes (tree.nodeCount + 1)
    tree.roots 0 = true

instance {certificateCount : Nat} (tree : PartsGadgetCaseTree certificateCount)
    (certificates : Fin certificateCount → PartsGadgetCertificate) :
    Decidable (tree.VerifiesRouting certificates) := by
  unfold PartsGadgetCaseTree.VerifiesRouting
  infer_instance

lemma partsGadgetCaseVerifiesNodeB_unsat {certificateCount : Nat}
    {certificates : Fin certificateCount → PartsGadgetCertificate}
    (hcertificates : ∀ index, (certificates index).Verifies)
    {coloring : Fin 73 → Fin 4} (hvalid : PartsGadgetValid coloring) :
    ∀ {fuel nodes path index},
      PartsGadgetCaseVerifiesNodeB certificates nodes fuel path index = true →
        PartsGadgetExtends coloring path → False := by
  intro fuel
  induction fuel with
  | zero =>
      intro nodes path index hverify _
      simp [PartsGadgetCaseVerifiesNodeB] at hverify
  | succ fuel ih =>
      intro nodes path index hverify hextends
      simp only [PartsGadgetCaseVerifiesNodeB] at hverify
      split at hverify
      · contradiction
      · rename_i certificate hnode
        simp only [decide_eq_true_eq] at hverify
        apply (certificates certificate).not_colorable
          (hcertificates certificate) hvalid
        rw [hverify]
        exact hextends
      · rename_i vertex children hnode
        rw [List.all_eq_true] at hverify
        let color := coloring vertex
        have hcolor := hverify color (mem_partsGadgetColors color)
        rw [Bool.or_eq_true] at hcolor
        rcases hcolor with hblocked | hnext
        · exact (not_partsGadgetBlocks_of_valid hvalid path hextends vertex)
            (partsGadgetBlocksB_eq_true.mp hblocked)
        · simp only [PartsGadgetCaseNode.child] at hnext
          split at hnext
          · contradiction
          · rename_i child hchild
            apply ih hnext
            intro assignment hin
            rw [List.mem_append] at hin
            rcases hin with hin | hin
            · exact hextends assignment hin
            · simp only [List.mem_singleton] at hin
              subst assignment
              rfl

/-- A routed family of verified certificates rules out its normalized roots. -/
theorem PartsGadgetCaseTree.not_colorable {certificateCount : Nat}
    (tree : PartsGadgetCaseTree certificateCount)
    (certificates : Fin certificateCount → PartsGadgetCertificate)
    (hrouting : tree.VerifiesRouting certificates)
    (hcertificates : ∀ index, (certificates index).Verifies)
    {coloring : Fin 73 → Fin 4} (hvalid : PartsGadgetValid coloring)
    (hroots : PartsGadgetExtends coloring tree.roots) : False := by
  exact partsGadgetCaseVerifiesNodeB_unsat hcertificates hvalid hrouting hroots

end HadwigerNelsonBounds
