/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.Certificates

/-! # Fast validation of certificates against packed incidence tables -/

namespace Erdos97Octagon.RawIncidence

/-- Validate the tail of a mutual-edge tree directly against a packed table. -/
def packedExtendsTreeB
    (code : UInt64) (reached : Finset Vertex) : List Vertex → Bool
  | [] => true
  | vertex :: remaining =>
      decide (vertex ∉ reached) &&
        decide (∃ previous ∈ reached,
          packedSelectsB code previous vertex = true ∧
            packedSelectsB code vertex previous = true) &&
        packedExtendsTreeB code (insert vertex reached) remaining

/-- Validate a mutual-edge spanning tree directly against a packed table. -/
def packedComponentTreeB
    (code : UInt64) (root : Vertex) : List Vertex → Bool
  | [] => false
  | first :: remaining =>
      decide (first = root) && packedExtendsTreeB code {root} remaining

private def packedTreeLabelledEdgeB
    (code : UInt64) (component : List Vertex) (a b : Vertex) : Bool :=
  (decide (a ∈ component) && packedSelectsB code a b) ||
    (decide (b ∈ component) && packedSelectsB code b a)

private def packedResidualValidB (code payload : UInt64) : Bool :=
  let classIndex := payloadClass payload
  let forward := decodeMap (payloadForwardCode payload)
  let inverse := decodeMap (payloadInverseCode payload)
  decide (classIndex < 13) &&
    (List.finRange 8).all (fun vertex => decide (inverse (forward vertex) = vertex)) &&
    (List.finRange 8).all (fun vertex => decide (forward (inverse vertex) = vertex)) &&
    (List.finRange 8).all (fun vertex =>
      (List.finRange 8).all (fun target => decide (
        packedSelectsB code vertex target = true ↔
          forward target ∈
            (residualRepresentative (Fin.ofNat 13 classIndex)).targets (forward vertex))))

/-- Kernel-check a certificate without first materializing eight finite sets. -/
def Certificate.validPackedB (code : UInt64) : Certificate → Bool
  | .k4 root component a b c d =>
      packedComponentTreeB code root component && decide [a, b, c, d].Nodup &&
        packedTreeLabelledEdgeB code component a b &&
        packedTreeLabelledEdgeB code component a c &&
        packedTreeLabelledEdgeB code component a d &&
        packedTreeLabelledEdgeB code component b c &&
        packedTreeLabelledEdgeB code component b d &&
        packedTreeLabelledEdgeB code component c d
  | .hubPentagon root component o a b c d e =>
      packedComponentTreeB code root component && decide [o, a, b, c, d, e].Nodup &&
        packedTreeLabelledEdgeB code component o a &&
        packedTreeLabelledEdgeB code component o b &&
        packedTreeLabelledEdgeB code component o c &&
        packedTreeLabelledEdgeB code component o d &&
        packedTreeLabelledEdgeB code component o e &&
        packedTreeLabelledEdgeB code component a b &&
        packedTreeLabelledEdgeB code component b c &&
        packedTreeLabelledEdgeB code component c d &&
        packedTreeLabelledEdgeB code component d e &&
        packedTreeLabelledEdgeB code component e a
  | .sharedThree a b q1 q2 q3 =>
      decide (a ≠ b) && decide (q1 ≠ q2) && decide (q1 ≠ q3) && decide (q2 ≠ q3) &&
        packedSelectsB code a q1 && packedSelectsB code a q2 &&
        packedSelectsB code a q3 && packedSelectsB code b q1 &&
        packedSelectsB code b q2 && packedSelectsB code b q3
  | .cycleStrip root component o x1 x2 x3 x4 x5 x6 =>
      packedComponentTreeB code root component && decide [o, x1, x2, x3, x4, x5, x6].Nodup &&
        packedTreeLabelledEdgeB code component o x1 &&
        packedTreeLabelledEdgeB code component o x2 &&
        packedTreeLabelledEdgeB code component o x6 &&
        packedTreeLabelledEdgeB code component x1 x2 &&
        packedTreeLabelledEdgeB code component x1 x3 &&
        packedTreeLabelledEdgeB code component x2 x3 &&
        packedTreeLabelledEdgeB code component x2 x4 &&
        packedTreeLabelledEdgeB code component x3 x4 &&
        packedTreeLabelledEdgeB code component x3 x5 &&
        packedTreeLabelledEdgeB code component x4 x5 &&
        packedTreeLabelledEdgeB code component x4 x6 &&
        packedTreeLabelledEdgeB code component x5 x6
  | .residual payload => packedResidualValidB code payload

private theorem packedExtendsTreeB_eq (code : UInt64) :
    ∀ reached remaining,
      packedExtendsTreeB code reached remaining =
        extendsTreeB (packedIncidence code) reached remaining := by
  intro reached remaining
  induction remaining generalizing reached with
  | nil => rfl
  | cons vertex remaining induction =>
      simp only [packedExtendsTreeB, extendsTreeB, induction,
        mem_packedIncidence, packedSelectsB]
      rfl

private theorem packedComponentTreeB_eq
    (code : UInt64) (root : Vertex) (component : List Vertex) :
    packedComponentTreeB code root component =
      componentTreeB (packedIncidence code) root component := by
  cases component with
  | nil => rfl
  | cons first remaining =>
      simp only [packedComponentTreeB, componentTreeB, packedExtendsTreeB_eq]

/-- Packed validation supplies the mathematical certificate predicate. -/
theorem Certificate.valid_of_validPackedB
    {code : UInt64} {certificate : Certificate}
    (hvalid : certificate.validPackedB code = true) :
    certificate.Valid (packedIncidence code) := by
  cases certificate with
  | residual payload =>
      simp only [Certificate.validPackedB, packedResidualValidB,
        Bool.and_eq_true] at hvalid
      rcases hvalid with ⟨⟨⟨hclass, hleft⟩, hright⟩, hedges⟩
      refine ⟨of_decide_eq_true hclass, ?_, ?_, ?_⟩
      · intro vertex
        exact of_decide_eq_true
          ((List.all_eq_true.mp hleft) vertex (List.mem_finRange vertex))
      · intro vertex
        exact of_decide_eq_true
          ((List.all_eq_true.mp hright) vertex (List.mem_finRange vertex))
      · intro vertex target
        have hvertex := (List.all_eq_true.mp hedges) vertex
          (List.mem_finRange vertex)
        have htarget := (List.all_eq_true.mp hvertex) target
          (List.mem_finRange target)
        simpa only [mem_packedIncidence] using of_decide_eq_true htarget
  | k4 root component a b c d =>
      simpa only [Certificate.validPackedB, Bool.and_eq_true, decide_eq_true_eq,
        packedTreeLabelledEdgeB, TreeLabelledEdge, Certificate.Valid, Bool.or_eq_true,
        packedComponentTreeB_eq, mem_packedIncidence, and_assoc] using hvalid
  | hubPentagon root component o a b c d e =>
      simpa only [Certificate.validPackedB, Bool.and_eq_true, decide_eq_true_eq,
        packedTreeLabelledEdgeB, TreeLabelledEdge, Certificate.Valid, Bool.or_eq_true,
        packedComponentTreeB_eq, mem_packedIncidence, and_assoc] using hvalid
  | sharedThree a b q1 q2 q3 =>
      simpa only [Certificate.validPackedB, Bool.and_eq_true, decide_eq_true_eq,
        Certificate.Valid, mem_packedIncidence, and_assoc] using hvalid
  | cycleStrip root component o x1 x2 x3 x4 x5 x6 =>
      simpa only [Certificate.validPackedB, Bool.and_eq_true, decide_eq_true_eq,
        packedTreeLabelledEdgeB, TreeLabelledEdge, Certificate.Valid, Bool.or_eq_true,
        packedComponentTreeB_eq, mem_packedIncidence, and_assoc] using hvalid

end Erdos97Octagon.RawIncidence
