/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.RichChipBridge
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.RichW5Aggregation

/-!
# The divisor denoted by a rich row-proof leaf

This module isolates the representation-independent divisor and degree
calculation from the closed-face soundness assembly.
-/

@[expose] public section

namespace Utilities.Subdivision.ClosedRowProof

open Utilities

open MarkedGraphs.Certificate
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral

namespace RichWitness

variable {m n p : ℕ}

/-- The divisor denoted by a rich witness on a particular closed face: raw
core coefficients are pushed to quotient classes and raw chip forms are
evaluated at their physical subdivision positions. -/
def richDivisor
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) (w : RichWitness)
    (fallback : Fin n) (x : List ℤ) : CFDiv d.graph :=
  w.richCoreDivisor d + w.rawChipDivisor d
    (fun slot form => evaluatedChipVertex d fallback x slot form)

/-- Evaluation and contraction preserve the witness's declared total degree. -/
theorem deg_richDivisor
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) (w : RichWitness)
    (fallback : Fin n) (x : List ℤ) :
    deg (w.richDivisor d fallback x) =
      (∑ v : Fin n, w.divisorCore.getD v.val 0) +
        (w.chips.map fun chip => chip.2.2).sum := by
  unfold richDivisor
  rw [map_add, w.deg_richCoreDivisor, w.deg_rawChipDivisor]

/-- A finite `getD` sum agrees with the list sum when the list has the
declared core length. -/
theorem sum_getD_eq_list_sum (xs : List ℤ) (n : ℕ) (hLength : xs.length = n) :
    (∑ v : Fin n, xs.getD v.val 0) = xs.sum := by
  induction xs generalizing n with
  | nil =>
      subst n
      simp
  | cons z xs ih =>
      cases n with
      | zero => simp at hLength
      | succ n =>
          simp only [List.length_cons] at hLength
          have hTail : xs.length = n := by omega
          rw [Fin.sum_univ_succ]
          change z + (∑ v : Fin n, xs.getD v.val 0) = z + xs.sum
          rw [ih n hTail]

/-- W7 turns the representation-independent degree calculation into the
degree declared by the rich leaf. -/
theorem deg_richDivisor_eq_declared {degree : ℤ}
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (fallback : Fin n) (x : List ℤ)
    (hLength : w.divisorCore.length = n) (hDegree :
      w.divisorCore.foldl (· + ·) 0 +
        w.chips.foldl (fun z c => z + c.2.2) 0 = degree) :
    deg (w.richDivisor d fallback x) = degree := by
  rw [w.deg_richDivisor, sum_getD_eq_list_sum w.divisorCore n hLength]
  rw [List.sum_eq_foldl, List.sum_eq_foldl, List.foldl_map]
  exact hDegree

end RichWitness

end Utilities.Subdivision.ClosedRowProof
