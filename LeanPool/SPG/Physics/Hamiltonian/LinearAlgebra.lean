/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.List.Basic

/-!
# Rational linear algebra helpers

This module provides list-based rational vector arithmetic, row reduction,
reduced row echelon bases, and nullspace computation used to solve for
symmetry-allowed Hamiltonian invariants.
-/

namespace SPG.Physics.Hamiltonian

/-- Add Vec. -/
def addVec (v w : List ℚ) : List ℚ := List.zipWith (· + ·) v w
/-- Smul Vec. -/
def smulVec (a : ℚ) (v : List ℚ) : List ℚ := v.map (fun x => a * x)
/-- Sub Vec. -/
def subVec (v w : List ℚ) : List ℚ := addVec v (smulVec (-1) w)

/-- Index and value of the first nonzero entry of a rational row, if any. -/
def pivotIndex (v : List ℚ) : Option (Nat × ℚ) :=
  go v 0
where
  /-- Scan from position `i`, returning the first nonzero entry with its index. -/
  go (xs : List ℚ) (i : Nat) : Option (Nat × ℚ) :=
    match xs with
    | [] => none
    | x :: rest => if x = 0 then go rest (i + 1) else some (i, x)

/-- Reduce Row. -/
def reduceRow (row : List ℚ) (basis : List (Nat × List ℚ)) : List ℚ :=
  basis.foldl (fun r (p, b) =>
    let c := r.getD p 0
    subVec r (smulVec c b)
  ) row

/-- Greedily select the rows whose pivots are linearly independent, returning the
associated tags. -/
def independentSubset {α : Type} (rows : List (List ℚ × α)) : List α :=
  go rows [] []
where
  /-- Accumulate independent rows, tracking the current reduced basis. -/
  go (todo : List (List ℚ × α)) (basis : List (Nat × List ℚ))
      (acc : List α) : List α :=
    match todo with
    | [] => acc.reverse
    | (r, a) :: rest =>
      let r' := reduceRow r basis
      match pivotIndex r' with
      | none => go rest basis acc
      | some (p, c) =>
        let rNorm := smulVec (1 / c) r'
        go rest ((p, rNorm) :: basis) (a :: acc)

/-- Rref Basis. -/
def rrefBasis (rows : List (List ℚ)) : List (Nat × List ℚ) :=
  rows.foldl (fun (basis : List (Nat × List ℚ)) row =>
    let r0 := reduceRow row basis
    match pivotIndex r0 with
    | none => basis
    | some (p, c) =>
      let rNorm := smulVec (1 / c) r0
      let basis' :=
        basis.map (fun (p2, r2) =>
          let c2 := r2.getD p 0
          (p2, subVec r2 (smulVec c2 rNorm))
        )
      (p, rNorm) :: basis'
  ) []

/-- Free Cols. -/
def freeCols (ncols : Nat) (pivots : List Nat) : List Nat :=
  (List.range ncols).filter (fun j => !(pivots.contains j))

/-- Nullspace Basis. -/
def nullspaceBasis (rows : List (List ℚ)) (ncols : Nat) : List (List ℚ) :=
  let basis := rrefBasis rows
  let pivots := basis.map (fun pr => pr.1)
  let frees := freeCols ncols pivots
  frees.map (fun f =>
    (List.range ncols).map (fun j =>
      if j = f then (1 : ℚ)
      else
        match basis.find? (fun pr => pr.1 = j) with
        | none => 0
        | some (_, r) => -(r.getD f 0)
    )
  )

/-- List Get?. -/
def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, n + 1 => listGet? as n

end SPG.Physics.Hamiltonian
