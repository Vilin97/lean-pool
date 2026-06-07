/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.List.Basic

namespace SPG.Physics.Hamiltonian

def add_vec (v w : List ℚ) : List ℚ := List.zipWith (· + ·) v w
def smul_vec (a : ℚ) (v : List ℚ) : List ℚ := v.map (fun x => a * x)
def sub_vec (v w : List ℚ) : List ℚ := add_vec v (smul_vec (-1) w)

def pivot_index (v : List ℚ) : Option (Nat × ℚ) :=
  let rec go (xs : List ℚ) (i : Nat) : Option (Nat × ℚ) :=
    match xs with
    | [] => none
    | x :: rest => if x = 0 then go rest (i + 1) else some (i, x)
  go v 0

def reduce_row (row : List ℚ) (basis : List (Nat × List ℚ)) : List ℚ :=
  basis.foldl (fun r (p, b) =>
    let c := r.getD p 0
    sub_vec r (smul_vec c b)
  ) row

def independent_subset {α : Type} (rows : List (List ℚ × α)) : List α :=
  let rec go (todo : List (List ℚ × α)) (basis : List (Nat × List ℚ)) (acc : List α) : List α :=
    match todo with
    | [] => acc.reverse
    | (r, a) :: rest =>
      let r' := reduce_row r basis
      match pivot_index r' with
      | none => go rest basis acc
      | some (p, c) =>
        let rNorm := smul_vec (1 / c) r'
        go rest ((p, rNorm) :: basis) (a :: acc)
  go rows [] []

def rref_basis (rows : List (List ℚ)) : List (Nat × List ℚ) :=
  rows.foldl (fun (basis : List (Nat × List ℚ)) row =>
    let r0 := reduce_row row basis
    match pivot_index r0 with
    | none => basis
    | some (p, c) =>
      let rNorm := smul_vec (1 / c) r0
      let basis' :=
        basis.map (fun (p2, r2) =>
          let c2 := r2.getD p 0
          (p2, sub_vec r2 (smul_vec c2 rNorm))
        )
      (p, rNorm) :: basis'
  ) []

def free_cols (ncols : Nat) (pivots : List Nat) : List Nat :=
  (List.range ncols).filter (fun j => !(pivots.contains j))

def nullspace_basis (rows : List (List ℚ)) (ncols : Nat) : List (List ℚ) :=
  let basis := rref_basis rows
  let pivots := basis.map (fun pr => pr.1)
  let frees := free_cols ncols pivots
  frees.map (fun f =>
    (List.range ncols).map (fun j =>
      if j = f then (1 : ℚ)
      else
        match basis.find? (fun pr => pr.1 = j) with
        | none => 0
        | some (_, r) => -(r.getD f 0)
    )
  )

def list_get? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, n + 1 => list_get? as n

end SPG.Physics.Hamiltonian
