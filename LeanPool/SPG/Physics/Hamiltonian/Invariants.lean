/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Physics.Hamiltonian.Poly
import LeanPool.SPG.Physics.Hamiltonian.Spin
import LeanPool.SPG.Physics.Hamiltonian.Ham
import LeanPool.SPG.Physics.Hamiltonian.LinearAlgebra

namespace SPG.Physics.Hamiltonian

open SPG
open SPG.Geometry.SpatialOps
open SPG.Geometry.SpinOps
open SPG.Interface
open SPG.Algebra

def spinBlocks : List SpinComp := [.I, .x, .y, .z]

def cpolyPartsOfExp (e : Exp3) : List CPoly :=
  let p := poly_of_exp e
  [⟨p, 0⟩, ⟨0, p⟩]

inductive PolyTerm
| const
| x | y | z
| xx | yy | zz | xy | yz | zx
deriving Repr, DecidableEq, Inhabited

def eval_poly (p : PolyTerm) (k : Vec3) : ℚ :=
  match p with
  | .const => 1
  | .x => k 0
  | .y => k 1
  | .z => k 2
  | .xx => k 0 * k 0
  | .yy => k 1 * k 1
  | .zz => k 2 * k 2
  | .xy => k 0 * k 1
  | .yz => k 1 * k 2
  | .zx => k 2 * k 0

def all_polys : List PolyTerm := [.const, .x, .y, .z, .xx, .yy, .zz, .xy, .yz, .zx]

def polyOfTerm : PolyTerm → Poly
  | .const => 1
  | .x => kx
  | .y => ky
  | .z => kz
  | .xx => kx * kx
  | .yy => ky * ky
  | .zz => kz * kz
  | .xy => kx * ky
  | .yz => ky * kz
  | .zx => kz * kx

def check_invariant (group : List SPGElement) (p : PolyTerm) (s : SpinComp) : Bool :=
  isInvariantHam group (singleTerm (polyOfTerm p) s)

def find_invariants (group : List SPGElement) : List (PolyTerm × SpinComp) :=
  let terms := (all_polys.product [.I, .x, .y, .z])
  let simple_invariants := terms.filter fun (p, s) => check_invariant group p s
  simple_invariants

def analyze_term_symmetry (group : List SPGElement) (f : SPG.Vec3 → ℚ) (s : SpinComp) (f_name : String)
    (s_name : String) : IO Unit := do
  IO.println s!"\n  Analyzing term: {f_name} * {s_name}"
  let test_k : SPG.Vec3 := ![1, 2, 3]
  let val_k := f test_k

  let elements_to_check := group.take 8

  let mut i := 0
  for g in elements_to_check do
    let val_gk := f (act_on_k g test_k)

    let s_prime := act_on_spin g s
    let coeff := project_spin s_prime s

    let is_eigen :=
             (s == .x && s_prime 1 == 0 && s_prime 2 == 0) ||
             (s == .y && s_prime 0 == 0 && s_prime 2 == 0) ||
             (s == .z && s_prime 0 == 0 && s_prime 1 == 0) ||
             (s == .I)

    let transformed_val := val_gk * coeff
    let invariant := is_eigen && (transformed_val == val_k)

    if !invariant then
      IO.println s!"    [Broken by g{i}]"
      IO.println s!"      g{i} spatial: {repr g.spatial}"
      IO.println s!"      g{i} spin: {if g.spin == spin_neg_I then "-I (Time Reversal)" else "I"}"
      IO.println s!"      k -> g k: {repr test_k} -> {repr (act_on_k g test_k)}"
      IO.println s!"      f(k) = {val_k}, f(g k) = {val_gk}"
      IO.println s!"      σ -> g σ g⁻¹: {s_name} -> {if s == .I then "I" else s!"{repr s_prime}"}"
      IO.println s!"      Factor from spin rot: {coeff}"
      IO.println s!"      Check: {val_gk} * {coeff} ?= {val_k} => {transformed_val == val_k}"
      if !is_eigen then
        IO.println s!"      (Spin mixing occurred: {repr s_prime} is not parallel to {s_name})"

    i := i + 1

def project_poly (group : List SPGElement) (p : Poly) : Poly :=
  let n : ℚ := group.length
  let invN : ℚ := if n = 0 then 0 else 1 / n
  let acc := group.foldl (fun acc g => acc + polyAction g p) 0
  (C invN) * acc

def poly_fixed_rows (group : List SPGElement) (d : Nat) : Nat × List Exp3 × List (List ℚ) :=
  let exps := monomials_of_degree d
  let n := exps.length
  let basisPolys : List Poly := exps.map (fun e => poly_of_exp e)
  let rows :=
    group.foldl (fun acc g =>
      let images : List Poly := basisPolys.map (fun p => polyAction g p)
      acc ++ (List.range n).map (fun i =>
        (List.range n).map (fun j =>
          let pi := images.getD j 0
          match list_get? exps i with
          | none => 0
          | some ei => coeff_of_poly pi ei - (if i = j then (1 : ℚ) else 0)
        )
      )
    ) []
  (n, exps, rows)

def ham_fixed_rows (group : List SPGElement) (d : Nat) : Nat × List Exp3 × List (List ℚ) :=
  let exps := monomials_of_degree d
  let n := exps.length
  let size := spinBlocks.length * n
  let zeroHam : KPHam := { scalar := 0, vector := fun _ => 0 }
  let basisHam : List KPHam :=
    (List.range size).map (fun idx =>
      let comp := idx / n
      let mi := idx % n
      match list_get? exps mi with
      | none => zeroHam
      | some e =>
        let p := poly_of_exp e
        match list_get? spinBlocks comp with
        | none => zeroHam
        | some s => singleTerm p s
    )
  let hamCoeff (H : KPHam) (blk : Nat) (e : Exp3) : ℚ :=
    match list_get? spinBlocks blk with
    | some .I => coeff_of_poly H.scalar e
    | some .x => coeff_of_poly (H.vector 0) e
    | some .y => coeff_of_poly (H.vector 1) e
    | some .z => coeff_of_poly (H.vector 2) e
    | none => 0
  let rows :=
    group.foldl (fun acc g =>
      let images : List KPHam := basisHam.map (fun h => transformHam g h)
      acc ++ (List.range size).map (fun i =>
        let compI := i / n
        let mi := i % n
        match list_get? exps mi with
        | none => (List.range size).map (fun _ => 0)
        | some e =>
          (List.range size).map (fun j =>
            let Hj := images.getD j zeroHam
            let a := hamCoeff Hj compI e
            a - (if i = j then (1 : ℚ) else 0)
          )
      )
    ) []
  (size, exps, rows)

def invariants_scalar_by_degree_solve (group : List SPGElement) (dmax : Nat) : List (Nat × List Poly) :=
  (List.range (dmax + 1)).map (fun d =>
    let (n, exps, rows) := poly_fixed_rows group d
    let sols :=
      if group.length = 0 then
        (List.range n).map (fun j =>
          (List.range n).map (fun i => if i = j then (1 : ℚ) else 0)
        )
      else
        nullspace_basis rows n
    (d, sols.map (lincomb_poly exps))
  )

def invariants_vector_by_degree_solve (group : List SPGElement) (dmax : Nat) : List (Nat × List KPHam) :=
  (List.range (dmax + 1)).map (fun d =>
    let (n, exps, rows) := ham_fixed_rows group d
    let sols :=
      if group.length = 0 then
        (List.range n).map (fun j =>
          (List.range n).map (fun i => if i = j then (1 : ℚ) else 0)
        )
      else
        nullspace_basis rows n
    (d, sols.map (lincomb_ham exps))
  )

def invariants_scalar_by_degree (group : List SPGElement) (dmax : Nat) : List (Nat × List Poly) :=
  (List.range (dmax + 1)).map (fun d =>
    let es := monomials_of_degree d
    let basis := es.map poly_of_exp
    let projected := basis.map (project_poly group)
    let nonzero := projected.filter (fun p => !is_zero_poly p)
    let rows := nonzero.map (fun p => (poly_coords es p, p))
    let indep := independent_subset rows
    (d, indep)
  )

def invariants_vector_by_degree (group : List SPGElement) (dmax : Nat) : List (Nat × List KPHam) :=
  (List.range (dmax + 1)).map (fun d =>
    let es := monomials_of_degree d
    let basis := es.map poly_of_exp
    let seeds : List KPHam :=
      spinBlocks.foldl (fun acc s => acc ++ basis.map (fun p => singleTerm p s)) []
    let projected := seeds.map (project_ham group)
    let nonzero := projected.filter (fun H => !is_zero_ham H)
    let rows := nonzero.map (fun H => (ham_coords es H, H))
    let indep := independent_subset rows
    (d, indep)
  )

def cham_fixed_rows (group : List SPGElement) (d : Nat) : Nat × List Exp3 × List (List ℚ) :=
  let exps := monomials_of_degree d
  let n := exps.length
  let compCount := spinBlocks.length * cpolyPartCount
  let size := compCount * n
  let zeroHam : CKPHam := { scalar := 0, vector := fun _ => 0 }
  let basisHam : List CKPHam :=
    (List.range size).map (fun idx =>
      let comp := idx / n
      let mi := idx % n
      match list_get? exps mi with
      | none => zeroHam
      | some e =>
        let blk := comp / cpolyPartCount
        let part := comp % cpolyPartCount
        let parts := cpolyPartsOfExp e
        match list_get? spinBlocks blk, list_get? parts part with
        | some s, some p => csingleTerm p s
        | _, _ => zeroHam
    )
  let cpolyCoeff (p : CPoly) (part : Nat) (e : Exp3) : ℚ :=
    match list_get? [p.re, p.im] part with
    | none => 0
    | some q => coeff_of_poly q e
  let hamCoeff (H : CKPHam) (comp : Nat) (e : Exp3) : ℚ :=
    let blk := comp / cpolyPartCount
    let part := comp % cpolyPartCount
    match list_get? spinBlocks blk with
    | some .I => cpolyCoeff H.scalar part e
    | some .x => cpolyCoeff (H.vector 0) part e
    | some .y => cpolyCoeff (H.vector 1) part e
    | some .z => cpolyCoeff (H.vector 2) part e
    | none => 0
  let rows :=
    group.foldl (fun acc g =>
      let images : List CKPHam := basisHam.map (fun h => ctransformHam g h)
      acc ++ (List.range size).map (fun i =>
        let compI := i / n
        let mi := i % n
        match list_get? exps mi with
        | none => (List.range size).map (fun _ => 0)
        | some e =>
          (List.range size).map (fun j =>
            let Hj := images.getD j zeroHam
            let a := hamCoeff Hj compI e
            a - (if i = j then (1 : ℚ) else 0)
          )
      )
    ) []
  (size, exps, rows)

def invariants_vector_by_degree_solveC (group : List SPGElement) (dmax : Nat) : List (Nat × List CKPHam) :=
  (List.range (dmax + 1)).map (fun d =>
    let (size, exps, rows) := cham_fixed_rows group d
    let sols :=
      if group.length = 0 then
        (List.range size).map (fun j =>
          (List.range size).map (fun i => if i = j then (1 : ℚ) else 0)
        )
      else
        nullspace_basis rows size
    (d, sols.map (lincomb_cham exps))
  )

def lincomb_cpoly (exps : List Exp3) (coeffs : List ℚ) : CPoly :=
  lincomb_cpoly_offset exps coeffs 0

def cpoly_fixed_rows (group : List SPGElement) (d : Nat) : Nat × List Exp3 × List (List ℚ) :=
  let exps := monomials_of_degree d
  let n := exps.length
  let size := cpolyPartCount * n
  let basisPolys : List CPoly :=
    (List.range size).map (fun idx =>
      let part := idx / n
      let mi := idx % n
      match list_get? exps mi with
      | none => 0
      | some e =>
        let parts := cpolyPartsOfExp e
        match list_get? parts part with
        | none => 0
        | some p => p
    )
  let cpolyCoeff (p : CPoly) (part : Nat) (e : Exp3) : ℚ :=
    match list_get? [p.re, p.im] part with
    | none => 0
    | some q => coeff_of_poly q e
  let rows :=
    group.foldl (fun acc g =>
      let images : List CPoly := basisPolys.map (fun p => cpolyAction g p)
      acc ++ (List.range size).map (fun i =>
        let partI := i / n
        let mi := i % n
        match list_get? exps mi with
        | none => (List.range size).map (fun _ => 0)
        | some e =>
          (List.range size).map (fun j =>
            let pj := images.getD j 0
            let a := cpolyCoeff pj partI e
            a - (if i = j then (1 : ℚ) else 0)
          )
      )
    ) []
  (size, exps, rows)

def invariants_scalar_by_degree_solveC (group : List SPGElement) (dmax : Nat) : List (Nat × List CPoly) :=
  (List.range (dmax + 1)).map (fun d =>
    let (size, exps, rows) := cpoly_fixed_rows group d
    let sols :=
      if group.length = 0 then
        (List.range size).map (fun j =>
          (List.range size).map (fun i => if i = j then (1 : ℚ) else 0)
        )
      else
        nullspace_basis rows size
    (d, sols.map (lincomb_cpoly exps))
  )

def group_from_laue_magnetic (laue_gens mag_gens : List SPGElement) : List SPGElement :=
  combine_generators laue_gens mag_gens

def hermitian_invariants_vector_by_degree_solveC (group : List SPGElement) (dmax : Nat) : List (Nat × List CKPHam) :=
  let blocks := invariants_vector_by_degree_solveC group dmax
  (List.range (dmax + 1)).map (fun d =>
    let exps := monomials_of_degree d
    let hs :=
      match blocks.find? (fun p => p.fst = d) with
      | none => []
      | some (_, hs) => hs
    let projected := hs.map project_hermitianCHam
    let nonzero := projected.filter (fun H => !is_zero_cham H)
    let rows := nonzero.map (fun H => (cham_coords exps H, H))
    let indep := independent_subset rows
    (d, indep)
  )

def invariants_vector_by_degree_solve_from_gens (laue_gens mag_gens : List SPGElement) (dmax : Nat) : List (Nat × List KPHam) :=
  invariants_vector_by_degree_solve (group_from_laue_magnetic laue_gens mag_gens) dmax

def allowed_cham_by_degree_from_gens (laue_gens mag_gens : List SPGElement) (dmax : Nat) : List (Nat × List CKPHam) :=
  hermitian_invariants_vector_by_degree_solveC (group_from_laue_magnetic laue_gens mag_gens) dmax

end SPG.Physics.Hamiltonian
