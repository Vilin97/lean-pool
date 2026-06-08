/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Physics.Hamiltonian.Poly
import LeanPool.SPG.Physics.Hamiltonian.Spin
import LeanPool.SPG.Physics.Hamiltonian.Ham
import LeanPool.SPG.Physics.Hamiltonian.LinearAlgebra

/-!
# Symmetry-allowed Hamiltonian invariants

This module enumerates the symmetry-allowed k·p Hamiltonian terms of a spin
point group.  It builds the fixed-point linear systems for scalar and vector
(spin) invariants up to a given degree, solves them via the nullspace
computation, and assembles the independent Hermitian invariants.
-/

namespace SPG.Physics.Hamiltonian

open SPG
open SPG.Geometry.SpatialOps
open SPG.Geometry.SpinOps
open SPG.Interface
open SPG.Algebra

/-- Spin Blocks. -/
def spinBlocks : List SpinComp := [.I, .x, .y, .z]

/-- Cpoly Parts Of Exp. -/
def cpolyPartsOfExp (e : Exp3) : List CPoly :=
  let p := polyOfExp e
  [⟨p, 0⟩, ⟨0, p⟩]

/-- A low-order monomial in the momentum components used as a Hamiltonian
prefactor: the constant, the three linear terms, and the six quadratic terms. -/
inductive PolyTerm
| const
| x | y | z
| xx | yy | zz | xy | yz | zx
deriving Repr, DecidableEq, Inhabited

/-- Eval Poly. -/
def evalPoly (p : PolyTerm) (k : Vec3) : ℚ :=
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

/-- All Polys. -/
def allPolys : List PolyTerm := [.const, .x, .y, .z, .xx, .yy, .zz, .xy, .yz, .zx]

/-- Poly Of Term. -/
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

/-- Decide whether the single term `polynomial · spin` is invariant under the
whole group. -/
def checkInvariant (group : List SPGElement) (p : PolyTerm) (s : SpinComp) : Bool :=
  isInvariantHam group (singleTerm (polyOfTerm p) s)

/-- Enumerate the low-order polynomial and spin terms that form
symmetry-allowed Hamiltonian invariants of the group. -/
def findInvariants (group : List SPGElement) : List (PolyTerm × SpinComp) :=
  let terms := (allPolys.product [.I, .x, .y, .z])
  let simple_invariants := terms.filter fun (p, s) => checkInvariant group p s
  simple_invariants

/-- Analyze Term Symmetry. -/
def analyzeTermSymmetry (group : List SPGElement) (f : SPG.Vec3 → ℚ)
    (s : SpinComp) (f_name : String) (s_name : String) : IO Unit := do
  IO.println s!"\n  Analyzing term: {f_name} * {s_name}"
  let test_k : SPG.Vec3 := ![1, 2, 3]
  let val_k := f test_k
  let elements_to_check := group.take 8
  let mut i := 0
  for g in elements_to_check do
    let val_gk := f (actOnK g test_k)
    let s_prime := actOnSpin g s
    let coeff := projectSpin s_prime s
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
      let spinLabel := if g.spin == spinNegI then "-I (Time Reversal)" else "I"
      IO.println s!"      g{i} spin: {spinLabel}"
      IO.println s!"      k -> g k: {repr test_k} -> {repr (actOnK g test_k)}"
      IO.println s!"      f(k) = {val_k}, f(g k) = {val_gk}"
      let spinImage := if s == .I then "I" else s!"{repr s_prime}"
      IO.println s!"      σ -> g σ g⁻¹: {s_name} -> {spinImage}"
      IO.println s!"      Factor from spin rot: {coeff}"
      IO.println s!"      Check: {val_gk} * {coeff} ?= {val_k} => {transformed_val == val_k}"
      if !is_eigen then
        IO.println
          s!"      (Spin mixing occurred: {repr s_prime} is not parallel to {s_name})"
    i := i + 1

/-- Project Poly. -/
def projectPoly (group : List SPGElement) (p : Poly) : Poly :=
  let n : ℚ := group.length
  let invN : ℚ := if n = 0 then 0 else 1 / n
  let acc := group.foldl (fun acc g => acc + polyAction g p) 0
  (C invN) * acc

/-- Poly Fixed Rows. -/
def polyFixedRows (group : List SPGElement) (d : Nat) : Nat × List Exp3 × List (List ℚ) :=
  let exps := monomialsOfDegree d
  let n := exps.length
  let basisPolys : List Poly := exps.map (fun e => polyOfExp e)
  let rows :=
    group.foldl (fun acc g =>
      let images : List Poly := basisPolys.map (fun p => polyAction g p)
      acc ++ (List.range n).map (fun i =>
        (List.range n).map (fun j =>
          let pi := images.getD j 0
          match listGet exps i with
          | none => 0
          | some ei => coeffOfPoly pi ei - (if i = j then (1 : ℚ) else 0)
        )
      )
    ) []
  (n, exps, rows)

/-- Ham Fixed Rows. -/
def hamFixedRows (group : List SPGElement) (d : Nat) : Nat × List Exp3 × List (List ℚ) :=
  let exps := monomialsOfDegree d
  let n := exps.length
  let size := spinBlocks.length * n
  let zeroHam : KPHam := { scalar := 0, vector := fun _ => 0 }
  let basisHam : List KPHam :=
    (List.range size).map (fun idx =>
      let comp := idx / n
      let mi := idx % n
      match listGet exps mi with
      | none => zeroHam
      | some e =>
        let p := polyOfExp e
        match listGet spinBlocks comp with
        | none => zeroHam
        | some s => singleTerm p s
    )
  let hamCoeff (H : KPHam) (blk : Nat) (e : Exp3) : ℚ :=
    match listGet spinBlocks blk with
    | some .I => coeffOfPoly H.scalar e
    | some .x => coeffOfPoly (H.vector 0) e
    | some .y => coeffOfPoly (H.vector 1) e
    | some .z => coeffOfPoly (H.vector 2) e
    | none => 0
  let rows :=
    group.foldl (fun acc g =>
      let images : List KPHam := basisHam.map (fun h => transformHam g h)
      acc ++ (List.range size).map (fun i =>
        let compI := i / n
        let mi := i % n
        match listGet exps mi with
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

/-- Invariants Scalar By Degree Solve. -/
def invariantsScalarByDegreeSolve (group : List SPGElement) (dmax : Nat) :
    List (Nat × List Poly) :=
  (List.range (dmax + 1)).map (fun d =>
    let (n, exps, rows) := polyFixedRows group d
    let sols :=
      if group.length = 0 then
        (List.range n).map (fun j =>
          (List.range n).map (fun i => if i = j then (1 : ℚ) else 0)
        )
      else
        nullspaceBasis rows n
    (d, sols.map (lincombPoly exps))
  )

/-- Invariants Vector By Degree Solve. -/
def invariantsVectorByDegreeSolve (group : List SPGElement) (dmax : Nat) :
    List (Nat × List KPHam) :=
  (List.range (dmax + 1)).map (fun d =>
    let (n, exps, rows) := hamFixedRows group d
    let sols :=
      if group.length = 0 then
        (List.range n).map (fun j =>
          (List.range n).map (fun i => if i = j then (1 : ℚ) else 0)
        )
      else
        nullspaceBasis rows n
    (d, sols.map (lincombHam exps))
  )

/-- Invariants Scalar By Degree. -/
def invariantsScalarByDegree (group : List SPGElement) (dmax : Nat) : List (Nat × List Poly) :=
  (List.range (dmax + 1)).map (fun d =>
    let es := monomialsOfDegree d
    let basis := es.map polyOfExp
    let projected := basis.map (projectPoly group)
    let nonzero := projected.filter (fun p => !isZeroPoly p)
    let rows := nonzero.map (fun p => (polyCoords es p, p))
    let indep := independentSubset rows
    (d, indep)
  )

/-- Invariants Vector By Degree. -/
def invariantsVectorByDegree (group : List SPGElement) (dmax : Nat) : List (Nat × List KPHam) :=
  (List.range (dmax + 1)).map (fun d =>
    let es := monomialsOfDegree d
    let basis := es.map polyOfExp
    let seeds : List KPHam :=
      spinBlocks.foldl (fun acc s => acc ++ basis.map (fun p => singleTerm p s)) []
    let projected := seeds.map (projectHam group)
    let nonzero := projected.filter (fun H => !isZeroHam H)
    let rows := nonzero.map (fun H => (hamCoords es H, H))
    let indep := independentSubset rows
    (d, indep)
  )

/-- Cham Fixed Rows. -/
def chamFixedRows (group : List SPGElement) (d : Nat) : Nat × List Exp3 × List (List ℚ) :=
  let exps := monomialsOfDegree d
  let n := exps.length
  let compCount := spinBlocks.length * cpolyPartCount
  let size := compCount * n
  let zeroHam : CKPHam := { scalar := 0, vector := fun _ => 0 }
  let basisHam : List CKPHam :=
    (List.range size).map (fun idx =>
      let comp := idx / n
      let mi := idx % n
      match listGet exps mi with
      | none => zeroHam
      | some e =>
        let blk := comp / cpolyPartCount
        let part := comp % cpolyPartCount
        let parts := cpolyPartsOfExp e
        match listGet spinBlocks blk, listGet parts part with
        | some s, some p => csingleTerm p s
        | _, _ => zeroHam
    )
  let cpolyCoeff (p : CPoly) (part : Nat) (e : Exp3) : ℚ :=
    match listGet [p.re, p.im] part with
    | none => 0
    | some q => coeffOfPoly q e
  let hamCoeff (H : CKPHam) (comp : Nat) (e : Exp3) : ℚ :=
    let blk := comp / cpolyPartCount
    let part := comp % cpolyPartCount
    match listGet spinBlocks blk with
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
        match listGet exps mi with
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

/-- Invariants Vector By Degree Solve C. -/
def invariantsVectorByDegreeSolveC (group : List SPGElement) (dmax : Nat) :
    List (Nat × List CKPHam) :=
  (List.range (dmax + 1)).map (fun d =>
    let (size, exps, rows) := chamFixedRows group d
    let sols :=
      if group.length = 0 then
        (List.range size).map (fun j =>
          (List.range size).map (fun i => if i = j then (1 : ℚ) else 0)
        )
      else
        nullspaceBasis rows size
    (d, sols.map (lincombCham exps))
  )

/-- Lincomb Cpoly. -/
def lincombCpoly (exps : List Exp3) (coeffs : List ℚ) : CPoly :=
  lincombCpolyOffset exps coeffs 0

/-- Cpoly Fixed Rows. -/
def cpolyFixedRows (group : List SPGElement) (d : Nat) : Nat × List Exp3 × List (List ℚ) :=
  let exps := monomialsOfDegree d
  let n := exps.length
  let size := cpolyPartCount * n
  let basisPolys : List CPoly :=
    (List.range size).map (fun idx =>
      let part := idx / n
      let mi := idx % n
      match listGet exps mi with
      | none => 0
      | some e =>
        let parts := cpolyPartsOfExp e
        match listGet parts part with
        | none => 0
        | some p => p
    )
  let cpolyCoeff (p : CPoly) (part : Nat) (e : Exp3) : ℚ :=
    match listGet [p.re, p.im] part with
    | none => 0
    | some q => coeffOfPoly q e
  let rows :=
    group.foldl (fun acc g =>
      let images : List CPoly := basisPolys.map (fun p => cpolyAction g p)
      acc ++ (List.range size).map (fun i =>
        let partI := i / n
        let mi := i % n
        match listGet exps mi with
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

/-- Invariants Scalar By Degree Solve C. -/
def invariantsScalarByDegreeSolveC (group : List SPGElement) (dmax : Nat) :
    List (Nat × List CPoly) :=
  (List.range (dmax + 1)).map (fun d =>
    let (size, exps, rows) := cpolyFixedRows group d
    let sols :=
      if group.length = 0 then
        (List.range size).map (fun j =>
          (List.range size).map (fun i => if i = j then (1 : ℚ) else 0)
        )
      else
        nullspaceBasis rows size
    (d, sols.map (lincombCpoly exps))
  )

/-- Group From Laue Magnetic. -/
def groupFromLaueMagnetic (laue_gens mag_gens : List SPGElement) : List SPGElement :=
  combineGenerators laue_gens mag_gens

/-- Hermitian Invariants Vector By Degree Solve C. -/
def hermitianInvariantsVectorByDegreeSolveC (group : List SPGElement)
    (dmax : Nat) : List (Nat × List CKPHam) :=
  let blocks := invariantsVectorByDegreeSolveC group dmax
  (List.range (dmax + 1)).map (fun d =>
    let exps := monomialsOfDegree d
    let hs :=
      match blocks.find? (fun p => p.fst = d) with
      | none => []
      | some (_, hs) => hs
    let projected := hs.map projectHermitianCHam
    let nonzero := projected.filter (fun H => !isZeroCham H)
    let rows := nonzero.map (fun H => (chamCoords exps H, H))
    let indep := independentSubset rows
    (d, indep)
  )

/-- Invariants Vector By Degree Solve From Gens. -/
def invariantsVectorByDegreeSolveFromGens (laue_gens mag_gens : List SPGElement)
    (dmax : Nat) : List (Nat × List KPHam) :=
  invariantsVectorByDegreeSolve (groupFromLaueMagnetic laue_gens mag_gens) dmax

/-- Allowed Cham By Degree From Gens. -/
def allowedChamByDegreeFromGens (laue_gens mag_gens : List SPGElement)
    (dmax : Nat) : List (Nat × List CKPHam) :=
  hermitianInvariantsVectorByDegreeSolveC
    (groupFromLaueMagnetic laue_gens mag_gens) dmax

end SPG.Physics.Hamiltonian
