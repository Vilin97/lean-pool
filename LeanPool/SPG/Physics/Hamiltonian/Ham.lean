/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Physics.Hamiltonian.Poly
import LeanPool.SPG.Physics.Hamiltonian.Spin

/-!
# k·p Hamiltonian terms

This module defines the `KPHam` and complex `CKPHam` structures of k·p
Hamiltonian terms (a scalar plus a spin vector of polynomials), the spin point
group action on them, invariance and projection operators, Hermitian
projection, and coordinate/printing helpers.
-/

namespace SPG.Physics.Hamiltonian

open SPG

/-- A k·p Hamiltonian term: a scalar polynomial (coefficient of the identity
spin matrix) together with a polynomial coefficient for each Pauli component. -/
structure KPHam where
  /-- Coefficient of the identity spin matrix. -/
  scalar : Poly
  /-- Coefficients of the three Pauli spin matrices `σx, σy, σz`. -/
  vector : Fin 3 → Poly
  deriving DecidableEq

/-- Zero Vec. -/
def zeroVec : Fin 3 → Poly := 0

/-- Single Term. -/
def singleTerm (p : Poly) (s : SpinComp) : KPHam :=
  match s with
  | .I => { scalar := p, vector := zeroVec }
  | .x => { scalar := 0, vector := fun j => if j = 0 then p else 0 }
  | .y => { scalar := 0, vector := fun j => if j = 1 then p else 0 }
  | .z => { scalar := 0, vector := fun j => if j = 2 then p else 0 }

/-- Transform Ham. -/
def transformHam (g : SPGElement) (H : KPHam) : KPHam :=
  let vecSubst : Fin 3 → Poly := fun i => polyAction g (H.vector i)
  let A := spinActionMat g
  let vec' : Fin 3 → Poly := fun j =>
    (C (A j 0)) * (vecSubst 0) + (C (A j 1)) * (vecSubst 1) + (C (A j 2)) * (vecSubst 2)
  { scalar := polyAction g H.scalar, vector := vec' }

/-- Decide whether a k·p Hamiltonian term is invariant under every element of
the spin point group. -/
def isInvariantHam (group : List SPGElement) (H : KPHam) : Bool :=
  group.all fun g => decide (transformHam g H = H)

/-- Project Ham. -/
def projectHam (group : List SPGElement) (H : KPHam) : KPHam :=
  let n : ℚ := group.length
  let invN : ℚ := if n = 0 then 0 else 1 / n
  let acc : KPHam :=
    group.foldl (fun (acc : KPHam) g =>
        let Hg := transformHam g H
        { scalar := acc.scalar + Hg.scalar,
          vector := fun j => acc.vector j + Hg.vector j })
      ({ scalar := 0, vector := fun _ => 0 } : KPHam)
  { scalar := (C invN) * acc.scalar, vector := fun j => (C invN) * acc.vector j }

/-- Ham Add. -/
def hamAdd (H1 H2 : KPHam) : KPHam :=
  { scalar := H1.scalar + H2.scalar, vector := fun j => H1.vector j + H2.vector j }

/-- Ham Smul. -/
def hamSmul (a : ℚ) (H : KPHam) : KPHam :=
  { scalar := (C a) * H.scalar, vector := fun j => (C a) * H.vector j }

/-- Is Zero Ham. -/
def isZeroHam (H : KPHam) : Bool :=
  isZeroPoly H.scalar &&
    (isZeroPoly (H.vector 0)) &&
    (isZeroPoly (H.vector 1)) &&
    (isZeroPoly (H.vector 2))

/-- Ham Coords. -/
def hamCoords (es : List Exp3) (H : KPHam) : List ℚ :=
  polyCoords es H.scalar ++
    polyCoords es (H.vector 0) ++
    polyCoords es (H.vector 1) ++
    polyCoords es (H.vector 2)

/-- Ham Block Offset. -/
def hamBlockOffset (block n : Nat) : Nat := block * n

/-- Lincomb Ham. -/
def lincombHam (exps : List Exp3) (coeffs : List ℚ) : KPHam :=
  let n := exps.length
  let scalar := lincombPolyOffset exps coeffs (hamBlockOffset 0 n)
  let vx := lincombPolyOffset exps coeffs (hamBlockOffset 1 n)
  let vy := lincombPolyOffset exps coeffs (hamBlockOffset 2 n)
  let vz := lincombPolyOffset exps coeffs (hamBlockOffset 3 n)
  { scalar := scalar, vector := fun j => if j = 0 then vx else if j = 1 then vy else vz }

/-- Ham To String. -/
def hamToString (H : KPHam) : String :=
  let parts :=
    (if !isZeroPoly H.scalar then [s!"({polyToString H.scalar})*I"] else []) ++
    (if !isZeroPoly (H.vector 0) then [s!"({polyToString (H.vector 0)})*σx"] else []) ++
    (if !isZeroPoly (H.vector 1) then [s!"({polyToString (H.vector 1)})*σy"] else []) ++
    (if !isZeroPoly (H.vector 2) then [s!"({polyToString (H.vector 2)})*σz"] else [])
  if parts.isEmpty then "0" else String.intercalate " + " parts

/-- A complex k·p Hamiltonian term: the complex analogue of `KPHam` with
complex polynomial coefficients. -/
structure CKPHam where
  /-- Complex coefficient of the identity spin matrix. -/
  scalar : CPoly
  /-- Complex coefficients of the three Pauli spin matrices. -/
  vector : Fin 3 → CPoly
  deriving DecidableEq

/-- C Of Poly. -/
def cOfPoly (p : Poly) : CPoly := ⟨p, 0⟩

/-- C Of Ham. -/
def cOfHam (H : KPHam) : CKPHam :=
  { scalar := cOfPoly H.scalar, vector := fun j => cOfPoly (H.vector j) }

/-- Re Of C Poly. -/
def reOfCPoly (p : CPoly) : Poly := p.re
/-- Im Of C Poly. -/
def imOfCPoly (p : CPoly) : Poly := p.im

/-- Re Of C Ham. -/
def reOfCHam (H : CKPHam) : KPHam :=
  { scalar := reOfCPoly H.scalar, vector := fun j => reOfCPoly (H.vector j) }

/-- Im Of C Ham. -/
def imOfCHam (H : CKPHam) : KPHam :=
  { scalar := imOfCPoly H.scalar, vector := fun j => imOfCPoly (H.vector j) }

/-- Czero Vec. -/
def czeroVec : Fin 3 → CPoly := 0

/-- Csingle Term. -/
def csingleTerm (p : CPoly) (s : SpinComp) : CKPHam :=
  match s with
  | .I => { scalar := p, vector := czeroVec }
  | .x => { scalar := 0, vector := fun j => if j = 0 then p else 0 }
  | .y => { scalar := 0, vector := fun j => if j = 1 then p else 0 }
  | .z => { scalar := 0, vector := fun j => if j = 2 then p else 0 }

/-- Ctransform Ham. -/
def ctransformHam (g : SPGElement) (H : CKPHam) : CKPHam :=
  let vecSubst : Fin 3 → CPoly := fun i => cpolyAction g (H.vector i)
  let A := spinActionMat g
  let vec' : Fin 3 → CPoly := fun j =>
    (cC (A j 0)) * (vecSubst 0) + (cC (A j 1)) * (vecSubst 1) + (cC (A j 2)) * (vecSubst 2)
  { scalar := cpolyAction g H.scalar, vector := vec' }

/-- Is Invariant C Ham. -/
def isInvariantCHam (group : List SPGElement) (H : CKPHam) : Bool :=
  group.all fun g => decide (ctransformHam g H = H)

/-- Cproject Ham. -/
def cprojectHam (group : List SPGElement) (H : CKPHam) : CKPHam :=
  let n : ℚ := group.length
  let invN : ℚ := if n = 0 then 0 else 1 / n
  let acc : CKPHam :=
    group.foldl (fun (acc : CKPHam) g =>
        let Hg := ctransformHam g H
        { scalar := acc.scalar + Hg.scalar,
          vector := fun j => acc.vector j + Hg.vector j })
      ({ scalar := 0, vector := fun _ => 0 } : CKPHam)
  { scalar := (cC invN) * acc.scalar, vector := fun j => (cC invN) * acc.vector j }

/-- Cham Add. -/
def chamAdd (H1 H2 : CKPHam) : CKPHam :=
  { scalar := H1.scalar + H2.scalar, vector := fun j => H1.vector j + H2.vector j }

/-- Cham Smul. -/
def chamSmul (a : ℚ) (H : CKPHam) : CKPHam :=
  { scalar := (cC a) * H.scalar, vector := fun j => (cC a) * H.vector j }

/-- Cherm Conj. -/
def chermConj (H : CKPHam) : CKPHam :=
  { scalar := cconj H.scalar, vector := fun j => cconj (H.vector j) }

/-- Is Hermitian C Ham. -/
def isHermitianCHam (H : CKPHam) : Bool :=
  decide (chermConj H = H)

/-- Project Hermitian C Ham. -/
def projectHermitianCHam (H : CKPHam) : CKPHam :=
  chamSmul ((1 : ℚ) / 2) (chamAdd H (chermConj H))

/-- Is Zero Cham. -/
def isZeroCham (H : CKPHam) : Bool :=
  isZeroCpoly H.scalar &&
    (isZeroCpoly (H.vector 0)) &&
    (isZeroCpoly (H.vector 1)) &&
    (isZeroCpoly (H.vector 2))

/-- Cham Coords. -/
def chamCoords (es : List Exp3) (H : CKPHam) : List ℚ :=
  cpolyCoords es H.scalar ++
    cpolyCoords es (H.vector 0) ++
    cpolyCoords es (H.vector 1) ++
    cpolyCoords es (H.vector 2)

/-- Cpoly Part Count. -/
def cpolyPartCount : Nat := 2

/-- Cham Block Offset. -/
def chamBlockOffset (block n : Nat) : Nat := block * cpolyPartCount * n

/-- Lincomb Cham. -/
def lincombCham (exps : List Exp3) (coeffs : List ℚ) : CKPHam :=
  let n := exps.length
  let scalar := lincombCpolyOffset exps coeffs (chamBlockOffset 0 n)
  let vx := lincombCpolyOffset exps coeffs (chamBlockOffset 1 n)
  let vy := lincombCpolyOffset exps coeffs (chamBlockOffset 2 n)
  let vz := lincombCpolyOffset exps coeffs (chamBlockOffset 3 n)
  { scalar := scalar, vector := fun j => if j = 0 then vx else if j = 1 then vy else vz }

/-- Cham To String. -/
def chamToString (H : CKPHam) : String :=
  let parts :=
    (if !isZeroCpoly H.scalar then [s!"({cpolyToString H.scalar})*I"] else []) ++
    (if !isZeroCpoly (H.vector 0) then [s!"({cpolyToString (H.vector 0)})*σx"] else []) ++
    (if !isZeroCpoly (H.vector 1) then [s!"({cpolyToString (H.vector 1)})*σy"] else []) ++
    (if !isZeroCpoly (H.vector 2) then [s!"({cpolyToString (H.vector 2)})*σz"] else [])
  if parts.isEmpty then "0" else String.intercalate " + " parts

end SPG.Physics.Hamiltonian
