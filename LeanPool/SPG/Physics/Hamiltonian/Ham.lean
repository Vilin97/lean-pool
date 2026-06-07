/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Physics.Hamiltonian.Poly
import LeanPool.SPG.Physics.Hamiltonian.Spin

namespace SPG.Physics.Hamiltonian

open SPG

structure KPHam where
  scalar : Poly
  vector : Fin 3 → Poly
  deriving DecidableEq

def zeroVec : Fin 3 → Poly := fun _ => 0

def singleTerm (p : Poly) (s : SpinComp) : KPHam :=
  match s with
  | .I => { scalar := p, vector := zeroVec }
  | .x => { scalar := 0, vector := fun j => if j = 0 then p else 0 }
  | .y => { scalar := 0, vector := fun j => if j = 1 then p else 0 }
  | .z => { scalar := 0, vector := fun j => if j = 2 then p else 0 }

def transformHam (g : SPGElement) (H : KPHam) : KPHam :=
  let vecSubst : Fin 3 → Poly := fun i => polyAction g (H.vector i)
  let A := spinActionMat g
  let vec' : Fin 3 → Poly := fun j =>
    (C (A j 0)) * (vecSubst 0) + (C (A j 1)) * (vecSubst 1) + (C (A j 2)) * (vecSubst 2)
  { scalar := polyAction g H.scalar, vector := vec' }

def isInvariantHam (group : List SPGElement) (H : KPHam) : Bool :=
  group.all fun g => decide (transformHam g H = H)

def project_ham (group : List SPGElement) (H : KPHam) : KPHam :=
  let n : ℚ := group.length
  let invN : ℚ := if n = 0 then 0 else 1 / n
  let acc : KPHam :=
    group.foldl (fun (acc : KPHam) g =>
        let Hg := transformHam g H
        { scalar := acc.scalar + Hg.scalar,
          vector := fun j => acc.vector j + Hg.vector j })
      ({ scalar := 0, vector := fun _ => 0 } : KPHam)
  { scalar := (C invN) * acc.scalar, vector := fun j => (C invN) * acc.vector j }

def ham_add (H1 H2 : KPHam) : KPHam :=
  { scalar := H1.scalar + H2.scalar, vector := fun j => H1.vector j + H2.vector j }

def ham_smul (a : ℚ) (H : KPHam) : KPHam :=
  { scalar := (C a) * H.scalar, vector := fun j => (C a) * H.vector j }

def is_zero_ham (H : KPHam) : Bool :=
  is_zero_poly H.scalar &&
    (is_zero_poly (H.vector 0)) &&
    (is_zero_poly (H.vector 1)) &&
    (is_zero_poly (H.vector 2))

def ham_coords (es : List Exp3) (H : KPHam) : List ℚ :=
  poly_coords es H.scalar ++
    poly_coords es (H.vector 0) ++
    poly_coords es (H.vector 1) ++
    poly_coords es (H.vector 2)

def hamBlockOffset (block n : Nat) : Nat := block * n

def lincomb_ham (exps : List Exp3) (coeffs : List ℚ) : KPHam :=
  let n := exps.length
  let scalar := lincomb_poly_offset exps coeffs (hamBlockOffset 0 n)
  let vx := lincomb_poly_offset exps coeffs (hamBlockOffset 1 n)
  let vy := lincomb_poly_offset exps coeffs (hamBlockOffset 2 n)
  let vz := lincomb_poly_offset exps coeffs (hamBlockOffset 3 n)
  { scalar := scalar, vector := fun j => if j = 0 then vx else if j = 1 then vy else vz }

def ham_to_string (H : KPHam) : String :=
  let parts :=
    (if !is_zero_poly H.scalar then [s!"({poly_to_string H.scalar})*I"] else []) ++
    (if !is_zero_poly (H.vector 0) then [s!"({poly_to_string (H.vector 0)})*σx"] else []) ++
    (if !is_zero_poly (H.vector 1) then [s!"({poly_to_string (H.vector 1)})*σy"] else []) ++
    (if !is_zero_poly (H.vector 2) then [s!"({poly_to_string (H.vector 2)})*σz"] else [])
  if parts.isEmpty then "0" else String.intercalate " + " parts

structure CKPHam where
  scalar : CPoly
  vector : Fin 3 → CPoly
  deriving DecidableEq

def cOfPoly (p : Poly) : CPoly := ⟨p, 0⟩

def cOfHam (H : KPHam) : CKPHam :=
  { scalar := cOfPoly H.scalar, vector := fun j => cOfPoly (H.vector j) }

def reOfCPoly (p : CPoly) : Poly := p.re
def imOfCPoly (p : CPoly) : Poly := p.im

def reOfCHam (H : CKPHam) : KPHam :=
  { scalar := reOfCPoly H.scalar, vector := fun j => reOfCPoly (H.vector j) }

def imOfCHam (H : CKPHam) : KPHam :=
  { scalar := imOfCPoly H.scalar, vector := fun j => imOfCPoly (H.vector j) }

def czeroVec : Fin 3 → CPoly := fun _ => 0

def csingleTerm (p : CPoly) (s : SpinComp) : CKPHam :=
  match s with
  | .I => { scalar := p, vector := czeroVec }
  | .x => { scalar := 0, vector := fun j => if j = 0 then p else 0 }
  | .y => { scalar := 0, vector := fun j => if j = 1 then p else 0 }
  | .z => { scalar := 0, vector := fun j => if j = 2 then p else 0 }

def ctransformHam (g : SPGElement) (H : CKPHam) : CKPHam :=
  let vecSubst : Fin 3 → CPoly := fun i => cpolyAction g (H.vector i)
  let A := spinActionMat g
  let vec' : Fin 3 → CPoly := fun j =>
    (cC (A j 0)) * (vecSubst 0) + (cC (A j 1)) * (vecSubst 1) + (cC (A j 2)) * (vecSubst 2)
  { scalar := cpolyAction g H.scalar, vector := vec' }

def isInvariantCHam (group : List SPGElement) (H : CKPHam) : Bool :=
  group.all fun g => decide (ctransformHam g H = H)

def cproject_ham (group : List SPGElement) (H : CKPHam) : CKPHam :=
  let n : ℚ := group.length
  let invN : ℚ := if n = 0 then 0 else 1 / n
  let acc : CKPHam :=
    group.foldl (fun (acc : CKPHam) g =>
        let Hg := ctransformHam g H
        { scalar := acc.scalar + Hg.scalar,
          vector := fun j => acc.vector j + Hg.vector j })
      ({ scalar := 0, vector := fun _ => 0 } : CKPHam)
  { scalar := (cC invN) * acc.scalar, vector := fun j => (cC invN) * acc.vector j }

def cham_add (H1 H2 : CKPHam) : CKPHam :=
  { scalar := H1.scalar + H2.scalar, vector := fun j => H1.vector j + H2.vector j }

def cham_smul (a : ℚ) (H : CKPHam) : CKPHam :=
  { scalar := (cC a) * H.scalar, vector := fun j => (cC a) * H.vector j }

def cherm_conj (H : CKPHam) : CKPHam :=
  { scalar := cconj H.scalar, vector := fun j => cconj (H.vector j) }

def isHermitianCHam (H : CKPHam) : Bool :=
  decide (cherm_conj H = H)

def project_hermitianCHam (H : CKPHam) : CKPHam :=
  cham_smul ((1 : ℚ) / 2) (cham_add H (cherm_conj H))

def is_zero_cham (H : CKPHam) : Bool :=
  is_zero_cpoly H.scalar &&
    (is_zero_cpoly (H.vector 0)) &&
    (is_zero_cpoly (H.vector 1)) &&
    (is_zero_cpoly (H.vector 2))

def cham_coords (es : List Exp3) (H : CKPHam) : List ℚ :=
  cpoly_coords es H.scalar ++
    cpoly_coords es (H.vector 0) ++
    cpoly_coords es (H.vector 1) ++
    cpoly_coords es (H.vector 2)

def cpolyPartCount : Nat := 2

def chamBlockOffset (block n : Nat) : Nat := block * cpolyPartCount * n

def lincomb_cham (exps : List Exp3) (coeffs : List ℚ) : CKPHam :=
  let n := exps.length
  let scalar := lincomb_cpoly_offset exps coeffs (chamBlockOffset 0 n)
  let vx := lincomb_cpoly_offset exps coeffs (chamBlockOffset 1 n)
  let vy := lincomb_cpoly_offset exps coeffs (chamBlockOffset 2 n)
  let vz := lincomb_cpoly_offset exps coeffs (chamBlockOffset 3 n)
  { scalar := scalar, vector := fun j => if j = 0 then vx else if j = 1 then vy else vz }

def cham_to_string (H : CKPHam) : String :=
  let parts :=
    (if !is_zero_cpoly H.scalar then [s!"({cpoly_to_string H.scalar})*I"] else []) ++
    (if !is_zero_cpoly (H.vector 0) then [s!"({cpoly_to_string (H.vector 0)})*σx"] else []) ++
    (if !is_zero_cpoly (H.vector 1) then [s!"({cpoly_to_string (H.vector 1)})*σy"] else []) ++
    (if !is_zero_cpoly (H.vector 2) then [s!"({cpoly_to_string (H.vector 2)})*σz"] else [])
  if parts.isEmpty then "0" else String.intercalate " + " parts

end SPG.Physics.Hamiltonian
