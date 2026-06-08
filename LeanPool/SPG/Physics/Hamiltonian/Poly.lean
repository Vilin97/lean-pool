/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Algebra.Basic
import LeanPool.SPG.Algebra.Group
import LeanPool.SPG.Geometry.SpatialOps
import LeanPool.SPG.Geometry.SpinOps
import LeanPool.SPG.Interface.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.List.Basic

/-!
# Multivariate rational polynomials in momentum

This module implements a normalized sparse representation of multivariate
rational polynomials in the three momentum components `kx, ky, kz`, together
with their ring operations, the spin point group action on polynomials, degree
enumeration, coordinate extraction, and a complex extension `CPoly`.
-/

namespace SPG.Physics.Hamiltonian

open SPG
open SPG.Geometry.SpatialOps
open SPG.Geometry.SpinOps
open SPG.Interface
open SPG.Algebra

/-- A monomial exponent `(i, j, k)` standing for `kx^i * ky^j * kz^k`. -/
abbrev Exp3 := Nat × (Nat × Nat)

/-- Exp Compare. -/
def expCompare (a b : Exp3) : Ordering :=
  let ax := a.1
  let ay := a.2.1
  let az := a.2.2
  let bx := b.1
  let bY := b.2.1
  let bz := b.2.2
  match compare ax bx with
  | .eq =>
    match compare ay bY with
    | .eq => compare az bz
    | o => o
  | o => o

/-- Exp Add. -/
def expAdd (a b : Exp3) : Exp3 :=
  (a.1 + b.1, (a.2.1 + b.2.1, a.2.2 + b.2.2))

/-- Exp Var. -/
def expVar : Fin 3 → Exp3
  | ⟨0, _⟩ => (1, (0, 0))
  | ⟨1, _⟩ => (0, (1, 0))
  | _      => (0, (0, 1))

/-- Insert Term. -/
def insertTerm (t : Exp3 × ℚ) : List (Exp3 × ℚ) → List (Exp3 × ℚ)
  | [] =>
    if t.2 = 0 then [] else [t]
  | (e', a') :: rest =>
    match expCompare t.1 e' with
    | .lt =>
      if t.2 = 0 then (e', a') :: rest else t :: (e', a') :: rest
    | .eq =>
      let a := t.2 + a'
      if a = 0 then rest else (e', a) :: rest
    | .gt =>
      (e', a') :: insertTerm t rest

/-- Norm Terms. -/
def normTerms (ts : List (Exp3 × ℚ)) : List (Exp3 × ℚ) :=
  ts.foldl (fun acc t => insertTerm t acc) []

/-- A multivariate rational polynomial in `kx, ky, kz`, stored as a normalized
sparse list of (exponent, coefficient) pairs. -/
structure Poly where
  /-- The nonzero terms, each an exponent paired with its rational coefficient. -/
  terms : List (Exp3 × ℚ)
  deriving DecidableEq

/-- Mk'. -/
def Poly.mk' (ts : List (Exp3 × ℚ)) : Poly :=
  ⟨normTerms ts⟩

/-- Add. -/
def Poly.add (p q : Poly) : Poly :=
  Poly.mk' (p.terms ++ q.terms)

/-- Neg. -/
def Poly.neg (p : Poly) : Poly :=
  Poly.mk' (p.terms.map fun (e, a) => (e, -a))

/-- Sub. -/
def Poly.sub (p q : Poly) : Poly :=
  Poly.add p (Poly.neg q)

/-- Mul. -/
def Poly.mul (p q : Poly) : Poly :=
  Poly.mk' <|
    p.terms.flatMap fun (e₁, a₁) =>
      q.terms.map fun (e₂, a₂) => (expAdd e₁ e₂, a₁ * a₂)

/-- Pow. -/
def Poly.pow (p : Poly) : Nat → Poly
  | 0 => Poly.mk' [((0, (0, 0)), 1)]
  | n + 1 => Poly.mul (Poly.pow p n) p

instance : OfNat Poly 0 := ⟨Poly.mk' []⟩
instance : OfNat Poly 1 := ⟨Poly.mk' [((0, (0, 0)), 1)]⟩
instance : Add Poly := ⟨Poly.add⟩
instance : Neg Poly := ⟨Poly.neg⟩
instance : Sub Poly := ⟨Poly.sub⟩
instance : Mul Poly := ⟨Poly.mul⟩
instance : Pow Poly Nat := ⟨Poly.pow⟩

/-- C. -/
def C (a : ℚ) : Poly :=
  Poly.mk' [((0, (0, 0)), a)]

/-- K Var. -/
def kVar (i : Fin 3) : Poly :=
  Poly.mk' [(expVar i, 1)]

/-- Kx. -/
def kx : Poly := kVar 0
/-- Ky. -/
def ky : Poly := kVar 1
/-- Kz. -/
def kz : Poly := kVar 2

/-- K Action Sign. -/
def kActionSign (g : SPGElement) : ℚ :=
  if g.spin == spinNegI then -1 else 1

/-- Linear Poly. -/
def linearPoly (coeffs : Vec3) : Poly :=
  (C (coeffs 0)) * kx + (C (coeffs 1)) * ky + (C (coeffs 2)) * kz

/-- Monom Eval. -/
def monomEval (subst : Fin 3 → Poly) (e : Exp3) : Poly :=
  let ex := e.1
  let ey := e.2.1
  let ez := e.2.2
  (subst 0) ^ ex * (subst 1) ^ ey * (subst 2) ^ ez

/-- Eval Subst. -/
def evalSubst (subst : Fin 3 → Poly) (p : Poly) : Poly :=
  p.terms.foldl (fun acc (e, a) => acc + (C a) * monomEval subst e) 0

/-- Poly Action. -/
def polyAction (g : SPGElement) (p : Poly) : Poly :=
  let subst : Fin 3 → Poly :=
    fun i =>
      linearPoly fun j => (kActionSign g) * g.spatial i j
  evalSubst subst p

/-- Degree Of. -/
def degreeOf (e : Exp3) : Nat := e.1 + e.2.1 + e.2.2

/-- Monomials Of Degree. -/
def monomialsOfDegree (d : Nat) : List Exp3 :=
  (List.range (d + 1)).foldl (fun acc x =>
    acc ++ (List.range (d - x + 1)).map (fun y => (x, (y, d - x - y)))
  ) []

/-- Poly Of Exp. -/
def polyOfExp (e : Exp3) : Poly :=
  let ex := e.1
  let ey := e.2.1
  let ez := e.2.2
  (kx ^ ex) * (ky ^ ey) * (kz ^ ez)

/-- Basis Polys Of Degree. -/
def basisPolysOfDegree (d : Nat) : List Poly :=
  (monomialsOfDegree d).map polyOfExp

/-- Is Zero Poly. -/
def isZeroPoly (p : Poly) : Bool := p.terms.isEmpty

/-- Coeff Of Poly. -/
def coeffOfPoly (p : Poly) (e : Exp3) : ℚ :=
  match p.terms.find? (fun t => t.1 = e) with
  | some (_, a) => a
  | none => 0

/-- Poly Coords. -/
def polyCoords (es : List Exp3) (p : Poly) : List ℚ :=
  es.map (coeffOfPoly p)

/-- Linear combination `∑ᵢ coeffs[i] · monomial(exps[i])` of monomials. -/
def lincombPoly (exps : List Exp3) (coeffs : List ℚ) : Poly :=
  go exps 0 0
where
  /-- Fold over the exponents, accumulating the coefficient-weighted monomials. -/
  go (es : List Exp3) (i : Nat) (acc : Poly) : Poly :=
    match es with
    | [] => acc
    | e :: rest =>
      go rest (i + 1) (acc + (C (coeffs.getD i 0)) * polyOfExp e)

/-- Linear combination of monomials reading coefficients starting at `offset`. -/
def lincombPolyOffset (exps : List Exp3) (coeffs : List ℚ) (offset : Nat) : Poly :=
  go exps 0 0
where
  /-- Fold over the exponents, reading coefficients from `offset + i`. -/
  go (es : List Exp3) (i : Nat) (acc : Poly) : Poly :=
    match es with
    | [] => acc
    | e :: rest =>
      go rest (i + 1) (acc + (C (coeffs.getD (offset + i) 0)) * polyOfExp e)

/-- Exp To String. -/
def expToString (e : Exp3) : String :=
  let ex := e.1
  let ey := e.2.1
  let ez := e.2.2
  let part (name : String) (n : Nat) : String :=
    if n = 0 then "" else if n = 1 then name else s!"{name}^{n}"
  let parts := [part "kx" ex, part "ky" ey, part "kz" ez].filter (fun s => s ≠ "")
  if parts.isEmpty then "1" else String.intercalate " " parts

/-- Poly To String. -/
def polyToString (p : Poly) : String :=
  if p.terms.isEmpty then "0"
  else
    let ts := p.terms.map (fun (e, a) =>
      let m := expToString e
      if m = "1" then s!"{a}"
      else if a = 1 then m
      else if a = -1 then s!"-{m}"
      else s!"{a}*{m}"
    )
    String.intercalate " + " ts

/-- A complex polynomial, represented by its real and imaginary parts. -/
structure CPoly where
  /-- The real part. -/
  re : Poly
  /-- The imaginary part. -/
  im : Poly
  deriving DecidableEq

/-- Mk'. -/
def CPoly.mk' (re im : Poly) : CPoly := ⟨re, im⟩

/-- Add. -/
def CPoly.add (p q : CPoly) : CPoly := ⟨p.re + q.re, p.im + q.im⟩
/-- Neg. -/
def CPoly.neg (p : CPoly) : CPoly := ⟨-p.re, -p.im⟩
/-- Sub. -/
def CPoly.sub (p q : CPoly) : CPoly := CPoly.add p (CPoly.neg q)

/-- Mul. -/
def CPoly.mul (p q : CPoly) : CPoly :=
  ⟨p.re * q.re - p.im * q.im, p.re * q.im + p.im * q.re⟩

/-- Pow. -/
def CPoly.pow (p : CPoly) : Nat → CPoly
  | 0 => ⟨1, 0⟩
  | n + 1 => CPoly.mul (CPoly.pow p n) p

instance : OfNat CPoly 0 := ⟨⟨0, 0⟩⟩
instance : OfNat CPoly 1 := ⟨⟨1, 0⟩⟩
instance : Add CPoly := ⟨CPoly.add⟩
instance : Neg CPoly := ⟨CPoly.neg⟩
instance : Sub CPoly := ⟨CPoly.sub⟩
instance : Mul CPoly := ⟨CPoly.mul⟩
instance : Pow CPoly Nat := ⟨CPoly.pow⟩

/-- C C. -/
def cC (a : ℚ) : CPoly := ⟨C a, 0⟩
/-- C I. -/
def cI : CPoly := ⟨0, 1⟩

/-- Cconj. -/
def cconj (p : CPoly) : CPoly := ⟨p.re, -p.im⟩

/-- Cpoly Action. -/
def cpolyAction (g : SPGElement) (p : CPoly) : CPoly :=
  let q : CPoly := ⟨polyAction g p.re, polyAction g p.im⟩
  if g.spin == spinNegI then cconj q else q

/-- Is Zero Cpoly. -/
def isZeroCpoly (p : CPoly) : Bool := isZeroPoly p.re && isZeroPoly p.im

/-- Cpoly Coords. -/
def cpolyCoords (es : List Exp3) (p : CPoly) : List ℚ :=
  polyCoords es p.re ++ polyCoords es p.im

/-- Lincomb Cpoly Offset. -/
def lincombCpolyOffset (exps : List Exp3) (coeffs : List ℚ) (offset : Nat) : CPoly :=
  let n := exps.length
  ⟨lincombPolyOffset exps coeffs offset, lincombPolyOffset exps coeffs (offset + n)⟩

/-- Cpoly To String. -/
def cpolyToString (p : CPoly) : String :=
  if isZeroPoly p.im then
    polyToString p.re
  else if isZeroPoly p.re then
    s!"i*({polyToString p.im})"
  else
    s!"({polyToString p.re}) + i*({polyToString p.im})"

/-- Is Invariant C Poly. -/
def isInvariantCPoly (group : List SPGElement) (p : CPoly) : Bool :=
  group.all fun g => decide (cpolyAction g p = p)

end SPG.Physics.Hamiltonian
