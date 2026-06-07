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

namespace SPG.Physics.Hamiltonian

open SPG
open SPG.Geometry.SpatialOps
open SPG.Geometry.SpinOps
open SPG.Interface
open SPG.Algebra

abbrev Exp3 := Nat × (Nat × Nat)

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

def expAdd (a b : Exp3) : Exp3 :=
  (a.1 + b.1, (a.2.1 + b.2.1, a.2.2 + b.2.2))

def expVar : Fin 3 → Exp3
  | ⟨0, _⟩ => (1, (0, 0))
  | ⟨1, _⟩ => (0, (1, 0))
  | _      => (0, (0, 1))

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

def normTerms (ts : List (Exp3 × ℚ)) : List (Exp3 × ℚ) :=
  ts.foldl (fun acc t => insertTerm t acc) []

structure Poly where
  terms : List (Exp3 × ℚ)
  deriving DecidableEq, Repr

def Poly.mk' (ts : List (Exp3 × ℚ)) : Poly :=
  ⟨normTerms ts⟩

def Poly.add (p q : Poly) : Poly :=
  Poly.mk' (p.terms ++ q.terms)

def Poly.neg (p : Poly) : Poly :=
  Poly.mk' (p.terms.map fun (e, a) => (e, -a))

def Poly.sub (p q : Poly) : Poly :=
  Poly.add p (Poly.neg q)

def Poly.mul (p q : Poly) : Poly :=
  Poly.mk' <|
    p.terms.flatMap fun (e₁, a₁) =>
      q.terms.map fun (e₂, a₂) => (expAdd e₁ e₂, a₁ * a₂)

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

def C (a : ℚ) : Poly :=
  Poly.mk' [((0, (0, 0)), a)]

def kVar (i : Fin 3) : Poly :=
  Poly.mk' [(expVar i, 1)]

def kx : Poly := kVar 0
def ky : Poly := kVar 1
def kz : Poly := kVar 2

def kActionSign (g : SPGElement) : ℚ :=
  if g.spin == spin_neg_I then -1 else 1

def linearPoly (coeffs : Vec3) : Poly :=
  (C (coeffs 0)) * kx + (C (coeffs 1)) * ky + (C (coeffs 2)) * kz

def monomEval (subst : Fin 3 → Poly) (e : Exp3) : Poly :=
  let ex := e.1
  let ey := e.2.1
  let ez := e.2.2
  (subst 0) ^ ex * (subst 1) ^ ey * (subst 2) ^ ez

def evalSubst (subst : Fin 3 → Poly) (p : Poly) : Poly :=
  p.terms.foldl (fun acc (e, a) => acc + (C a) * monomEval subst e) 0

def polyAction (g : SPGElement) (p : Poly) : Poly :=
  let subst : Fin 3 → Poly :=
    fun i =>
      linearPoly fun j => (kActionSign g) * g.spatial i j
  evalSubst subst p

def degree_of (e : Exp3) : Nat := e.1 + e.2.1 + e.2.2

def monomials_of_degree (d : Nat) : List Exp3 :=
  (List.range (d + 1)).foldl (fun acc x =>
    acc ++ (List.range (d - x + 1)).map (fun y => (x, (y, d - x - y)))
  ) []

def poly_of_exp (e : Exp3) : Poly :=
  let ex := e.1
  let ey := e.2.1
  let ez := e.2.2
  (kx ^ ex) * (ky ^ ey) * (kz ^ ez)

def basis_polys_of_degree (d : Nat) : List Poly :=
  (monomials_of_degree d).map poly_of_exp

def is_zero_poly (p : Poly) : Bool := p.terms.isEmpty

def coeff_of_poly (p : Poly) (e : Exp3) : ℚ :=
  match p.terms.find? (fun t => t.1 = e) with
  | some (_, a) => a
  | none => 0

def poly_coords (es : List Exp3) (p : Poly) : List ℚ :=
  es.map (coeff_of_poly p)

def lincomb_poly (exps : List Exp3) (coeffs : List ℚ) : Poly :=
  let rec go (es : List Exp3) (i : Nat) (acc : Poly) : Poly :=
    match es with
    | [] => acc
    | e :: rest =>
      go rest (i + 1) (acc + (C (coeffs.getD i 0)) * poly_of_exp e)
  go exps 0 0

def lincomb_poly_offset (exps : List Exp3) (coeffs : List ℚ) (offset : Nat) : Poly :=
  let rec go (es : List Exp3) (i : Nat) (acc : Poly) : Poly :=
    match es with
    | [] => acc
    | e :: rest =>
      go rest (i + 1) (acc + (C (coeffs.getD (offset + i) 0)) * poly_of_exp e)
  go exps 0 0

def exp_to_string (e : Exp3) : String :=
  let ex := e.1
  let ey := e.2.1
  let ez := e.2.2
  let part (name : String) (n : Nat) : String :=
    if n = 0 then "" else if n = 1 then name else s!"{name}^{n}"
  let parts := [part "kx" ex, part "ky" ey, part "kz" ez].filter (fun s => s ≠ "")
  if parts.isEmpty then "1" else String.intercalate " " parts

def poly_to_string (p : Poly) : String :=
  if p.terms.isEmpty then "0"
  else
    let ts := p.terms.map (fun (e, a) =>
      let m := exp_to_string e
      if m = "1" then s!"{a}"
      else if a = 1 then m
      else if a = -1 then s!"-{m}"
      else s!"{a}*{m}"
    )
    String.intercalate " + " ts

structure CPoly where
  re : Poly
  im : Poly
  deriving DecidableEq, Repr

def CPoly.mk' (re im : Poly) : CPoly := ⟨re, im⟩

def CPoly.add (p q : CPoly) : CPoly := ⟨p.re + q.re, p.im + q.im⟩
def CPoly.neg (p : CPoly) : CPoly := ⟨-p.re, -p.im⟩
def CPoly.sub (p q : CPoly) : CPoly := CPoly.add p (CPoly.neg q)

def CPoly.mul (p q : CPoly) : CPoly :=
  ⟨p.re * q.re - p.im * q.im, p.re * q.im + p.im * q.re⟩

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

def cC (a : ℚ) : CPoly := ⟨C a, 0⟩
def cI : CPoly := ⟨0, 1⟩

def cconj (p : CPoly) : CPoly := ⟨p.re, -p.im⟩

def cpolyAction (g : SPGElement) (p : CPoly) : CPoly :=
  let q : CPoly := ⟨polyAction g p.re, polyAction g p.im⟩
  if g.spin == spin_neg_I then cconj q else q

def is_zero_cpoly (p : CPoly) : Bool := is_zero_poly p.re && is_zero_poly p.im

def cpoly_coords (es : List Exp3) (p : CPoly) : List ℚ :=
  poly_coords es p.re ++ poly_coords es p.im

def lincomb_cpoly_offset (exps : List Exp3) (coeffs : List ℚ) (offset : Nat) : CPoly :=
  let n := exps.length
  ⟨lincomb_poly_offset exps coeffs offset, lincomb_poly_offset exps coeffs (offset + n)⟩

def cpoly_to_string (p : CPoly) : String :=
  if is_zero_poly p.im then
    poly_to_string p.re
  else if is_zero_poly p.re then
    s!"i*({poly_to_string p.im})"
  else
    s!"({poly_to_string p.re}) + i*({poly_to_string p.im})"

def isInvariantCPoly (group : List SPGElement) (p : CPoly) : Bool :=
  group.all fun g => decide (cpolyAction g p = p)

end SPG.Physics.Hamiltonian
