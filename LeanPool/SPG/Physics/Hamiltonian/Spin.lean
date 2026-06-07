/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Algebra.Basic
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

inductive SpinComp
| I | x | y | z
deriving Repr, DecidableEq, Inhabited

def act_on_k (g : SPGElement) (k : Vec3) : Vec3 :=
  let k_rot := Matrix.mulVec g.spatial k
  if g.spin == spin_neg_I then
    -k_rot
  else
    k_rot

def act_on_spin (g : SPGElement) (s : SpinComp) : Vec3 :=
  let s_vec : Vec3 := match s with
    | .x => ![1, 0, 0]
    | .y => ![0, 1, 0]
    | .z => ![0, 0, 1]
    | .I => ![0, 0, 0]

  if s == .I then ![0, 0, 0]
  else
    let detR := Matrix.det g.spatial
    let rotated := Matrix.mulVec g.spatial s_vec
    let axial_rotated := detR • rotated

    if g.spin == spin_neg_I then
      -axial_rotated
    else
      axial_rotated

def project_spin (v : Vec3) (target : SpinComp) : ℚ :=
  match target with
  | .x => v 0
  | .y => v 1
  | .z => v 2
  | .I => 0

def spinCompOfFin (i : Fin 3) : SpinComp :=
  match i.val with
  | 0 => .x
  | 1 => .y
  | _ => .z

def spinActionMat (g : SPGElement) : Matrix (Fin 3) (Fin 3) ℚ :=
  fun j i => (act_on_spin g (spinCompOfFin i)) j

end SPG.Physics.Hamiltonian
