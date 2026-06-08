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

/-!
# Spin components and their transformations

This module introduces the `SpinComp` enumeration of spin components and the
actions of spin point group elements on momentum vectors and spin components,
including the spin action matrix.
-/

namespace SPG.Physics.Hamiltonian

open SPG
open SPG.Geometry.SpatialOps
open SPG.Geometry.SpinOps
open SPG.Interface

/-- A spin component: the identity `I` or one of the three Pauli directions
`x, y, z`. -/
inductive SpinComp
| I | x | y | z
deriving Repr, DecidableEq, Inhabited

/-- Action of a spin point group element on a momentum vector `k`, flipping its
sign under a time-reversal (spin-reversal) operation. -/
def actOnK (g : SPGElement) (k : Vec3) : Vec3 :=
  let k_rot := Matrix.mulVec g.spatial k
  if g.spin == spinNegI then
    -k_rot
  else
    k_rot

/-- Act On Spin. -/
def actOnSpin (g : SPGElement) (s : SpinComp) : Vec3 :=
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
    if g.spin == spinNegI then
      -axial_rotated
    else
      axial_rotated

/-- Project Spin. -/
def projectSpin (v : Vec3) (target : SpinComp) : ℚ :=
  match target with
  | .x => v 0
  | .y => v 1
  | .z => v 2
  | .I => 0

/-- Spin Comp Of Fin. -/
def spinCompOfFin (i : Fin 3) : SpinComp :=
  match i.val with
  | 0 => .x
  | 1 => .y
  | _ => .z

/-- Spin Action Mat. -/
def spinActionMat (g : SPGElement) : Matrix (Fin 3) (Fin 3) ℚ :=
  fun j i => (actOnSpin g (spinCompOfFin i)) j

end SPG.Physics.Hamiltonian
