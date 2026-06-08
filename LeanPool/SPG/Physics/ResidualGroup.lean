/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Algebra.Actions
import LeanPool.SPG.Physics.Hamiltonian.Spin

/-!
# Residual group under an electric field

This module computes the residual subgroup of a spin point group that fixes a
uniform electric-field direction, extracts the sign of the `σz` spin component
under each element, and uses it to decide whether a Gamma-point Zeeman-type
term is symmetry-forbidden.
-/

namespace SPG.Physics

open SPG
open SPG.Physics.Hamiltonian

/-- Residual subgroup under a fixed (uniform) electric-field direction `e` (polar vector). -/
def residualGroup (group_elements : List SPGElement) (e : Vec3) : List SPGElement :=
  group_elements.filter (fun g => decide (electricAction g e = e))

/--
Extract the sign factor `s(g) ∈ {+1,-1}` of `σz` under the minimal collinear assumption:
`g · σz · g⁻¹ = s(g) σz`.

Returns `none` when `σz` is mixed into `σx/σy`, meaning the minimal `σz`-only closure fails.
-/
def sigmaZSign? (g : SPGElement) : Option Int :=
  let v := actOnSpin g .z
  if v 0 = 0 then
    if v 1 = 0 then
      if v 2 = 1 then some 1
      else if v 2 = -1 then some (-1)
      else none
    else none
  else none

/--
Residual-group criterion for forbidding a Gamma-point Zeeman-type term `g(E) σz`:
if the residual group contains any element with `s(g) = -1`, then the term is symmetry-forbidden.
-/
def forbidsGammaZeemanByS (group_elements : List SPGElement) (e : Vec3) : Bool :=
  let gE := residualGroup group_elements e
  gE.any (fun g =>
    match sigmaZSign? g with
    | some (-1) => true
    | _ => false
  )

end SPG.Physics
