/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Algebra.Actions

/-!
# Symmetry breaking and magnetic point groups

This module computes the magnetic point group fixing a given order-parameter
orientation and decides whether the resulting group permits a nonzero electric
polarization along the `z` axis.
-/

namespace SPG.Physics

/-- The magnetic point group: the subset of group elements fixing the given
magnetic order-parameter orientation. -/
def getMpg (group_elements : List SPGElement) (orientation : Vec3) : List SPGElement :=
  group_elements.filter (fun g =>
    let v_prime := magneticAction g orientation
    v_prime == orientation
  )

/-- Decide whether a magnetic point group permits a nonzero electric
polarization along the `z` axis. -/
def allowsZPolarization (mpg : List SPGElement) : Bool :=
  let z_axis : Vec3 := ![0, 0, 1]
  mpg.all (fun g =>
    let v_prime := electricAction g z_axis
    v_prime == z_axis
  )

end SPG.Physics
