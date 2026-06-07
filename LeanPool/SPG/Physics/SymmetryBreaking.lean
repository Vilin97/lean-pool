/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Algebra.Actions

namespace SPG.Physics

def get_mpg (group_elements : List SPGElement) (orientation : Vec3) : List SPGElement :=
  group_elements.filter (fun g =>
    let v_prime := magnetic_action g orientation
    v_prime == orientation
  )

def allows_z_polarization (mpg : List SPGElement) : Bool :=
  let z_axis : Vec3 := ![0, 0, 1]
  mpg.all (fun g =>
    let v_prime := electric_action g z_axis
    v_prime == z_axis
  )

end SPG.Physics
