/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Algebra.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Rat
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace SPG

def magnetic_action (g : SPGElement) (v : Vec3) : Vec3 :=
  let detR := Matrix.det g.spatial
  let rotated := Matrix.mulVec g.spatial v
  Matrix.mulVec g.spin (detR • rotated)

def electric_action (g : SPGElement) (v : Vec3) : Vec3 :=
  Matrix.mulVec g.spatial v

end SPG
