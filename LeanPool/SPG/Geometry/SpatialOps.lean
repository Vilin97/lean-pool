/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import Mathlib.Data.Matrix.Basic

/-!
# Spatial operation matrices

This module collects the rational `3 × 3` matrices of the common spatial point
operations (inversion, fourfold rotations, twofold rotation, mirror) used to
build spin point groups.
-/

namespace SPG.Geometry.SpatialOps

/-- Mat Inv. -/
def matInv : Matrix (Fin 3) (Fin 3) ℚ := -1

/-- Mat4 Z. -/
def mat4Z : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![0, -1, 0], ![1, 0, 0], ![0, 0, 1]]

/-- Mat4bar Z. -/
def mat4barZ : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![0, 1, 0], ![-1, 0, 0], ![0, 0, -1]]

/-- Mat2 X. -/
def mat2X : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![1, 0, 0], ![0, -1, 0], ![0, 0, -1]]

/-- Mat M Xy. -/
def matMXy : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![0, 1, 0], ![1, 0, 0], ![0, 0, 1]]

end SPG.Geometry.SpatialOps
