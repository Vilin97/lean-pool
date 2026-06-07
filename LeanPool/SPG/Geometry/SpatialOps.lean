/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import Mathlib.Data.Matrix.Basic

namespace SPG.Geometry.SpatialOps

def mat_inv : Matrix (Fin 3) (Fin 3) ℚ := -1

def mat_4_z : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![0, -1, 0], ![1, 0, 0], ![0, 0, 1]]

def mat_4bar_z : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![0, 1, 0], ![-1, 0, 0], ![0, 0, -1]]

def mat_2_x : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![1, 0, 0], ![0, -1, 0], ![0, 0, -1]]

def mat_m_xy : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![0, 1, 0], ![1, 0, 0], ![0, 0, 1]]

end SPG.Geometry.SpatialOps
