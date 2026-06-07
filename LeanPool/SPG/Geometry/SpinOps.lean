/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import Mathlib.Data.Matrix.Basic

namespace SPG.Geometry.SpinOps

def spin_I : Matrix (Fin 3) (Fin 3) ℚ :=
  1

def spin_neg_I : Matrix (Fin 3) (Fin 3) ℚ :=
  -1

end SPG.Geometry.SpinOps
