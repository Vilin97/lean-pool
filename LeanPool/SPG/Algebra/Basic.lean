/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Rat

namespace SPG

abbrev Vec3 := Fin 3 → ℚ

structure SPGElement where
  spatial : Matrix (Fin 3) (Fin 3) ℚ
  spin : Matrix (Fin 3) (Fin 3) ℚ
  deriving DecidableEq, Inhabited

instance : Mul SPGElement where
  mul a b := { spatial := a.spatial * b.spatial, spin := a.spin * b.spin }

def matrix_repr (m : Matrix (Fin 3) (Fin 3) ℚ) : Std.Format :=
  let rows := List.range 3 |>.map (fun i =>
    let row := List.range 3 |>.map (fun j =>
      match i, j with
      | 0, 0 => repr (m 0 0)
      | 0, 1 => repr (m 0 1)
      | 0, 2 => repr (m 0 2)
      | 1, 0 => repr (m 1 0)
      | 1, 1 => repr (m 1 1)
      | 1, 2 => repr (m 1 2)
      | 2, 0 => repr (m 2 0)
      | 2, 1 => repr (m 2 1)
      | 2, 2 => repr (m 2 2)
      | _, _ => Std.Format.text "error"
    )
    Std.Format.text s!"{row}"
  )
  Std.Format.joinSep rows (Std.Format.text "\n")

instance : Repr SPGElement where
  reprPrec s _ :=
    Std.Format.text "SPGElement(\n  spatial: " ++ matrix_repr s.spatial ++ Std.Format.text ",\n  spin: " ++ matrix_repr s.spin ++ Std.Format.text "\n)"


end SPG
