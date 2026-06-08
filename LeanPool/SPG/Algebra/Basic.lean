/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Rat

/-!
# Basic data of spin point groups

This module introduces the rational vector type `Vec3` and the `SPGElement`
structure pairing a spatial and a spin `3 × 3` rational matrix, together with
their multiplication and printing instances.
-/

namespace SPG

/-- A rational three-dimensional vector. -/
abbrev Vec3 := Fin 3 → ℚ

/-- An element of a spin point group: a spatial operation together with the
spin-space operation acting on the magnetic moments. -/
structure SPGElement where
  /-- The spatial part of the operation, a rational `3 × 3` matrix. -/
  spatial : Matrix (Fin 3) (Fin 3) ℚ
  /-- The spin part of the operation, a rational `3 × 3` matrix. -/
  spin : Matrix (Fin 3) (Fin 3) ℚ
  deriving DecidableEq, Inhabited

instance : Mul SPGElement where
  mul a b := { spatial := a.spatial * b.spatial, spin := a.spin * b.spin }

/-- Pretty-print a rational `3 × 3` matrix as rows of entries. -/
def matrixRepr (m : Matrix (Fin 3) (Fin 3) ℚ) : Std.Format :=
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
    Std.Format.text "SPGElement(\n  spatial: " ++ matrixRepr s.spatial ++
      Std.Format.text ",\n  spin: " ++ matrixRepr s.spin ++
      Std.Format.text "\n)"

end SPG
