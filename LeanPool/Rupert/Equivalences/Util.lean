/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Hom
import LeanPool.Rupert.Basic
import LeanPool.Rupert.Set
open Pointwise
open Matrix

/-- Projecting from ℝ³ to ℝ² is linear -/
noncomputable
def proj_xy_linear : ℝ³ →ₗ[ℝ] ℝ² :=
  {
   toFun := proj_xy,
   map_add' := by
     intro x y;
     ext i; fin_cases i <;> simp [proj_xy]
   ,
   map_smul' := by
     intro x y; ext i; fin_cases i <;> simp [proj_xy]
   }

/-- Rotation by an element of `SO3`, viewed as an affine map. -/
noncomputable
def rotation_affine (rot : SO3) : ℝ³ →ᵃ[ℝ] ℝ³ := (Matrix.toEuclideanLin rot).toAffineMap

/-- Translating is affine. -/
noncomputable
def offset_affine (off : E 2) : ℝ² →ᵃ[ℝ] ℝ² :=
  {toFun v := off + v, linear := LinearMap.id, map_vadd' p v := add_vadd_comm v off p }

/-- Projection of a rotated point onto the xy-plane, as an affine map. -/
noncomputable
def proj_xy_rotation_is_affine (rot : SO3) : ℝ³ →ᵃ[ℝ] ℝ² :=
  AffineMap.comp proj_xy_linear.toAffineMap (rotation_affine rot)

/-- Full affine transform used for projected Rupert shadows. -/
noncomputable
def full_transform_affine (off : E 2) (rot : SO3) : ℝ³ →ᵃ[ℝ] ℝ² :=
  AffineMap.comp (offset_affine off) (proj_xy_rotation_is_affine rot)
