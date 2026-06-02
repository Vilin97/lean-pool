/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Algebra.Order.Archimedean.Real.Hom
import LeanPool.Rupert.Basic
import LeanPool.Rupert.Set

/-!
# LeanPool.Rupert.Equivalences.Util

Imported Lean Pool material for `LeanPool.Rupert.Equivalences.Util`.
-/
open Pointwise
open Matrix

/-- Projecting from ℝ³ to ℝ² is linear -/
noncomputable
def projXyLinear : ℝ³ →ₗ[ℝ] ℝ² :=
  {
   toFun := projXy,
   map_add' := by
     intro x y;
     ext i; fin_cases i <;> simp [projXy]
   ,
   map_smul' := by
     intro x y; ext i; fin_cases i <;> simp [projXy]
   }

/-- Rotation by an element of `SO3`, viewed as an affine map. -/
noncomputable
def rotationAffine (rot : SO3) : ℝ³ →ᵃ[ℝ] ℝ³ := (Matrix.toEuclideanLin rot).toAffineMap

/-- Translating is affine. -/
noncomputable
def offsetAffine (off : E 2) : ℝ² →ᵃ[ℝ] ℝ² :=
  {toFun v := off + v, linear := LinearMap.id, map_vadd' p v := add_vadd_comm v off p }

/-- Projection of a rotated point onto the xy-plane, as an affine map. -/
noncomputable
def projXyRotationIsAffine (rot : SO3) : ℝ³ →ᵃ[ℝ] ℝ² :=
  AffineMap.comp projXyLinear.toAffineMap (rotationAffine rot)

/-- Full affine transform used for projected Rupert shadows. -/
noncomputable
def fullTransformAffine (off : E 2) (rot : SO3) : ℝ³ →ᵃ[ℝ] ℝ² :=
  AffineMap.comp (offsetAffine off) (projXyRotationIsAffine rot)
