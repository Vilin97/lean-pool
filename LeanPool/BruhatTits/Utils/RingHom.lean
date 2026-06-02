/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# LeanPool.BruhatTits.Utils.RingHom
-/

open Module

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

-- up until line 70, this is now in mathlib (https://github.com/leanprover-community/mathlib4/pull/17433)
-- all in Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs.lean
-- for some reason `Units.map f.mapMatrix` does not work.
/-- Map an element of `GL` along a ring homomorphism. -/
def GL.map {α : Type*} [DecidableEq α] [Fintype α] (g : GL α R) : GL α S where
  val := f.mapMatrix g
  inv := f.mapMatrix g.inv
  val_inv := by rw [← map_mul]; simp
  inv_val := by rw [← map_mul]; simp
-- Matrix.GeneralLinearGroup.map

variable {α : Type*} [DecidableEq α] [Fintype α]

@[simp]
lemma GL.val_map (g : GL α R) : (GL.map f g).val = f.mapMatrix g.val := by
  rfl

@[simp]
lemma GL.map_apply (i j : α) (g : GL α R) : GL.map f g i j = f (g i j) := by
  rfl
--this is called Matrix.GeneralLinearGroup.map_apply and similarly for the ones below

lemma GL.map_one : GL.map f (1 : GL α R) = 1 := by
  ext i j
  simp [GL.map, Matrix.one_apply]

lemma GL.map_mul (g h : GL α R) : GL.map f (g * h) = GL.map f g * GL.map f h := by
  ext i j
  simp [GL.map, Matrix.mul_apply]

lemma GL.map_inv (g : GL α R) : GL.map f g⁻¹ = (GL.map f g)⁻¹ := by
  ext i j
  rfl

lemma GL.map_det (g : GL α R) : Matrix.GeneralLinearGroup.det (GL.map f g) =
    Units.map f (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp only [map, RingHom.mapMatrix_apply, Units.inv_eq_val_inv, Matrix.coe_units_inv,
    Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, MonoidHom.coe_coe]
  symm
  apply RingHom.map_det

lemma GL.map_mul_map_inv (g : GL α R) : GL.map f g * GL.map f g⁻¹ = 1 := by
  apply Units.ext
  simp only [map, RingHom.mapMatrix_apply, Units.inv_eq_val_inv, Matrix.coe_units_inv, inv_inv,
    Units.val_mul, Units.val_one]
  change f.mapMatrix g.val * f.mapMatrix g.val⁻¹ = 1
  rw [← _root_.map_mul]
  simp

lemma GL.map_inv_mul_map (g : GL α R) : GL.map f g⁻¹ * GL.map f g = 1 := by
  apply Units.ext
  simp only [map, RingHom.mapMatrix_apply, Units.inv_eq_val_inv, Matrix.coe_units_inv, inv_inv,
    Units.val_mul, Units.val_one]
  change f.mapMatrix g.val⁻¹ * f.mapMatrix g.val = 1
  rw [← _root_.map_mul]
  simp

lemma GL.coe_map_mul_map_inv (g : GL α R) : g.val.map f * g.val⁻¹.map f = 1 := by
  rw [← Matrix.map_mul]
  simp

lemma GL.coe_map_inv_mul_map (g : GL α R) : g.val⁻¹.map f * g.val.map f = 1 := by
  rw [← Matrix.map_mul]
  simp

lemma GL_map_eq {ι : Type*} [DecidableEq ι] [Fintype ι]
    {R S : Type*} [CommRing R] [CommRing S] (g : GL ι R) (f : R →+* S) :
    GL.map f g = Matrix.GeneralLinearGroup.map f g :=
  rfl

lemma GL.mem_range_map_iff {f : R →+* S} (hf : Function.Injective f)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (g : GL ι S) :
    g ∈ Set.range (Matrix.GeneralLinearGroup.map f) ↔
      (∀ (i j : ι), g i j ∈ Set.range f) ∧
        ↑g.det⁻¹ ∈ Set.range f := by
  refine ⟨fun ⟨k, hk⟩ ↦ hk ▸ by simp [Matrix.GeneralLinearGroup.map_det], fun ⟨h1, ⟨u, hu⟩⟩ ↦ ?_⟩
  choose r hr using h1
  refine ⟨.mk'' r ?_, by ext; simp [Matrix.GeneralLinearGroup.mk'', Matrix.nonsingInvUnit, hr]⟩
  rw [isUnit_iff_exists_inv]
  use u
  apply hf
  simp only [_root_.map_mul, RingHom.map_det, RingHom.mapMatrix_apply, _root_.map_one]
  rw [hu]
  convert (Matrix.GeneralLinearGroup.det g).val_inv using 2
  congr; ext; simp [hr]

variable {K : Type*} [CommRing K] (R : Subring K)

/-- Coerce matrices over `R` to matrices over `K`. -/
instance instCoeHeadMatrixSubtypeMemSubringLeanPool {α β : Type*} :
    CoeHead (Matrix α β R) (Matrix α β K) where
  coe g := g.map R.subtype

/-- Coerce invertible matrices over `R` to matrices over `K`. -/
instance instCoeHeadGeneralLinearGroupSubtypeMemSubringLeanPool
    {α : Type*} [DecidableEq α] [Fintype α] : CoeHead (GL α R) (GL α K) where
  coe g := GL.map R.subtype g

--the following lemmas are used in CartanUniqueness.lean
@[simp]
lemma Subring.coe_map_mul_map_inv (g : GL α R) :
    g.val.map Subtype.val * g.val⁻¹.map Subtype.val = 1 :=
  GL.coe_map_mul_map_inv R.subtype g

@[simp]
lemma Subring.coe_map_inv_mul_map (g : GL α R) :
    g.val⁻¹.map Subtype.val * g.val.map Subtype.val = 1 :=
  GL.coe_map_inv_mul_map R.subtype g

@[simp]
lemma Subring.coe_det (g : Matrix α α R) : (g.map Subtype.val).det = g.det := by
  erw [← R.subtype.map_det]
  simp
