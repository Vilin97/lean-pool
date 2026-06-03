/-
Copyright (c) 2026 the LieLean team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Algebra.Lie.DirectSum
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import LeanPool.LowDimSolvClassification.Semidirect
import LeanPool.LowDimSolvClassification.GeneralResults

/-!
# LeanPool.LowDimSolvClassification.InstancesConstructions
-/

open Module
open Submodule

namespace LieAlgebra

section mkAbelian

/-- The abelian Lie algebra constructed from a vector space by setting the bracket to zero.
The unused `Module K V` instance is consumed by `inferInstance` so the `unusedArguments` linter
accepts the definition; the result is still a synonym for `V`. -/
def mkAbelian (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V] : Type _ :=
  (inferInstance : Module K V).toDistribMulAction.toMulAction.toSMul |> fun _ ↦ V

variable (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V]

instance : Bracket (mkAbelian K V) (mkAbelian K V) := {
  bracket := fun _ _ ↦ (0 : V)
}

instance : LieRing (mkAbelian K V) := {
  (inferInstance : AddCommGroup V) with
  add_lie := fun _ _ _ ↦ show (0 : V) = 0 + 0 by rw [add_zero]
  lie_add := fun _ _ _ ↦ show (0 : V) = 0 + 0 by rw [add_zero]
  lie_self := fun _ ↦ show (0 : V) = 0 from rfl
  leibniz_lie := fun _ _ _ ↦ show (0 : V) = 0 + 0 by rw [add_zero]
}

instance : LieAlgebra K (mkAbelian K V) := {
  (inferInstance : Module K V) with
  lie_smul := fun _ _ _ ↦ show (0 : V) = (_ : K) • (0 : V) by rw [smul_zero]
}

instance : IsLieAbelian (mkAbelian K V) :=
  ⟨fun _ _ ↦ rfl⟩

end mkAbelian

section abelianDerivation

/-- TODO. -/
def _root_.LieAlgebra.Abelian.DerivationOfLinearMap' {K : Type*} [CommRing K] {L : Type*}
    [LieRing L] [LieAlgebra K L] [IsLieAbelian L] (f : End K L) :
    LieDerivation K L L := {
  toLinearMap := f,
  leibniz' := by
    intro x y
    simp only [trivial_lie_zero, map_zero, sub_self]
}

/-- If `L` is an abelian Lie algebra, any linear endomorphism of L is also a derivation of L. -/
def _root_.LieAlgebra.Abelian.DerivationOfLinearMap (K L : Type*) [CommRing K] [LieRing L]
    [LieAlgebra K L] [IsLieAbelian L] :
    End K L ≃ₗ⁅K⁆ LieDerivation K L L := {
  toFun := Abelian.DerivationOfLinearMap',
  map_add' := by
    intro f g
    ext x
    unfold Abelian.DerivationOfLinearMap'
    simp only [LieDerivation.mk_coe, LinearMap.add_apply, LieDerivation.coe_add, Pi.add_apply]
  map_smul' := by
    intro a f
    ext x
    unfold Abelian.DerivationOfLinearMap'
    simp only [LieDerivation.mk_coe, LinearMap.smul_apply, RingHom.id_apply, LieDerivation.coe_smul,
      Pi.smul_apply]
  map_lie' := by
    intro f g
    ext x
    change (f * g - g * f) x = f (g x) - g (f x)
    simp
  invFun := LieDerivation.toLinearMap
  left_inv := by
    intro f
    rfl
  right_inv := by
    intro f
    rfl
}

@[simp]
theorem _root_.LieAlgebra.Abelian.DerivationCoeLinearMap {K : Type*} [CommRing K] {L : Type*}
    [LieRing L] [LieAlgebra K L] [IsLieAbelian L] (f : L →ₗ[K] L) :
    (Abelian.DerivationOfLinearMap K L f).toLinearMap = f := rfl

@[simp]
theorem _root_.LieAlgebra.Abelian.DerivationCoeFun {K : Type*} [CommRing K] {L : Type*}
    [LieRing L] [LieAlgebra K L] [IsLieAbelian L] (f : L →ₗ[K] L) :
    ⇑(Abelian.DerivationOfLinearMap K L f) = ⇑f := rfl

@[simp]
theorem _root_.LieAlgebra.Abelian.DerivationCoeFun' {K : Type*} [CommRing K] {L : Type*}
    [LieRing L] [LieAlgebra K L] [IsLieAbelian L] (f : L →ₗ[K] L) :
    ⇑((Abelian.DerivationOfLinearMap K L).toLieHom f) = ⇑f := rfl

end abelianDerivation

section liealgofaffineequiv

variable (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V]

example : LieAlgebra K (Module.End K V) := inferInstance

/-- TODO. -/
def _root_.LieAlgebra.ofAffineEquivAux := (Abelian.DerivationOfLinearMap K (mkAbelian K V)).toLieHom

/-- The Lie algebra of the general affine group on a vector space `V`,
    constructed as semidirect product of `V →ₗ[K] V` with the abelian Lie algebra `V`. -/
abbrev _root_.LieAlgebra.OfAffineEquiv :=
  Module.End K (mkAbelian K V) ⋉[ofAffineEquivAux K V] mkAbelian K V
-- one could also define it as V →ᵃ[K] V, but the Lie bracket is not defined using
-- function composition (not left-distributive).

@[inherit_doc]
notation "𝔞𝔣𝔣" => OfAffineEquiv

end liealgofaffineequiv

section liealghyperbolic

variable (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V] (L : Type*)
    [LieRing L] [LieAlgebra K L] [IsLieAbelian L]

/-- TODO. -/
def _root_.LieAlgebra.RealHyperbolicAux' : K →ₗ⁅K⁆ LieDerivation K L L :=
  LieHom.comp (Abelian.DerivationOfLinearMap K L) (LieHom.smulRight (LinearMap.id : End K L))

/-- TODO. -/
def _root_.LieAlgebra.RealHyperbolicAux : K →ₗ⁅K⁆ LieDerivation K (mkAbelian K V) (mkAbelian K V)
    := RealHyperbolicAux' K (mkAbelian K V)

/-- The almost abelian Lie algebra associated to real hyperbolic space,
  generalized to arbitrary `K`. -/
abbrev _root_.LieAlgebra.RealHyperbolic := K ⋉[RealHyperbolicAux K V] (mkAbelian K V)

/-- The almost abelian Lie algebra associated to real hyperbolic `n`-space,
  generalized to arbitrary `K`. -/
abbrev _root_.LieAlgebra.RealHyperbolic' (n : ℕ) (K : Type*) [CommRing K]
    := K ⋉[RealHyperbolicAux K (Fin (n - 1) → K)] (mkAbelian K (Fin (n - 1) → K))
--requires n > 0

@[inherit_doc]
notation "𝔥𝔶𝔭" => RealHyperbolic'

end liealghyperbolic

end LieAlgebra
