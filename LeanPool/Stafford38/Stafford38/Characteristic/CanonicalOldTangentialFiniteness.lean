/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalTangentialRingEquivalence


/-!
Finiteness over the original tangential polynomial ring after changing phase variables.
-/

@[expose] public section

namespace Stafford38.Characteristic.CanonicalOldTangentialFiniteness

open Stafford38.Characteristic
open Stafford38.Characteristic.CanonicalTangentialSymbolFiniteness
open Stafford38.Characteristic.CanonicalTangentialRingEquivalence
open Stafford38.Characteristic.CanonicalNormalSymbolFiniteness
open Stafford38.Characteristic.NormalSymbolPolynomial
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylPBW
open Stafford38.WeylEulerResidue

noncomputable section
variable {k : Type*} [Field k]

/-- The polynomial coefficient ring in the original tangential position and momentum variables. -/
abbrev oldTangentialCoeffRing (n : ℕ) := MvPolynomial (Fin n ⊕ Fin n) k

/- The coefficient action written in the old, non-subtype variables. -/
/-- The original tangential coefficient action transported from the full symbol algebra. -/
@[instance_reducible]
def oldCoeffModule
    (n : ℕ) (E : Type*) [AddCommGroup E]
    [Module (SymbolRing k (n + 1)) E] :
    Module (oldTangentialCoeffRing (k := k) n) E :=
  Module.compHom E
    (((tangentialPolynomialActionHom (k := k) n).comp Polynomial.C).comp
      (oldSymbolTangentialAlgEquiv (k := k) n).toRingHom)

/-- The transported module structure over the original tangential coefficient ring. -/
local instance (priority := 10) oldCoeffModuleInstance
    (n : ℕ) (E : Type*) [AddCommGroup E]
    [Module (SymbolRing k (n + 1)) E] :
    Module (oldTangentialCoeffRing (k := k) n) E :=
  oldCoeffModule (k := k) n E

/-- Multiplication by the distinguished position symbol, viewed as a tangential linear map. -/
def oldCoordinateMap (n : ℕ) (E : Type*) [AddCommGroup E]
    [Module (SymbolRing k (n + 1)) E] :
    E →ₗ[oldTangentialCoeffRing (k := k) n] E := by
  refine
    { toFun := fun z =>
      (MvPolynomial.X (Sum.inl (0 : Fin (n + 1))) : SymbolRing k (n + 1)) • z
      map_add' := smul_add _
      map_smul' := ?_ }
  intro r z
  let a := (((tangentialPolynomialActionHom (k := k) n).comp Polynomial.C).comp
    (oldSymbolTangentialAlgEquiv (k := k) n).toRingHom) r
  change (MvPolynomial.X (Sum.inl (0 : Fin (n + 1))) : SymbolRing k (n + 1)) •
      (a • z) = a •
        ((MvPolynomial.X (Sum.inl (0 : Fin (n + 1))) : SymbolRing k (n + 1)) • z)
  rw [← mul_smul, ← mul_smul, mul_comm]

theorem oldCoordinateMap_apply (n : ℕ) (E : Type*)
    [AddCommGroup E] [Module (SymbolRing k (n + 1)) E] (z : E) :
    oldCoordinateMap (k := k) n E z =
      (MvPolynomial.X (Sum.inl (0 : Fin (n + 1))) : SymbolRing k (n + 1)) • z := rfl

theorem oldCoeffModule_oldSymbol_X_action
    (n : ℕ) (E : Type*) [AddCommGroup E]
    [Module (SymbolRing k (n + 1)) E]
    (i : Fin n ⊕ Fin n) (z : E) :
    @SMul.smul (oldTangentialCoeffRing (k := k) n) E
        (oldCoeffModule (k := k) n E).toSMul
        (MvPolynomial.X i) z =
      (MvPolynomial.X (oldIndex i) : SymbolRing k (n + 1)) • z := by
  change ((tangentialPolynomialActionHom (k := k) n).comp Polynomial.C)
      (oldSymbolTangentialAlgEquiv (k := k) n (MvPolynomial.X i)) • z = _
  rw [tangentialCoeffActionHom_oldSymbol_X]

theorem canonical_finite_old_coordinate_kernel_cokernel
    {n N : ℕ} {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    let E := OrderAssociatedGradedModule k
      (canonicalRightIdeal (presentedCoordinate k n) d N)
    Module.Finite (oldTangentialCoeffRing (k := k) n)
        (LinearMap.ker (oldCoordinateMap (k := k) n E)) ∧
      Module.Finite (oldTangentialCoeffRing (k := k) n)
        (E ⧸ LinearMap.range (oldCoordinateMap (k := k) n E)) := by
  let T := oldTangentialCoeffRing (k := k) n
  let C := tangentialCoeffRing (k := k) n
  let E := OrderAssociatedGradedModule k
    (canonicalRightIdeal (presentedCoordinate k n) d N)
  let e := oldSymbolTangentialAlgEquiv (k := k) n
  let : Algebra T C := e.toRingHom.toAlgebra
  let : Module T C := Module.compHom C e.toRingHom
  let : Module C E := tangentialCoeffModule (k := k) n E
  let : Module T E := oldCoeffModule (k := k) n E
  let : IsScalarTower T C E := ⟨by
    intro r c z
    change (((tangentialPolynomialActionHom (k := k) n).comp Polynomial.C)
        (e r * c)) • z =
      (((tangentialPolynomialActionHom (k := k) n).comp Polynomial.C) (e r)) •
        ((((tangentialPolynomialActionHom (k := k) n).comp Polynomial.C) c) • z)
    rw [map_mul, mul_smul]⟩
  have : Module.Finite T C :=
    Module.Finite.of_surjective (Module.compHom.toLinearMap e.toRingHom) e.surjective
  let f := tangentialCoordinateMap (k := k) n E
  have hf : oldCoordinateMap (k := k) n E = f.restrictScalars T := by
    ext z
    exact (oldCoordinateMap_apply n E z).trans (tangentialCoordinateMap_apply n E z).symm
  have hfinite := canonical_orderAssociatedGradedModule_finite_tangential_coordinate hd
  have : Module.Finite C f.ker := hfinite.1
  have : Module.Finite C (E ⧸ f.range) := hfinite.2
  have : Module.Finite T f.ker := Module.Finite.trans C f.ker
  have : Module.Finite T (E ⧸ f.range) := Module.Finite.trans C (E ⧸ f.range)
  change Module.Finite T (oldCoordinateMap (k := k) n E).ker ∧
    Module.Finite T (E ⧸ (oldCoordinateMap (k := k) n E).range)
  rw [hf, LinearMap.ker_restrictScalars, LinearMap.range_restrictScalars]
  constructor
  · exact Module.Finite.equiv
      ((Submodule.restrictScalarsEquiv (R := C) (M := E) T f.ker).restrictScalars T).symm
  · exact Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv T f.range).symm


end
end Stafford38.Characteristic.CanonicalOldTangentialFiniteness
