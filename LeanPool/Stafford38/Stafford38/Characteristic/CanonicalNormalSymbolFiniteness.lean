/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.NormalSymbolPolynomial
public import LeanPool.Stafford38.Stafford38.Characteristic.AssociatedGradedFinite
public import LeanPool.Stafford38.Stafford38.Characteristic.MonicAnnihilatorFinite


/-!
Finiteness of the canonical graded quotient from a monic normal-symbol annihilator.
-/

@[expose] public section

namespace Stafford38.Characteristic.CanonicalNormalSymbolFiniteness

open Stafford38.Characteristic
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.Characteristic.NormalSymbolPolynomial
open Stafford38.Characteristic.MonicAnnihilatorFinite
open Stafford38.CharacteristicInitialIdeal
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylFiltration
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylEulerResidue
open Stafford38.Geometry.ConormalAxisContradiction

noncomputable section
variable {k : Type*} [Field k]

/-- The polynomial coefficient ring in all phase variables except the distinguished normal
momentum. -/
abbrev normalCoeffRing (n : ℕ) :=
  MvPolynomial {v : PhaseVar (n + 1) // v ≠ Sum.inr (0 : Fin (n + 1))} k

/-- The ring map from polynomials in the normal momentum to the order-symbol algebra. -/
def normalPolynomialActionHom (n : ℕ) :
    Polynomial (normalCoeffRing (k := k) n) →+* SymbolRing k (n + 1) :=
  (normalSymbolAlgEquiv (k := k) n).symm.toRingHom

/-- The polynomial-ring action obtained by transporting the symbol action
across the normal-variable equivalence. -/
@[instance_reducible]
def normalPolynomialModule (n : ℕ) (E : Type*) [AddCommGroup E]
    [Module (SymbolRing k (n + 1)) E] :
    Module (Polynomial (normalCoeffRing (k := k) n)) E :=
  Module.compHom E (normalPolynomialActionHom (k := k) n)

/-- The corresponding action of the ring of all non-normal symbols. -/
@[instance_reducible]
def normalCoeffModule (n : ℕ) (E : Type*) [AddCommGroup E]
    [Module (SymbolRing k (n + 1)) E] : Module (normalCoeffRing (k := k) n) E :=
  Module.compHom E
    ((normalPolynomialActionHom (k := k) n).comp Polynomial.C)

/-- The actual canonical order-associated graded module is finite over the
polynomial ring in all symbols except the distinguished normal covariable. -/
theorem canonical_orderAssociatedGradedModule_finite_normalCoeffRing
    {n N : ℕ} {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    @Module.Finite (normalCoeffRing (k := k) n)
      (OrderAssociatedGradedModule k
        (canonicalRightIdeal (presentedCoordinate k n) d N))
      _ _ (normalCoeffModule (k := k) n _) := by
  let R := normalCoeffRing (k := k) n
  let E := OrderAssociatedGradedModule k
    (canonicalRightIdeal (presentedCoordinate k n) d N)
  let e := normalSymbolAlgEquiv (k := k) n
  let g : Polynomial R := canonicalNormalPolynomial (k := k) (n := n) (N := N) d
  let : Module (Polynomial R) E := normalPolynomialModule (k := k) n E
  let : Module R E := normalCoeffModule (k := k) n E
  let : IsScalarTower R (Polynomial R) E :=
    ⟨by
      intro r p z
      change (e.symm (r • p)) • z =
        e.symm (Polynomial.C r) • e.symm p • z
      rw [Polynomial.smul_eq_C_mul, map_mul, mul_smul]⟩
  let generator : E := orderAssociatedGradedGenerator k
    (canonicalRightIdeal (presentedCoordinate k n) d N)
  let generatorMap : Polynomial R →ₗ[Polynomial R] E :=
    LinearMap.toSpanSingleton (Polynomial R) E generator
  have hsurj : Function.Surjective generatorMap := by
    intro z
    obtain ⟨P, hP⟩ := exists_smul_orderAssociatedGradedGenerator k
      (canonicalRightIdeal (presentedCoordinate k n) d N) z
    refine ⟨e P, ?_⟩
    change e.symm (e P) • generator = z
    rw [e.symm_apply_apply]
    exact hP
  let : Module.Finite (Polynomial R) E :=
    Module.Finite.of_surjective generatorMap hsurj
  apply finite_of_monic_annihilator g
  · exact canonicalNormalPolynomial_monic hd
  · intro z
    change e.symm g • z = 0
    apply Module.mem_annihilator.mp
    rw [annihilator_orderAssociatedGradedModule]
    change (normalSymbolAlgEquiv (k := k) n).symm
      (canonicalNormalPolynomial (k := k) (n := n) (N := N) d) ∈ _
    rw [canonicalNormalPolynomial,
      (normalSymbolAlgEquiv (k := k) n).symm_apply_apply]
    exact canonical_orderPrincipalComponent_mem_initialIdeal k n N hd


end
end Stafford38.Characteristic.CanonicalNormalSymbolFiniteness
