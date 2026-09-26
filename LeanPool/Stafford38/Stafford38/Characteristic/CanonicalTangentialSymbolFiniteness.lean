/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalNormalSymbolFiniteness


/-!
Finiteness of canonical graded modules over the tangential symbol ring.
-/

@[expose] public section

namespace Stafford38.Characteristic.CanonicalTangentialSymbolFiniteness

open Stafford38.Characteristic
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.Characteristic.NormalSymbolPolynomial
open Stafford38.Characteristic.CanonicalNormalSymbolFiniteness
open Stafford38.Characteristic.MonicAnnihilatorFinite
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylFiltration
open Stafford38.WeylEulerResidue
open Stafford38.WeylPBWMonicBridge

noncomputable section
variable {k : Type*} [Field k]

/-- The phase variables other than the distinguished normal momentum. -/
abbrev NormalVar (n : ℕ) :=
  {v : PhaseVar (n + 1) // v ≠ Sum.inr (0 : Fin (n + 1))}
/-- The phase variables remaining after removing the distinguished normal position and momentum. -/
abbrev TangentialVar (n : ℕ) :=
  {v : NormalVar n // v ≠ ⟨Sum.inl (0 : Fin (n + 1)), by simp⟩}

/-- The polynomial ring in the tangential phase variables. -/
abbrev tangentialCoeffRing (n : ℕ) :=
  MvPolynomial (TangentialVar n) k

/-- The equivalence separating the normal position from the tangential phase variables. -/
def tangentialVariableEquiv (n : ℕ) :
    Option (TangentialVar n) ≃ NormalVar n :=
  Equiv.optionSubtypeNe
    (⟨Sum.inl (0 : Fin (n + 1)), by simp⟩ : NormalVar n)

/-- The normal coefficient ring expressed as polynomials in the distinguished position. -/
def normalCoeffTangentialAlgEquiv (n : ℕ) :
    normalCoeffRing (k := k) n ≃ₐ[k]
      Polynomial (tangentialCoeffRing (k := k) n) :=
  (MvPolynomial.renameEquiv k (tangentialVariableEquiv n).symm).trans
    (MvPolynomial.optionEquivLeft k (TangentialVar n))

/-- The ring map transporting tangential polynomials to the full order-symbol algebra. -/
def tangentialPolynomialActionHom (n : ℕ) :
    Polynomial (tangentialCoeffRing (k := k) n) →+*
      SymbolRing k (n + 1) :=
  (normalPolynomialActionHom (k := k) n).comp
    ((Polynomial.C : normalCoeffRing (k := k) n →+*
      Polynomial (normalCoeffRing (k := k) n)).comp
      (normalCoeffTangentialAlgEquiv (k := k) n).symm.toRingHom)

/-- The action of polynomials in the normal position with tangential coefficients. -/
@[instance_reducible]
def tangentialPolynomialModule
    (n : ℕ) (E : Type*) [AddCommGroup E]
    [Module (SymbolRing k (n + 1)) E] :
    Module (Polynomial (tangentialCoeffRing (k := k) n)) E :=
  Module.compHom E (tangentialPolynomialActionHom (k := k) n)

/-- The tangential coefficient action obtained by restricting the transported polynomial action. -/
@[instance_reducible]
def tangentialCoeffModule
    (n : ℕ) (E : Type*) [AddCommGroup E]
    [Module (SymbolRing k (n + 1)) E] :
    Module (tangentialCoeffRing (k := k) n) E :=
  Module.compHom E
    ((tangentialPolynomialActionHom (k := k) n).comp Polynomial.C)

/-- The transported module structure over polynomials with tangential coefficients. -/
local instance tangentialPolynomialModuleInstance
    (n : ℕ) (E : Type*) [AddCommGroup E]
    [Module (SymbolRing k (n + 1)) E] :
    Module (Polynomial (tangentialCoeffRing (k := k) n)) E :=
  tangentialPolynomialModule (k := k) n E

/-- The transported module structure over the tangential coefficient ring. -/
local instance tangentialCoeffModuleInstance
    (n : ℕ) (E : Type*) [AddCommGroup E]
    [Module (SymbolRing k (n + 1)) E] :
    Module (tangentialCoeffRing (k := k) n) E :=
  tangentialCoeffModule (k := k) n E

/-- Multiplication by the polynomial variable after splitting off `x₀`.
The lemma below identifies this transported operator with the actual `x₀`
symbol action. -/
def tangentialCoordinateMap (n : ℕ) (E : Type*) [AddCommGroup E]
    [Module (SymbolRing k (n + 1)) E] :
    E →ₗ[tangentialCoeffRing (k := k) n] E := by
  refine
    { toFun := fun z => (Polynomial.X :
          Polynomial (tangentialCoeffRing (k := k) n)) • z
      map_add' := smul_add _
      map_smul' := ?_ }
  intro r z
  change (Polynomial.X : Polynomial (tangentialCoeffRing (k := k) n)) •
      (Polynomial.C r • z) =
    Polynomial.C r •
      ((Polynomial.X : Polynomial (tangentialCoeffRing (k := k) n)) • z)
  rw [← mul_smul, ← mul_smul, mul_comm]

theorem tangentialCoordinateMap_apply (n : ℕ) (E : Type*)
    [AddCommGroup E] [Module (SymbolRing k (n + 1)) E] (z : E) :
    tangentialCoordinateMap (k := k) n E z =
      (MvPolynomial.X (Sum.inl (0 : Fin (n + 1))) :
        SymbolRing k (n + 1)) • z := by
  change (normalSymbolAlgEquiv (k := k) n).symm
      (Polynomial.C ((normalCoeffTangentialAlgEquiv (k := k) n).symm
        Polynomial.X)) • z = _
  congr 1
  apply (normalSymbolAlgEquiv (k := k) n).injective
  rw [(normalSymbolAlgEquiv (k := k) n).apply_symm_apply]
  have hx : (normalCoeffTangentialAlgEquiv (k := k) n).symm
      Polynomial.X = MvPolynomial.X
        (⟨Sum.inl (0 : Fin (n + 1)), by simp⟩ : NormalVar n) := by
    apply (normalCoeffTangentialAlgEquiv (k := k) n).injective
    rw [(normalCoeffTangentialAlgEquiv (k := k) n).apply_symm_apply]
    simp [normalCoeffTangentialAlgEquiv, tangentialVariableEquiv]
  rw [hx]
  exact (normalSymbolAlgEquiv_otherVariable (k := k) n
    (Sum.inl (0 : Fin (n + 1))) (by simp)).symm

/-- Kernel and cokernel of the actual distinguished coordinate symbol on the
canonical associated graded quotient are finite over the ring omitting both
that coordinate and the normal covariable. -/
theorem canonical_orderAssociatedGradedModule_finite_tangential_coordinate
    {n N : ℕ} {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    let E := OrderAssociatedGradedModule k
      (canonicalRightIdeal (presentedCoordinate k n) d N)
    @Module.Finite (tangentialCoeffRing (k := k) n)
      (LinearMap.ker (tangentialCoordinateMap (k := k) n E)) _ _
        (inferInstance) ∧
    @Module.Finite (tangentialCoeffRing (k := k) n)
      (E ⧸ LinearMap.range (tangentialCoordinateMap (k := k) n E)) _ _
        (inferInstance) := by
  let T := tangentialCoeffRing (k := k) n
  let R := normalCoeffRing (k := k) n
  let E := OrderAssociatedGradedModule k
    (canonicalRightIdeal (presentedCoordinate k n) d N)
  let e := normalCoeffTangentialAlgEquiv (k := k) n
  let : Module R E := normalCoeffModule (k := k) n E
  have hR : Module.Finite R E :=
    canonical_orderAssociatedGradedModule_finite_normalCoeffRing hd
  let : Module (Polynomial T) E := tangentialPolynomialModule (k := k) n E
  let : Module T E := tangentialCoeffModule (k := k) n E
  let : IsScalarTower T (Polynomial T) E :=
    ⟨by
      intro r p z
      rw [Polynomial.smul_eq_C_mul, mul_smul]
      change Polynomial.C r • (p • z) = Polynomial.C r • (p • z)
      rfl⟩
  have hscalar (r : R) (z : E) : e r • z = r • z := by
    change (normalSymbolAlgEquiv (k := k) n).symm
        (Polynomial.C (e.symm (e r))) • z =
      (normalSymbolAlgEquiv (k := k) n).symm (Polynomial.C r) • z
    rw [e.symm_apply_apply]
  have : Module.Finite (Polynomial T) E := by
    rcases hR with ⟨⟨s, hs⟩⟩
    refine ⟨⟨s, top_unique ?_⟩⟩
    intro z hz
    have hzold : z ∈ Submodule.span R (s : Set E) := by
      rw [hs]
      exact Submodule.mem_top
    exact Submodule.span_induction
      (p := fun z _ => z ∈ Submodule.span (Polynomial T) (s : Set E))
      (fun x hx => Submodule.subset_span hx)
      (Submodule.zero_mem _)
      (fun _ _ _ _ hx hy => Submodule.add_mem _ hx hy)
      (fun r x _ hx => by
        rw [← hscalar r x]
        exact Submodule.smul_mem _ (e r) hx)
      hzold
  let f := LinearMap.lsmul (Polynomial T) E Polynomial.X
  have hf : tangentialCoordinateMap (k := k) n E =
      f.restrictScalars T := by
    ext z
    rfl
  dsimp only
  rw [hf]
  exact finite_kernel_and_cokernel_variable (R := T) (E := E)


end
end Stafford38.Characteristic.CanonicalTangentialSymbolFiniteness
