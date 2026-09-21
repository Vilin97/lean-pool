/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Weyl.LeadingSymbol
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Associated graded pieces of the PBW filtrations

The strict lower piece in degree `N` is the kernel of degree-`N` principal
component projection. Restricting that projection to the filtered piece is
surjective onto the weighted-homogeneous symbol submodule, so each filtered
quotient is canonically linearly equivalent to its symbol component. The
external graded multiplication is a downstream construction.
-/

namespace Stafford38.WeylAssociatedGraded

open Stafford38.Characteristic
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBW
open Stafford38.WeylFiltration
open Stafford38.WeylLeadingSymbol

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- The part of a filtration piece strictly below degree `N`; degree zero has
zero lower piece. -/
def presentedStrictLowerPiece {n : ℕ} (w : PhaseVar n → ℕ) :
    (N : ℕ) → Submodule k (PresentedWeyl k n)
  | 0 => ⊥
  | N + 1 => presentedWeightPiece k w N

theorem presentedStrictLowerPiece_le {n N : ℕ}
    (w : PhaseVar n → ℕ) :
    presentedStrictLowerPiece k w N ≤ presentedWeightPiece k w N := by
  cases N with
  | zero => exact bot_le
  | succ N => exact presentedWeightPiece_mono k w (Nat.le_succ N)

theorem presentedPrincipalComponent_eq_zero_iff_mem_strictLower
    {n N : ℕ} (w : PhaseVar n → ℕ) (z : PresentedWeyl k n)
    (hz : z ∈ presentedWeightPiece k w N) :
    presentedPrincipalComponent k w N z = 0 ↔
      z ∈ presentedStrictLowerPiece k w N := by
  constructor
  · intro hp
    cases N with
    | zero =>
        rw [presentedStrictLowerPiece, Submodule.mem_bot]
        apply (presentedNormalFormLinearEquiv k n).injective
        ext m
        have hle := (mem_presentedWeightPiece k w 0 z).mp hz
        have hpc := congrArg (MvPolynomial.coeff m) hp
        rw [coeff_presentedPrincipalComponent,
          MvPolynomial.coeff_zero] at hpc
        by_cases hc :
            MvPolynomial.coeff m (presentedNormalFormLinearEquiv k n z) = 0
        · rw [hc]
          simp
        · have hw : monomialWeight w m = 0 := Nat.eq_zero_of_le_zero (hle m hc)
          simpa [hw] using hpc
    | succ N =>
        rw [presentedStrictLowerPiece, mem_presentedWeightPiece]
        intro m hm
        have hle := (mem_presentedWeightPiece k w (N + 1) z).mp hz m hm
        have hpc := congrArg (MvPolynomial.coeff m) hp
        rw [coeff_presentedPrincipalComponent,
          MvPolynomial.coeff_zero] at hpc
        by_contra hnot
        have heq : monomialWeight w m = N + 1 := by omega
        simp [heq, hm] at hpc
  · intro hlower
    cases N with
    | zero =>
        rw [presentedStrictLowerPiece, Submodule.mem_bot] at hlower
        subst z
        exact map_zero _
    | succ N =>
        exact presentedPrincipalComponent_eq_zero_of_mem_of_lt k w z
          hlower (Nat.lt_succ_self N)

/-- The principal component restricted to the degree-`N` filtration piece,
with codomain narrowed to the degree-`N` homogeneous symbol submodule. -/
def principalComponentOnPiece {n : ℕ} (w : PhaseVar n → ℕ) (N : ℕ) :
    presentedWeightPiece k w N →ₗ[k]
      MvPolynomial.weightedHomogeneousSubmodule k w N where
  toFun z := ⟨presentedPrincipalComponent k w N z,
    MvPolynomial.weightedHomogeneousComponent_mem w
      (presentedNormalFormLinearEquiv k n z) N⟩
  map_add' x y := by
    ext
    simp [presentedPrincipalComponent]
  map_smul' c x := by
    ext
    simp [presentedPrincipalComponent]

theorem mem_ker_principalComponentOnPiece_iff {n N : ℕ}
    (w : PhaseVar n → ℕ) (z : presentedWeightPiece k w N) :
    z ∈ LinearMap.ker (principalComponentOnPiece k w N) ↔
      (z : PresentedWeyl k n) ∈ presentedStrictLowerPiece k w N := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have hp : presentedPrincipalComponent k w N z = 0 :=
      congrArg (fun f : MvPolynomial.weightedHomogeneousSubmodule k w N =>
        (f : SymbolRing k n)) h
    exact (presentedPrincipalComponent_eq_zero_iff_mem_strictLower
      k w z z.property).mp hp
  · intro hlower
    apply Subtype.ext
    exact (presentedPrincipalComponent_eq_zero_iff_mem_strictLower
      k w z z.property).mpr hlower

/-- The kernel of principal-component projection is exactly the strict lower
filtration piece, viewed inside the degree-`N` piece. -/
theorem ker_principalComponentOnPiece_eq {n N : ℕ}
    (w : PhaseVar n → ℕ) :
    LinearMap.ker (principalComponentOnPiece k w N) =
      (presentedStrictLowerPiece k w N).comap
        (presentedWeightPiece k w N).subtype := by
  ext z
  exact mem_ker_principalComponentOnPiece_iff k w z

theorem principalComponentOnPiece_surjective {n N : ℕ}
    (w : PhaseVar n → ℕ) :
    Function.Surjective (principalComponentOnPiece k w N) := by
  intro f
  let z : PresentedWeyl k n :=
    (presentedNormalFormLinearEquiv k n).symm (f : SymbolRing k n)
  have hz : z ∈ presentedWeightPiece k w N := by
    rw [mem_presentedWeightPiece]
    intro m hm
    have hnormal : presentedNormalFormLinearEquiv k n z = (f : SymbolRing k n) := by
      exact (presentedNormalFormLinearEquiv k n).apply_symm_apply f
    rw [hnormal] at hm
    have hw := f.property hm
    rw [finsupp_weight_eq_monomialWeight] at hw
    exact le_of_eq hw
  refine ⟨⟨z, hz⟩, ?_⟩
  apply Subtype.ext
  change presentedPrincipalComponent k w N z = (f : SymbolRing k n)
  rw [presentedPrincipalComponent, LinearMap.comp_apply]
  change MvPolynomial.weightedHomogeneousComponent w N
      (presentedNormalFormLinearEquiv k n z) = (f : SymbolRing k n)
  rw [show presentedNormalFormLinearEquiv k n z = (f : SymbolRing k n) from
    (presentedNormalFormLinearEquiv k n).apply_symm_apply f]
  exact f.property.weightedHomogeneousComponent_same

local instance (priority := 10000) presentedWeightPieceHasQuotient {n : ℕ}
    (w : PhaseVar n → ℕ) (N : ℕ) :
    HasQuotient (presentedWeightPiece k w N)
      (Submodule k (presentedWeightPiece k w N)) :=
  @Submodule.hasQuotient k (presentedWeightPiece k w N) _
    (presentedWeightPiece k w N).addCommGroup
    (presentedWeightPiece k w N).module

/-- The degree-`N` associated graded piece, presented canonically as the
quotient by the kernel of principal-component projection. The preceding
kernel theorem identifies this kernel with the strict lower filtration. -/
abbrev presentedAssociatedGradedPiece {n : ℕ}
    (w : PhaseVar n → ℕ) (N : ℕ) :=
  (presentedWeightPiece k w N) ⧸
    LinearMap.ker (principalComponentOnPiece k w N)

local instance (priority := 10000) presentedAssociatedGradedPieceAddCommGroup
    {n : ℕ} (w : PhaseVar n → ℕ) (N : ℕ) :
    AddCommGroup (presentedAssociatedGradedPiece k w N) :=
  @Submodule.Quotient.addCommGroup k (presentedWeightPiece k w N) _
    (presentedWeightPiece k w N).addCommGroup
    (presentedWeightPiece k w N).module
    (LinearMap.ker (principalComponentOnPiece k w N))

local instance (priority := 10000) presentedAssociatedGradedPieceModule
    {n : ℕ} (w : PhaseVar n → ℕ) (N : ℕ) :
    Module k (presentedAssociatedGradedPiece k w N) :=
  @Submodule.Quotient.module k (presentedWeightPiece k w N) _
    (presentedWeightPiece k w N).addCommGroup
    (presentedWeightPiece k w N).module
    (LinearMap.ker (principalComponentOnPiece k w N))

/-- Every associated graded piece is linearly equivalent to the corresponding
weighted-homogeneous symbol submodule. -/
def presentedAssociatedGradedPieceEquiv {n : ℕ}
    (w : PhaseVar n → ℕ) (N : ℕ) :
    presentedAssociatedGradedPiece k w N ≃ₗ[k]
      MvPolynomial.weightedHomogeneousSubmodule k w N :=
  @LinearMap.quotKerEquivOfSurjective k
    (presentedWeightPiece k w N)
    (MvPolynomial.weightedHomogeneousSubmodule k w N) _
    (presentedWeightPiece k w N).addCommGroup
    (MvPolynomial.weightedHomogeneousSubmodule k w N).addCommGroup
    (presentedWeightPiece k w N).module
    (MvPolynomial.weightedHomogeneousSubmodule k w N).module
    (principalComponentOnPiece k w N)
    (principalComponentOnPiece_surjective k w)

theorem presentedAssociatedGradedPieceEquiv_mk {n N : ℕ}
    (w : PhaseVar n → ℕ) (z : presentedWeightPiece k w N) :
    presentedAssociatedGradedPieceEquiv k w N (Submodule.Quotient.mk z) =
      principalComponentOnPiece k w N z := by
  rfl


end

end Stafford38.WeylAssociatedGraded
