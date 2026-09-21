/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormQuotient
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Group.Quotient
/-!
# The norm quotient induced by a specified finite local Artin map

The first isomorphism theorem determines the quotient equivalence from any
specified continuous surjective homomorphism with the field-norm kernel.
This is distinct from uniqueness of the Artin map itself.
-/

noncomputable section

namespace ClassFieldTheory

universe u v

/-- Any specified continuous surjective homomorphism with the field-norm
kernel induces one and only one continuous equivalence of the norm quotient.
The equivalence evaluates to the specified map on every quotient class. -/
theorem finiteAbelianLocalReciprocity_quotientEquiv_of_artin
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (artin : Kˣ →ₜ* (L ≃ₐ[K] L))
    (hsurj : Function.Surjective artin)
    (hker : artin.ker = fieldNormSubgroup K L) :
    ∃! e : FieldNormQuotient K L ≃ₜ* (L ≃ₐ[K] L),
      ∀ x : Kˣ, e (QuotientGroup.mk' (fieldNormSubgroup K L) x) = artin x := by
  have hOpen : IsOpen (fieldNormSubgroup K L : Set Kˣ) := by
    have hOpenKer : IsOpen (artin.ker : Set Kˣ) := by
      change IsOpen (artin ⁻¹' {1})
      exact (isOpen_discrete {1}).preimage artin.continuous
    rwa [← hker]
  have hDiscrete : DiscreteTopology (FieldNormQuotient K L) :=
    QuotientGroup.discreteTopology hOpen
  let e₀ : FieldNormQuotient K L ≃* (L ≃ₐ[K] L) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective artin.toMonoidHom hsurj)
  let e : FieldNormQuotient K L ≃ₜ* (L ≃ₐ[K] L) :=
    { e₀ with
      continuous_toFun := @continuous_of_discreteTopology
        (FieldNormQuotient K L) _ hDiscrete (L ≃ₐ[K] L) _ e₀
      continuous_invFun := continuous_of_discreteTopology }
  have he (x : Kˣ) :
      e (QuotientGroup.mk' (fieldNormSubgroup K L) x) = artin x := by
    change e₀ (QuotientGroup.mk' (fieldNormSubgroup K L) x) = artin x
    change (QuotientGroup.quotientKerEquivOfSurjective
      artin.toMonoidHom hsurj)
      ((QuotientGroup.quotientMulEquivOfEq hker.symm)
        (QuotientGroup.mk x)) = artin x
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply ContinuousMulEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (fieldNormSubgroup K L) y
  exact (he' x).trans (he x).symm

end ClassFieldTheory
