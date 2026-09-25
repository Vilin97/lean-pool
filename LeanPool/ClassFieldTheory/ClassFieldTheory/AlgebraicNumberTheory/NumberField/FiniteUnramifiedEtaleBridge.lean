/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FiniteUnramifiedTower
public import Mathlib.RingTheory.Etale.Basic
/-!
# Finite-place unramifiedness bridges for number fields

This file transports finite-place unramifiedness across an equivalence of top
fields and connects the number-theoretic predicate to the commutative-algebra
notions of formal unramifiedness and étaleness for rings of integers.
-/

@[expose] public section

open scoped NumberField

noncomputable section

universe u v w

namespace ClassFieldTower.Martinet

/-- Finite-place unramifiedness is preserved when the top number field is
replaced by an equivalent algebra over the base field. -/
theorem finitePlaceUnramifiedness_congrTop
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M)
    (h : IsUnramifiedAtFinitePlaces K L) :
    IsUnramifiedAtFinitePlaces K M := by
  let hAlgebra : Algebra L M :=
    e.toRingHom.toAlgebra
  let _ := hAlgebra
  let hScalarTower : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (e.commutes x).symm)
  let _ := hScalarTower
  let eLM : L ≃ₐ[L] M :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun _ => rfl)
  let eOLM : (𝓞 L) ≃ₐ[𝓞 L] (𝓞 M) :=
    NumberField.RingOfIntegers.mapAlgEquiv eLM
  let hFormallyUnramified :
      Algebra.FormallyUnramified (𝓞 L) (𝓞 M) :=
    Algebra.FormallyUnramified.of_equiv eOLM
  let _ := hFormallyUnramified
  have hLM : IsUnramifiedAtFinitePlaces L M := by
    intro P
    infer_instance
  exact IsUnramifiedAtFinitePlaces.trans h hLM

/-- A formally unramified extension of rings of integers is unramified at
every finite place of the top number field. -/
theorem finitePlaceUnramifiedness_of_formallyUnramified
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L]
    [Algebra.FormallyUnramified (𝓞 K) (𝓞 L)] :
    IsUnramifiedAtFinitePlaces K L := by
  intro P
  infer_instance

/-- An étale extension of rings of integers is unramified at every finite
place. In particular, this applies to finite étale ring-of-integers
extensions. -/
theorem finitePlaceUnramifiedness_of_etale
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L]
    [Algebra.Etale (𝓞 K) (𝓞 L)] :
    IsUnramifiedAtFinitePlaces K L :=
  finitePlaceUnramifiedness_of_formallyUnramified

end ClassFieldTower.Martinet
