/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Topology.Algebra.Group.Units
/-!
# Ideles of a number field

This file defines the ideles of a number field.

The finite ideles are defined as the restricted product of the multiplicative
groups of the finite completions with respect to the unit groups of their
valuation rings.  This is deliberately not the topology induced from the
finite adele ring: the latter is not the idele topology.  The infinite factor
is the unit group of the finite product of the archimedean completions.
-/

@[expose] public section

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable
section


variable (K : Type*) [Field K] [NumberField K]

/-- The finite idele group attached to a Dedekind domain and its fraction
field.  The number-field definition below specializes this to the ring of
integers. -/
abbrev FiniteIdeleGroupOf
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F] :=
  Πʳ v : HeightOneSpectrum R,
    [(v.adicCompletion F)ˣ, (v.adicCompletionIntegers F).units]

/-- The group of finite ideles of a number field. -/
abbrev FiniteIdeleGroup :=
  FiniteIdeleGroupOf (𝓞 K) K

/-- The product of the multiplicative groups of the archimedean completions. -/
abbrev InfiniteIdeleGroup :=
  (NumberField.InfiniteAdeleRing K)ˣ

/-- The idele group `I_K`. -/
abbrev IdeleGroup :=
  InfiniteIdeleGroup K × FiniteIdeleGroup K

namespace FiniteIdeleGroup

variable {K}

/-- Evaluation of a finite idele at a finite place. -/
def component (v : HeightOneSpectrum (𝓞 K)) :
    FiniteIdeleGroup K →* (v.adicCompletion K)ˣ where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem component_apply (a : FiniteIdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    component v a = a v :=
  rfl

/-- A finite idele is a local integral unit at all but finitely many finite
places. -/
theorem eventually_mem_localUnits (a : FiniteIdeleGroup K) :
    ∀ᶠ v in Filter.cofinite,
      a v ∈ (v.adicCompletionIntegers K).units :=
  a.2

end FiniteIdeleGroup

namespace InfiniteIdeleGroup

variable {K}

/-- The component of an infinite idele at an archimedean place. -/
def component (v : InfinitePlace K) :
    InfiniteIdeleGroup K →* v.Completionˣ :=
  (Pi.evalMonoidHom (fun w : InfinitePlace K ↦ w.Completionˣ) v).comp
    ContinuousMulEquiv.piUnits.toMonoidHom

omit [NumberField K] in
@[simp]
theorem component_apply (a : InfiniteIdeleGroup K) (v : InfinitePlace K) :
    component v a = ContinuousMulEquiv.piUnits a v :=
  rfl

end InfiniteIdeleGroup

namespace IdeleGroup

variable {K}

/-- Algebraically, the finite ideles over a Dedekind domain are the units of
its finite adele ring. -/
def finiteEquivFiniteAdeleUnitsOf
  (R : Type*) [CommRing R] [IsDedekindDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F] :
    FiniteIdeleGroupOf R F ≃*
    (IsDedekindDomain.FiniteAdeleRing R F)ˣ :=
  (RestrictedProduct.unitsEquiv
    (ι := HeightOneSpectrum R)
    (S := fun v : HeightOneSpectrum R ↦ ValuationSubring (v.adicCompletion F))
    (B := fun v : HeightOneSpectrum R ↦ v.adicCompletionIntegers F)
    (𝓕 := Filter.cofinite)
    (fun v : HeightOneSpectrum R ↦ v.adicCompletion F)).symm

/-- The component of an idele at an archimedean place. -/
def infiniteComponent (v : InfinitePlace K) :
    IdeleGroup K →* v.Completionˣ :=
  (InfiniteIdeleGroup.component v).comp (MonoidHom.fst _ _)

/-- The component of an idele at a finite place. -/
def finiteComponent (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup K →* (v.adicCompletion K)ˣ :=
  (FiniteIdeleGroup.component v).comp (MonoidHom.snd _ _)

@[simp]
theorem infiniteComponent_apply (a : IdeleGroup K) (v : InfinitePlace K) :
    infiniteComponent v a = ContinuousMulEquiv.piUnits a.1 v :=
  rfl

@[simp]
theorem finiteComponent_apply (a : IdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    finiteComponent v a = a.2 v :=
  rfl

/-- Algebraically, the finite ideles are the units of the finite adele ring.
The topology on the left is the restricted-product topology and is not
transported through this equivalence. -/
def finiteEquivFiniteAdeleUnits :
    FiniteIdeleGroup K ≃*
      (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ :=
  finiteEquivFiniteAdeleUnitsOf (𝓞 K) K

/-- Algebraically, the idele group is the unit group of the adele ring.

This is only a multiplicative equivalence.  It is intentionally not stated as
a homeomorphism because the idele topology is finer than the topology induced
from the adele ring. -/
def equivAdeleRingUnits :
    IdeleGroup K ≃* (NumberField.AdeleRing (𝓞 K) K)ˣ :=
  ((MulEquiv.refl (InfiniteIdeleGroup K)).prodCongr
      (finiteEquivFiniteAdeleUnits (K := K))).trans
    MulEquiv.prodUnits.symm

@[simp]
theorem equivAdeleRingUnits_fst (a : IdeleGroup K) :
    (MulEquiv.prodUnits (equivAdeleRingUnits a)).1 = a.1 := by
  rfl

@[simp]
theorem equivAdeleRingUnits_snd (a : IdeleGroup K) :
    (MulEquiv.prodUnits (equivAdeleRingUnits a)).2 =
      finiteEquivFiniteAdeleUnits (K := K) a.2 := by
  rfl

end IdeleGroup
