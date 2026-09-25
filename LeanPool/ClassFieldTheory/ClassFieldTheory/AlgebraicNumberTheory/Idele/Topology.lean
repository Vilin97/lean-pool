/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
/-!
# The idele topology

The idele group `I_K` carries the restricted-product topology. This file records
the topological-group structure and the continuity of every local
component map.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


variable (K : Type*) [Field K] [NumberField K]

/-- The local integral-unit subgroup is open in the multiplicative group of a
finite completion. -/
theorem isOpen_finiteLocalUnits (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen
      ((v.adicCompletionIntegers K).units :
        Set (v.adicCompletion K)ˣ) :=
  Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)

instance finiteLocalUnitsOpen :
    Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen
        ((v.adicCompletionIntegers K).units :
          Set (v.adicCompletion K)ˣ)) :=
  ⟨isOpen_finiteLocalUnits K⟩

instance finiteIdeleGroupIsTopologicalGroup :
    IsTopologicalGroup (FiniteIdeleGroup K) :=
  inferInstance

instance ideleGroupIsTopologicalGroup :
    IsTopologicalGroup (IdeleGroup K) :=
  inferInstance

instance finiteIdeleGroupT2Space :
    T2Space (FiniteIdeleGroup K) :=
  inferInstance

instance infiniteAdeleRingT2Space :
    T2Space (NumberField.InfiniteAdeleRing K) := by
  change T2Space ((v : InfinitePlace K) → v.Completion)
  infer_instance

instance infiniteIdeleGroupT2Space :
    T2Space (InfiniteIdeleGroup K) :=
  inferInstance

instance ideleGroupT2Space :
    T2Space (IdeleGroup K) :=
  inferInstance

namespace IdeleGroup

variable {K}

/-- Evaluation at an archimedean place is a continuous homomorphism. -/
def infiniteComponentContinuous (v : InfinitePlace K) :
    IdeleGroup K →ₜ* v.Completionˣ where
  __ := infiniteComponent v
  continuous_toFun :=
    (continuous_apply v).comp
      (ContinuousMulEquiv.piUnits.continuous.comp continuous_fst)

/-- Evaluation at a finite place is a continuous homomorphism. -/
def finiteComponentContinuous (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup K →ₜ* (v.adicCompletion K)ˣ where
  __ := finiteComponent v
  continuous_toFun :=
    (RestrictedProduct.continuous_eval v).comp continuous_snd

@[simp]
theorem infiniteComponentContinuous_apply
    (a : IdeleGroup K) (v : InfinitePlace K) :
    infiniteComponentContinuous v a =
      ContinuousMulEquiv.piUnits a.1 v :=
  rfl

@[simp]
theorem finiteComponentContinuous_apply
    (a : IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    finiteComponentContinuous v a = a.2 v :=
  rfl

end IdeleGroup
