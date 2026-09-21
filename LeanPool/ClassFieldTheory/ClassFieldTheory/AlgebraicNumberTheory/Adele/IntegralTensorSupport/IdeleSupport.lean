/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.LocalTensorDecomposition
/-!
# Finite support for integral relative ideles

This module combines coefficient support with the exceptional places of the
local tensor decomposition, producing one finite set that controls integrality
of a relative idele and its inverse.
-/

open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The single finite support controlling both coefficient integrality
of a relative idele and the integral compatibility of the local tensor decomposition. -/
noncomputable def relativeIdeleLocalTensorDecompositionSupport
    (z : RelativeIdeleGroup K L) :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact
    relativeIdeleCoefficientSupport
        (K := K) (L := L) z ∪
      integralTensorBadPlaces
        (K := K) (L := L)

/-- The support is exposed through this membership characterization. -/

@[simp]
theorem mem_relativeIdeleLocalTensorDecompositionSupport_iff
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ relativeIdeleLocalTensorDecompositionSupport
        (K := K) (L := L) z ↔
      w ∈ relativeIdeleCoefficientSupport
          (K := K) (L := L) z ∨
        w ∈ integralTensorBadPlaces
          (K := K) (L := L) := by
  simp [relativeIdeleLocalTensorDecompositionSupport]

/-- Outside one explicit finite support, the actual finite component of
a relative idele and its inverse are units in every valuation-ring
factor of the local tensor decomposition. -/
theorem relativeIdele_finiteComponent_localTensorDecompositionIntegralUnit_of_notMem
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeIdeleLocalTensorDecompositionSupport
      (K := K) (L := L) z) :
    RelativeLocalTensorDecompositionIntegralUnitAt
      (K := K) (L := L) w
      (RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w z) := by
  have hsep :
      w ∉ relativeIdeleCoefficientSupport
          (K := K) (L := L) z ∧
        w ∉ integralTensorBadPlaces
          (K := K) (L := L) := by
    simpa [relativeIdeleLocalTensorDecompositionSupport] using hw
  exact
    relativeBasisIntegralUnitAt_imp_localTensorDecompositionIntegralUnit_of_notMem
      (K := K) (L := L) w hsep.2
      (relativeIdele_finiteComponent_basisIntegralUnit_of_notMem
        (K := K) (L := L) z w hsep.1)
