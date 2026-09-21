/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.BaseChange
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormalClosureNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
/-!
# Normalized finite-prime ideles

This file defines the idele supported at one finite place with normalized
local order one, and computes its associated fractional ideal and ideal
class. These constructions are independent of class field theory.
-/

open scoped NumberField

noncomputable section

namespace IdeleGroup

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- The idele supported at `v` whose normalized local order is one. -/
def finitePrimeIdele
    (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup K :=
  finitePlaceIdele v (FiniteIdeleGroup.chosenLocalOrderSection v 1)

/-- The fractional ideal of the normalized one-place prime idele is the
corresponding prime ideal. -/
@[simp]
theorem fractionalIdeal_finitePrimeIdele
    (v : HeightOneSpectrum (𝓞 K)) :
    fractionalIdeal (finitePrimeIdele v) =
      FractionalIdealGroup.prime v := by
  apply FractionalIdealGroup.ext_count
  intro w
  change
    FractionalIdeal.count K w
        ((FiniteIdeleGroup.fractionalIdeal
          (finitePrimeIdele v).2 :
            FractionalIdealGroup K) :
          FractionalIdeal
            (nonZeroDivisors (𝓞 K)) K) =
      FractionalIdeal.count K w
        ((FractionalIdealGroup.prime v :
            FractionalIdealGroup K) :
          FractionalIdeal
            (nonZeroDivisors (𝓞 K)) K)
  rw [FiniteIdeleGroup.fractionalIdeal]
  change
    FractionalIdeal.count K w
        (((FractionalIdealGroup.factorization
          (FiniteIdeleGroup.valuationVector
            (finitePrimeIdele v).2) :
              FractionalIdealGroup K) :
            FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K)) =
      FractionalIdeal.count K w
        (v.asIdeal :
          FractionalIdeal
            (nonZeroDivisors (𝓞 K)) K)
  rw [FractionalIdealGroup.count_factorization,
    FiniteIdeleGroup.valuationVector_apply]
  by_cases hw : w = v
  · subst w
    rw [← finiteComponent_apply, finitePrimeIdele,
      finitePlaceIdele_finiteComponent_same,
      FiniteIdeleGroup.localOrder_chosenLocalOrderSection,
      FractionalIdeal.count_self]
  · rw [← finiteComponent_apply, finitePrimeIdele,
      finitePlaceIdele_finiteComponent_of_ne
        v w (FiniteIdeleGroup.chosenLocalOrderSection v 1) hw,
      map_one]
    change
      0 =
        FractionalIdeal.count K w
          (v.asIdeal :
            FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K)
    rw [FractionalIdeal.count_maximal_coprime K w (Ne.symm hw)]

/-- The ordinary ideal class of the normalized one-place prime idele is the
class of the corresponding prime ideal. -/
@[simp]
theorem idealClass_finitePrimeIdele
    (v : HeightOneSpectrum (𝓞 K)) :
    idealClass (finitePrimeIdele v) =
      ClassGroup.mk K (FractionalIdealGroup.prime v) := by
  change
    ClassGroup.mk K (fractionalIdeal (finitePrimeIdele v)) =
      ClassGroup.mk K (FractionalIdealGroup.prime v)
  rw [fractionalIdeal_finitePrimeIdele]

end IdeleGroup
