/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.AbelianConductorFiniteNormCriterion
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
/-!
# The finite conductor exponent is a genuine local minimum

The local norm condition is satisfied at the conductor exponent and at
every larger exponent, and at no smaller exponent.  The norm is taken from
the whole completion tensor algebra, with no arbitrary place above `v`.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

/-- The conductor exponent is the least index whose higher-unit group lies
in the finite-place tensor norm image. In particular this set is nonempty. -/
theorem IsAbelianConductor.finiteExponent_isLeast_tensorNorm
    {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    {c : RayClassModulus K}
    (hc : IsAbelianConductor K L c)
    (v : HeightOneSpectrum (𝓞 K)) :
    IsLeast (α := ℕ) (fun n =>
      rayLocalHigherUnitGroup v n ≤
        (Units.map (Algebra.norm (v.adicCompletion K)) :
          (v.adicCompletion K ⊗[K] L)ˣ →*
            (v.adicCompletion K)ˣ).range) (c.finitePart v) := by
  constructor
  · exact (hc.finiteExponent_le_iff_higherUnit_le_tensorNorm v
      (c.finitePart v)).mp le_rfl
  · intro n hn
    exact (hc.finiteExponent_le_iff_higherUnit_le_tensorNorm v n).mpr hn

end ClassFieldTheory
