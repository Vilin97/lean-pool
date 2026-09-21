/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.Restriction
import Mathlib.Probability.Independence.Basic

/-!
# Structural laws on the carrier

This file restates the law-level structural predicates of
`Homogenization.Probability.RandomField` on the honest-fields carrier
`RegCoeffLaw d = Measure (RegCoeffField d)`, using the carrier endomorphisms of
`Endomorphisms.lean` in place of the raw-`CoeffField` ones.  The semantic shapes
are preserved:

* `IsStationaryR` — invariance under integer translations;
* `IsRestrictionUnitRangeDependentR` — independence of the restriction
  σ-algebras of unit-separated measurable sets (the `MeasurableSet`
  side-conditions are the D7-approved refinement making `RestrictionSigmaR`
  well defined);
* `IsIsotropicInLawR` — invariance under signed-permutation rotations;
* `IsAdjointInvariantInLawR` — invariance under the entrywise adjoint.

Each `Measure.map` is well formed: the underlying endomorphism is measurable
(`measurable_translateReg`, `measurable_rotateReg`, `measurable_adjointReg`), and
we record the corresponding integral/integrable transfer lemmas.

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

namespace Homogenization

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Stationarity -/

/-- A carrier law is **stationary** if it is invariant under every integer
translation (mirrors `IsStationary`). -/
def IsStationaryR (P : RegCoeffLaw d) : Prop :=
  ∀ z : Fin d → ℤ, Measure.map (translateReg (intVecToRealVec z)) P = P

/-- Integral transfer under integer translation for a stationary carrier law. -/
theorem IsStationaryR.integral_comp_translateReg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : RegCoeffLaw d} (hP : IsStationaryR P) (z : Fin d → ℤ)
    (f : RegCoeffField d → E) (hf : AEStronglyMeasurable f P) :
    ∫ a, f (translateReg (intVecToRealVec z) a) ∂P = ∫ a, f a ∂P :=
  integral_comp_eq_of_map_eq (measurable_translateReg (intVecToRealVec z)) (hP z) f hf

/-! ## Unit-range dependence -/

/-- A carrier law is **restriction-unit-range dependent** if the restriction
σ-algebras of any two sup-unit-separated measurable sets are independent.
This is the pointwise-restriction lane, with the `MeasurableSet` refinement,
and is distinct from the exact source-integral/Euclidean locality assumption;
the differing separation predicates preclude a generic P2 implication. -/
def IsRestrictionUnitRangeDependentR (P : RegCoeffLaw d) : Prop :=
  ∀ (U V : Set (Vec d)) (hU : MeasurableSet U) (hV : MeasurableSet V),
    AreUnitSeparated U V →
      ProbabilityTheory.Indep (RestrictionSigmaR U hU) (RestrictionSigmaR V hV) P

/-! ## Isotropy -/

/-- A carrier law is **isotropic** if it is invariant under every
signed-permutation rotation (mirrors `IsIsotropicInLaw`). -/
def IsIsotropicInLawR (P : RegCoeffLaw d) : Prop :=
  ∀ (R : Mat d) (hR : IsSignedPermutationMatrix R), Measure.map (rotateReg R hR) P = P

/-- Integral transfer under a signed-permutation rotation for an isotropic law. -/
theorem IsIsotropicInLawR.integral_comp_rotateReg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : RegCoeffLaw d} (hP : IsIsotropicInLawR P) {R : Mat d}
    (hR : IsSignedPermutationMatrix R) (f : RegCoeffField d → E)
    (hf : AEStronglyMeasurable f P) :
    ∫ a, f (rotateReg R hR a) ∂P = ∫ a, f a ∂P :=
  integral_comp_eq_of_map_eq (measurable_rotateReg R hR) (hP R hR) f hf

/-! ## Adjoint invariance -/

/-- A carrier law is **adjoint invariant** if it is invariant under the entrywise
adjoint (mirrors `IsAdjointInvariantInLaw`). -/
def IsAdjointInvariantInLawR (P : RegCoeffLaw d) : Prop :=
  Measure.map adjointReg P = P

/-- Integral transfer under the adjoint for an adjoint-invariant law. -/
theorem IsAdjointInvariantInLawR.integral_comp_adjointReg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : RegCoeffLaw d} (hP : IsAdjointInvariantInLawR P)
    (f : RegCoeffField d → E) (hf : AEStronglyMeasurable f P) :
    ∫ a, f (adjointReg a) ∂P = ∫ a, f a ∂P :=
  integral_comp_eq_of_map_eq measurable_adjointReg hP f hf

end

end Homogenization
