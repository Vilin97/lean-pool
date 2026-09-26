/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ClosedPlaceEulerRecurrence
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionDivisorClassRecurrence
public import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaEuler

/-!
# Indexed zeta rationality for an exact-constant function field

This file composes the exhaustive divisor-class recurrence with the proved
closed-place Euler recurrence.  The only input at this boundary is the
uniform Riemann--Roch formula for arbitrary divisors.  The denominator still
uses the divisor-degree index; replacing it by the standard degree-one
denominator is a separate constant-field theorem.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier
open scoped Polynomial

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance indexedZetaConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance indexedZetaConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- There is exactly one effective exhaustive divisor of degree zero. -/
theorem finiteExtensionEffectiveDivisorCount_zero :
    finiteExtensionEffectiveDivisorCount K L 0 = 1 := by
  rw [finiteExtensionEffectiveDivisorCount]
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨0, by simp [finiteExtensionEffectiveDivisorDegree]⟩, ?_⟩
  intro D
  apply Subtype.ext
  let : Finsupp.NonTorsionWeight ℕ
      (fun P : FiniteExtensionPlace K L =>
        finiteExtensionPlaceDegree K L P) :=
    Finsupp.nonTorsionWeight_of ℕ
      (w := fun P : FiniteExtensionPlace K L =>
        finiteExtensionPlaceDegree K L P)
      (fun P => (finiteExtensionPlaceDegree_pos K L P).ne')
  apply (Finsupp.weight_eq_zero_iff_eq_zero
    (fun P : FiniteExtensionPlace K L =>
      finiteExtensionPlaceDegree K L P)).mp
  simpa [finiteExtensionEffectiveDivisorDegree, Finsupp.weight_apply,
    nsmul_eq_mul] using D.2

/-- Uniform Riemann--Roch, exact constants, and the exhaustive Euler product
give the indexed rational form of the closed-place zeta series. -/
theorem exists_finiteExtensionClosedPlaceZeta_indexed_rational
    (genus threshold : ℕ)
    (hconstants : algebraicClosure K L =
      (⊥ : IntermediateField K L))
    (hRiemann : HasFiniteExtensionUniformEventualRiemannFormula
      K L genus threshold) :
    ∃ P : Polynomial ℂ,
      P.coeff 0 = 1 ∧
        HasIndexedCurveZetaRationalForm
          (formalPointCountZeta
            (finiteExtensionClosedPlaceExtensionCount K L))
          (Nat.card K) (finiteExtensionDivisorDegreeIndex K L) P := by
  apply
    exists_formalPointCountZeta_indexed_rational_of_effectiveDivisor_recurrences
      (finiteExtensionEffectiveDivisorCount K L)
      (finiteExtensionClosedPlaceExtensionCount K L)
      (Nat.card K) (finiteExtensionDivisorDegreeIndex K L) threshold
      (finiteExtensionDivisorDegreeIndex_pos K L)
      (finiteExtensionEffectiveDivisorCount_zero K L)
      (finiteExtensionEffectiveDivisorPointCountRecurrence K L)
  intro n hn
  exact finiteExtensionEffectiveDivisorCount_indexed_eventual_recurrence_complex
    K L genus threshold n hconstants hRiemann hn

end

end BGS.HasseWeil
