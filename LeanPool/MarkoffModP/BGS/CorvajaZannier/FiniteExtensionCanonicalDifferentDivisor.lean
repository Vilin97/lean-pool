/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalWronskian
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveInfinityDifferentDegree
public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# The canonical different divisor of a finite function-field extension

For a finite separable extension `L / K(X)`, this module packages the local
correction divisor of the differential `dX`.  Its coefficient is the different
exponent at a finite place and `different exponent - 2 * ramification index`
above infinity.  The weighted degree is therefore the total different degree
minus twice the extension degree.
-/

@[expose] public section

open scoped BigOperators nonZeroDivisors Polynomial
open IsDedekindDomain

namespace BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) canonicalDifferentPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance canonicalDifferentPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  ⟨fun r s x => by
    simp only [Algebra.smul_def]
    rw [map_mul]
    change (algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) r) *
      algebraMap (RatFunc K) L s) * x =
      algebraMap K[X] L r * (algebraMap (RatFunc K) L s * x)
    rw [show algebraMap K[X] L r =
      algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) r) by rfl]
    ring⟩

local instance canonicalDifferentFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance canonicalDifferentFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance canonicalDifferentPolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance canonicalDifferentFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance canonicalDifferentFiniteBaseFaithfulSmulFractionRing :
    FaithfulSMul K[X]
      (FractionRing (RatFuncFiniteIntegralClosure K L)) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  have hS := IsFractionRing.injective (RatFuncFiniteIntegralClosure K L)
    (FractionRing (RatFuncFiniteIntegralClosure K L)) hxy
  exact FunctionField.ringOfIntegers.algebraMap_injective K L hS

local instance canonicalDifferentFiniteFractionRingAlgebra :
    Algebra (FractionRing K[X])
      (FractionRing (RatFuncFiniteIntegralClosure K L)) :=
  FractionRing.liftAlgebra K[X]
    (FractionRing (RatFuncFiniteIntegralClosure K L))

local instance canonicalDifferentFiniteFractionRingSeparable :
    Algebra.IsSeparable (FractionRing K[X])
      (FractionRing (RatFuncFiniteIntegralClosure K L)) := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (ratFuncFiniteFractionRingEquiv K).symm.toRingEquiv
    (ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm.toRingEquiv ?_
  ext z
  exact IsFractionRing.algEquiv_commutes
    (ratFuncFiniteFractionRingEquiv K).symm
    (ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm z

local instance canonicalDifferentInfinityIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance canonicalDifferentInfinityIntegralClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance canonicalDifferentInfinityTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance canonicalDifferentInfinityIntegralClosureIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance canonicalDifferentInfinityIntegralClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance canonicalDifferentInfinityIntegralClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance canonicalDifferentInfinityPlaceFintype :
    Fintype (FiniteExtensionInfinityPlace K L) :=
  Set.Finite.fintype
    (IsDedekindDomain.primesOver_finite
      (ratFuncInfinityPlace K).asIdeal
      (RatFuncInfinityIntegralClosure K L))

/-- The finite-place part of the different divisor, with integer coefficients. -/
def finiteExtensionFiniteDifferentDivisor
    (hDifferent : differentIdeal K[X]
      (RatFuncFiniteIntegralClosure K L) ≠ ⊥) :
    FiniteExtensionFinitePlace K L →₀ ℤ :=
  (differentMultiplicityDivisor K[X]
      (RatFuncFiniteIntegralClosure K L) hDifferent).mapRange
    (fun n : ℕ => (n : ℤ)) (by simp)

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
@[simp] theorem finiteExtensionFiniteDifferentDivisor_apply
    (hDifferent : differentIdeal K[X]
      (RatFuncFiniteIntegralClosure K L) ≠ ⊥)
    (q : FiniteExtensionFinitePlace K L) :
    finiteExtensionFiniteDifferentDivisor K L hDifferent q =
      (multiplicity q.asIdeal
        (differentIdeal K[X] (RatFuncFiniteIntegralClosure K L)) : ℤ) := by
  simp [finiteExtensionFiniteDifferentDivisor,
    differentMultiplicityDivisor_apply]

/-- Above infinity, the canonical correction is the different exponent minus
twice the ramification index over the parameter `X⁻¹`. -/
def finiteExtensionInfinityCanonicalDifferentDivisor :
    FiniteExtensionInfinityPlace K L →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm (fun P =>
    (multiplicity P.1
      (differentIdeal (RatFuncInfinityIntegers K)
        (RatFuncInfinityIntegralClosure K L)) : ℤ) -
      2 * (P.1.ramificationIdx (RatFuncInfinityIntegers K) : ℤ))

omit [DecidableEq K] in
@[simp] theorem finiteExtensionInfinityCanonicalDifferentDivisor_apply
    (P : FiniteExtensionInfinityPlace K L) :
    finiteExtensionInfinityCanonicalDifferentDivisor K L P =
      (multiplicity P.1
        (differentIdeal (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K L)) : ℤ) -
        2 * (P.1.ramificationIdx (RatFuncInfinityIntegers K) : ℤ) := by
  simp [finiteExtensionInfinityCanonicalDifferentDivisor]

/-- The exhaustive canonical divisor attached to `dX`: the finite different
at finite places and `different - 2e` above infinity. -/
def finiteExtensionCanonicalDifferentDivisor
    (hDifferent : differentIdeal K[X]
      (RatFuncFiniteIntegralClosure K L) ≠ ⊥) :
    FiniteExtensionPlace K L →₀ ℤ :=
  (finiteExtensionFiniteDifferentDivisor K L hDifferent).sumElim
    (finiteExtensionInfinityCanonicalDifferentDivisor K L)

omit [DecidableEq K] in
@[simp] theorem finiteExtensionCanonicalDifferentDivisor_inl
    (hDifferent : differentIdeal K[X]
      (RatFuncFiniteIntegralClosure K L) ≠ ⊥)
    (q : FiniteExtensionFinitePlace K L) :
    finiteExtensionCanonicalDifferentDivisor K L hDifferent (.inl q) =
      (multiplicity q.asIdeal
        (differentIdeal K[X] (RatFuncFiniteIntegralClosure K L)) : ℤ) := by
  simp [finiteExtensionCanonicalDifferentDivisor]

omit [DecidableEq K] in
@[simp] theorem finiteExtensionCanonicalDifferentDivisor_inr
    (hDifferent : differentIdeal K[X]
      (RatFuncFiniteIntegralClosure K L) ≠ ⊥)
    (P : FiniteExtensionInfinityPlace K L) :
    finiteExtensionCanonicalDifferentDivisor K L hDifferent (.inr P) =
      (multiplicity P.1
        (differentIdeal (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K L)) : ℤ) -
        2 * (P.1.ramificationIdx (RatFuncInfinityIntegers K) : ℤ) := by
  simp [finiteExtensionCanonicalDifferentDivisor]

/-- Residue- and base-place-degree weighted finite different degree. -/
def finiteExtensionFiniteDifferentDegree
    (hDifferent : differentIdeal K[X]
      (RatFuncFiniteIntegralClosure K L) ≠ ⊥) : ℕ :=
  (differentMultiplicityDivisor K[X]
      (RatFuncFiniteIntegralClosure K L) hDifferent).sum
    (fun q e => e * q.asIdeal.inertiaDeg K[X] *
      ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q))

omit [DecidableEq K] in
theorem finiteExtensionInfinity_sum_ramification_inertia_eq_finrank :
    (∑ P : FiniteExtensionInfinityPlace K L,
      P.1.ramificationIdx (RatFuncInfinityIntegers K) *
        P.1.inertiaDeg (RatFuncInfinityIntegers K)) =
      Module.finrank (RatFunc K) L := by
  calc
    _ = Module.finrank (RatFuncInfinityIntegers K)
        (RatFuncInfinityIntegralClosure K L) :=
      Ideal.sum_ramification_inertia_eq_finrank
        (ratFuncInfinityPlace K).asIdeal
          (RatFuncInfinityIntegralClosure K L)
    _ = Module.finrank (RatFunc K) L :=
      (IsFractionRing.finrank_eq
        (RatFuncInfinityIntegers K) (RatFunc K)
          (RatFuncInfinityIntegralClosure K L) L).symm

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- The finite different is nonzero in the separable extension model. -/
theorem finiteExtensionFiniteDifferentIdeal_ne_bot :
    differentIdeal K[X] (RatFuncFiniteIntegralClosure K L) ≠ ⊥ := by
  exact differentIdeal_ne_bot

/-- Degree formula for the canonical different divisor, given the standard
ramification-inertia sum above infinity. -/
theorem finiteExtensionCanonicalDifferentDivisor_degree_of_ramification_sum
    (hDifferent : differentIdeal K[X]
      (RatFuncFiniteIntegralClosure K L) ≠ ⊥)
    (hRamification :
      (∑ P : FiniteExtensionInfinityPlace K L,
        P.1.ramificationIdx (RatFuncInfinityIntegers K) *
          P.1.inertiaDeg (RatFuncInfinityIntegers K)) =
        Module.finrank (RatFunc K) L) :
    finiteExtensionDivisorDegree K L
        (finiteExtensionCanonicalDifferentDivisor K L hDifferent) =
      (finiteExtensionFiniteDifferentDegree K L hDifferent : ℤ) +
        (infinityDifferentDegree K L : ℤ) -
          2 * (Module.finrank (RatFunc K) L : ℤ) := by
  rw [finiteExtensionDivisorDegree, finiteExtensionCanonicalDifferentDivisor,
    Finsupp.sum_sumElim]
  have hfinite :
      (finiteExtensionFiniteDifferentDivisor K L hDifferent).sum
          (fun q e => e *
            (finiteExtensionPlaceDegree K L (.inl q) : ℤ)) =
        (finiteExtensionFiniteDifferentDegree K L hDifferent : ℤ) := by
    rw [finiteExtensionFiniteDifferentDivisor,
      Finsupp.sum_mapRange_index (fun _ => by simp)]
    simp only [finiteExtensionPlaceDegree]
    rw [finiteExtensionFiniteDifferentDegree, Nat.cast_finsupp_sum]
    apply Finsupp.sum_congr
    intro q hq
    push_cast
    ring
  have hfinite' :
      (finiteExtensionFiniteDifferentDivisor K L hDifferent).sum
          ((fun v e => e *
            (finiteExtensionPlaceDegree K L v : ℤ)) ∘ Sum.inl) =
        (finiteExtensionFiniteDifferentDegree K L hDifferent : ℤ) := by
    change
      (finiteExtensionFiniteDifferentDivisor K L hDifferent).sum
          (fun q e => e *
            (finiteExtensionPlaceDegree K L (.inl q) : ℤ)) = _
    exact hfinite
  rw [hfinite']
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simp only [Function.comp_apply, finiteExtensionPlaceDegree,
    finiteExtensionInfinityCanonicalDifferentDivisor_apply]
  rw [infinityDifferentDegree, Nat.cast_sum]
  push_cast
  rw [← hRamification]
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hdiff :
      (∑ P : FiniteExtensionInfinityPlace K L,
        (multiplicity P.1
          (differentIdeal (RatFuncInfinityIntegers K)
            (RatFuncInfinityIntegralClosure K L)) : ℤ) *
          (P.1.inertiaDeg (RatFuncInfinityIntegers K) : ℤ)) =
      ∑ P : FiniteExtensionInfinityPlace K L,
        (P.1.inertiaDeg (RatFuncInfinityIntegers K) : ℤ) *
          (multiplicity P.1
            (differentIdeal (RatFuncInfinityIntegers K)
              (RatFuncInfinityIntegralClosure K L)) : ℤ) := by
    apply Finset.sum_congr rfl
    intro P hP
    ring
  rw [hdiff]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

/-- The canonical different divisor has weighted degree equal to the finite
different degree plus the infinity different degree minus twice `[L : K(X)]`. -/
theorem finiteExtensionCanonicalDifferentDivisor_degree :
    finiteExtensionDivisorDegree K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) =
      (finiteExtensionFiniteDifferentDegree K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L) : ℤ) +
        (infinityDifferentDegree K L : ℤ) -
          2 * (Module.finrank (RatFunc K) L : ℤ) := by
  exact finiteExtensionCanonicalDifferentDivisor_degree_of_ramification_sum
    K L (finiteExtensionFiniteDifferentIdeal_ne_bot K L)
      (finiteExtensionInfinity_sum_ramification_inertia_eq_finrank K L)

/-- Separate finite-discriminant and complementary infinity bounds combine
into the expected canonical bound `totalDifferent - 2 * [L : K(X)]`. -/
theorem finiteExtensionCanonicalDifferentDivisor_degree_le_of_bounds
    (finiteDiscriminantDegree totalDifferentBudget : ℕ)
    (hFinite : finiteExtensionFiniteDifferentDegree K L
        (finiteExtensionFiniteDifferentIdeal_ne_bot K L) ≤
      finiteDiscriminantDegree)
    (hInfinity : (infinityDifferentDegree K L : ℤ) ≤
      (totalDifferentBudget : ℤ) - (finiteDiscriminantDegree : ℤ)) :
    finiteExtensionDivisorDegree K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) ≤
      (totalDifferentBudget : ℤ) -
        2 * (Module.finrank (RatFunc K) L : ℤ) := by
  rw [finiteExtensionCanonicalDifferentDivisor_degree]
  have hFiniteInt :
      (finiteExtensionFiniteDifferentDegree K L
        (finiteExtensionFiniteDifferentIdeal_ne_bot K L) : ℤ) ≤
        (finiteDiscriminantDegree : ℤ) := by
    exact_mod_cast hFinite
  omega

end

end BGS.CorvajaZannier
