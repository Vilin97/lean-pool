/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindCanonicalDifferentScaling
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindLocalizationDerivationPreservation
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalDifferentDivisor
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PerfectConstants
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveAuxiliaryFinitePlace
public import Mathlib.Tactic

/-!
# Canonical derivation scalings at finite extension places

This file instantiates the abstract different-annihilator construction for a
finite separable extension of `K(X)`.  If the Frobenius-constant derivation is
normalized by `D(X) = 1`, the resulting scalar has order equal to the finite
coefficient of the canonical different divisor.  The quotient-rule bridge then
shows that the scaled derivation preserves the complete localized DVR used by
the finite-place Wronskian estimates.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

open scoped nonZeroDivisors Polynomial
open IsDedekindDomain

variable (K : Type*) [Field K] [PerfectField K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]
variable {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]

local instance (priority := 10) canonicalScalingPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance canonicalScalingPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance canonicalScalingFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance canonicalScalingFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance canonicalScalingPolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance canonicalScalingFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance canonicalScalingFiniteBaseFaithfulSmulFractionRing :
    FaithfulSMul K[X]
      (FractionRing (RatFuncFiniteIntegralClosure K L)) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  have hS := IsFractionRing.injective (RatFuncFiniteIntegralClosure K L)
    (FractionRing (RatFuncFiniteIntegralClosure K L)) hxy
  exact FunctionField.ringOfIntegers.algebraMap_injective K L hS

local instance canonicalScalingFiniteFractionRingAlgebra :
    Algebra (FractionRing K[X])
      (FractionRing (RatFuncFiniteIntegralClosure K L)) :=
  FractionRing.liftAlgebra K[X]
    (FractionRing (RatFuncFiniteIntegralClosure K L))

local instance canonicalScalingFiniteFractionRingSeparable :
    Algebra.IsSeparable (FractionRing K[X])
      (FractionRing (RatFuncFiniteIntegralClosure K L)) := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (ratFuncFiniteFractionRingEquiv K).symm.toRingEquiv
    (ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm.toRingEquiv ?_
  ext z
  exact IsFractionRing.algEquiv_commutes
    (ratFuncFiniteFractionRingEquiv K).symm
    (ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm z

/-- At every finite place, the normalized Frobenius-constant derivation admits
a scalar whose order is the canonical different coefficient and whose scalar
multiple preserves the localized DVR. -/
theorem exists_finiteExtensionFinitePlace_canonicalDifferent_scaling_certificate
    (D : Derivation (frobeniusSubfield L p) L L)
    (hDX : D (algebraMap (RatFunc K) L RatFunc.X) = 1)
    (q : FiniteExtensionFinitePlace K L) :
    ∃ c : L, c ≠ 0 ∧
      finitePlaceOrder q c =
        finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L) (.inl q) ∧
      ∀ r : FiniteExtensionFinitePlaceLocalRing K L q,
        ∃ s : FiniteExtensionFinitePlaceLocalRing K L q,
          (c • D) (finiteExtensionFinitePlaceLocalizationToField
              (K := K) (L := L) q r) =
            finiteExtensionFinitePlaceLocalizationToField
              (K := K) (L := L) q s := by
  let : Algebra K L :=
    RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
      (algebraMap K (RatFunc K)))
  let : IsScalarTower K (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K K[X] L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let F := frobeniusSubfield L p
  let : Algebra K F :=
    (perfectConstantsToFrobeniusSubfield (K := K) (L := L) (p := p)).toAlgebra
  let : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq' rfl
  let Ds : Derivation K K[X] K[X] := Polynomial.mkDerivation K 1
  let E : Derivation K L L := D.restrictScalars K
  have hE : ∀ s : K[X],
      E (algebraMap K[X] L s) = algebraMap K[X] L (Ds s) := by
    have hder : E.compAlgebraMap K[X] =
        (Algebra.linearMap K[X] L).compDer Ds := by
      apply Polynomial.derivation_ext
      calc
        (E.compAlgebraMap K[X]) Polynomial.X =
            E (algebraMap K[X] L Polynomial.X) := rfl
        _ = D (algebraMap (RatFunc K) L RatFunc.X) := by
          rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) L]
          rw [RatFunc.algebraMap_X]
          rfl
        _ = 1 := hDX
        _ = ((Algebra.linearMap K[X] L).compDer Ds) Polynomial.X := by
          simp [Ds]
    intro s
    exact Derivation.congr_fun hder s
  obtain ⟨δ, hδ, _hδmem, _hδmult, hδorder, _hδann, hδpreserves⟩ :=
    exists_finitePlace_different_localGenerator_scaling_certificate
      (C := K) (S := K[X]) (T := RatFuncFiniteIntegralClosure K L)
      (U := L) (F := L) q Ds E hE
  let c : L := algebraMap (RatFuncFiniteIntegralClosure K L) L δ
  have hc : c ≠ 0 := by
    exact (IsFractionRing.injective (RatFuncFiniteIntegralClosure K L) L).ne hδ
  refine ⟨c, hc, ?_, ?_⟩
  · simpa only [c, finiteExtensionCanonicalDifferentDivisor_inl] using hδorder
  · let := finiteExtensionFinitePlaceLocalAlgebra (K := K) (L := L) q
    let : IsScalarTower (RatFuncFiniteIntegralClosure K L)
        (FiniteExtensionFinitePlaceLocalRing K L q) L := by
      apply IsScalarTower.of_algebraMap_eq'
      exact (finiteExtensionFinitePlaceLocalizationToField_comp_algebraMap
        (K := K) (L := L) q).symm
    have hGlobal : ∀ t : RatFuncFiniteIntegralClosure K L,
        ∃ t' : RatFuncFiniteIntegralClosure K L,
          (c • D) (algebraMap (RatFuncFiniteIntegralClosure K L) L t) =
            algebraMap (RatFuncFiniteIntegralClosure K L) L t' := by
      intro t
      obtain ⟨t', ht'⟩ := hδpreserves t
      refine ⟨t', ?_⟩
      simpa only [c, E, Derivation.smul_apply, Algebra.smul_def,
        Algebra.algebraMap_self_apply, Derivation.restrictScalars_apply] using ht'
    exact ambientDerivation_preserves_localizationAtPrime_of_preserves
      q.asIdeal (c • D) hGlobal

end

end BGS.CorvajaZannier
