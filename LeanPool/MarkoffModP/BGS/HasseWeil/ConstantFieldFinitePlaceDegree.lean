/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantFieldFinitePlace
public import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointLeadingCoefficient

/-!
# Finite-place degrees under constant-field extension

The finite integral closures before and after constant extension are the same
subring of the enlarged function field.  This file upgrades that ring
equivalence to an equivalence over the original constant field and transports
it to residue fields.  Consequently, if `Q_E` is the finite place obtained
from `Q` after replacing `K` by `E`, then

`deg_K(Q) = [E : K] * deg_E(Q_E)`.

This is the arithmetic content missing from a bare equivalence of finite-place
types: an `E`-rational place is a place of degree `[E : K]` over `K`.
-/

@[expose] public section

open scoped Polynomial

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

attribute [local instance high] Module.Free.of_divisionRing

variable (K E L : Type*) [Field K] [Field E] [Field L]
  [DecidableEq K] [DecidableEq E]
  [DecidableEq (RatFunc K)] [DecidableEq (RatFunc E)]
  [Algebra K E]
  [Algebra (RatFunc K) L] [Algebra (RatFunc E) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]
  [FiniteDimensional (RatFunc E) L]
  [Algebra.IsSeparable (RatFunc E) L]

local instance degreePolynomialCoefficientAlgebra : Algebra K[X] E[X] :=
  (Polynomial.mapRingHom (algebraMap K E)).toAlgebra

local instance degreeBasePolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance degreeExtensionPolynomialAlgebra : Algebra E[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc E) L).comp
    (algebraMap E[X] (RatFunc E)))

local instance degreeBaseFiniteClosureConstantAlgebra :
    Algebra K (RatFuncFiniteIntegralClosure K L) :=
  RingHom.toAlgebra ((algebraMap K[X]
    (RatFuncFiniteIntegralClosure K L)).comp (algebraMap K K[X]))

local instance degreeExtensionFiniteClosureConstantAlgebra :
    Algebra E (RatFuncFiniteIntegralClosure E L) :=
  RingHom.toAlgebra ((algebraMap E[X]
    (RatFuncFiniteIntegralClosure E L)).comp (algebraMap E E[X]))

local instance degreeExtensionFiniteClosureBaseConstantAlgebra :
    Algebra K (RatFuncFiniteIntegralClosure E L) :=
  RingHom.toAlgebra ((algebraMap E
    (RatFuncFiniteIntegralClosure E L)).comp (algebraMap K E))

local instance degreeExtensionFiniteClosureConstantTower :
    IsScalarTower K E (RatFuncFiniteIntegralClosure E L) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The identity equivalence between the two finite integral closures respects
the original constants. -/
def ratFuncFiniteIntegralClosureBaseChangeAlgEquiv
    [Algebra.IsIntegral K E]
    (hcomm : ∀ p : K[X],
      algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) p) =
        algebraMap (RatFunc E) L
          (algebraMap E[X] (RatFunc E)
            (algebraMap K[X] E[X] p))) :
    RatFuncFiniteIntegralClosure K L ≃ₐ[K]
      RatFuncFiniteIntegralClosure E L :=
  { ratFuncFiniteIntegralClosureRingEquiv K E L hcomm with
    commutes' := fun k => by
      apply Subtype.ext
      change algebraMap (RatFunc K) L
          (algebraMap K[X] (RatFunc K) (Polynomial.C k)) =
        algebraMap (RatFunc E) L
          (algebraMap E[X] (RatFunc E)
            (Polynomial.C (algebraMap K E k)))
      simpa using hcomm (Polynomial.C k) }

/-- The finite-integral-closure equivalence transports residue fields as
`K`-algebras. -/
def finitePlaceResidueFieldBaseChangeAlgEquiv
    [Algebra.IsIntegral K E]
    (hcomm : ∀ p : K[X],
      algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) p) =
        algebraMap (RatFunc E) L
          (algebraMap E[X] (RatFunc E)
            (algebraMap K[X] E[X] p)))
    (Q : FiniteExtensionFinitePlace K L) :
    Q.asIdeal.ResidueField ≃ₐ[K]
      ((IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
        (ratFuncFiniteIntegralClosureRingEquiv K E L hcomm) Q).asIdeal).ResidueField :=
  Ideal.residueFieldAlgEquiv Q.asIdeal
    ((IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
      (ratFuncFiniteIntegralClosureRingEquiv K E L hcomm) Q).asIdeal)
    (ratFuncFiniteIntegralClosureBaseChangeAlgEquiv K E L hcomm)
    (by
      change Q.asIdeal =
        (Q.asIdeal.comap
          (ratFuncFiniteIntegralClosureRingEquiv K E L hcomm).symm).comap
            (ratFuncFiniteIntegralClosureRingEquiv K E L hcomm)
      exact (Ideal.comap_of_equiv
        (ratFuncFiniteIntegralClosureRingEquiv K E L hcomm)).symm)

/-- A finite place in the common top function field has base-field degree
equal to the constant-extension degree times its extended-field degree. -/
theorem finiteExtensionFinitePlace_degree_baseChange
    [Algebra.IsIntegral K E]
    (hcomm : ∀ p : K[X],
      algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) p) =
        algebraMap (RatFunc E) L
          (algebraMap E[X] (RatFunc E)
            (algebraMap K[X] E[X] p)))
    (Q : FiniteExtensionFinitePlace K L) :
    finiteExtensionPlaceDegree K L (.inl Q) =
      Module.finrank K E *
        finiteExtensionPlaceDegree E L (.inl
          (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
            (ratFuncFiniteIntegralClosureRingEquiv K E L hcomm) Q)) := by
  let QE : FiniteExtensionFinitePlace E L :=
    IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
      (ratFuncFiniteIntegralClosureRingEquiv K E L hcomm) Q
  let e := finitePlaceResidueFieldBaseChangeAlgEquiv K E L hcomm Q
  rw [finiteExtensionFinitePlace_degree_eq_finrank_residueField K L Q]
  rw [finiteExtensionFinitePlace_degree_eq_finrank_residueField E L QE]
  calc
    Module.finrank K Q.asIdeal.ResidueField =
        Module.finrank K QE.asIdeal.ResidueField :=
      e.toLinearEquiv.finrank_eq
    _ = Module.finrank K E * Module.finrank E QE.asIdeal.ResidueField :=
      (Module.finrank_mul_finrank K E QE.asIdeal.ResidueField).symm

/-- A place is rational over the extended constant field exactly when its
degree over the original constant field is the degree of the constant
extension. -/
theorem finiteExtensionFinitePlace_baseChange_rational_iff
    [Algebra.IsIntegral K E] [FiniteDimensional K E]
    (hcomm : ∀ p : K[X],
      algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) p) =
        algebraMap (RatFunc E) L
          (algebraMap E[X] (RatFunc E)
            (algebraMap K[X] E[X] p)))
    (Q : FiniteExtensionFinitePlace K L) :
    finiteExtensionPlaceDegree E L (.inl
        (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
          (ratFuncFiniteIntegralClosureRingEquiv K E L hcomm) Q)) = 1 ↔
      finiteExtensionPlaceDegree K L (.inl Q) = Module.finrank K E := by
  rw [finiteExtensionFinitePlace_degree_baseChange K E L hcomm Q]
  constructor
  · intro h
    rw [h, Nat.mul_one]
  · intro h
    apply Nat.eq_of_mul_eq_mul_left
      (Module.finrank_pos : 0 < Module.finrank K E)
    simpa using h

/-- Base change identifies the finite places of degree `[E : K]` with the
rational finite places over `E`. -/
def finiteExtensionFinitePlaceDegreeEquivRationalBaseChange
    [Algebra.IsIntegral K E] [FiniteDimensional K E]
    (hcomm : ∀ p : K[X],
      algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) p) =
        algebraMap (RatFunc E) L
          (algebraMap E[X] (RatFunc E)
            (algebraMap K[X] E[X] p))) :
    {Q : FiniteExtensionFinitePlace K L //
        finiteExtensionPlaceDegree K L (.inl Q) = Module.finrank K E} ≃
      FiniteExtensionRationalFinitePlace E L :=
  let e := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
    (ratFuncFiniteIntegralClosureRingEquiv K E L hcomm)
  e.subtypeEquiv fun Q =>
    (finiteExtensionFinitePlace_baseChange_rational_iff
      K E L hcomm Q).symm

/-- Cardinal form of the finite rational-place base-change correspondence. -/
theorem natCard_finiteExtensionRationalFinitePlace_eq_degree_baseChange
    [Algebra.IsIntegral K E] [FiniteDimensional K E] :
    (hcomm : ∀ p : K[X],
      algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) p) =
        algebraMap (RatFunc E) L
          (algebraMap E[X] (RatFunc E)
            (algebraMap K[X] E[X] p))) →
    Nat.card (FiniteExtensionRationalFinitePlace E L) =
      Nat.card {Q : FiniteExtensionFinitePlace K L //
        finiteExtensionPlaceDegree K L (.inl Q) = Module.finrank K E} := by
  intro hcomm
  exact Nat.card_congr
    (finiteExtensionFinitePlaceDegreeEquivRationalBaseChange
      K E L hcomm).symm

end

end BGS.HasseWeil
