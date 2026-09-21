/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantFieldFinitePlaceDegree

/-!
# Transporting normalization ideals to finite places

The project's finite places are height-one prime ideals in
`RatFuncFiniteIntegralClosure S T`.  Constant-extension arguments naturally
produce another normalization model together with an equivalence over
`S[X]`.  This file transports height-one ideals, residue fields, residue
degrees, and contractions across such an equivalence.

There is one typeclass subtlety.  A canonical embedding `RatFunc S → T`
induces an `S[X]`-algebra structure on `T`, while a geometric construction
may already carry a propositionally equal polynomial algebra structure.
The algebra-map bridge below turns a pointwise compatibility theorem into an
equivalence with `RatFuncFiniteIntegralClosure S T`; it does not assume the
two structures are definitionally equal.
-/

open scoped Polynomial

open IsDedekindDomain

namespace BGS.HasseWeil

noncomputable section

variable {C A B R : Type*}
  [CommRing C] [CommRing A] [CommRing B] [CommRing R]
  [Algebra C A] [Algebra C B]

/-- An algebra equivalence transports height-one prime ideals. -/
def heightOneSpectrumEquivOfAlgEquiv (e : A ≃ₐ[C] B) :
    HeightOneSpectrum A ≃ HeightOneSpectrum B :=
  HeightOneSpectrum.equivOfRingEquiv e.toRingEquiv

@[simp]
theorem heightOneSpectrumEquivOfAlgEquiv_asIdeal (e : A ≃ₐ[C] B)
    (q : HeightOneSpectrum A) :
    (heightOneSpectrumEquivOfAlgEquiv e q).asIdeal =
      q.asIdeal.comap e.symm :=
  rfl

/-- Residue fields at corresponding height-one ideals are equivalent over
the common coefficient ring. -/
def heightOneSpectrumResidueFieldAlgEquiv (e : A ≃ₐ[C] B)
    (q : HeightOneSpectrum A) :
    q.asIdeal.ResidueField ≃ₐ[C]
      (heightOneSpectrumEquivOfAlgEquiv e q).asIdeal.ResidueField :=
  Ideal.residueFieldAlgEquiv q.asIdeal
    (heightOneSpectrumEquivOfAlgEquiv e q).asIdeal e
    (by
      change q.asIdeal = (q.asIdeal.comap e.symm).comap e
      exact (Ideal.comap_of_equiv e.toRingEquiv).symm)

/-- Corresponding residue fields have the same degree over the common
coefficient field. -/
theorem heightOneSpectrum_residueField_finrank_eq
    {k A B : Type*} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) (q : HeightOneSpectrum A) :
    Module.finrank k q.asIdeal.ResidueField =
      Module.finrank k
        (heightOneSpectrumEquivOfAlgEquiv e q).asIdeal.ResidueField :=
  (heightOneSpectrumResidueFieldAlgEquiv e q).toLinearEquiv.finrank_eq

section Contraction

variable [IsDedekindDomain R] [IsDomain A] [IsDomain B]
  [Algebra R A] [Algebra R B]
  [Algebra.IsIntegral R A] [Algebra.IsIntegral R B]

/-- Transport by an equivalence over the base ring preserves the prime ideal
below a height-one ideal. -/
@[simp]
theorem heightOneSpectrumEquivOfAlgEquiv_under
    (e : A ≃ₐ[R] B) (q : HeightOneSpectrum A) :
    HeightOneSpectrum.under R (heightOneSpectrumEquivOfAlgEquiv e q) =
      HeightOneSpectrum.under R q := by
  apply HeightOneSpectrum.ext
  ext x
  change e.symm (algebraMap R B x) ∈ q.asIdeal ↔
    algebraMap R A x ∈ q.asIdeal
  rw [e.symm.commutes]

/-- The same contraction result when the equivalence is over a smaller
coefficient ring and compatibility with the base algebra maps is supplied
separately. -/
@[simp]
theorem heightOneSpectrumEquivOfAlgEquiv_under_of_algebraMap_eq
    (e : A ≃ₐ[C] B)
    (h : e.toRingHom.comp (algebraMap R A) = algebraMap R B)
    (q : HeightOneSpectrum A) :
    HeightOneSpectrum.under R (heightOneSpectrumEquivOfAlgEquiv e q) =
      HeightOneSpectrum.under R q := by
  apply HeightOneSpectrum.ext
  ext x
  change e.symm (algebraMap R B x) ∈ q.asIdeal ↔
    algebraMap R A x ∈ q.asIdeal
  have hx := DFunLike.congr_fun h x
  rw [← hx]
  change e.symm (e (algebraMap R A x)) ∈ q.asIdeal ↔
    algebraMap R A x ∈ q.asIdeal
  rw [e.symm_apply_apply]

end Contraction

section PolynomialAlgebraBridge

open BGS.CorvajaZannier

variable (S T : Type*) [Field S] [Field T]
  [Algebra (RatFunc S) T]

/-- The polynomial algebra structure on `T` induced by its
`RatFunc S`-algebra structure. -/
@[reducible]
noncomputable def ratFuncInducedPolynomialAlgebra : Algebra S[X] T :=
  RingHom.toAlgebra ((algebraMap (RatFunc S) T).comp
    (algebraMap S[X] (RatFunc S)))

/-- Pointwise compatibility of polynomial algebra maps identifies a chosen
`S[X]`-algebra structure with the structure induced from `RatFunc S`. -/
theorem ratFuncInducedPolynomialAlgebra_eq
    (a : Algebra S[X] T)
    (h : ∀ p : S[X],
      algebraMap (RatFunc S) T (algebraMap S[X] (RatFunc S) p) =
        @algebraMap S[X] T _ _ a p) :
    ratFuncInducedPolynomialAlgebra S T = a := by
  apply Algebra.algebra_ext
  intro p
  exact h p

/-- Equality of the ambient polynomial algebra structures identifies their
integral closures, one of which is the project's rational-function model. -/
noncomputable def integralClosureAlgEquivRatFuncFiniteOfEq
    (a : Algebra S[X] T)
    (h : ratFuncInducedPolynomialAlgebra S T = a) :
    letI := a
    integralClosure S[X] T ≃ₐ[S[X]] RatFuncFiniteIntegralClosure S T := by
  subst a
  exact AlgEquiv.refl

/-- A polynomial restriction formula for `RatFunc S → T` gives the
normalization equivalence needed by the finite-place model. -/
noncomputable def integralClosureAlgEquivRatFuncFiniteOfAlgebraMap
    (a : Algebra S[X] T)
    (h : ∀ p : S[X],
      algebraMap (RatFunc S) T (algebraMap S[X] (RatFunc S) p) =
        @algebraMap S[X] T _ _ a p) :
    letI := a
    integralClosure S[X] T ≃ₐ[S[X]] RatFuncFiniteIntegralClosure S T :=
  integralClosureAlgEquivRatFuncFiniteOfEq S T a
    (ratFuncInducedPolynomialAlgebra_eq S T a h)

variable (A : Type*) [CommRing A] [Algebra S[X] A]

/-- Compose a geometric normalization equivalence with the polynomial
algebra bridge, landing in `RatFuncFiniteIntegralClosure S T`. -/
noncomputable def normalizationAlgEquivRatFuncFiniteOfAlgebraMap
    (a : Algebra S[X] T)
    (e : letI := a
      A ≃ₐ[S[X]] integralClosure S[X] T)
    (h : ∀ p : S[X],
      algebraMap (RatFunc S) T (algebraMap S[X] (RatFunc S) p) =
        @algebraMap S[X] T _ _ a p) :
    A ≃ₐ[S[X]] RatFuncFiniteIntegralClosure S T := by
  letI := a
  exact e.trans
    (integralClosureAlgEquivRatFuncFiniteOfAlgebraMap S T a h)

end PolynomialAlgebraBridge

section FiniteExtensionFinitePlace

open BGS.CorvajaZannier

variable (S T A : Type*) [Field S] [Field T] [CommRing A]
  [Algebra (RatFunc S) T]

local instance finitePlacePolynomialTopAlgebra : Algebra S[X] T :=
  ratFuncInducedPolynomialAlgebra S T

variable [Algebra S[X] A]

local instance finitePlaceSourceConstantAlgebra : Algebra S A :=
  RingHom.toAlgebra ((algebraMap S[X] A).comp (algebraMap S S[X]))

local instance finitePlaceTargetConstantAlgebra :
    Algebra S (RatFuncFiniteIntegralClosure S T) :=
  RingHom.toAlgebra ((algebraMap S[X]
    (RatFuncFiniteIntegralClosure S T)).comp (algebraMap S S[X]))

local instance finitePlaceSourceConstantTower : IsScalarTower S S[X] A :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance finitePlaceTargetConstantTower :
    IsScalarTower S S[X] (RatFuncFiniteIntegralClosure S T) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance finitePlaceTargetIntegral :
    Algebra.IsIntegral S[X] (RatFuncFiniteIntegralClosure S T) :=
  IsIntegralClosure.isIntegral_algebra S[X] T

/-- An equivalence of normalization models over `S[X]` transports their
height-one ideals to the project's finite-place type. -/
def finiteExtensionFinitePlaceEquivOfNormalizationAlgEquiv
    (e : A ≃ₐ[S[X]] RatFuncFiniteIntegralClosure S T) :
    HeightOneSpectrum A ≃ FiniteExtensionFinitePlace S T :=
  heightOneSpectrumEquivOfAlgEquiv (e.restrictScalars S)

@[simp]
theorem finiteExtensionFinitePlaceEquivOfNormalizationAlgEquiv_asIdeal
    (e : A ≃ₐ[S[X]] RatFuncFiniteIntegralClosure S T)
    (q : HeightOneSpectrum A) :
    (finiteExtensionFinitePlaceEquivOfNormalizationAlgEquiv
      S T A e q).asIdeal = q.asIdeal.comap e.symm :=
  rfl

/-- A normalization equivalence transports the residue field at each
height-one ideal as an `S`-algebra. -/
def finiteExtensionFinitePlaceResidueFieldAlgEquivOfNormalization
    (e : A ≃ₐ[S[X]] RatFuncFiniteIntegralClosure S T)
    (q : HeightOneSpectrum A) :
    q.asIdeal.ResidueField ≃ₐ[S]
      (finiteExtensionFinitePlaceEquivOfNormalizationAlgEquiv
        S T A e q).asIdeal.ResidueField :=
  heightOneSpectrumResidueFieldAlgEquiv (e.restrictScalars S) q

/-- The constant-field residue degree is unchanged when replacing a
normalization by an equivalent model. -/
theorem finiteExtensionFinitePlace_residueField_finrank_eq_of_normalization
    (e : A ≃ₐ[S[X]] RatFuncFiniteIntegralClosure S T)
    (q : HeightOneSpectrum A) :
    Module.finrank S q.asIdeal.ResidueField =
      Module.finrank S
        (finiteExtensionFinitePlaceEquivOfNormalizationAlgEquiv
          S T A e q).asIdeal.ResidueField :=
  (finiteExtensionFinitePlaceResidueFieldAlgEquivOfNormalization
    S T A e q).toLinearEquiv.finrank_eq

variable [IsDomain A] [Algebra.IsIntegral S[X] A]

/-- The finite place below a transported ideal agrees with the contraction
of the source ideal to `S[X]`. -/
@[simp]
theorem finiteExtensionFinitePlaceEquivOfNormalizationAlgEquiv_under
    (e : A ≃ₐ[S[X]] RatFuncFiniteIntegralClosure S T)
    (q : HeightOneSpectrum A) :
    HeightOneSpectrum.under S[X]
        (finiteExtensionFinitePlaceEquivOfNormalizationAlgEquiv S T A e q) =
      HeightOneSpectrum.under S[X] q := by
  exact heightOneSpectrumEquivOfAlgEquiv_under e q

end FiniteExtensionFinitePlace

end


end BGS.HasseWeil
