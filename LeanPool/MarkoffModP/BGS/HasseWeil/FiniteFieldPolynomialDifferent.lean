/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Unramified.Field

/-!
# The different of a separable coefficient extension

Let `S / C` be a finite separable extension of fields.  For the coefficientwise
algebra structure on `S[X]` over `C[X]`, the different ideal is the unit ideal.

The proof first identifies `S[X]` with the polynomial base change
`C[X] ⊗[C] S`.  Formal unramifiedness therefore follows from separability of
`S / C`.  After localizing both polynomial rings, the induced extension of
rational function fields is finite and formally unramified, hence separable.
The local characterization of the Dedekind different then excludes every
maximal ideal from the support of the different.

The final corollary specializes this to arbitrary extensions of finite fields;
their finiteness and separability are supplied by typeclass inference.
-/

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section

variable (C S : Type*) [Field C] [Field S]
  [Algebra C S] [FiniteDimensional C S] [Algebra.IsSeparable C S]

local instance differentCoefficientPolynomialAlgebra : Algebra C[X] S[X] :=
  Polynomial.algebra C S

local instance differentCoefficientPolynomialTower : IsScalarTower C C[X] S[X] :=
  IsScalarTower.of_algebraMap_eq' (by
    ext c
    simp)

local instance differentConstantPolynomialTower : IsScalarTower C S S[X] :=
  IsScalarTower.of_algebraMap_eq' (by
    ext c
    simp)

attribute [local instance] FractionRing.liftAlgebra

local instance differentCoefficientPolynomialModuleFinite : Module.Finite C[X] S[X] := by
  letI : Module.Finite C[X] (C[X] ⊗[C] S) :=
    Module.Finite.base_change C C[X] S
  exact Module.Finite.equiv
    (Algebra.IsPushout.equiv C C[X] S S[X]).toLinearEquiv

local instance differentCoefficientPolynomialFormallyUnramified :
    Algebra.FormallyUnramified C[X] S[X] := by
  letI : Algebra.FormallyUnramified C S :=
    Algebra.FormallyUnramified.of_isSeparable C S
  letI : Algebra.FormallyUnramified C[X] (C[X] ⊗[C] S) :=
    Algebra.FormallyUnramified.base_change C[X]
  exact Algebra.FormallyUnramified.of_equiv
    (Algebra.IsPushout.equiv C C[X] S S[X])

local instance differentCoefficientRationalFunctionAlgebraic :
    Algebra.IsAlgebraic (FractionRing C[X]) (FractionRing S[X]) :=
  isAlgebraic_of_isFractionRing C[X] S[X] ..

local instance differentCoefficientPolynomialIntegralClosure :
    IsIntegralClosure S[X] C[X] (FractionRing S[X]) :=
  IsIntegralClosure.of_isIntegrallyClosed S[X] C[X] (FractionRing S[X])

local instance differentCoefficientRationalFunctionLocalization :
    IsLocalization
      (Algebra.algebraMapSubmonoid S[X] (nonZeroDivisors C[X]))
      (FractionRing S[X]) :=
  IsIntegralClosure.isLocalization C[X] (FractionRing C[X])
    (FractionRing S[X]) S[X]

local instance differentCoefficientRationalFunctionFiniteDimensional :
    FiniteDimensional (FractionRing C[X]) (FractionRing S[X]) :=
  Module.Finite.of_isLocalization C[X] S[X] (nonZeroDivisors C[X])

local instance differentCoefficientRationalFunctionFormallyUnramified :
    Algebra.FormallyUnramified
      (FractionRing C[X]) (FractionRing S[X]) := by
  letI : Algebra.FormallyUnramified C[X] (FractionRing S[X]) := inferInstance
  exact Algebra.FormallyUnramified.localization_base (nonZeroDivisors C[X])

local instance differentCoefficientRationalFunctionSeparable :
    Algebra.IsSeparable (FractionRing C[X]) (FractionRing S[X]) :=
  Algebra.FormallyUnramified.isSeparable
    (FractionRing C[X]) (FractionRing S[X])

omit [FiniteDimensional C S] in
/-- A finite separable extension of coefficient fields induces a formally
unramified extension of polynomial rings. -/
theorem coefficientPolynomial_formallyUnramified :
    Algebra.FormallyUnramified C[X] S[X] :=
  inferInstance

/-- A finite separable extension of coefficient fields induces a separable
extension of the corresponding rational function fields. -/
theorem coefficientRationalFunction_isSeparable :
    Algebra.IsSeparable (FractionRing C[X]) (FractionRing S[X]) :=
  inferInstance

/-- For a finite separable coefficient-field extension, the different of the
coefficientwise polynomial-ring extension is the unit ideal. -/
theorem coefficientPolynomial_differentIdeal_eq_top :
    differentIdeal C[X] S[X] = ⊤ := by
  by_contra htop
  obtain ⟨P, hPmax, hdiffP⟩ :=
    Ideal.exists_le_maximal (differentIdeal C[X] S[X]) htop
  letI : P.IsPrime := hPmax.isPrime
  have hunram : Algebra.IsUnramifiedAt C[X] P := by
    exact
      Algebra.formallyUnramified_iff_forall.mp
        (show Algebra.FormallyUnramified C[X] S[X] from inferInstance)
        ⟨P, hPmax.isPrime⟩
  exact
    (not_dvd_differentIdeal_iff.mpr hunram)
      (Ideal.dvd_iff_le.mpr hdiffP)

/-- In particular, every extension of finite fields has unit different after
coefficientwise extension of polynomial rings. -/
theorem finiteFieldPolynomial_differentIdeal_eq_top
    (k F : Type*) [Field k] [Fintype k] [Field F] [Finite F] [Algebra k F] :
    differentIdeal k[X] F[X] = ⊤ :=
  coefficientPolynomial_differentIdeal_eq_top k F

end

end BGS.HasseWeil
