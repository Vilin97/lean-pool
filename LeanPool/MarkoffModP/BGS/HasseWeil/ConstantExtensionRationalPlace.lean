/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionFinitePlaceBridge

/-!
# Rational finite places after exact constant extension

For a finite Galois function-field extension, the degree of a place above a
rational base place divides the relative field degree.  Combining this fact
with the constant-extension degree formula shows that an extension of
constants whose degree is divisible by the Galois degree makes every such
lifted place rational.

This is the numerical-to-geometric bridge used when Stichtenoth chooses the
constant-extension degree to be divisible by the Galois-group order.
-/

open scoped Polynomial

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (M : Type*) [Field M] [Algebra (RatFunc K) M]
  [FiniteDimensional (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) M]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]
  [Algebra M L] [IsScalarTower (RatFunc K) M L] [IsGalois M L]

/-- In a finite Galois tower, a finite place over a degree-one intermediate
place has degree dividing the relative field degree. -/
theorem finiteExtensionFinitePlace_degree_dvd_relative_finrank_of_under_degree_one
    (Q : FiniteExtensionFinitePlace K L)
    (hUnder : finiteExtensionPlaceDegree K M
      (.inl (finitePlaceUnder K M L Q)) = 1) :
    finiteExtensionPlaceDegree K L (.inl Q) ∣ Module.finrank M L := by
  let P := finitePlaceUnder K M L Q
  let Q₀ : FinitePlaceUnderFiber K M L P := ⟨Q, rfl⟩
  have hfiber :=
    finitePlaceUnderFiber_card_mul_ramificationIdx_mul_inertiaDeg_eq_field_finrank
      K M L P Q₀
  have hdegree :=
    finiteExtensionPlaceDegree_inl_eq_mul_relativeInertiaDeg K M L Q
  rw [hUnder, one_mul] at hdegree
  rw [hdegree, ← hfiber]
  exact dvd_mul_left _ _

section ExactConstantExtension

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [DecidableEq C] [DecidableEq S]
  [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [IsGalois (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance exactRationalBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance (priority := 10000) exactRationalBasePolynomialAlgebra :
    Algebra C[X] N :=
  bridgeBasePolynomialAlgebra C N

local instance (priority := 10000) exactRationalTargetPolynomialAlgebra :
    Algebra S[X] (ExactConstantExtension C N S) :=
  bridgeTargetPolynomialAlgebra C S N

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- If the constant-extension degree is divisible by the Galois degree, then
an upstairs finite place whose contraction lies over a rational base place
has degree one over the enlarged constants. -/
theorem exactConstantExtensionUpstairsFinitePlace_degree_eq_one_of_under_degree_one
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S)))
    (hUnder : finiteExtensionPlaceDegree C (RatFunc C)
      (.inl (finitePlaceUnder C (RatFunc C) N
        (exactConstantExtensionDownstairsFinitePlace C S N hExact q))) = 1)
    (hDegree : Module.finrank (RatFunc C) N ∣ Module.finrank C S) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    finiteExtensionPlaceDegree S (ExactConstantExtension C N S)
      (.inl (exactConstantExtensionUpstairsFinitePlace C S N hExact q)) = 1 := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let P := exactConstantExtensionDownstairsFinitePlace C S N hExact q
  have hPdiv : finiteExtensionPlaceDegree C N (.inl P) ∣
      Module.finrank (RatFunc C) N :=
    finiteExtensionFinitePlace_degree_dvd_relative_finrank_of_under_degree_one
      C (RatFunc C) N P hUnder
  have hPdivS : finiteExtensionPlaceDegree C N (.inl P) ∣
      Module.finrank C S := hPdiv.trans hDegree
  rw [exactConstantExtensionFinitePlace_degree_eq_div_gcd C S N hExact q,
    Nat.gcd_eq_right_iff_dvd.mpr hPdivS]
  apply Nat.div_self
  apply Nat.pos_of_ne_zero
  intro hzero
  have hzeroP : finiteExtensionPlaceDegree C N (.inl P) = 0 := by
    simpa [P] using hzero
  obtain ⟨c, hc⟩ := hPdiv
  have hfinrankZero : Module.finrank (RatFunc C) N = 0 := by
    simpa [hzeroP] using hc
  exact (Module.finrank_pos.ne' hfinrankZero)

end ExactConstantExtension

end


end BGS.HasseWeil
