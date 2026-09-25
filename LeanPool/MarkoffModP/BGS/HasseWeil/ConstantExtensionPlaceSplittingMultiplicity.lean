/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionClosedPlaceCount
public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFinitePlaceCompatibility

/-!
# Splitting multiplicity in an exact extension of constants

This file proves the finite-place multiplicity in the standard splitting law
for an exact extension of constants.  The proof does not assume the splitting
law: it proves that inertia is trivial by restricting an inertia element to
the embedded enlarged constant field, computes the relative residue degree
from the already established absolute degree formula, and applies the Galois
fiber identity.
-/

@[expose] public section

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier


/-- A prime ideal in an algebra over a field cannot identify two distinct
elements of that field. -/
private theorem eq_of_algebraMap_sub_mem_prime
    (K R : Type*) [Field K] [CommRing R] [Algebra K R]
    (P : Ideal R) [P.IsPrime] (a b : K)
    (h : algebraMap K R a - algebraMap K R b ∈ P) :
    a = b := by
  by_contra hab
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hunit : IsUnit (algebraMap K R (a - b)) :=
    (isUnit_iff_ne_zero.mpr hne).map (algebraMap K R)
  have hmem : algebraMap K R (a - b) ∈ P := by
    simpa using h
  exact (inferInstance : P.IsPrime).ne_top
    (P.eq_top_of_isUnit_mem hmem hunit)

/-- If the intermediate field is the original function field itself, the
constant quotient is faithful.  This is the exactness input used to kill
inertia. -/
private theorem exactConstantExtensionConstantQuotient_eq_one_imp_eq_one
    (C N S : Type*) [Field C] [Field N] [Field S]
    [Algebra C N] [Algebra C S]
    [FiniteDimensional C S] [IsGalois C S]
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : letI : Field (ExactConstantExtension C N S) :=
          exactConstantExtensionField C N S hExact
        letI : Algebra N (ExactConstantExtension C N S) :=
          exactConstantExtensionBaseAlgebra C N N S
        ExactConstantExtension C N S ≃ₐ[N]
          ExactConstantExtension C N S)
    (hg : letI : Field (ExactConstantExtension C N S) :=
          exactConstantExtensionField C N S hExact
        letI : Algebra N (ExactConstantExtension C N S) :=
          exactConstantExtensionBaseAlgebra C N N S
        exactConstantExtensionConstantQuotient C N N S hExact g = 1) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra N (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C N N S
    g = 1 := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C N N S
  have hker : g ∈
      (exactConstantExtensionConstantQuotient C N N S hExact).ker :=
    MonoidHom.mem_ker.mpr hg
  rw [exactConstantExtensionConstantQuotient_ker C N N S hExact] at hker
  obtain ⟨u, hu⟩ := hker
  have huOne : u = 1 := Subsingleton.elim _ _
  calc
    g = exactConstantExtensionFunctionAutHom C N N S u := hu.symm
    _ = exactConstantExtensionFunctionAutHom C N N S 1 :=
      congrArg (exactConstantExtensionFunctionAutHom C N N S) huOne
    _ = 1 := map_one (exactConstantExtensionFunctionAutHom C N N S)

/-- Arithmetic cancellation used to recover the relative residue degree from
the two absolute degree formulas. -/
private theorem eq_div_gcd_of_mul_eq_mul_div_gcd
    (r d f : ℕ) (hd : 0 < d)
    (h : d * f = r * (d / Nat.gcd r d)) :
    f = r / Nat.gcd r d := by
  apply Nat.eq_of_mul_eq_mul_left hd
  calc
    d * f = r * (d / Nat.gcd r d) := h
    _ = (Nat.gcd r d * (r / Nat.gcd r d)) *
          (d / Nat.gcd r d) := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left r d)]
    _ = (Nat.gcd r d * (d / Nat.gcd r d)) *
          (r / Nat.gcd r d) := by ac_rfl
    _ = d * (r / Nat.gcd r d) := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right r d)]

/-- Cancelling the nonzero complementary factor in the gcd decomposition of
`r`. -/
private theorem eq_gcd_of_mul_div_gcd_eq
    (r d a : ℕ) (hr : 0 < r)
    (h : a * (r / Nat.gcd r d) = r) :
    a = Nat.gcd r d := by
  have hquot : 0 < r / Nat.gcd r d :=
    Nat.div_pos
      (Nat.le_of_dvd hr (Nat.gcd_dvd_left r d))
      (Nat.gcd_pos_of_pos_left d hr)
  apply Nat.eq_of_mul_eq_mul_right hquot
  calc
    a * (r / Nat.gcd r d) = r := h
    _ = Nat.gcd r d * (r / Nat.gcd r d) :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left r d)).symm

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [DecidableEq C] [DecidableEq S]
  [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance splittingBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance splittingBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance splittingBasePolynomialAlgebra : Algebra C[X] N :=
  bridgeBasePolynomialAlgebra C N

local instance splittingTargetPolynomialAlgebra :
    Algebra S[X] (ExactConstantExtension C N S) :=
  bridgeTargetPolynomialAlgebra C S N

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- Every finite place is unramified in an exact extension of constants. -/
theorem exactConstantExtensionFinitePlace_ramificationIdx_eq_one
    (Q : letI : Field (ExactConstantExtension C N S) :=
          exactConstantExtensionField C N S hExact
        letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
          exactConstantExtensionBaseAlgebra C (RatFunc C) N S
        FiniteExtensionFinitePlace C (ExactConstantExtension C N S)) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : Algebra N (ExactConstantExtension C N S) :=
      exactConstantExtensionAlgebra C N S
    letI : SMul N (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module N (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : IsScalarTower (RatFunc C) N
        (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseTower C (RatFunc C) N S
    finitePlaceRelativeRamificationIdx C N
      (ExactConstantExtension C N S) Q = 1 := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc C)
      (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc
      C S N hExact
  let : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul N (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module N (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : IsScalarTower (RatFunc C) N
      (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : IsGalois N (ExactConstantExtension C N S) :=
    exactConstantExtension_isGalois C N N S hExact
  let : Algebra S (RatFuncFiniteIntegralClosure C
      (ExactConstantExtension C N S)) :=
    exactConstantExtensionFiniteIntegralClosureConstantAlgebra
      C N S hExact
  let : MulSemiringAction
      (ExactConstantExtension C N S ≃ₐ[N]
        ExactConstantExtension C N S)
      (RatFuncFiniteIntegralClosure C
        (ExactConstantExtension C N S)) :=
    finiteIntegralClosureGalAction C N
      (ExactConstantExtension C N S)
  rw [← finitePlaceInertiaGroup_card_eq_ramificationIdx C N
    (ExactConstantExtension C N S) Q]
  have hsubsingleton :
      Subsingleton (finitePlaceInertiaGroup C N
        (ExactConstantExtension C N S) Q) := by
    constructor
    intro g h
    apply Subtype.ext
    have inertiaElement_eq_one
        (u : finitePlaceInertiaGroup C N
          (ExactConstantExtension C N S) Q) : u.1 = 1 := by
      have hquot : exactConstantExtensionConstantQuotient
          C N N S hExact u.1 = 1 := by
        apply AlgEquiv.ext
        intro s
        have hinertia :=
          AddSubgroup.mem_inertia.mp u.2
            (algebraMap S (RatFuncFiniteIntegralClosure C
              (ExactConstantExtension C N S)) s)
        rw [exactConstantExtensionConstantQuotient_action_on_finiteNormalization
          C N S hExact N] at hinertia
        exact eq_of_algebraMap_sub_mem_prime S
          (RatFuncFiniteIntegralClosure C
            (ExactConstantExtension C N S)) Q.asIdeal _ _ hinertia
      exact exactConstantExtensionConstantQuotient_eq_one_imp_eq_one
        C N S hExact u.1 hquot
    have hgOne := inertiaElement_eq_one g
    have hhOne := inertiaElement_eq_one h
    exact hgOne.trans hhOne.symm
  let := hsubsingleton
  exact Nat.card_unique

/-- A downstairs finite place of degree `d` has exactly
`gcd([S : C], d)` finite places above it in the exact extension of constants.

The chosen explicit normalization prime supplies one point of the fiber; the
cardinality is that of the entire actual restriction fiber, not merely a
cardinality of a selected presentation. -/
theorem exactConstantExtensionFinitePlace_fiber_card_eq_gcd
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : SMul (RatFunc S) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc S) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : FiniteDimensional (RatFunc S)
        (ExactConstantExtension C N S) :=
      finiteDimensional_over_extendedRatFunc C S N hExact
    letI : Algebra.IsSeparable (RatFunc S)
        (ExactConstantExtension C N S) :=
      isSeparable_over_extendedRatFunc C S N hExact
    letI : Algebra N (ExactConstantExtension C N S) :=
      exactConstantExtensionAlgebra C N S
    letI : SMul N (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module N (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : IsScalarTower (RatFunc C) N
        (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseTower C (RatFunc C) N S
    letI : IsGalois N (ExactConstantExtension C N S) :=
      exactConstantExtension_isGalois C N N S hExact
    Fintype.card (FinitePlaceUnderFiber C N
        (ExactConstantExtension C N S)
        (exactConstantExtensionDownstairsFinitePlace
          C S N hExact q)) =
      Nat.gcd (Module.finrank C S)
        (finiteExtensionPlaceDegree C N
          (.inl (exactConstantExtensionDownstairsFinitePlace
            C S N hExact q))) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc C)
      (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc
      C S N hExact
  let : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc S)
      (ExactConstantExtension C N S) :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc S)
      (ExactConstantExtension C N S) :=
    isSeparable_over_extendedRatFunc C S N hExact
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul N (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module N (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : IsScalarTower (RatFunc C) N
      (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : IsGalois N (ExactConstantExtension C N S) :=
    exactConstantExtension_isGalois C N N S hExact
  let P := exactConstantExtensionDownstairsFinitePlace C S N hExact q
  let Q := exactConstantExtensionCompatibleBaseFinitePlace C S N hExact q
  let Qs := exactConstantExtensionUpstairsFinitePlace C S N hExact q
  let r := Module.finrank C S
  let d := finiteExtensionPlaceDegree C N (.inl P)
  have hUnder : finitePlaceUnder C N
      (ExactConstantExtension C N S) Q = P :=
    exactConstantExtensionCompatibleBaseFinitePlace_under_original
      C S N hExact q
  have hBase := finiteExtensionFinitePlace_degree_baseChange
    C S (ExactConstantExtension C N S)
      (exactConstantExtension_ratFunc_polynomialCompatibility
        C S N hExact) Q
  rw [exactConstantExtensionCompatibleBaseFinitePlace_baseChange]
    at hBase
  have hUpstairs : finiteExtensionPlaceDegree S
      (ExactConstantExtension C N S) (.inl Qs) =
        d / Nat.gcd r d := by
    exact exactConstantExtensionFinitePlace_degree_eq_div_gcd
      C S N hExact q
  have hTop : finiteExtensionPlaceDegree C
      (ExactConstantExtension C N S) (.inl Q) =
        r * (d / Nat.gcd r d) := by
    exact hBase.trans (congrArg (fun n => r * n) hUpstairs)
  have hTower := finiteExtensionPlaceDegree_inl_eq_mul_relativeInertiaDeg
    C N (ExactConstantExtension C N S) Q
  rw [hUnder] at hTower
  have hd : 0 < d := finiteExtensionPlaceDegree_pos C N (.inl P)
  have hInertia : finitePlaceRelativeInertiaDeg C N
      (ExactConstantExtension C N S) Q = r / Nat.gcd r d :=
    eq_div_gcd_of_mul_eq_mul_div_gcd r d _ hd
      (hTower.symm.trans hTop)
  let Q0 : FinitePlaceUnderFiber C N
      (ExactConstantExtension C N S) P := ⟨Q, hUnder⟩
  have hFund :=
    finitePlaceUnderFiber_card_mul_ramificationIdx_mul_inertiaDeg_eq_field_finrank
      C N (ExactConstantExtension C N S) P Q0
  have hRam : finitePlaceRelativeRamificationIdx C N
      (ExactConstantExtension C N S) Q = 1 :=
    exactConstantExtensionFinitePlace_ramificationIdx_eq_one
      C S N hExact Q
  rw [exactConstantExtension_finrank C N S] at hFund
  have hCount : Fintype.card (FinitePlaceUnderFiber C N
      (ExactConstantExtension C N S) P) * (r / Nat.gcd r d) = r := by
    simpa [Q0, hRam, hInertia, r] using hFund
  exact eq_gcd_of_mul_div_gcd_eq r d _ Module.finrank_pos hCount

/-- The explicit `S[X]`-normalization presentation exhausts the actual finite
places of the constant extension, viewed over the original constant field
`C`. -/
noncomputable def exactConstantExtensionPresentedFinitePlaceEquiv :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    IsDedekindDomain.HeightOneSpectrum
        (integralClosure S[X] (ExactConstantExtension C N S)) ≃
      FiniteExtensionFinitePlace C (ExactConstantExtension C N S) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : Algebra C (integralClosure C[X] N) :=
    RingHom.toAlgebra
      ((algebraMap C[X] (integralClosure C[X] N)).comp
        (algebraMap C C[X]))
  letI : IsScalarTower C C[X] (integralClosure C[X] N) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra S[X] (S ⊗[C] integralClosure C[X] N) :=
    bridgeTensorNormalizationPolynomialAlgebra C S N
  letI : Algebra S (integralClosure S[X]
      (ExactConstantExtension C N S)) :=
    RingHom.toAlgebra
      ((algebraMap S[X] (integralClosure S[X]
        (ExactConstantExtension C N S))).comp (algebraMap S S[X]))
  let first := heightOneSpectrumEquivOfAlgEquiv
    (finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N).symm
  let second := finiteExtensionFinitePlaceEquivOfNormalizationAlgEquiv
    S (ExactConstantExtension C N S)
      (S ⊗[C] integralClosure C[X] N)
      (exactConstantExtensionNormalizationAlgEquiv C S N hExact)
  let third := (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
    (ratFuncFiniteIntegralClosureRingEquiv C S
      (ExactConstantExtension C N S)
      (exactConstantExtension_ratFunc_polynomialCompatibility
        C S N hExact))).symm
  exact first.trans (second.trans third)

@[simp]
theorem exactConstantExtensionPresentedFinitePlaceEquiv_apply
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    exactConstantExtensionPresentedFinitePlaceEquiv C S N hExact q =
      exactConstantExtensionCompatibleBaseFinitePlace C S N hExact q := by
  rfl

/-- Restricting the global presentation equivalence to a fixed downstairs
place identifies the presented contraction fiber with the entire actual
place-restriction fiber. -/
noncomputable def exactConstantExtensionPresentedFinitePlaceFiberEquiv
    (P : FiniteExtensionFinitePlace C N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : Algebra N (ExactConstantExtension C N S) :=
      exactConstantExtensionAlgebra C N S
    letI : SMul N (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module N (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : IsScalarTower (RatFunc C) N
        (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseTower C (RatFunc C) N S
    {q : IsDedekindDomain.HeightOneSpectrum
        (integralClosure S[X] (ExactConstantExtension C N S)) //
      exactConstantExtensionDownstairsFinitePlace
        C S N hExact q = P} ≃
      FinitePlaceUnderFiber C N (ExactConstantExtension C N S) P := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  letI : FiniteDimensional (RatFunc C)
      (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc
      C S N hExact
  letI : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  letI : SMul N (ExactConstantExtension C N S) :=
    Algebra.toSMul
  letI : Module N (ExactConstantExtension C N S) :=
    Algebra.toModule
  letI : IsScalarTower (RatFunc C) N
      (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let e := exactConstantExtensionPresentedFinitePlaceEquiv
    C S N hExact
  exact
    { toFun := fun q =>
        ⟨e q.1, by
          rw [exactConstantExtensionPresentedFinitePlaceEquiv_apply]
          exact (exactConstantExtensionCompatibleBaseFinitePlace_under_original
            C S N hExact q.1).trans q.2⟩
      invFun := fun Q =>
        ⟨e.symm Q.1, by
          have hUnder :=
            exactConstantExtensionCompatibleBaseFinitePlace_under_original
              C S N hExact (e.symm Q.1)
          have he : exactConstantExtensionCompatibleBaseFinitePlace
              C S N hExact (e.symm Q.1) = Q.1 := by
            calc
              _ = e (e.symm Q.1) :=
                (exactConstantExtensionPresentedFinitePlaceEquiv_apply
                  C S N hExact (e.symm Q.1)).symm
              _ = Q.1 := e.apply_symm_apply Q.1
          rw [he] at hUnder
          exact hUnder.symm.trans Q.2⟩
      left_inv := fun q => by
        apply Subtype.ext
        exact e.symm_apply_apply q.1
      right_inv := fun Q => by
        apply Subtype.ext
        exact e.apply_symm_apply Q.1 }

/-- The presented finite contraction fiber itself has the standard gcd
cardinality.  This is the presentation-level exhaustiveness form of the
constant-extension splitting law. -/
theorem exactConstantExtensionPresentedFinitePlaceFiber_natCard_eq_gcd
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    Nat.card {q' : IsDedekindDomain.HeightOneSpectrum
        (integralClosure S[X] (ExactConstantExtension C N S)) //
      exactConstantExtensionDownstairsFinitePlace C S N hExact q' =
        exactConstantExtensionDownstairsFinitePlace C S N hExact q} =
      Nat.gcd (Module.finrank C S)
        (finiteExtensionPlaceDegree C N
          (.inl (exactConstantExtensionDownstairsFinitePlace
            C S N hExact q))) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc C)
      (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc
      C S N hExact
  let : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul N (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module N (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : IsScalarTower (RatFunc C) N
      (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let P := exactConstantExtensionDownstairsFinitePlace C S N hExact q
  calc
    Nat.card {q' : IsDedekindDomain.HeightOneSpectrum
        (integralClosure S[X] (ExactConstantExtension C N S)) //
      exactConstantExtensionDownstairsFinitePlace C S N hExact q' = P} =
        Nat.card (FinitePlaceUnderFiber C N
          (ExactConstantExtension C N S) P) :=
      Nat.card_congr
        (exactConstantExtensionPresentedFinitePlaceFiberEquiv
          C S N hExact P)
    _ = Fintype.card (FinitePlaceUnderFiber C N
          (ExactConstantExtension C N S) P) :=
      Nat.card_eq_fintype_card
    _ = Nat.gcd (Module.finrank C S)
        (finiteExtensionPlaceDegree C N (.inl P)) :=
      exactConstantExtensionFinitePlace_fiber_card_eq_gcd
        C S N hExact q

section InfinityConstantEmbedding

local instance splittingInfinityBaseConstantAlgebra :
    Algebra C (RatFuncInfinityIntegers C) :=
  (ratFuncInfinityConstantRingHom C).toAlgebra

local instance splittingInfinityBaseRatFuncAlgebra :
    Algebra (RatFuncInfinityIntegers C) (RatFunc C) :=
  RingHom.toAlgebra
    (SubringClass.subtype ((RatFunc.inftyValuation C).integer))

local instance splittingInfinityExactBaseAlgebra :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    Algebra (RatFuncInfinityIntegers C)
      (ExactConstantExtension C N S) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  exact RingHom.toAlgebra
    ((algebraMap (RatFunc C) (ExactConstantExtension C N S)).comp
      (algebraMap (RatFuncInfinityIntegers C) (RatFunc C)))

/-- The enlarged constants map into the infinity normalization over the
original constant field. -/
noncomputable def exactConstantExtensionConstantToInfinityIntegralClosureRingHom :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    S →+* RatFuncInfinityIntegralClosure C
      (ExactConstantExtension C N S) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : Fintype S := Fintype.ofFinite S
  let f : S →ₐ[C] ExactConstantExtension C N S :=
    Algebra.TensorProduct.includeLeft
  exact
    { toFun := fun s =>
        ⟨f s, by
          refine ⟨Polynomial.X ^ Nat.card S - Polynomial.X, ?_, ?_⟩
          · apply Polynomial.monic_X_pow_sub
            rw [Polynomial.degree_X]
            exact_mod_cast
              (lt_of_lt_of_le Nat.one_lt_two
                (Finite.one_lt_card : 2 ≤ Nat.card S))
          · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
              Polynomial.eval₂_X]
            change (f s) ^ Nat.card S - f s = 0
            rw [← map_pow, Nat.card_eq_fintype_card,
              FiniteField.pow_card s, sub_self]⟩
      map_one' := by ext; exact map_one f
      map_mul' := fun x y => by ext; exact map_mul f x y
      map_zero' := by ext; exact map_zero f
      map_add' := fun x y => by ext; exact map_add f x y }

/-- The enlarged-constant algebra structure on the infinity normalization. -/
@[reducible] noncomputable def
    exactConstantExtensionInfinityIntegralClosureConstantAlgebra :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    Algebra S (RatFuncInfinityIntegralClosure C
      (ExactConstantExtension C N S)) :=
  RingHom.toAlgebra
    (exactConstantExtensionConstantToInfinityIntegralClosureRingHom
      C S N hExact)

end InfinityConstantEmbedding

end

end BGS.HasseWeil
