/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageBaseChange
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveBidegreeBridge
import Mathlib.FieldTheory.RatFunc.Luroth

/-!
# Constants in an absolutely irreducible plane-curve function field

This file develops the constant-field step needed by the function-field
Bombieri--Stepanov proof of Hasse--Weil.  The key algebraic point is that,
after enlarging the constants inside the original function field, the
base-changed plane equation is still the primitive cleared minimal relation
of the second coordinate over the first-coordinate rational subfield.

No geometric Hasse--Weil statement is assumed here.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open Polynomial

noncomputable section

/-- The iterated-polynomial presentation evaluates at the same ordered pair
as the original bivariate polynomial. -/
theorem evalBivariate_planeCurveToBivariate
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : MvPolynomial (Fin 2) K) (x y : L) :
    evalBivariate y x (planeCurveToBivariate K f) =
      MvPolynomial.eval₂ (algebraMap K L) ![x, y] f := by
  let lhs : MvPolynomial (Fin 2) K →+* L :=
    (Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom (algebraMap K L) y) x).comp
        (planeCurveToBivariate K).toRingEquiv.toRingHom
  let rhs : MvPolynomial (Fin 2) K →+* L :=
    MvPolynomial.eval₂Hom (algebraMap K L) ![x, y]
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, rhs]
    · intro i
      fin_cases i <;> simp [lhs, rhs]
  change lhs f = rhs f
  rw [hhom]

/-- Swap the iterated presentation so that the second affine coordinate is
the outer polynomial variable. -/
def planeCurveSecondOuterRelation
    (K : Type*) [Field K] (f : MvPolynomial (Fin 2) K) :
    Polynomial (Polynomial K) :=
  transposeBivariate (planeCurveToBivariate K f)

theorem evalBivariate_planeCurveSecondOuterRelation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : MvPolynomial (Fin 2) K) (x y : L) :
    evalBivariate x y (planeCurveSecondOuterRelation K f) =
      MvPolynomial.eval₂ (algebraMap K L) ![x, y] f := by
  rw [planeCurveSecondOuterRelation, evalBivariate_transposeBivariate]
  exact evalBivariate_planeCurveToBivariate f x y

/-- Irreducibility is preserved by the two variable-presentation
equivalences. -/
theorem planeCurveSecondOuterRelation_irreducible
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) :
    Irreducible (planeCurveSecondOuterRelation K f) := by
  have hfirst : Irreducible (planeCurveToBivariate K f) :=
    hf.map (planeCurveToBivariate K).toMulEquiv
  rw [planeCurveSecondOuterRelation, transposeBivariate_eq_bivariateSwap]
  exact hfirst.map (Polynomial.Bivariate.swap (R := K)).toMulEquiv

/-- The outer degree in the swapped presentation is exactly the degree in
the second affine coordinate. -/
theorem planeCurveSecondOuterRelation_natDegree
    (K : Type*) [Field K] (f : MvPolynomial (Fin 2) K) :
    (planeCurveSecondOuterRelation K f).natDegree =
      MvPolynomial.degreeOf 1 f := by
  rw [planeCurveSecondOuterRelation,
    transposeBivariate_planeCurveToBivariate,
    bivariateEquiv_symm_natDegree_eq_degreeOf_one]

/-- Over any enlarged constant field inside the ambient function field, an
irreducible plane equation is associated to the primitive cleared minimal
relation of the second coordinate. -/
theorem primitiveClearedMinpolyRelation_associated_planeRelation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (x y : L) (hx : Transcendental K x)
    (hy : IsIntegral (IntermediateField.adjoin K {x}) y)
    (hzero : MvPolynomial.eval₂ (algebraMap K L) ![x, y] f = 0) :
    Associated (primitiveClearedMinpolyRelation x hx y)
      (planeCurveSecondOuterRelation K f) := by
  have hdvd : primitiveClearedMinpolyRelation x hx y ∣
      planeCurveSecondOuterRelation K f := by
    apply primitiveClearedMinpolyRelation_dvd_of_evalBivariate_eq_zero
      x hx y hy
    simpa [evalBivariate_planeCurveSecondOuterRelation] using hzero
  exact (primitiveClearedMinpolyRelation_irreducible x hx y hy).associated_of_dvd
    (planeCurveSecondOuterRelation_irreducible hf) hdvd

/-- Consequently the minimal-polynomial degree over `K(x)` is the second
coordinate degree of the irreducible plane relation. -/
theorem minpoly_natDegree_eq_planeRelation_secondDegree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (x y : L) (hx : Transcendental K x)
    (hy : IsIntegral (IntermediateField.adjoin K {x}) y)
    (hzero : MvPolynomial.eval₂ (algebraMap K L) ![x, y] f = 0) :
    (minpoly (IntermediateField.adjoin K {x}) y).natDegree =
      MvPolynomial.degreeOf 1 f := by
  have hassociated :=
    primitiveClearedMinpolyRelation_associated_planeRelation
      f hf x y hx hy hzero
  calc
    (minpoly (IntermediateField.adjoin K {x}) y).natDegree =
        (primitiveClearedMinpolyRelation x hx y).natDegree :=
      (primitiveClearedMinpolyRelation_natDegree x hx y hy).symm
    _ = (planeCurveSecondOuterRelation K f).natDegree := by
      apply Nat.le_antisymm
      · exact Polynomial.natDegree_le_of_dvd hassociated.dvd
          (planeCurveSecondOuterRelation_irreducible hf).ne_zero
      · exact Polynomial.natDegree_le_of_dvd hassociated.symm.dvd
          (primitiveClearedMinpolyRelation_ne_zero x hx y)
    _ = MvPolynomial.degreeOf 1 f :=
      planeCurveSecondOuterRelation_natDegree K f

/-- A rational function field has no constants algebraic over its coefficient
field beyond the coefficient field itself.  Lüroth's theorem makes this a
short argument: any nontrivial intermediate field has a transcendental
generator, whereas every element of the relative algebraic closure is
algebraic. -/
theorem ratFunc_algebraicClosure_eq_bot (K : Type*) [Field K] :
    algebraicClosure K (RatFunc K) = ⊥ := by
  by_contra hne
  let E : IntermediateField K (RatFunc K) :=
    algebraicClosure K (RatFunc K)
  have hmem : RatFunc.Luroth.generator E ∈ E :=
    RatFunc.Luroth.generator_mem
  have halgebraic : IsAlgebraic K (RatFunc.Luroth.generator E) :=
    mem_algebraicClosure_iff.mp hmem
  exact (RatFunc.Luroth.transcendental_generator hne) halgebraic

/-- The field generated by one transcendental element has the same exact
constant field as a rational function field. -/
theorem adjoin_transcendental_algebraicClosure_eq_bot
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (x : L) (hx : Transcendental K x) :
    algebraicClosure K (IntermediateField.adjoin K {x}) = ⊥ := by
  let e : RatFunc K ≃ₐ[K] IntermediateField.adjoin K {x} :=
    RatFunc.algEquivOfTranscendental x hx
  have hmap := algebraicClosure.map_eq_of_algEquiv e
  rw [ratFunc_algebraicClosure_eq_bot] at hmap
  simpa only [IntermediateField.map_bot] using hmap.symm

/-- **Exact constant field of an absolutely irreducible plane curve.**

If the defining equation remains irreducible over an algebraic closure and
the second coordinate is separating, then the only elements of its function
field algebraic over `K` are the elements of `K` itself.

The proof compares the degree over `K(x)` with the degree after adjoining the
relative algebraic closure `E` to the constants.  Absolute irreducibility and
the cleared-minimal-polynomial relation show that both degrees are exactly
`degreeOf 1 f`.  The tower formula therefore forces `E(x) = K(x)`.  Finally,
the rational-function constant-field theorem above forces every element of
`E` back into `K`. -/
theorem planeCurveFunctionField_algebraicClosure_eq_bot
    {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K)
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure habsolute
    letI := planeCurveCoordinateRing_isDomain hf
    algebraicClosure K (PlaneCurveFunctionField f) = ⊥ := by
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure habsolute
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L := PlaneCurveFunctionField f
  let E : IntermediateField K L := algebraicClosure K L
  let x : L := planeCurveFunction f 0
  let y : L := planeCurveFunction f 1
  let F : IntermediateField K L := IntermediateField.adjoin K {x}
  let A : IntermediateField E L := IntermediateField.adjoin E {x}
  have hdegree : 0 < MvPolynomial.degreeOf 1 f :=
    degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond
  have hxK : Transcendental K x :=
    firstCoordinate_transcendental hf hdegree
  have hxE : Transcendental E x := hxK.algebraicClosure
  let fE : MvPolynomial (Fin 2) E :=
    MvPolynomial.map (algebraMap K E) f
  have hfE : Irreducible fE :=
    irreducible_map_of_irreducible_map_algebraicClosure
      (algebraMap K E) f habsolute
  have hdegreeE : MvPolynomial.degreeOf 1 fE =
      MvPolynomial.degreeOf 1 f :=
    degreeOf_map_eq_of_injective (algebraMap K E)
      (algebraMap K E).injective 1 f
  have hzeroE :
      MvPolynomial.eval₂ (algebraMap E L) ![x, y] fE = 0 := by
    simp only [fE, MvPolynomial.eval₂_map]
    change MvPolynomial.eval₂
      ((algebraMap E L).comp (algebraMap K E)) ![x, y] f = 0
    have hcomp : (algebraMap E L).comp (algebraMap K E) =
        algebraMap K L := by
      ext c
      exact IsScalarTower.algebraMap_apply K E L c
    rw [hcomp]
    have hcoordinates : ![x, y] = planeCurveFunction f := by
      funext i
      fin_cases i <;> rfl
    rw [hcoordinates]
    exact eval₂_planeCurveFunction_eq_zero f
  have hFA : F ≤ A.restrictScalars K := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact IntermediateField.subset_adjoin E {x} (Set.mem_singleton x)
  letI : Algebra F A := (IntermediateField.inclusion hFA).toAlgebra
  letI : IsScalarTower F A L :=
    IsScalarTower.of_algebraMap_eq' (R := F) (S := A) (A := L) rfl
  have hpoly : polynomialOverFirstCoordinate f ≠ 0 :=
    polynomialOverFirstCoordinate_ne_zero_of_irreducible hf hdegree
  have hyF : IsAlgebraic F y := by
    exact secondCoordinate_isAlgebraic_over_first f hpoly
  have hyAalg : IsAlgebraic A y :=
    hyF.extendScalars (algebraMap F A).injective
  have hyA : IsIntegral A y := isAlgebraic_iff_isIntegral.mp hyAalg
  have hminA : (minpoly A y).natDegree = MvPolynomial.degreeOf 1 f := by
    calc
      (minpoly A y).natDegree = MvPolynomial.degreeOf 1 fE :=
        minpoly_natDegree_eq_planeRelation_secondDegree
          fE hfE x y hxE hyA hzeroE
      _ = MvPolynomial.degreeOf 1 f := hdegreeE
  have hpairK : IntermediateField.adjoin K {x, y} = ⊤ := by
    rw [← range_planeCurveFunction f]
    exact adjoin_planeCurveFunctions_eq_top
  have hpairE : IntermediateField.adjoin E {x, y} = ⊤ := by
    apply top_unique
    intro z _hz
    have hzK : z ∈ IntermediateField.adjoin K {x, y} := by
      rw [hpairK]
      trivial
    have hle : IntermediateField.adjoin K {x, y} ≤
        (IntermediateField.adjoin E {x, y}).restrictScalars K := by
      apply IntermediateField.adjoin_le_iff.mpr
      intro u hu
      exact IntermediateField.subset_adjoin E {x, y} hu
    exact hle hzK
  have htopA : IntermediateField.adjoin A {y} = ⊤ := by
    apply IntermediateField.restrictScalars_injective E
    rw [IntermediateField.restrictScalars_top]
    change (IntermediateField.adjoin
      (IntermediateField.adjoin E {x}) {y}).restrictScalars E = ⊤
    rw [IntermediateField.adjoin_adjoin_left]
    simpa only [Set.singleton_union] using hpairE
  letI : FiniteDimensional A (IntermediateField.adjoin A {y}) :=
    IntermediateField.adjoin.finiteDimensional hyA
  letI : FiniteDimensional A (⊤ : IntermediateField A L) := by
    rw [← htopA]
    infer_instance
  letI : FiniteDimensional A L :=
    IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  have hfinA : Module.finrank A L = MvPolynomial.degreeOf 1 f := by
    calc
      Module.finrank A L = Module.finrank A
          (⊤ : IntermediateField A L) := by
        rw [IntermediateField.finrank_top']
      _ = Module.finrank A (IntermediateField.adjoin A {y}) := by
        rw [htopA]
      _ = (minpoly A y).natDegree :=
        IntermediateField.adjoin.finrank hyA
      _ = MvPolynomial.degreeOf 1 f := hminA
  letI : FiniteDimensional F L :=
    (finiteSeparable_over_firstCoordinate_of_irreducible
      hf hpartialSecond).1
  have hfinF : Module.finrank F L = MvPolynomial.degreeOf 1 f :=
    finrank_over_firstCoordinate_eq_degreeOf_second_of_irreducible
      hf hpartialSecond
  letI : FiniteDimensional F A :=
    FiniteDimensional.of_injective
      (IsScalarTower.toAlgHom F A L).toLinearMap
      (RingHom.injective _)
  have hmul : Module.finrank F A * Module.finrank A L =
      Module.finrank F L := Module.finrank_mul_finrank F A L
  have hfinFA : Module.finrank F A = 1 := by
    rw [hfinA, hfinF] at hmul
    nlinarith
  have hsurj : Function.Surjective (algebraMap F A) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfinFA).2
  have hArestrict : A.restrictScalars K = F := by
    apply le_antisymm
    · intro z hz
      let zA : A := ⟨z, hz⟩
      obtain ⟨w, hw⟩ := hsurj zA
      have hcoe : (w : L) = z := by
        exact congrArg (fun a : A ↦ (a : L)) hw
      change z ∈ F
      rw [← hcoe]
      exact w.property
    · exact hFA
  apply le_antisymm
  · intro z hz
    have hzA : z ∈ A := by
      exact A.algebraMap_mem ⟨z, hz⟩
    have hzF : z ∈ F := by
      have : z ∈ A.restrictScalars K := hzA
      rwa [hArestrict] at this
    let zF : F := ⟨z, hzF⟩
    have hzAlgL : IsAlgebraic K z :=
      mem_algebraicClosure_iff.mp hz
    have hzAlgF : IsAlgebraic K zF := by
      apply (isAlgebraic_algHom_iff
        (IsScalarTower.toAlgHom K F L) (RingHom.injective _)).mp
      change IsAlgebraic K (zF : L)
      simpa [L] using hzAlgL
    have hzClosure : zF ∈ algebraicClosure K F :=
      mem_algebraicClosure_iff.mpr hzAlgF
    have hclosure : algebraicClosure K F = ⊥ :=
      adjoin_transcendental_algebraicClosure_eq_bot x hxK
    rw [hclosure, IntermediateField.mem_bot] at hzClosure
    rw [IntermediateField.mem_bot]
    obtain ⟨c, hc⟩ := hzClosure
    refine ⟨c, ?_⟩
    exact congrArg Subtype.val hc
  · exact bot_le

/-- Exact constants persist after an arbitrary extension of the coefficient
field.  Absolute irreducibility over `K` supplies absolute irreducibility over
`E`, and injectivity of the coefficient embedding preserves the separating
second partial derivative. -/
theorem planeCurveBaseChangeFunctionField_algebraicClosure_eq_bot
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (f : MvPolynomial (Fin 2) K)
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    let fE := MvPolynomial.map (algebraMap K E) f
    let hfE := irreducible_map_of_irreducible_map_algebraicClosure
      (algebraMap K E) f habsolute
    letI := planeCurveCoordinateRing_isDomain hfE
    algebraicClosure E (PlaneCurveFunctionField fE) = ⊥ := by
  let fE := MvPolynomial.map (algebraMap K E) f
  have habsoluteE : Irreducible
      (MvPolynomial.map (algebraMap E (AlgebraicClosure E)) fE) := by
    have h := irreducible_map_of_irreducible_map_algebraicClosure
      ((algebraMap E (AlgebraicClosure E)).comp (algebraMap K E))
      f habsolute
    simpa only [fE, MvPolynomial.map_map] using h
  have hpartialSecondE : MvPolynomial.pderiv 1 fE ≠ 0 := by
    rw [MvPolynomial.pderiv_map]
    intro hz
    apply hpartialSecond
    apply MvPolynomial.map_injective (algebraMap K E)
      (algebraMap K E).injective
    simpa using hz
  exact planeCurveFunctionField_algebraicClosure_eq_bot
    fE habsoluteE hpartialSecondE

end

end BGS.HasseWeil
