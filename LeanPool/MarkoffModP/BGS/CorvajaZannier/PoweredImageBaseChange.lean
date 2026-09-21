/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageFrobeniusRelation
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageHeightFactor
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurvePoweredImageDegreeBudget
import Mathlib.Tactic

/-!
# Constant-field base change for the powered-image index

The canonical powered-image relation remains associated to its coefficient
base change.  Comparing the exact tower-degree factorizations on the two
curves then shows that the source-to-powered-image finrank is invariant under
extension of constants.  This is the descent bridge from the algebraically
closed stabilizer argument to the original constant field.
-/

open scoped TensorProduct Polynomial
open Polynomial

namespace BGS.CorvajaZannier

noncomputable section

/-- Bivariate evaluation commutes with an extension of the coefficient
field. -/
theorem bivariateEvalAlgHom_map_mapRingHom
    {K E L : Type*} [Field K] [Field E] [CommRing L]
    [Algebra K E] [Algebra K L] [Algebra E L]
    [IsScalarTower K E L]
    (u v : L) (P : Polynomial (Polynomial K)) :
    bivariateEvalAlgHom (K := E) u v
        (P.map (Polynomial.mapRingHom (algebraMap K E))) =
      bivariateEvalAlgHom (K := K) u v P := by
  unfold bivariateEvalAlgHom
  simp only [Polynomial.eval₂AlgHom_apply]
  rw [Polynomial.eval₂_map]
  congr 1
  apply Polynomial.ringHom_ext
  · intro c
    simp [IsScalarTower.algebraMap_apply K E L]
  · simp

/-- The coefficient-extension map between affine plane-curve coordinate
rings. -/
noncomputable def planeCurveCoordinateRingMap
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (f : MvPolynomial (Fin 2) K) :
    PlaneCurveCoordinateRing f →ₐ[K]
      PlaneCurveCoordinateRing (MvPolynomial.map (algebraMap K E) f) := by
  let ι : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) E :=
    { toRingHom := MvPolynomial.map (algebraMap K E)
      commutes' := by
        intro c
        simp [MvPolynomial.algebraMap_eq] }
  apply Ideal.quotientMapₐ
    (Ideal.span {MvPolynomial.map (algebraMap K E) f}) ι
  intro q hq
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hq
  apply Ideal.mem_span_singleton.mpr
  refine ⟨MvPolynomial.map (algebraMap K E) r, ?_⟩
  simp [ι]

/-- The coordinate-ring base-change map preserves the two coordinate
classes. -/
@[simp] theorem planeCurveCoordinateRingMap_coordinate
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (f : MvPolynomial (Fin 2) K) (i : Fin 2) :
    planeCurveCoordinateRingMap (E := E) f (planeCurveCoordinate f i) =
      planeCurveCoordinate (MvPolynomial.map (algebraMap K E) f) i := by
  simp [planeCurveCoordinateRingMap, planeCurveCoordinate,
    planeCurveQuotientMap]

/-- The coefficient base change of the canonical powered-image relation
vanishes on the generic powered coordinates of the base-changed curve. -/
theorem evalBivariate_poweredCoordinateImageRelation_map_eq_zero
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hfE : Irreducible (MvPolynomial.map (algebraMap K E) f))
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    let fE := MvPolynomial.map (algebraMap K E) f
    letI := planeCurveCoordinateRing_isDomain hfE
    let g := poweredCoordinateImageRelation hf hpartialSecond m hm n
    evalBivariate
        ((planeCurveFunction fE 0) ^ m)
        ((planeCurveFunction fE 1) ^ n)
        (g.map (Polynomial.mapRingHom (algebraMap K E))) = 0 := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let fE := MvPolynomial.map (algebraMap K E) f
  letI : IsDomain (PlaneCurveCoordinateRing fE) :=
    planeCurveCoordinateRing_isDomain hfE
  let g := poweredCoordinateImageRelation hf hpartialSecond m hm n
  let A := PlaneCurveCoordinateRing f
  let AE := PlaneCurveCoordinateRing fE
  let L := PlaneCurveFunctionField f
  let LE := PlaneCurveFunctionField fE
  let xA : A := (planeCurveCoordinate f 0) ^ m
  let yA : A := (planeCurveCoordinate f 1) ^ n
  let xL : L := (planeCurveFunction f 0) ^ m
  let yL : L := (planeCurveFunction f 1) ^ n
  let ι : A →ₐ[K] L := IsScalarTower.toAlgHom K A L
  let φ : Polynomial (Polynomial K) →ₐ[K] A :=
    bivariateEvalAlgHom (K := K) xA yA
  let ψ : Polynomial (Polynomial K) →ₐ[K] L :=
    bivariateEvalAlgHom (K := K) xL yL
  have hcomp : ι.comp φ = ψ := by
    simpa [φ, ψ, xA, xL, yA, yL, ι, planeCurveFunction] using
      (bivariateEvalAlgHom_comp (K := K) ι xA yA)
  have hzeroL : ψ g = 0 := by
    simpa [ψ, xL, yL, g] using
      (evalBivariate_poweredCoordinateImageRelation_eq_zero
        hf hpartialSecond m hm n)
  have hι : Function.Injective ι := by
    exact IsFractionRing.injective A L
  have hzeroA : φ g = 0 := by
    apply hι
    rw [map_zero, ← AlgHom.comp_apply, hcomp]
    exact hzeroL
  let ρ : A →ₐ[K] AE := planeCurveCoordinateRingMap (E := E) f
  have hzeroAE : ρ (φ g) = 0 := by rw [hzeroA, map_zero]
  have hx : ρ xA = (planeCurveCoordinate fE 0) ^ m := by
    dsimp only [ρ, xA]
    rw [map_pow, planeCurveCoordinateRingMap_coordinate]
  have hy : ρ yA = (planeCurveCoordinate fE 1) ^ n := by
    dsimp only [ρ, yA]
    rw [map_pow, planeCurveCoordinateRingMap_coordinate]
  have hcoord : bivariateEvalAlgHom (K := K)
      ((planeCurveCoordinate fE 0) ^ m)
      ((planeCurveCoordinate fE 1) ^ n) g = 0 := by
    change (ρ.comp φ) g = 0 at hzeroAE
    rw [bivariateEvalAlgHom_comp] at hzeroAE
    simpa only [hx, hy] using hzeroAE
  have hcoordMap : bivariateEvalAlgHom (K := E)
      ((planeCurveCoordinate fE 0) ^ m)
      ((planeCurveCoordinate fE 1) ^ n)
      (g.map (Polynomial.mapRingHom (algebraMap K E))) = 0 := by
    rw [bivariateEvalAlgHom_map_mapRingHom]
    exact hcoord
  let η : AE →ₐ[E] LE := IsScalarTower.toAlgHom E AE LE
  have hfun := congrArg η hcoordMap
  rw [map_zero] at hfun
  change (η.comp (bivariateEvalAlgHom (K := E)
      ((planeCurveCoordinate fE 0) ^ m)
      ((planeCurveCoordinate fE 1) ^ n)))
      (g.map (Polynomial.mapRingHom (algebraMap K E))) = 0 at hfun
  rw [bivariateEvalAlgHom_comp] at hfun
  change evalBivariate
      ((η (planeCurveCoordinate fE 0)) ^ m)
      ((η (planeCurveCoordinate fE 1)) ^ n)
      (g.map (Polynomial.mapRingHom (algebraMap K E))) = 0
  simpa only [map_pow, bivariateEvalAlgHom_eq_evalBivariate] using hfun

/-- The canonical powered-image relation of the base-changed curve is
associated to the coefficient base change of the original relation. -/
theorem poweredCoordinateImageRelation_map_associated_baseChange
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hf : Irreducible f)
    (hfE : Irreducible (MvPolynomial.map (algebraMap K E) f))
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hpartialSecondE :
      MvPolynomial.pderiv 1 (MvPolynomial.map (algebraMap K E) f) ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    Associated
      (poweredCoordinateImageRelation hfE hpartialSecondE m hm n)
      ((poweredCoordinateImageRelation hf hpartialSecond m hm n).map
        (Polynomial.mapRingHom (algebraMap K E))) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let fE := MvPolynomial.map (algebraMap K E) f
  letI : IsDomain (PlaneCurveCoordinateRing fE) :=
    planeCurveCoordinateRing_isDomain hfE
  let LE := PlaneCurveFunctionField fE
  letI : FiniteDimensional (FirstPoweredCoordinateSubfield fE m) LE :=
    finiteDimensional_over_firstPoweredCoordinate hfE hpartialSecondE m hm
  have hv : IsIntegral (FirstPoweredCoordinateSubfield fE m)
      ((planeCurveFunction fE 1) ^ n) := Algebra.IsIntegral.isIntegral _
  have hdvd :
      poweredCoordinateImageRelation hfE hpartialSecondE m hm n ∣
        (poweredCoordinateImageRelation hf hpartialSecond m hm n).map
          (Polynomial.mapRingHom (algebraMap K E)) := by
    change primitiveClearedMinpolyRelation
        ((planeCurveFunction fE 0) ^ m)
        (firstPoweredCoordinate_transcendental
          hfE hpartialSecondE m hm)
        ((planeCurveFunction fE 1) ^ n) ∣ _
    exact primitiveClearedMinpolyRelation_dvd_of_evalBivariate_eq_zero
      ((planeCurveFunction fE 0) ^ m)
      (firstPoweredCoordinate_transcendental hfE hpartialSecondE m hm)
      ((planeCurveFunction fE 1) ^ n) hv _
      (evalBivariate_poweredCoordinateImageRelation_map_eq_zero
        hf hfE hpartialSecond m hm n)
  exact (poweredCoordinateImageRelation_irreducible
      hfE hpartialSecondE m hm n).associated_of_dvd
    (poweredCoordinateImageRelation_irreducible_map
      (E := E) habsolute hf hpartialSecond m hm n) hdvd

/-- The relevant powered-image relation degree is invariant under extension
of constants. -/
theorem poweredCoordinateImageRelation_map_natDegree_eq_baseChange
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hf : Irreducible f)
    (hfE : Irreducible (MvPolynomial.map (algebraMap K E) f))
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hpartialSecondE :
      MvPolynomial.pderiv 1 (MvPolynomial.map (algebraMap K E) f) ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    (poweredCoordinateImageRelation hfE hpartialSecondE m hm n).natDegree =
      (poweredCoordinateImageRelation hf hpartialSecond m hm n).natDegree := by
  let gE := poweredCoordinateImageRelation hfE hpartialSecondE m hm n
  let gMap := (poweredCoordinateImageRelation hf hpartialSecond m hm n).map
    (Polynomial.mapRingHom (algebraMap K E))
  have hassoc : Associated gE gMap :=
    poweredCoordinateImageRelation_map_associated_baseChange
      habsolute hf hfE hpartialSecond hpartialSecondE m hm n
  have hgE0 : gE ≠ 0 := (poweredCoordinateImageRelation_irreducible
    hfE hpartialSecondE m hm n).ne_zero
  have hgMap0 : gMap ≠ 0 := (poweredCoordinateImageRelation_irreducible_map
    (E := E) habsolute hf hpartialSecond m hm n).ne_zero
  have hle : gE.natDegree ≤ gMap.natDegree :=
    Polynomial.natDegree_le_of_dvd hassoc.dvd hgMap0
  have hge : gMap.natDegree ≤ gE.natDegree :=
    Polynomial.natDegree_le_of_dvd hassoc.symm.dvd hgE0
  have hmapDegree : gMap.natDegree =
      (poweredCoordinateImageRelation hf hpartialSecond m hm n).natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      (Polynomial.map_injective (algebraMap K E) (algebraMap K E).injective) _
  exact (Nat.le_antisymm hle hge).trans hmapDegree

/-- Extension of constants preserves the common source-to-powered-image
degree. -/
theorem finrank_poweredCoordinateImageField_eq_baseChange
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    let fE := MvPolynomial.map (algebraMap K E) f
    let hfE := irreducible_map_of_irreducible_map_algebraicClosure
      (algebraMap K E) f habsolute
    letI := planeCurveCoordinateRing_isDomain hf
    letI := planeCurveCoordinateRing_isDomain hfE
    Module.finrank (PoweredCoordinateImageField f m n)
        (PlaneCurveFunctionField f) =
      Module.finrank (PoweredCoordinateImageField fE m n)
        (PlaneCurveFunctionField fE) := by
  let fE := MvPolynomial.map (algebraMap K E) f
  let hfE : Irreducible fE :=
    irreducible_map_of_irreducible_map_algebraicClosure
      (algebraMap K E) f habsolute
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : IsDomain (PlaneCurveCoordinateRing fE) :=
    planeCurveCoordinateRing_isDomain hfE
  have hpartialSecondE : MvPolynomial.pderiv 1 fE ≠ 0 := by
    rw [MvPolynomial.pderiv_map]
    intro hz
    apply hpartialSecond
    apply MvPolynomial.map_injective (algebraMap K E) (algebraMap K E).injective
    simpa using hz
  let aK := (poweredCoordinateImageRelation hf hpartialSecond m hm n).natDegree
  let aE := (poweredCoordinateImageRelation hfE hpartialSecondE m hm n).natDegree
  let dK := Module.finrank (PoweredImageOverFirst f m n)
    (PlaneCurveFunctionField f)
  let dE := Module.finrank (PoweredImageOverFirst fE m n)
    (PlaneCurveFunctionField fE)
  have ha : aE = aK :=
    poweredCoordinateImageRelation_map_natDegree_eq_baseChange
      habsolute hf hfE hpartialSecond hpartialSecondE m hm n
  have hK : aK * dK = m * MvPolynomial.degreeOf 1 f :=
    poweredCoordinateImageRelation_natDegree_mul_commonIndex
      hf hpartialSecond m n hm
  have hE : aE * dE = m * MvPolynomial.degreeOf 1 fE :=
    poweredCoordinateImageRelation_natDegree_mul_commonIndex
      hfE hpartialSecondE m n hm
  have hdegree : MvPolynomial.degreeOf 1 fE = MvPolynomial.degreeOf 1 f :=
    degreeOf_map_eq_of_injective (algebraMap K E)
      (algebraMap K E).injective 1 f
  have hprod : aK * dK = aK * dE := by
    calc
      aK * dK = m * MvPolynomial.degreeOf 1 f := hK
      _ = m * MvPolynomial.degreeOf 1 fE := by rw [hdegree]
      _ = aE * dE := hE.symm
      _ = aK * dE := by rw [ha]
  have haPos : 0 < aK :=
    poweredCoordinateImageRelation_natDegree_pos
      hf hpartialSecond m hm n
  have hd : dK = dE := Nat.eq_of_mul_eq_mul_left haPos hprod
  calc
    Module.finrank (PoweredCoordinateImageField f m n)
        (PlaneCurveFunctionField f) = dK :=
      (finrank_poweredImageOverFirst_eq_imageField m n).symm
    _ = dE := hd
    _ = Module.finrank (PoweredCoordinateImageField fE m n)
        (PlaneCurveFunctionField fE) :=
      finrank_poweredImageOverFirst_eq_imageField m n

end
end BGS.CorvajaZannier
