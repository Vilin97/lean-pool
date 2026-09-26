/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ExtensionPointCount
public import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneSquareFieldStepanovCountAutomatic
public import Mathlib.Tactic

/-!
# A Stepanov upper bound along the even-degree extension sequence

Let `K_n = FiniteField.Extension K p n` and
`K_{2n} = FiniteField.Extension K p (2 * n)`.  Since `n ∣ 2 * n`, finite-field
theory supplies a `K`-algebra embedding `K_n → K_{2n}`.  With this algebra
structure the latter is a quadratic extension of the former, so the
square-field Stepanov estimate applies directly to the canonical degree
`2 * n` point count.

This is only a one-sided affine estimate.  It does not assert the missing
lower bound, the sharp Hasse--Weil constant, or a two-sided zeta estimate.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section


/-- An injective extension of coefficients preserves a support-wise
bidegree bound. -/
theorem hasBidegreeAtMost_map_of_injective
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (hφ : Function.Injective φ)
    {f : MvPolynomial (Fin 2) R} {firstDegree secondDegree : Nat}
    (hdegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree) :
    BGS.External.HasBidegreeAtMost
      (MvPolynomial.map φ f) firstDegree secondDegree := by
  intro monomial hmonomial
  apply hdegree monomial
  rwa [MvPolynomial.support_map_of_injective f hφ] at hmonomial

/-- An injective extension of coefficients preserves the exact coarse genus
budget used by the plane Stepanov argument. -/
theorem planeCurveBidegreeGenusBudget_map_of_injective
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (f : MvPolynomial (Fin 2) R) :
    planeCurveBidegreeGenusBudget (MvPolynomial.map φ f) =
      planeCurveBidegreeGenusBudget f := by
  simp only [planeCurveBidegreeGenusBudget,
    degreeOf_map_eq_of_injective φ hφ]

variable (K : Type*) [Field K] [Fintype K]
variable (p n : Nat) [Fact p.Prime] [CharP K p] [NeZero n]

/-- A chosen `K`-algebra embedding from the degree-`n` extension into the
degree-`2n` extension.  Its existence is the finite-field divisibility
criterion `n ∣ 2n`. -/
def halfExtensionToEvenExtensionAlgHom :
    FiniteField.Extension K p n →ₐ[K]
      FiniteField.Extension K p (2 * n) :=
  (FiniteField.nonempty_algHom_of_finrank_dvd (by
    rw [FiniteField.finrank_extension K p n,
      FiniteField.finrank_extension K p (2 * n)]
    exact ⟨2, by omega⟩)).some

/-- The canonical degree-`2n` finite extension, viewed through the chosen
degree-`n` subfield, has relative degree two. -/
theorem finrank_evenExtension_over_halfExtension :
    let E := FiniteField.Extension K p n
    let S := FiniteField.Extension K p (2 * n)
    let ι : E →ₐ[K] S := halfExtensionToEvenExtensionAlgHom K p n
    letI : Algebra E S := ι.toAlgebra
    Module.finrank E S = 2 := by
  classical
  let E := FiniteField.Extension K p n
  let S := FiniteField.Extension K p (2 * n)
  let ι : E →ₐ[K] S := halfExtensionToEvenExtensionAlgHom K p n
  let : Algebra E S := ι.toAlgebra
  let : IsScalarTower K E S := IsScalarTower.of_algebraMap_eq' (by
    ext c
    exact (ι.commutes c).symm)
  let : Module.Finite E S := Module.Finite.of_finite
  have hmul : Module.finrank K E * Module.finrank E S =
      Module.finrank K S := Module.finrank_mul_finrank K E S
  rw [FiniteField.finrank_extension K p n,
    FiniteField.finrank_extension K p (2 * n)] at hmul
  have hn : 0 < n := NeZero.pos n
  apply Nat.eq_of_mul_eq_mul_left hn
  calc
    n * Module.finrank E S = 2 * n := hmul
    _ = n * 2 := Nat.mul_comm 2 n

/-- The automatic plane Stepanov estimate on the canonical even-degree
extension sequence.  The main error term is exactly
`(2 * genusBudget + 1) * (#K)^n`; the final displayed term is the explicit
critical-locus bound coming from the supplied bidegree.

This theorem is intentionally one-sided and should not be called a
Hasse--Weil theorem. -/
theorem extensionAffinePointCount_two_mul_le_stepanov
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree : Nat}
    (hdegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree)
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hlarge :
      (planeCurveBidegreeGenusBudget f + 1) *
          (planeCurveBidegreeGenusBudget f + 2) ≤
        (Fintype.card K) ^ n) :
    extensionAffinePointCount K p (2 * n) f ≤
      (Fintype.card K) ^ (2 * n) +
        (2 * planeCurveBidegreeGenusBudget f + 1) *
          (Fintype.card K) ^ n +
        ((2 * secondDegree - 1) * firstDegree) * secondDegree := by
  classical
  let E := FiniteField.Extension K p n
  let S := FiniteField.Extension K p (2 * n)
  let ι : E →ₐ[K] S := halfExtensionToEvenExtensionAlgHom K p n
  let : Algebra E S := ι.toAlgebra
  let : IsScalarTower K E S := IsScalarTower.of_algebraMap_eq' (by
    ext c
    exact (ι.commutes c).symm)
  let : Module.Finite E S := Module.Finite.of_finite
  let : Fintype E := Fintype.ofFinite E
  let : Fintype S := Fintype.ofFinite S
  let fS : MvPolynomial (Fin 2) S :=
    extensionPlaneCurvePolynomial K p (2 * n) f
  have hfinrank : Module.finrank E S = 2 :=
    finrank_evenExtension_over_halfExtension K p n
  have hcardE : Fintype.card E = (Fintype.card K) ^ n := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    exact FiniteField.natCard_extension K p n
  have hcardS : Fintype.card S = (Fintype.card E) ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := E), hfinrank]
  have hcardSbase : Fintype.card S = (Fintype.card K) ^ (2 * n) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    exact FiniteField.natCard_extension K p (2 * n)
  have hfS : Irreducible fS := by
    exact irreducible_map_of_irreducible_map_algebraicClosure
      (algebraMap K S) f habsolute
  have hpartialFirstS : MvPolynomial.pderiv 0 fS ≠ 0 := by
    exact extensionPlaneCurvePolynomial_pderiv_ne_zero
      K p (2 * n) f 0 hpartialFirst
  have hpartialSecondS : MvPolynomial.pderiv 1 fS ≠ 0 := by
    exact extensionPlaneCurvePolynomial_pderiv_ne_zero
      K p (2 * n) f 1 hpartialSecond
  have hdegreeS : BGS.External.HasBidegreeAtMost
      fS firstDegree secondDegree := by
    exact hasBidegreeAtMost_map_of_injective
      (algebraMap K S) (algebraMap K S).injective hdegree
  have hgenus : planeCurveBidegreeGenusBudget fS =
      planeCurveBidegreeGenusBudget f := by
    exact planeCurveBidegreeGenusBudget_map_of_injective
      (algebraMap K S) (algebraMap K S).injective f
  have hlargeS :
      (planeCurveBidegreeGenusBudget fS + 1) *
          (planeCurveBidegreeGenusBudget fS + 2) ≤ Fintype.card E := by
    simpa only [hgenus, hcardE] using hlarge
  have habsoluteS : Irreducible
      (MvPolynomial.map (algebraMap S (AlgebraicClosure S)) fS) := by
    exact extensionPlaneCurvePolynomial_absolutelyIrreducible
      K p (2 * n) f habsolute
  let : IsDomain (PlaneCurveCoordinateRing fS) :=
    planeCurveCoordinateRing_isDomain hfS
  let hx := firstCoordinate_transcendental hfS
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecondS)
  let L := PlaneCurveFunctionField fS
  let : Algebra (RatFunc S) L :=
    planeCurveFirstCoordinateRatFuncAlgebra fS hx
  let canonicalAlg : Algebra S L := inferInstance
  let constantAlg : Algebra S L :=
    RingHom.toAlgebra ((algebraMap (RatFunc S) L).comp
      (algebraMap S (RatFunc S)))
  have hconstantAlg : constantAlg = canonicalAlg := by
    apply Algebra.algebra_ext
    intro c
    change (@ratFuncSpecialization S L _ _ canonicalAlg
      (planeCurveFunction fS 0) hx) (RatFunc.C c) =
        @algebraMap S L _ _ canonicalAlg c
    have h := DFunLike.congr_fun
      (@ratFuncSpecialization_comp_polynomial_algebraMap
        S L _ _ canonicalAlg (planeCurveFunction fS 0) hx)
      (Polynomial.C c)
    simpa using h
  have hconstantsCanonical :
      @algebraicClosure S L _ _ canonicalAlg = ⊥ := by
    simpa only [L] using
      planeCurveFunctionField_algebraicClosure_eq_bot
        fS habsoluteS hpartialSecondS
  have hconstants :
      @algebraicClosure S L _ _ constantAlg = ⊥ := by
    rw [hconstantAlg]
    exact hconstantsCanonical
  have hbound := planeCurve_affinePoint_card_le_squareField_bidegree
    E S hdegreeS hfS hpartialFirstS hpartialSecondS hcardS hlargeS
  dsimp only at hbound
  specialize hbound hconstants
  simpa only [extensionAffinePointCount, affineBivariatePointCount,
    fS, hgenus, hcardE, hcardSbase, Fintype.card_eq_nat_card] using hbound

end

end BGS.HasseWeil
