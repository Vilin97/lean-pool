/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveFiniteDifferentBound
import LeanPool.MarkoffModP.BGS.CorvajaZannier.TorsionBidegreeCount
import Mathlib.Tactic

/-!
# A coarse affine singular-point bound for plane curves

For a bivariate polynomial `f`, write it as a polynomial `F` in the second
coordinate with coefficients in the first-coordinate polynomial ring.  We
eliminate the second coordinate from `F` and `F.derivative` by their ordinary
resultant, with the two degree parameters fixed before specialization.

Fixing those parameters is essential: specializing the first coordinate can
lower the degree, so neither a default resultant whose parameters are chosen
after specialization nor a specialized discriminant is the correct object.
The fixed resultant nevertheless vanishes at the first coordinate of every
common zero of `f` and its second partial derivative.  Irreducibility and a
nonzero second partial derivative make the resultant nonzero, and elementary
root and fiber counts then bound all affine singular points by
`((2 * secondDegree - 1) * firstDegree) * secondDegree`.
-/

namespace BGS.HasseWeil

noncomputable section

open Polynomial

variable {K : Type*} [Field K]

theorem planeCurvePolynomialInSecondCoordinate_derivative
    (f : MvPolynomial (Fin 2) K) :
    (BGS.CorvajaZannier.planeCurvePolynomialInSecondCoordinate f).derivative =
      BGS.CorvajaZannier.planeCurvePolynomialInSecondCoordinate
        (MvPolynomial.pderiv 1 f) := by
  rw [BGS.CorvajaZannier.planeCurvePolynomialInSecondCoordinate_eq_bivariateEquiv,
    BGS.CorvajaZannier.planeCurvePolynomialInSecondCoordinate_eq_bivariateEquiv]
  apply (Polynomial.Bivariate.equivMvPolynomial K).injective
  simpa using
    (Polynomial.Bivariate.pderiv_one_equivMvPolynomial
      ((Polynomial.Bivariate.equivMvPolynomial K).symm f)).symm

/-- The first-coordinate eliminant of the equation and its derivative in the
second coordinate. -/
noncomputable def secondCoordinateCriticalResultant
    (f : MvPolynomial (Fin 2) K) : Polynomial K :=
  let F := BGS.CorvajaZannier.planeCurvePolynomialInSecondCoordinate f
  Polynomial.resultant F F.derivative F.natDegree F.derivative.natDegree

theorem secondCoordinateCriticalResultant_natDegree_le
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree) :
    (secondCoordinateCriticalResultant f).natDegree ≤
      (2 * secondDegree - 1) * firstDegree := by
  let F : Polynomial (Polynomial K) :=
    BGS.CorvajaZannier.planeCurvePolynomialInSecondCoordinate f
  have hFDegree : F.natDegree ≤ secondDegree := by
    simpa [F] using
      (BGS.CorvajaZannier.degreeOf_second_le_of_hasBidegreeAtMost hdegree)
  have hderivDegree : F.derivative.natDegree ≤ secondDegree - 1 :=
    (Polynomial.natDegree_derivative_le F).trans
      (Nat.sub_le_sub_right hFDegree 1)
  have hFcoeff : ∀ i, (F.coeff i).natDegree ≤ firstDegree := by
    intro i
    simpa [F] using
      BGS.CorvajaZannier.planeCurvePolynomialInSecondCoordinate_coeff_natDegree_le
        hdegree i
  have hderivCoeff : ∀ i, (F.derivative.coeff i).natDegree ≤ firstDegree := by
    intro i
    rw [Polynomial.coeff_derivative]
    calc
      (F.coeff (i + 1) * (i + 1)).natDegree ≤
          (F.coeff (i + 1)).natDegree +
            ((i + 1 : Polynomial K)).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ firstDegree + 0 :=
        Nat.add_le_add (hFcoeff (i + 1)) (by
          simpa using
            (Polynomial.natDegree_natCast (R := K) (i + 1)).le)
      _ = firstDegree := Nat.add_zero _
  have hresultant :=
    BGS.CorvajaZannier.natDegree_resultant_le_of_degree_le
      F F.derivative secondDegree (secondDegree - 1)
        firstDegree firstDegree hFDegree hderivDegree hFcoeff hderivCoeff
  change (Polynomial.resultant F F.derivative).natDegree ≤ _
  calc
    (Polynomial.resultant F F.derivative).natDegree ≤
        secondDegree * firstDegree +
          (secondDegree - 1) * firstDegree := hresultant
    _ = (2 * secondDegree - 1) * firstDegree := by
      rw [← Nat.add_mul]
      congr 1
      omega

theorem secondCoordinateCriticalResultant_eval_eq_zero_of_common_zero
    {f : MvPolynomial (Fin 2) K}
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) (x y : K)
    (hfxy : MvPolynomial.eval ![x, y] f = 0)
    (hderivxy : MvPolynomial.eval ![x, y]
      (MvPolynomial.pderiv 1 f) = 0) :
    (secondCoordinateCriticalResultant f).eval x = 0 := by
  let F : Polynomial (Polynomial K) :=
    BGS.CorvajaZannier.planeCurvePolynomialInSecondCoordinate f
  let ev : Polynomial K →+* K := Polynomial.evalRingHom x
  have hFxy : (F.map ev).eval y = 0 := by
    change (BGS.CorvajaZannier.secondCoordinateSpecialization f x).eval y = 0
    simpa using hfxy
  have hderivFxy : (F.derivative.map ev).eval y = 0 := by
    rw [show F.derivative =
      BGS.CorvajaZannier.planeCurvePolynomialInSecondCoordinate
        (MvPolynomial.pderiv 1 f) by
      simpa [F] using planeCurvePolynomialInSecondCoordinate_derivative f]
    change (BGS.CorvajaZannier.secondCoordinateSpecialization
      (MvPolynomial.pderiv 1 f) x).eval y = 0
    simpa using hderivxy
  have hFdegree : 0 < F.natDegree := by
    simpa [F] using
      BGS.CorvajaZannier.degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond
  have hspecialized :
      Polynomial.resultant (F.map ev) (F.derivative.map ev)
        F.natDegree F.derivative.natDegree = 0 := by
    exact BGS.CorvajaZannier.resultant_eq_zero_of_common_root
      (F.map ev) (F.derivative.map ev) F.natDegree F.derivative.natDegree
        Polynomial.natDegree_map_le Polynomial.natDegree_map_le
        (Or.inl hFdegree.ne') y hFxy hderivFxy
  rw [Polynomial.resultant_map_map] at hspecialized
  simpa [secondCoordinateCriticalResultant, F, ev] using hspecialized

theorem secondCoordinateCriticalResultant_ne_zero
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    secondCoordinateCriticalResultant f ≠ 0 := by
  let F : Polynomial (Polynomial K) :=
    BGS.CorvajaZannier.planeCurvePolynomialInSecondCoordinate f
  let ι : Polynomial K →+* RatFunc K := algebraMap (Polynomial K) (RatFunc K)
  have hFderivative : F.derivative ≠ 0 := by
    rw [show F.derivative =
      BGS.CorvajaZannier.planeCurvePolynomialInSecondCoordinate
        (MvPolynomial.pderiv 1 f) by
      simpa [F] using planeCurvePolynomialInSecondCoordinate_derivative f]
    intro hzero
    apply hpartialSecond
    apply BGS.CorvajaZannier.planeCurvePolynomialInSecondCoordinate.injective
    simpa using hzero
  have hFmapIrreducible : Irreducible (F.map ι) := by
    simpa [F, ι] using
      BGS.CorvajaZannier.planeCurvePolynomialInSecondCoordinate_ratFunc_irreducible
        hf hpartialSecond
  have hFmapDerivative : (F.map ι).derivative ≠ 0 := by
    simpa only [Polynomial.derivative_map] using
      (by simpa only [Polynomial.map_zero] using
        (Polynomial.map_injective ι
          (IsFractionRing.injective (Polynomial K) (RatFunc K))).ne hFderivative)
  have hseparable : (F.map ι).Separable :=
    (Polynomial.separable_iff_derivative_ne_zero hFmapIrreducible).2
      hFmapDerivative
  have hmapResultantDefault :
      Polynomial.resultant (F.map ι) (F.derivative.map ι) ≠ 0 := by
    change IsCoprime (F.map ι) (F.map ι).derivative at hseparable
    exact Polynomial.resultant_ne_zero _ _ (by
      simpa only [Polynomial.derivative_map] using hseparable)
  have hmapFdegree : (F.map ι).natDegree = F.natDegree :=
    by simpa [ι] using
      (Polynomial.natDegree_map_eq_of_injective
        (IsFractionRing.injective (Polynomial K) (RatFunc K)) F)
  have hmapDdegree : (F.derivative.map ι).natDegree = F.derivative.natDegree :=
    by simpa [ι] using
      (Polynomial.natDegree_map_eq_of_injective
        (IsFractionRing.injective (Polynomial K) (RatFunc K)) F.derivative)
  have hmapResultant :
      Polynomial.resultant (F.map ι) (F.derivative.map ι)
        F.natDegree F.derivative.natDegree ≠ 0 := by
    simpa only [hmapFdegree, hmapDdegree] using hmapResultantDefault
  intro hzero
  apply hmapResultant
  rw [Polynomial.resultant_map_map]
  simpa [secondCoordinateCriticalResultant, F, ι] using congrArg ι hzero

/-- Affine points where the curve equation and its second-coordinate
derivative vanish.  This set contains every affine singular point. -/
noncomputable def affineSecondCoordinateCriticalPoints
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K) : Finset (K × K) := by
  classical
  exact Finset.univ.filter fun z =>
    MvPolynomial.eval ![z.1, z.2] f = 0 ∧
      MvPolynomial.eval ![z.1, z.2] (MvPolynomial.pderiv 1 f) = 0

@[simp]
theorem mem_affineSecondCoordinateCriticalPoints_iff
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {f : MvPolynomial (Fin 2) K} {z : K × K} :
    z ∈ affineSecondCoordinateCriticalPoints K f ↔
      MvPolynomial.eval ![z.1, z.2] f = 0 ∧
        MvPolynomial.eval ![z.1, z.2] (MvPolynomial.pderiv 1 f) = 0 := by
  classical
  simp [affineSecondCoordinateCriticalPoints]

/-- Affine singular points: the equation and both coordinate partial
derivatives vanish. -/
noncomputable def affinePlaneCurveSingularPoints
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K) : Finset (K × K) := by
  classical
  exact Finset.univ.filter fun z =>
    MvPolynomial.eval ![z.1, z.2] f = 0 ∧
      MvPolynomial.eval ![z.1, z.2] (MvPolynomial.pderiv 0 f) = 0 ∧
        MvPolynomial.eval ![z.1, z.2] (MvPolynomial.pderiv 1 f) = 0

@[simp]
theorem mem_affinePlaneCurveSingularPoints_iff
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {f : MvPolynomial (Fin 2) K} {z : K × K} :
    z ∈ affinePlaneCurveSingularPoints K f ↔
      MvPolynomial.eval ![z.1, z.2] f = 0 ∧
        MvPolynomial.eval ![z.1, z.2] (MvPolynomial.pderiv 0 f) = 0 ∧
          MvPolynomial.eval ![z.1, z.2] (MvPolynomial.pderiv 1 f) = 0 := by
  classical
  simp [affinePlaneCurveSingularPoints]

theorem polynomialEvalZeroSubtype_card_le_natDegree
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (P : Polynomial K) (hP : P ≠ 0) :
    Fintype.card {x : K // P.eval x = 0} ≤ P.natDegree := by
  classical
  let rootEmbedding : {x : K // P.eval x = 0} ↪ P.roots.toFinset :=
    { toFun := fun x => ⟨x, by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
        exact x.2⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun z : P.roots.toFinset => (z : K)) hxy }
  calc
    Fintype.card {x : K // P.eval x = 0} ≤ P.roots.toFinset.card := by
      simpa only [Fintype.card_coe] using
        Fintype.card_le_of_injective rootEmbedding rootEmbedding.injective
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P

theorem affineSecondCoordinateCriticalPoints_card_le
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree)
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    (affineSecondCoordinateCriticalPoints K f).card ≤
      ((2 * secondDegree - 1) * firstDegree) * secondDegree := by
  classical
  let S := affineSecondCoordinateCriticalPoints K f
  let R := secondCoordinateCriticalResultant f
  let X := {x : K // R.eval x = 0}
  let Y := fun x : X =>
    {y : K //
      (BGS.CorvajaZannier.secondCoordinateSpecialization f x.1).eval y = 0}
  let embedding : {z // z ∈ S} ↪ Sigma Y :=
    { toFun := fun z =>
        ⟨⟨z.1.1, by
            have hz := mem_affineSecondCoordinateCriticalPoints_iff.mp z.2
            exact secondCoordinateCriticalResultant_eval_eq_zero_of_common_zero
              hpartialSecond z.1.1 z.1.2 hz.1 hz.2⟩,
          ⟨z.1.2, by
            rw [BGS.CorvajaZannier.secondCoordinateSpecialization_eval]
            exact (mem_affineSecondCoordinateCriticalPoints_iff.mp z.2).1⟩⟩
      inj' := by
        intro z w hzw
        apply Subtype.ext
        apply Prod.ext
        · exact congrArg (fun q : Sigma Y => (q.1 : K)) hzw
        · exact congrArg (fun q : Sigma Y => (q.2.1 : K)) hzw }
  have hsecond : 0 < MvPolynomial.degreeOf 1 f :=
    BGS.CorvajaZannier.degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond
  have hFiber (x : X) : Fintype.card (Y x) ≤ secondDegree := by
    exact (polynomialEvalZeroSubtype_card_le_natDegree
      (BGS.CorvajaZannier.secondCoordinateSpecialization f x.1)
      (BGS.CorvajaZannier.secondCoordinateSpecialization_ne_zero_of_irreducible
        hf hsecond x.1)).trans
      (BGS.CorvajaZannier.secondCoordinateSpecialization_natDegree_le
        hdegree x.1)
  have hRne : R ≠ 0 := by
    simpa [R] using secondCoordinateCriticalResultant_ne_zero hf hpartialSecond
  have hBase : Fintype.card X ≤ R.natDegree := by
    exact polynomialEvalZeroSubtype_card_le_natDegree R hRne
  have hRdegree : R.natDegree ≤ (2 * secondDegree - 1) * firstDegree := by
    simpa [R] using secondCoordinateCriticalResultant_natDegree_le hdegree
  calc
    S.card = Fintype.card {z // z ∈ S} := by simp
    _ ≤ Fintype.card (Sigma Y) :=
      Fintype.card_le_of_injective embedding embedding.injective
    _ = ∑ x, Fintype.card (Y x) := Fintype.card_sigma
    _ ≤ ∑ _x : X, secondDegree := by
      exact Finset.sum_le_sum fun x _ => hFiber x
    _ = Fintype.card X * secondDegree := by simp
    _ ≤ R.natDegree * secondDegree := Nat.mul_le_mul_right _ hBase
    _ ≤ ((2 * secondDegree - 1) * firstDegree) * secondDegree :=
      Nat.mul_le_mul_right _ hRdegree

/-- A coarse bidegree bound for the number of affine singular points of an
irreducible separating plane curve. -/
theorem affinePlaneCurveSingularPoints_card_le
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree)
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    (affinePlaneCurveSingularPoints K f).card ≤
      ((2 * secondDegree - 1) * firstDegree) * secondDegree := by
  apply (Finset.card_le_card ?_).trans
    (affineSecondCoordinateCriticalPoints_card_le hdegree hf hpartialSecond)
  intro z hz
  rw [mem_affineSecondCoordinateCriticalPoints_iff]
  have hz' := mem_affinePlaneCurveSingularPoints_iff.mp hz
  exact ⟨hz'.1, hz'.2.2⟩

end

end BGS.HasseWeil
