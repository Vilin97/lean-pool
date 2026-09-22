/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveDiscriminantBound
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic

/-!
# Bidegree bounds for finite torus-curve intersections

For an irreducible bivariate curve with positive degree in both coordinates,
every coordinate fiber is cut out by a nonzero univariate polynomial.  Counting
roots in each fiber gives the sharp elementary estimates
`firstOrder * secondDegree` and `secondOrder * firstDegree`; their minimum is
the elementary divisor bound used at the Corvaja--Zannier endpoint.

The irreducibility and positive-coordinate-degree hypotheses are essential:
a polynomial with a vertical or horizontal component can contain an entire row
or column of the torsion grid.
-/

open Polynomial

namespace BGS.CorvajaZannier

noncomputable section

variable {K : Type*} [Field K]

/-- Specialize the first coordinate of a bivariate polynomial, leaving a
univariate polynomial in the second coordinate. -/
def secondCoordinateSpecialization
    (f : MvPolynomial (Fin 2) K) (x : K) : Polynomial K :=
  (planeCurvePolynomialInSecondCoordinate f).map (Polynomial.evalRingHom x)

@[simp]
theorem secondCoordinateSpecialization_eval
    (f : MvPolynomial (Fin 2) K) (x y : K) :
    (secondCoordinateSpecialization f x).eval y =
      MvPolynomial.eval ![x, y] f := by
  let g := MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) f
  let Q := MvPolynomial.finSuccEquiv K 1 g
  let e := MvPolynomial.uniqueAlgEquiv K (Fin 1)
  have hevalHom :
      (Polynomial.evalRingHom x).comp e.toRingEquiv.toRingHom =
        MvPolynomial.eval ![x] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [e]
    · intro i
      fin_cases i
      simp [e, MvPolynomial.uniqueAlgEquiv_apply]
  have hiterated := MvPolynomial.eval_eq_eval_mv_eval' ![x] y g
  change Polynomial.eval y
      (Polynomial.map (Polynomial.evalRingHom x)
        (Polynomial.map e.toRingEquiv.toRingHom Q)) = _
  rw [Polynomial.map_map, hevalHom]
  rw [← hiterated]
  simp [g, MvPolynomial.eval_rename]

/-- An irreducible curve of positive second-coordinate degree has no
identically zero fiber over a fixed first coordinate. -/
theorem secondCoordinateSpecialization_ne_zero_of_irreducible
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hsecond : 0 < MvPolynomial.degreeOf 1 f) (x : K) :
    secondCoordinateSpecialization f x ≠ 0 := by
  let F : Polynomial (Polynomial K) := planeCurvePolynomialInSecondCoordinate f
  have hF : Irreducible F :=
    hf.map planeCurvePolynomialInSecondCoordinate
  have hFdegree : 0 < F.natDegree := by
    simpa [F] using hsecond
  intro hspecialization
  have hcoeffEval : ∀ i, (F.coeff i).eval x = 0 := by
    intro i
    have hi := congrArg (fun P : Polynomial K => P.coeff i) hspecialization
    simpa [secondCoordinateSpecialization, F] using hi
  have hcoeffDvd : ∀ i, Polynomial.X - Polynomial.C x ∣ F.coeff i := by
    intro i
    exact Polynomial.dvd_iff_isRoot.mpr (hcoeffEval i)
  have hdvd : Polynomial.C (Polynomial.X - Polynomial.C x) ∣ F :=
    Polynomial.C_dvd_iff_dvd_coeff _ _ |>.mpr hcoeffDvd
  obtain ⟨q, hfactor⟩ := hdvd
  have hfactor' : F = Polynomial.C (Polynomial.X - Polynomial.C x) * q :=
    hfactor
  rcases hF.isUnit_or_isUnit hfactor' with hunit | hqunit
  · exact (Polynomial.not_isUnit_X_sub_C x)
      (Polynomial.isUnit_C.mp hunit)
  · have hdegreeZero : F.natDegree = 0 := by
      rw [hfactor']
      apply Nat.eq_zero_of_le_zero
      calc
        (Polynomial.C (Polynomial.X - Polynomial.C x) * q).natDegree
            ≤ (Polynomial.C (Polynomial.X - Polynomial.C x)).natDegree +
                q.natDegree := Polynomial.natDegree_mul_le
        _ = 0 := by rw [Polynomial.natDegree_C,
          Polynomial.natDegree_eq_zero_of_isUnit hqunit]
    exact (Nat.ne_of_gt hFdegree) hdegreeZero

/-- A support-wise bidegree bound controls every specialized fiber degree. -/
theorem secondCoordinateSpecialization_natDegree_le
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree)
    (x : K) :
    (secondCoordinateSpecialization f x).natDegree ≤ secondDegree := by
  calc
    (secondCoordinateSpecialization f x).natDegree ≤
        (planeCurvePolynomialInSecondCoordinate f).natDegree :=
      Polynomial.natDegree_map_le
    _ = MvPolynomial.degreeOf 1 f :=
      planeCurvePolynomialInSecondCoordinate_natDegree f
    _ ≤ secondDegree :=
      degreeOf_second_le_of_hasBidegreeAtMost hdegree

/-- Specialization cannot increase the second-coordinate degree. -/
theorem secondCoordinateSpecialization_natDegree_le_degreeOf_second
    (f : MvPolynomial (Fin 2) K) (x : K) :
    (secondCoordinateSpecialization f x).natDegree ≤
      MvPolynomial.degreeOf 1 f := by
  calc
    (secondCoordinateSpecialization f x).natDegree ≤
        (planeCurvePolynomialInSecondCoordinate f).natDegree :=
      Polynomial.natDegree_map_le
    _ = MvPolynomial.degreeOf 1 f :=
      planeCurvePolynomialInSecondCoordinate_natDegree f

private theorem evalZeroSubtype_card_le_natDegree
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (P : Polynomial K) (hP : P ≠ 0) :
    Fintype.card {x : K // P.eval x = 0} ≤ P.natDegree := by
  classical
  let rootEmbedding : {x : K // P.eval x = 0} ↪ P.roots.toFinset :=
    { toFun := fun x => ⟨x, by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
        exact x.2⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : P.roots.toFinset => (z : K)) h }
  calc
    Fintype.card {x : K // P.eval x = 0} ≤ P.roots.toFinset.card :=
      by
        simpa only [Fintype.card_coe] using
          Fintype.card_le_of_injective rootEmbedding rootEmbedding.injective
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P

/-- Fiber counting over first-coordinate roots of unity, stated using an
explicit second-coordinate degree bound. -/
theorem torusCurveTorsionIntersection_card_le_firstOrder_mul_of_degreeOf_second_le
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K)
    (secondDegree firstOrder secondOrder : ℕ)
    (hdegreeSecond : MvPolynomial.degreeOf 1 f ≤ secondDegree)
    (hf : Irreducible f)
    (hsecond : 0 < MvPolynomial.degreeOf 1 f)
    (hfirstOrder : 0 < firstOrder) :
    (BGS.External.torusCurveTorsionIntersection
      K f firstOrder secondOrder).card ≤ firstOrder * secondDegree := by
  classical
  let S := BGS.External.torusCurveTorsionIntersection
    K f firstOrder secondOrder
  let : NeZero firstOrder := ⟨hfirstOrder.ne'⟩
  let : Fintype (rootsOfUnity firstOrder K) := Fintype.ofFinite _
  let T := fun x : rootsOfUnity firstOrder K =>
    {y : K // (secondCoordinateSpecialization f (x.1 : K)).eval y = 0}
  let embedding : {z // z ∈ S} ↪ Sigma T :=
    { toFun := fun z =>
        ⟨⟨z.1.1, (mem_rootsOfUnity firstOrder z.1.1).2
            (BGS.External.mem_torusCurveTorsionIntersection_iff.mp z.2).2.1⟩,
          ⟨(z.1.2 : K), by
            rw [secondCoordinateSpecialization_eval]
            exact (BGS.External.mem_torusCurveTorsionIntersection_iff.mp z.2).1⟩⟩
      inj' := by
        intro z w hzw
        apply Subtype.ext
        apply Prod.ext
        · exact congrArg (fun q : Sigma T => (q.1 : Kˣ)) hzw
        · apply Units.ext
          exact congrArg (fun q : Sigma T => (q.2.1 : K)) hzw }
  have hFiber (x : rootsOfUnity firstOrder K) :
      Fintype.card (T x) ≤ secondDegree := by
    exact (evalZeroSubtype_card_le_natDegree
      (secondCoordinateSpecialization f (x.1 : K))
      (secondCoordinateSpecialization_ne_zero_of_irreducible
        hf hsecond (x.1 : K))).trans
      ((secondCoordinateSpecialization_natDegree_le_degreeOf_second
        f (x.1 : K)).trans hdegreeSecond)
  calc
    S.card = Fintype.card {z // z ∈ S} := by simp
    _ ≤ Fintype.card (Sigma T) :=
      Fintype.card_le_of_injective embedding embedding.injective
    _ = ∑ x, Fintype.card (T x) := Fintype.card_sigma
    _ ≤ ∑ _x : rootsOfUnity firstOrder K, secondDegree := by
      exact Finset.sum_le_sum fun x _ => hFiber x
    _ = Fintype.card (rootsOfUnity firstOrder K) * secondDegree := by
      simp
    _ ≤ firstOrder * secondDegree :=
      Nat.mul_le_mul_right secondDegree (by
        simpa only [Nat.card_eq_fintype_card] using
          card_rootsOfUnity K firstOrder)

/-- The torsion intersection has at most `firstOrder * secondDegree` points. -/
theorem torusCurveTorsionIntersection_card_le_firstOrder_mul_secondDegree
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K)
    (firstDegree secondDegree firstOrder secondOrder : ℕ)
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree)
    (hf : Irreducible f)
    (hsecond : 0 < MvPolynomial.degreeOf 1 f)
    (hfirstOrder : 0 < firstOrder) :
    (BGS.External.torusCurveTorsionIntersection
      K f firstOrder secondOrder).card ≤ firstOrder * secondDegree :=
  torusCurveTorsionIntersection_card_le_firstOrder_mul_of_degreeOf_second_le
    f secondDegree firstOrder secondOrder
      (degreeOf_second_le_of_hasBidegreeAtMost hdegree)
      hf hsecond hfirstOrder

/-- Swap the two coordinates of a bivariate polynomial. -/
def swapPlaneCurveCoordinates (f : MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 2) K :=
  MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) f

@[simp]
theorem eval_swapPlaneCurveCoordinates (f : MvPolynomial (Fin 2) K)
    (x y : K) :
    MvPolynomial.eval ![y, x] (swapPlaneCurveCoordinates f) =
      MvPolynomial.eval ![x, y] f := by
  simp [swapPlaneCurveCoordinates, MvPolynomial.eval_rename]

/-- Swapping both curve coordinates and torsion orders preserves the torsion
intersection. -/
def torusCurveTorsionIntersectionSwapEquiv
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K) (firstOrder secondOrder : ℕ) :
    {z // z ∈ BGS.External.torusCurveTorsionIntersection
      K f firstOrder secondOrder} ≃
    {z // z ∈ BGS.External.torusCurveTorsionIntersection
      K (swapPlaneCurveCoordinates f) secondOrder firstOrder} := by
  classical
  let swapPoint : Kˣ × Kˣ → Kˣ × Kˣ := fun z => (z.2, z.1)
  refine
    { toFun := fun z => ⟨swapPoint z.1, ?_⟩
      invFun := fun z => ⟨swapPoint z.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [BGS.External.mem_torusCurveTorsionIntersection_iff]
    have hz := BGS.External.mem_torusCurveTorsionIntersection_iff.mp z.2
    exact ⟨by
      simpa [swapPoint] using hz.1,
      hz.2.2, hz.2.1⟩
  · rw [BGS.External.mem_torusCurveTorsionIntersection_iff]
    have hz := BGS.External.mem_torusCurveTorsionIntersection_iff.mp z.2
    exact ⟨by
      simpa [swapPoint] using hz.1,
      hz.2.2, hz.2.1⟩
  · intro z
    apply Subtype.ext
    rfl
  · intro z
    apply Subtype.ext
    rfl

/-- Coordinate swapping preserves the torsion-intersection cardinality. -/
theorem torusCurveTorsionIntersection_card_swap
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K) (firstOrder secondOrder : ℕ) :
    (BGS.External.torusCurveTorsionIntersection
      K f firstOrder secondOrder).card =
    (BGS.External.torusCurveTorsionIntersection K
      (swapPlaneCurveCoordinates f) secondOrder firstOrder).card := by
  classical
  calc
    (BGS.External.torusCurveTorsionIntersection
      K f firstOrder secondOrder).card =
        Fintype.card {z // z ∈ BGS.External.torusCurveTorsionIntersection
          K f firstOrder secondOrder} :=
      (Fintype.card_coe
        (BGS.External.torusCurveTorsionIntersection
          K f firstOrder secondOrder)).symm
    _ = Fintype.card {z // z ∈ BGS.External.torusCurveTorsionIntersection K
          (swapPlaneCurveCoordinates f) secondOrder firstOrder} :=
      Fintype.card_congr
        (torusCurveTorsionIntersectionSwapEquiv f firstOrder secondOrder)
    _ = (BGS.External.torusCurveTorsionIntersection K
          (swapPlaneCurveCoordinates f) secondOrder firstOrder).card :=
      Fintype.card_coe
        (BGS.External.torusCurveTorsionIntersection K
          (swapPlaneCurveCoordinates f) secondOrder firstOrder)

/-- The torsion intersection has at most `secondOrder * firstDegree` points. -/
theorem torusCurveTorsionIntersection_card_le_secondOrder_mul_firstDegree
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K)
    (firstDegree secondDegree firstOrder secondOrder : ℕ)
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree)
    (hf : Irreducible f)
    (hfirst : 0 < MvPolynomial.degreeOf 0 f)
    (hsecondOrder : 0 < secondOrder) :
    (BGS.External.torusCurveTorsionIntersection
      K f firstOrder secondOrder).card ≤ secondOrder * firstDegree := by
  let fSwap := swapPlaneCurveCoordinates f
  have hfSwap : Irreducible fSwap := by
    exact hf.map (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1))
  have hdegreeSwap : MvPolynomial.degreeOf 1 fSwap ≤ firstDegree := by
    have hdegreeEq := MvPolynomial.degreeOf_rename_of_injective
      (Equiv.swap (0 : Fin 2) 1).injective (0 : Fin 2) (p := f)
    rw [show (Equiv.swap (0 : Fin 2) 1) 0 = 1 by decide] at hdegreeEq
    exact hdegreeEq.le.trans
      (degreeOf_first_le_of_hasBidegreeAtMost hdegree)
  have hpositiveSwap : 0 < MvPolynomial.degreeOf 1 fSwap := by
    have hdegreeEq := MvPolynomial.degreeOf_rename_of_injective
      (Equiv.swap (0 : Fin 2) 1).injective (0 : Fin 2) (p := f)
    rw [show (Equiv.swap (0 : Fin 2) 1) 0 = 1 by decide] at hdegreeEq
    exact hdegreeEq.symm ▸ hfirst
  rw [torusCurveTorsionIntersection_card_swap]
  exact torusCurveTorsionIntersection_card_le_firstOrder_mul_of_degreeOf_second_le
    fSwap firstDegree secondOrder firstOrder hdegreeSwap hfSwap
      hpositiveSwap hsecondOrder

/-- The sharp elementary bidegree/order bound under the precise algebraic
hypotheses needed for fiber counting. -/
theorem torusCurveTorsionIntersection_card_le_min_bidegree_order_of_irreducible
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K)
    (firstDegree secondDegree firstOrder secondOrder : ℕ)
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree)
    (hf : Irreducible f)
    (hfirst : 0 < MvPolynomial.degreeOf 0 f)
    (hsecond : 0 < MvPolynomial.degreeOf 1 f)
    (hfirstOrder : 0 < firstOrder) (hsecondOrder : 0 < secondOrder) :
    (BGS.External.torusCurveTorsionIntersection
      K f firstOrder secondOrder).card ≤
        min (firstOrder * secondDegree) (secondOrder * firstDegree) := by
  apply le_min
  · exact torusCurveTorsionIntersection_card_le_firstOrder_mul_secondDegree
      f firstDegree secondDegree firstOrder secondOrder hdegree hf
        hsecond hfirstOrder
  · exact torusCurveTorsionIntersection_card_le_secondOrder_mul_firstDegree
      f firstDegree secondDegree firstOrder secondOrder hdegree hf
        hfirst hsecondOrder

/-- The sharp elementary bidegree/order bound for an admissible torus curve. -/
theorem torusCurveTorsionIntersection_card_le_min_bidegree_order
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K)
    (firstDegree secondDegree firstOrder secondOrder : ℕ)
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree)
    (hcurve : BGS.External.IsCorvajaZannierPlaneCurve f)
    (hfirstOrder : 0 < firstOrder) (hsecondOrder : 0 < secondOrder) :
    (BGS.External.torusCurveTorsionIntersection
      K f firstOrder secondOrder).card ≤
        min (firstOrder * secondDegree) (secondOrder * firstDegree) := by
  have hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure hcurve.1
  exact torusCurveTorsionIntersection_card_le_min_bidegree_order_of_irreducible
    f firstDegree secondDegree firstOrder secondOrder hdegree hf
      (degreeOf_first_pos_of_pderiv_ne_zero hcurve.2.2.1)
      (degreeOf_second_pos_of_pderiv_ne_zero hcurve.2.2.2)
      hfirstOrder hsecondOrder

end

end BGS.CorvajaZannier
