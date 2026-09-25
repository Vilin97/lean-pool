/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneSingularPointBound
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.TorsionBidegreeCount
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.TorsionPointNormalization

/-!
# Elementary affine plane-curve fiber bounds

For an irreducible plane curve with positive degree in one coordinate, every
fiber in that direction is cut out by a nonzero univariate polynomial.  This
gives the two elementary bounds

`#C(K) ≤ #K * degree_y(f)` and `#C(K) ≤ #K * degree_x(f)`.

These estimates handle the large-bidegree branch of the final affine
Hasse--Weil theorem, where a trivial fiber count is stronger than carrying
normalization error terms.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Affine points are the sigma type of their first coordinate and the roots
of the corresponding second-coordinate specialization. -/
def affinePlaneCurvePointEquivSecondCoordinateRoots
    (f : MvPolynomial (Fin 2) K) :
    AffinePlaneCurvePoint f ≃
      Σ x : K, {y : K // (secondCoordinateSpecialization f x).eval y = 0} where
  toFun z := ⟨z.1.1, ⟨z.1.2, by
    rw [secondCoordinateSpecialization_eval]
    exact z.2⟩⟩
  invFun z := ⟨(z.1, z.2.1), by
    rw [← secondCoordinateSpecialization_eval]
    exact z.2.2⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv z := by
    cases z
    rfl

/-- Counting the roots in every first-coordinate fiber bounds all affine
points by the field cardinality times a second-coordinate degree bound. -/
theorem affinePlaneCurvePoint_card_le_card_mul_of_degreeOf_second_le
    {f : MvPolynomial (Fin 2) K} {secondDegree : ℕ}
    (hf : Irreducible f)
    (hsecond : 0 < MvPolynomial.degreeOf 1 f)
    (hdegreeSecond : MvPolynomial.degreeOf 1 f ≤ secondDegree) :
    Fintype.card (AffinePlaneCurvePoint f) ≤
      Fintype.card K * secondDegree := by
  let roots := fun x : K =>
    {y : K // (secondCoordinateSpecialization f x).eval y = 0}
  have hFiber (x : K) : Fintype.card (roots x) ≤ secondDegree :=
    (polynomialEvalZeroSubtype_card_le_natDegree
      (secondCoordinateSpecialization f x)
      (secondCoordinateSpecialization_ne_zero_of_irreducible hf hsecond x)).trans
      ((secondCoordinateSpecialization_natDegree_le_degreeOf_second f x).trans
        hdegreeSecond)
  calc
    Fintype.card (AffinePlaneCurvePoint f) =
        Fintype.card (Σ x : K, roots x) :=
      Fintype.card_congr (affinePlaneCurvePointEquivSecondCoordinateRoots f)
    _ = ∑ x : K, Fintype.card (roots x) := Fintype.card_sigma
    _ ≤ ∑ _x : K, secondDegree :=
      Finset.sum_le_sum fun x _ => hFiber x
    _ = Fintype.card K * secondDegree := by simp

/-- Public bidegree form of the second-coordinate fiber bound. -/
theorem affinePlaneCurvePoint_card_le_card_mul_secondDegree
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree)
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    Fintype.card (AffinePlaneCurvePoint f) ≤
      Fintype.card K * secondDegree := by
  exact affinePlaneCurvePoint_card_le_card_mul_of_degreeOf_second_le
    hf (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
      (degreeOf_second_le_of_hasBidegreeAtMost hdegree)

/-- Swapping the two affine coordinates identifies the point sets of `f` and
the coordinate-swapped polynomial. -/
def affinePlaneCurvePointEquivSwap (f : MvPolynomial (Fin 2) K) :
    AffinePlaneCurvePoint f ≃
      AffinePlaneCurvePoint (swapPlaneCurveCoordinates f) where
  toFun z := ⟨(z.1.2, z.1.1), by
    rw [eval_swapPlaneCurveCoordinates]
    exact z.2⟩
  invFun z := ⟨(z.1.2, z.1.1), by
    have hz := z.2
    rw [eval_swapPlaneCurveCoordinates] at hz
    exact hz⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl

omit [Fintype K] [DecidableEq K] in
/-- Coordinate swapping preserves irreducibility. -/
theorem irreducible_swapPlaneCurveCoordinates
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f) :
    Irreducible (swapPlaneCurveCoordinates f) := by
  change Irreducible
    (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1) f)
  exact hf.map (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1))

omit [Fintype K] [DecidableEq K] in
/-- After swapping, the second-coordinate degree is the original
first-coordinate degree. -/
theorem degreeOf_second_swapPlaneCurveCoordinates
    (f : MvPolynomial (Fin 2) K) :
    MvPolynomial.degreeOf 1 (swapPlaneCurveCoordinates f) =
      MvPolynomial.degreeOf 0 f := by
  change MvPolynomial.degreeOf 1
      (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) f) = _
  simpa using
    (MvPolynomial.degreeOf_rename_of_injective
      (p := f) (Equiv.swap (0 : Fin 2) 1).injective (0 : Fin 2))

/-- Public bidegree form of the symmetric first-coordinate fiber bound. -/
theorem affinePlaneCurvePoint_card_le_card_mul_firstDegree
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree)
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0) :
    Fintype.card (AffinePlaneCurvePoint f) ≤
      Fintype.card K * firstDegree := by
  rw [Fintype.card_congr (affinePlaneCurvePointEquivSwap f)]
  apply affinePlaneCurvePoint_card_le_card_mul_of_degreeOf_second_le
    (irreducible_swapPlaneCurveCoordinates hf)
  · rw [degreeOf_second_swapPlaneCurveCoordinates]
    exact degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst
  · rw [degreeOf_second_swapPlaneCurveCoordinates]
    exact degreeOf_first_le_of_hasBidegreeAtMost hdegree

/-- The external finite-set presentation has the same cardinality as the
affine-point subtype used by the normalization development. -/
def affinePlaneCurveZerosEquivAffinePlaneCurvePoint
    (f : MvPolynomial (Fin 2) K) :
    ↑(BGS.External.affinePlaneCurveZeros K f) ≃ AffinePlaneCurvePoint f :=
  Equiv.subtypeEquivRight fun _ => BGS.External.mem_affinePlaneCurveZeros_iff

theorem affinePlaneCurveZeros_card_eq_affinePlaneCurvePoint_card
    (f : MvPolynomial (Fin 2) K) :
    (BGS.External.affinePlaneCurveZeros K f).card =
      Fintype.card (AffinePlaneCurvePoint f) := by
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (affinePlaneCurveZerosEquivAffinePlaneCurvePoint f)

end

end BGS.HasseWeil
