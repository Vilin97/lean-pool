/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.Prefix
public import LeanPool.BooleanMultiplication.N4.QuadraticProjection

/-!
# Homogeneous ANF/exterior bridge

The exterior calculations are connected to Boolean ANFs through the degree
three and degree four coefficient projections below.  Only fixed products of
an input variable with one of the three rational places (and pairs of those
places) require coordinate normalization.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Cubic coefficients as a three-form array, with repeated-index coordinates zero. -/
@[expose] def anfThreeProjection : ANF 8 →ₗ[F₂] ThreeForm where
  toFun p i j k :=
    if ({i, j, k} : Finset (Fin 8)).card = 3 then
      p.coeff ⟨{i, j, k}⟩ else 0
  map_add' p q := by
    funext i j k
    by_cases h : ({i, j, k} : Finset (Fin 8)).card = 3 <;> simp [h]
  map_smul' a p := by
    funext i j k
    by_cases h : ({i, j, k} : Finset (Fin 8)).card = 3 <;> simp [h]

/-- Quartic coefficients as a four-form array, with repeated-index coordinates zero. -/
@[expose] def anfFourProjection : ANF 8 →ₗ[F₂] FourForm where
  toFun p i j k l :=
    if ({i, j, k, l} : Finset (Fin 8)).card = 4 then
      p.coeff ⟨{i, j, k, l}⟩ else 0
  map_add' p q := by
    funext i j k l
    by_cases h : ({i, j, k, l} : Finset (Fin 8)).card = 4 <;> simp [h]
  map_smul' a p := by
    funext i j k l
    by_cases h : ({i, j, k, l} : Finset (Fin 8)).card = 4 <;> simp [h]

/-- The Boolean ANF of the given linear form. -/
@[expose] def linearANF (ell : LinearForm) : ANF 8 :=
  ∑ i : Fin 8, ell i • X i

/-- The Boolean ANF with the given constant and linear parts. -/
@[expose] def affineANF (a : F₂) (ell : LinearForm) : ANF 8 :=
  a • (1 : ANF 8) + linearANF ell

/-- The target ANF of a linear combination of rational-place evaluations. -/
@[expose] def rationalANF (α : Fin 3 → F₂) : ANF 8 :=
  targetANF (rationalCoeffRep α)

theorem rationalANF_eq_sum (α : Fin 3 → F₂) :
    rationalANF α =
      ∑ θ : Fin 3, α θ • targetANF (rationalPlaceCoeff θ) := by
  change targetANFLinear (rationalCoeffRep α) = _
  rw [rationalCoeffRep]
  simp [rationalPlaceCoeff, Fin.sum_univ_succ, map_add, map_smul, targetANFLinear_apply,
    add_assoc]

/-- The product coefficient index corresponding to two input coefficient indices. -/
@[expose] def hankelIndex (i j : Fin 4) : Fin 7 := ⟨i.val + j.val, by omega⟩

/-- The squarefree mixed monomial for one coefficient from each input polynomial. -/
@[expose] def targetPair (i j : Fin 4) : Finset (Fin 8) := {aCoord i, bCoord j}

/-- The target Hankel form as its sixteen cross monomials. -/
theorem targetANF_eq_double_sum (c : TargetCoeff) :
    targetANF c =
      ∑ i : Fin 4, ∑ j : Fin 4,
        c (hankelIndex i j) • monomial (targetPair i j) := by
  simp [targetANF, UnrestrictedBooleanMul.Mul, mulCoefficient, Fin.sum_univ_succ, hankelIndex,
    targetPair, aCoord, bCoord, aVar, bVar, X, monomial_mul]
  ring

/-- A target-product coefficient is a finite convolution of its mixed monomials. -/
theorem coeff_targetANF_mul_targetANF (c d : TargetCoeff) (s : Finset (Fin 8)) :
    (targetANF c * targetANF d).coeff ⟨s⟩ =
      ∑ u : Fin 4, ∑ v : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4,
        (c (hankelIndex i j) * d (hankelIndex u v)) *
          (if targetPair i j ∪ targetPair u v = s then (1 : F₂) else 0) := by
  rw [targetANF_eq_double_sum, targetANF_eq_double_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul, MonoidAlgebra.coeff_sum,
    MonoidAlgebra.coeff_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    monomial_mul, coeff_monomial]

/-- The cubic coordinate array of a squarefree monomial. -/
@[expose] def monomialThree (s : Finset (Fin 8)) : ThreeForm := fun i j k =>
  if ({i, j, k} : Finset (Fin 8)).card = 3 then
    if s = {i, j, k} then 1 else 0
  else 0

theorem anfThreeProjection_monomial (s : Finset (Fin 8)) :
    anfThreeProjection (monomial s) = monomialThree s := by
  funext i j k
  by_cases hcard : ({i, j, k} : Finset (Fin 8)).card = 3 <;>
    simp [anfThreeProjection, monomialThree, hcard, coeff_monomial]

/-- Cubic part of an input variable times a rational-place product. -/
def cubicPlaceModel (r : Fin 8) (θ : Fin 3) : ThreeForm :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    rationalPlaceCoeff θ (hankelIndex i j) •
      monomialThree ({r} ∪ targetPair i j)

/-- The linear form selecting one input coordinate. -/
@[expose] def coordinateLinear (r : Fin 8) : LinearForm := fun i =>
  if i = r then 1 else 0

private theorem anfThreeProjection_three_X (r a b : Fin 8) :
    anfThreeProjection (X r * (X a * X b)) =
      vectorWedgeTwo (coordinateLinear r)
        (vectorWedge (coordinateLinear a) (coordinateLinear b)) := by
  rw [show X r * (X a * X b) = monomial {r, a, b} by
    rw [X, X, X, monomial_mul, monomial_mul]
    congr 1]
  rw [anfThreeProjection_monomial]
  funext i j k
  simp only [monomialThree, vectorWedgeTwo, vectorWedge, coordinateLinear]
  by_cases hcard : ({i, j, k} : Finset (Fin 8)).card = 3
  · have hij : i ≠ j := by
      intro hij
      subst j
      have hle := Finset.card_le_two (a := i) (b := k)
      have hcard' : ({i, k} : Finset (Fin 8)).card = 3 := by
        simpa using hcard
      exact (Nat.ne_of_lt (lt_of_le_of_lt hle (by decide))) hcard'
    have hik : i ≠ k := by
      intro hik
      subst k
      have hle := Finset.card_le_two (a := i) (b := j)
      have hcard' : ({i, j} : Finset (Fin 8)).card = 3 := by
        simpa [Finset.pair_comm] using hcard
      exact (Nat.ne_of_lt (lt_of_le_of_lt hle (by decide))) hcard'
    have hjk : j ≠ k := by
      intro hjk
      subst k
      have hle := Finset.card_le_two (a := i) (b := j)
      have hcard' : ({i, j} : Finset (Fin 8)).card = 3 := by
        simpa using hcard
      exact (Nat.ne_of_lt (lt_of_le_of_lt hle (by decide))) hcard'
    rw [ite_eq_left hcard]
    by_cases hset : ({r, a, b} : Finset (Fin 8)) = {i, j, k}
    · rw [ite_eq_left hset]
      have hrab : ({r, a, b} : Finset (Fin 8)).card = 3 := by
        rw [hset]
        exact hcard
      have hra : r ≠ a := by
        intro h
        subst a
        have hcard' : ({r, b} : Finset (Fin 8)).card = 3 := by
          simpa using hrab
        have hle := Finset.card_le_two (a := r) (b := b)
        omega
      have hrb : r ≠ b := by
        intro h
        subst b
        have hcard' : ({r, a} : Finset (Fin 8)).card = 3 := by
          simpa [Finset.pair_comm] using hrab
        have hle := Finset.card_le_two (a := r) (b := a)
        omega
      have hab : a ≠ b := by
        intro h
        subst b
        have hcard' : ({r, a} : Finset (Fin 8)).card = 3 := by
          simpa using hrab
        have hle := Finset.card_le_two (a := r) (b := a)
        omega
      have hr : r = i ∨ r = j ∨ r = k := by
        have hrmem : r ∈ ({i, j, k} : Finset (Fin 8)) := by
          rw [← hset]
          simp
        simpa using hrmem
      have ha : a = i ∨ a = j ∨ a = k := by
        have hamem : a ∈ ({i, j, k} : Finset (Fin 8)) := by
          rw [← hset]
          simp
        simpa using hamem
      have hb : b = i ∨ b = j ∨ b = k := by
        have hbmem : b ∈ ({i, j, k} : Finset (Fin 8)) := by
          rw [← hset]
          simp
        simpa using hbmem
      rcases hr with rfl | rfl | rfl <;>
        rcases ha with rfl | rfl | rfl <;>
        rcases hb with rfl | rfl | rfl
      all_goals
        clear hset hcard hrab
        simp_all []
    · rw [ite_eq_right hset]
      by_cases hri : r = i
      · subst r
        simp only [ite_eq_right hij.symm, ite_eq_right hik.symm, zero_mul, add_zero]
        split_ifs <;>
          simp_all [Finset.ext_iff, or_comm, or_left_comm, ]
      by_cases hrj : r = j
      · subst r
        simp only [ite_eq_right hij, ite_eq_right hjk.symm, zero_mul, zero_add, add_zero]
        split_ifs <;>
          simp_all [Finset.ext_iff, or_comm, or_left_comm, ]
      by_cases hrk : r = k
      · subst r
        simp only [ite_eq_right hik, ite_eq_right hjk, zero_mul, zero_add, add_zero]
        split_ifs <;>
          simp_all [Finset.ext_iff, or_comm, or_left_comm, ]
      · simp [Ne.symm hri, Ne.symm hrj, Ne.symm hrk]
  · rw [ite_eq_right hcard]
    by_cases hij : i = j
    · subst j
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    by_cases hik : i = k
    · subst k
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    by_cases hjk : j = k
    · subst k
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    · exact False.elim (hcard (by simp [hij, hik, hjk]))

theorem vectorWedgeTwo_add_right_h (u : LinearForm) (q r : TwoForm) :
    vectorWedgeTwo u (q + r) =
      vectorWedgeTwo u q + vectorWedgeTwo u r := by
  funext i j k
  simp only [vectorWedgeTwo, Pi.add_apply]
  ring

theorem vectorWedgeTwo_smul_right_h (u : LinearForm) (a : F₂)
    (q : TwoForm) :
    vectorWedgeTwo u (a • q) = a • vectorWedgeTwo u q := by
  funext i j k
  simp only [vectorWedgeTwo, Pi.smul_apply, smul_eq_mul]
  ring

/-- The vector and two-form exterior product as a bilinear map. -/
@[expose]
def vectorWedgeTwoBilinear :
    LinearForm →ₗ[F₂] TwoForm →ₗ[F₂] ThreeForm where
  toFun u :=
    { toFun := fun q => vectorWedgeTwo u q
      map_add' := vectorWedgeTwo_add_right_h u
      map_smul' := fun a q => vectorWedgeTwo_smul_right_h u a q }
  map_add' u v := by
    apply LinearMap.ext
    intro q
    change vectorWedgeTwo (u + v) q =
      vectorWedgeTwo u q + vectorWedgeTwo v q
    exact vectorWedgeTwo_add_left u v q
  map_smul' a u := by
    apply LinearMap.ext
    intro q
    change vectorWedgeTwo (a • u) q = a • vectorWedgeTwo u q
    exact vectorWedgeTwo_smul_left a u q

theorem monomialThree_union_targetPair (r : Fin 8) (i j : Fin 4) :
    monomialThree ({r} ∪ targetPair i j) =
      vectorWedgeTwo (coordinateLinear r)
        (vectorWedge (coordinateLinear (aCoord i))
          (coordinateLinear (bCoord j))) := by
  rw [← anfThreeProjection_monomial]
  rw [show monomial ({r} ∪ targetPair i j) =
      X r * (X (aCoord i) * X (bCoord j)) by
    simp [targetPair, X, monomial_mul]]
  exact anfThreeProjection_three_X r (aCoord i) (bCoord j)

theorem targetTwo_eq_double_wedge (c : TargetCoeff) :
    targetTwo c =
      ∑ i : Fin 4, ∑ j : Fin 4, c (hankelIndex i j) •
        vectorWedge (coordinateLinear (aCoord i))
          (coordinateLinear (bCoord j)) := by
  rw [← anfTwoProjection_targetANF, targetANF_eq_double_sum]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [show monomial (targetPair i j) = X (aCoord i) * X (bCoord j) by
    simp [targetPair, X, monomial_mul]]
  rw [anfTwoProjection_X_mul_X]
  congr 2 <;> funext k <;> simp [coordinateLinear]

private theorem cubicPlaceModel_eq :
    ∀ (r : Fin 8) (θ : Fin 3),
      cubicPlaceModel r θ =
        vectorWedgeTwo (coordinateLinear r) (rationalPlaceTwo θ) := by
  intro r θ
  rw [← targetTwo_rationalPlaceCoeff, targetTwo_eq_double_wedge]
  change cubicPlaceModel r θ =
    vectorWedgeTwoBilinear (coordinateLinear r)
      (∑ i : Fin 4, ∑ j : Fin 4,
        rationalPlaceCoeff θ (hankelIndex i j) •
          vectorWedge (coordinateLinear (aCoord i))
            (coordinateLinear (bCoord j)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  rw [monomialThree_union_targetPair]
  rfl

private theorem anfThreeProjection_X_rationalPlace :
    ∀ (i : Fin 8) (θ : Fin 3),
      anfThreeProjection (X i * targetANF (rationalPlaceCoeff θ)) =
        vectorWedgeTwo (anfLinearProjection (X i)) (rationalPlaceTwo θ) := by
  intro i θ
  have hlin : anfLinearProjection (X i) = coordinateLinear i := by
    funext j
    simp [coordinateLinear, eq_comm]
  rw [hlin]
  rw [targetANF_eq_double_sum]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, X, monomial_mul,
    anfThreeProjection_monomial]
  exact cubicPlaceModel_eq i θ

theorem linear_eq_sum_coordinate (ell : LinearForm) :
    ell = ∑ i : Fin 8, ell i • coordinateLinear i := by
  funext j
  fin_cases j <;> simp [coordinateLinear]

private theorem anfThreeProjection_linear_mul_place
    (ell : LinearForm) (θ : Fin 3) :
    anfThreeProjection
        (linearANF ell * targetANF (rationalPlaceCoeff θ)) =
      vectorWedgeTwo ell (rationalPlaceTwo θ) := by
  rw [linearANF]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul]
  simp_rw [anfThreeProjection_X_rationalPlace]
  have hlin : ∀ i : Fin 8,
      anfLinearProjection (X i) = coordinateLinear i := by
    intro i
    funext j
    simp [coordinateLinear, eq_comm]
  simp_rw [hlin]
  change (∑ i : Fin 8, ell i •
      vectorWedgeTwo (coordinateLinear i) (rationalPlaceTwo θ)) = _
  change _ = vectorWedgeTwoBilinear ell (rationalPlaceTwo θ)
  symm
  calc
    vectorWedgeTwoBilinear ell (rationalPlaceTwo θ) =
        vectorWedgeTwoBilinear
          (∑ i : Fin 8, ell i • coordinateLinear i)
          (rationalPlaceTwo θ) := by rw [← linear_eq_sum_coordinate ell]
    _ = ∑ i : Fin 8, ell i •
        vectorWedgeTwo (coordinateLinear i) (rationalPlaceTwo θ) := by
      simp only [map_sum, map_smul]
      rfl

theorem anfThreeProjection_linear_mul_rational
    (ell : LinearForm) (β : Fin 3 → F₂) :
    anfThreeProjection (linearANF ell * rationalANF β) =
      vectorWedgeTwo ell (rationalTwo β) := by
  rw [rationalANF_eq_sum]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    anfThreeProjection_linear_mul_place]
  change (∑ θ : Fin 3, β θ •
      vectorWedgeTwo ell (rationalPlaceTwo θ)) = _
  change _ = vectorWedgeTwoBilinear ell (rationalTwo β)
  rw [rationalTwo]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro θ _
  rfl

/-- Three quartic monomials detecting the rational-place wedge coordinates. -/
@[expose] def quarticProbeSet : Fin 3 → Finset (Fin 8) :=
  ![{0, 1, 4, 6}, {1, 3, 5, 7}, {0, 3, 4, 7}]

/-- Extract the three designated quartic coefficients of an ANF. -/
@[expose] def quarticProbeANF : ANF 8 →ₗ[F₂] (Fin 3 → F₂) where
  toFun p t := p.coeff ⟨quarticProbeSet t⟩
  map_add' p q := by ext t; simp
  map_smul' a p := by ext t; simp

@[simp] theorem quarticProbeANF_monomial
    (s : Finset (Fin 8)) (t : Fin 3) :
    quarticProbeANF (monomial s) t =
      if s = quarticProbeSet t then 1 else 0 := by
  simp [quarticProbeANF, coeff_monomial]

/-- The three designated coordinates of a wedge of two two-forms. -/
@[expose] def quarticWedgeProbe (q r : TwoForm) : Fin 3 → F₂ :=
  ![wedgeTwo q r 0 1 4 6, wedgeTwo q r 1 3 5 7,
    wedgeTwo q r 0 3 4 7]

private theorem targetANF_targetBasis_homogeneous (s : Fin 7) :
    targetANF (targetBasis s) = Mul 4 s := by
  simp [targetANF, targetBasis_apply]

private theorem quarticProbe_Mul_mul_zero :
    ∀ t : Fin 7,
      quarticProbeANF
          (Mul 4 0 * Mul 4 t) =
        quarticWedgeProbe (targetTwo (targetBasis 0))
          (targetTwo (targetBasis t)) := by
  intro t
  funext u
  rw [← targetANF_targetBasis_homogeneous, ← targetANF_targetBasis_homogeneous]
  change (targetANF (targetBasis 0) * targetANF (targetBasis t)).coeff
    ⟨quarticProbeSet u⟩ = _
  rw [coeff_targetANF_mul_targetANF]
  simp only [targetBasis, Pi.basisFun_apply]
  revert t u
  decide +kernel

private theorem quarticProbe_Mul_mul_one :
    ∀ t : Fin 7,
      quarticProbeANF (Mul 4 1 * Mul 4 t) =
        quarticWedgeProbe (targetTwo (targetBasis 1))
          (targetTwo (targetBasis t)) := by
  intro t
  funext u
  rw [← targetANF_targetBasis_homogeneous, ← targetANF_targetBasis_homogeneous]
  change (targetANF (targetBasis 1) * targetANF (targetBasis t)).coeff
    ⟨quarticProbeSet u⟩ = _
  rw [coeff_targetANF_mul_targetANF]
  simp only [targetBasis, Pi.basisFun_apply]
  revert t u
  decide +kernel

private theorem quarticProbe_Mul_mul_two :
    ∀ t : Fin 7,
      quarticProbeANF (Mul 4 2 * Mul 4 t) =
        quarticWedgeProbe (targetTwo (targetBasis 2))
          (targetTwo (targetBasis t)) := by
  intro t
  funext u
  rw [← targetANF_targetBasis_homogeneous, ← targetANF_targetBasis_homogeneous]
  change (targetANF (targetBasis 2) * targetANF (targetBasis t)).coeff
    ⟨quarticProbeSet u⟩ = _
  rw [coeff_targetANF_mul_targetANF]
  simp only [targetBasis, Pi.basisFun_apply]
  revert t u
  decide +kernel

private theorem quarticProbe_Mul_mul_three :
    ∀ t : Fin 7,
      quarticProbeANF (Mul 4 3 * Mul 4 t) =
        quarticWedgeProbe (targetTwo (targetBasis 3))
          (targetTwo (targetBasis t)) := by
  intro t
  funext u
  rw [← targetANF_targetBasis_homogeneous, ← targetANF_targetBasis_homogeneous]
  change (targetANF (targetBasis 3) * targetANF (targetBasis t)).coeff
    ⟨quarticProbeSet u⟩ = _
  rw [coeff_targetANF_mul_targetANF]
  simp only [targetBasis, Pi.basisFun_apply]
  revert t u
  decide +kernel

private theorem quarticProbe_Mul_mul_four :
    ∀ t : Fin 7,
      quarticProbeANF (Mul 4 4 * Mul 4 t) =
        quarticWedgeProbe (targetTwo (targetBasis 4))
          (targetTwo (targetBasis t)) := by
  intro t
  funext u
  rw [← targetANF_targetBasis_homogeneous, ← targetANF_targetBasis_homogeneous]
  change (targetANF (targetBasis 4) * targetANF (targetBasis t)).coeff
    ⟨quarticProbeSet u⟩ = _
  rw [coeff_targetANF_mul_targetANF]
  simp only [targetBasis, Pi.basisFun_apply]
  revert t u
  decide +kernel

private theorem quarticProbe_Mul_mul_five :
    ∀ t : Fin 7,
      quarticProbeANF (Mul 4 5 * Mul 4 t) =
        quarticWedgeProbe (targetTwo (targetBasis 5))
          (targetTwo (targetBasis t)) := by
  intro t
  funext u
  rw [← targetANF_targetBasis_homogeneous, ← targetANF_targetBasis_homogeneous]
  change (targetANF (targetBasis 5) * targetANF (targetBasis t)).coeff
    ⟨quarticProbeSet u⟩ = _
  rw [coeff_targetANF_mul_targetANF]
  simp only [targetBasis, Pi.basisFun_apply]
  revert t u
  decide +kernel

private theorem quarticProbe_Mul_mul_six :
    ∀ t : Fin 7,
      quarticProbeANF (Mul 4 6 * Mul 4 t) =
        quarticWedgeProbe (targetTwo (targetBasis 6))
          (targetTwo (targetBasis t)) := by
  intro t
  funext u
  rw [← targetANF_targetBasis_homogeneous, ← targetANF_targetBasis_homogeneous]
  change (targetANF (targetBasis 6) * targetANF (targetBasis t)).coeff
    ⟨quarticProbeSet u⟩ = _
  rw [coeff_targetANF_mul_targetANF]
  simp only [targetBasis, Pi.basisFun_apply]
  revert t u
  decide +kernel

private theorem quarticProbe_Mul_mul (s t : Fin 7) :
    quarticProbeANF (Mul 4 s * Mul 4 t) =
      quarticWedgeProbe (targetTwo (targetBasis s))
        (targetTwo (targetBasis t)) := by
  fin_cases s
  · exact quarticProbe_Mul_mul_zero t
  · exact quarticProbe_Mul_mul_one t
  · exact quarticProbe_Mul_mul_two t
  · exact quarticProbe_Mul_mul_three t
  · exact quarticProbe_Mul_mul_four t
  · exact quarticProbe_Mul_mul_five t
  · exact quarticProbe_Mul_mul_six t

/-- The exterior product of two two-forms as a bilinear map. -/
def wedgeTwoBilinear : TwoForm →ₗ[F₂] TwoForm →ₗ[F₂] FourForm where
  toFun q :=
    { toFun := fun r => wedgeTwo q r
      map_add' := wedgeTwo_add_right q
      map_smul' := by
        intro a r
        funext i j k l
        simp only [wedgeTwo, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  map_add' q r := by
    apply LinearMap.ext
    intro s
    change wedgeTwo (q + r) s = wedgeTwo q s + wedgeTwo r s
    exact wedgeTwo_add_left q r s
  map_smul' a q := by
    apply LinearMap.ext
    intro r
    funext i j k l
    change wedgeTwo (a • q) r i j k l =
      (a • wedgeTwo q r) i j k l
    simp only [wedgeTwo, Pi.smul_apply, smul_eq_mul]
    ring

/-- The three quartic wedge probes as a bilinear map. -/
def quarticWedgeProbeBilinear :
    TwoForm →ₗ[F₂] TwoForm →ₗ[F₂] (Fin 3 → F₂) where
  toFun q :=
    { toFun := fun r => quarticWedgeProbe q r
      map_add' := by
        intro r s
        funext t
        fin_cases t <;> simp [quarticWedgeProbe, wedgeTwo] <;> ring
      map_smul' := by
        intro a r
        funext t
        fin_cases t <;>
          simp [quarticWedgeProbe, wedgeTwo, RingHom.id_apply] <;> ring }
  map_add' q r := by
    apply LinearMap.ext
    intro s
    funext t
    fin_cases t <;> simp [quarticWedgeProbe, wedgeTwo] <;> ring
  map_smul' a q := by
    apply LinearMap.ext
    intro r
    change quarticWedgeProbe (a • q) r = a • quarticWedgeProbe q r
    funext t
    fin_cases t <;>
      simp [quarticWedgeProbe, wedgeTwo] <;> ring

private theorem targetTwo_eq_sum_basis (c : TargetCoeff) :
    targetTwo c = ∑ s : Fin 7, c s • targetTwo (targetBasis s) := by
  change targetTwoLinear c =
    ∑ s : Fin 7, c s • targetTwoLinear (targetBasis s)
  have h := congrArg targetTwoLinear (targetBasis_reconstruction c)
  simpa only [map_sum, map_smul] using h.symm

private theorem quarticProbe_Mul_mul_targetANF
    (s : Fin 7) (d : TargetCoeff) :
    quarticProbeANF (Mul 4 s * targetANF d) =
      quarticWedgeProbe (targetTwo (targetBasis s)) (targetTwo d) := by
  rw [targetANF]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, quarticProbe_Mul_mul]
  change (∑ t : Fin 7, d t •
      quarticWedgeProbe (targetTwo (targetBasis s))
        (targetTwo (targetBasis t))) =
    quarticWedgeProbeBilinear (targetTwo (targetBasis s)) (targetTwo d)
  rw [targetTwo_eq_sum_basis d]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro t _
  rfl

theorem quarticProbe_targetANF_mul_targetANF
    (c d : TargetCoeff) :
    quarticProbeANF (targetANF c * targetANF d) =
      quarticWedgeProbe (targetTwo c) (targetTwo d) := by
  change quarticProbeANF
      ((∑ s : Fin 7, c s • Mul 4 s) * targetANF d) = _
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul]
  calc
    (∑ s : Fin 7, c s •
        quarticProbeANF (Mul 4 s * targetANF d)) =
        ∑ s : Fin 7, c s •
          quarticWedgeProbe (targetTwo (targetBasis s)) (targetTwo d) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [quarticProbe_Mul_mul_targetANF]
    _ = quarticWedgeProbeBilinear (targetTwo c) (targetTwo d) := by
      rw [targetTwo_eq_sum_basis c]
      simp only [map_sum, map_smul]
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
      apply Finset.sum_congr rfl
      intro s _
      rfl

theorem quarticProbe_rational_mul_rational
    (α β : Fin 3 → F₂) :
    quarticProbeANF (rationalANF α * rationalANF β) =
      quarticWedgeProbe (rationalTwo α) (rationalTwo β) := by
  change quarticProbeANF
      (targetANF (rationalCoeffRep α) *
        targetANF (rationalCoeffRep β)) = _
  rw [quarticProbe_targetANF_mul_targetANF,
    targetTwo_rationalCoeffRep, targetTwo_rationalCoeffRep]

theorem anfThreeProjection_eq_zero_of_mem_targetAmbient
    {p : ANF 8} (hp : p ∈ targetAmbient 8 (mulTarget 4)) :
    anfThreeProjection p = 0 := by
  funext i j k
  by_cases hcard : ({i, j, k} : Finset (Fin 8)).card = 3
  · change (if ({i, j, k} : Finset (Fin 8)).card = 3 then
        p.coeff ⟨{i, j, k}⟩ else 0) = 0
    rw [ite_eq_left hcard]
    exact targetAmbient_coeff_zero_of_three_le hp ⟨{i, j, k}⟩
      (by simp [hcard])
  · simp [anfThreeProjection, hcard]

theorem quarticProbeANF_eq_zero_of_mem_targetAmbient
    {p : ANF 8} (hp : p ∈ targetAmbient 8 (mulTarget 4)) :
    quarticProbeANF p = 0 := by
  funext t
  change p.coeff ⟨quarticProbeSet t⟩ = 0
  apply targetAmbient_coeff_zero_of_three_le hp
  have hcard : (quarticProbeSet t).card = 4 := by
    fin_cases t <;> decide
  simp [hcard]

/-- The three recorded quartic coordinates are already enough to detect
dependence inside the rational-place three-space. -/
theorem rational_probe_zero_dependent (α β : Fin 3 → F₂)
    (h : quarticWedgeProbe (rationalTwo α) (rationalTwo β) = 0) :
    α = 0 ∨ β = 0 ∨ α = β := by
  have hp0 := congrFun h 0
  have hp1 := congrFun h 1
  have hp2 := congrFun h 2
  simp only [quarticWedgeProbe, Matrix.cons_val_zero, Pi.zero_apply] at hp0
  simp only [quarticWedgeProbe, Matrix.cons_val_one, Pi.zero_apply] at hp1
  simp only [quarticWedgeProbe, Matrix.cons_val_two, Pi.zero_apply] at hp2
  have h01 : α 0 * β 1 + α 1 * β 0 = 0 := by
    rw [← rational_wedge_coord_01 α β]
    exact hp0
  have h12 : α 1 * β 2 + α 2 * β 1 = 0 := by
    rw [← rational_wedge_coord_12 α β]
    exact hp1
  have h02 : α 0 * β 2 + α 2 * β 0 = 0 := by
    have hm := (rational_wedge_coord_mid α β).symm.trans hp2
    rw [h01, h12] at hm
    simpa using hm
  apply dependent_of_vectorWedge_zero α β
  intro i j
  fin_cases i <;> fin_cases j
  · exact CharTwo.add_self_eq_zero _
  · exact h01
  · exact h02
  · rw [add_comm]
    exact h01
  · exact CharTwo.add_self_eq_zero _
  · exact h12
  · rw [add_comm]
    exact h02
  · rw [add_comm]
    exact h12
  · exact CharTwo.add_self_eq_zero _

theorem rational_wedge_zero_of_probe_zero (α β : Fin 3 → F₂)
    (h : quarticWedgeProbe (rationalTwo α) (rationalTwo β) = 0) :
    wedgeTwo (rationalTwo α) (rationalTwo β) = 0 := by
  rcases rational_probe_zero_dependent α β h with hα | hβ | hαβ
  · subst α
    rw [rationalTwo_zero]
    funext i j k l
    simp [wedgeTwo]
  · subst β
    rw [rationalTwo_zero]
    funext i j k l
    simp [wedgeTwo]
  · subst β
    exact wedgeTwo_self _

end

end N4
end UnrestrictedBooleanMul
