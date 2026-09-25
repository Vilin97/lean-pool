/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Cage.Connectivity
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.CorvajaZannierEscape
public import LeanPool.MarkoffModP.BGS.Dynamics.StrictMeasureEscape

/-!
# Iterating the middle-game escape to the cage
-/

@[expose] public section

namespace BGS.Markoff

open Filter

noncomputable section

private theorem three_ne_zero_zmod_of_prime_ne_three
    (p : ℕ) [Fact p.Prime] (hpThree : p ≠ 3) : (3 : ZMod p) ≠ 0 := by
  intro hzero
  have hpDvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hzero
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hpDvd with hpOne | hpEq
  · exact (Fact.out : p.Prime).ne_one hpOne
  · exact hpThree hpEq

/-- Maximum of the three coordinate rotation orders. -/
def maximalCoordinateRotationOrder {R : Type*} [CommRing R]
    (x : NormalizedPoint R) : ℕ :=
  max (rotationOrder x.u1) (max (rotationOrder x.u2) (rotationOrder x.u3))

theorem rotationOrder_first_le_maximalCoordinateRotationOrder
    {R : Type*} [CommRing R] (x : NormalizedPoint R) :
    rotationOrder x.u1 ≤ maximalCoordinateRotationOrder x := by
  simp [maximalCoordinateRotationOrder]

theorem rotationOrder_second_le_maximalCoordinateRotationOrder
    {R : Type*} [CommRing R] (x : NormalizedPoint R) :
    rotationOrder x.u2 ≤ maximalCoordinateRotationOrder x := by
  simp [maximalCoordinateRotationOrder]

theorem rotationOrder_third_le_maximalCoordinateRotationOrder
    {R : Type*} [CommRing R] (x : NormalizedPoint R) :
    rotationOrder x.u3 ≤ maximalCoordinateRotationOrder x := by
  simp [maximalCoordinateRotationOrder]

/-- A coordinate permutation puts a coordinate of maximum rotation order first. -/
theorem exists_sameNormalizedComponent_firstRotation_eq_maximal
    {R : Type*} [CommRing R] [Invertible (3 : R)]
    (x : NormalizedMarkoffSurface R) :
    ∃ y : NormalizedMarkoffSurface R,
      SameNormalizedComponent x y ∧
        rotationOrder y.1.u1 = maximalCoordinateRotationOrder x.1 := by
  by_cases hfirst : rotationOrder x.1.u2 ≤ rotationOrder x.1.u1 ∧
      rotationOrder x.1.u3 ≤ rotationOrder x.1.u1
  · refine ⟨x, sameNormalizedComponent_refl x, ?_⟩
    simp [maximalCoordinateRotationOrder, hfirst.1, hfirst.2]
  · by_cases hsecond : rotationOrder x.1.u1 ≤ rotationOrder x.1.u2 ∧
        rotationOrder x.1.u3 ≤ rotationOrder x.1.u2
    · let y := normalizedSwap12Surface x
      refine ⟨y, sameNormalizedComponent_swap12Surface x, ?_⟩
      simp [y, normalizedSwap12, maximalCoordinateRotationOrder,
        hsecond.1, hsecond.2]
    · have hthirdFirst : rotationOrder x.1.u1 ≤ rotationOrder x.1.u3 := by omega
      have hthirdSecond : rotationOrder x.1.u2 ≤ rotationOrder x.1.u3 := by omega
      let y := normalizedSwap12Surface (normalizedSwap23Surface x)
      have hcomp := sameNormalizedComponent_trans
        (sameNormalizedComponent_swap23Surface x)
        (sameNormalizedComponent_swap12Surface (normalizedSwap23Surface x))
      refine ⟨y, hcomp, ?_⟩
      simp [y, normalizedSwap12, normalizedSwap23, maximalCoordinateRotationOrder,
        hthirdFirst, hthirdSecond]

/-- One genuine middle-game step strictly increases the maximum coordinate order. -/
theorem exists_sameNormalizedComponent_maximalOrder_increase_of_middleRange
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    [Fintype (quadraticFiniteField p)] (hpTwo : p ≠ 2)
    {δ : ℝ} (hδ : 0 < δ) (hδQuarter : δ ≤ (1 : ℝ) / 4)
    (hfour : (4 : ℝ) < (p : ℝ) ^ δ)
    (hsize : ∀ currentOrder : ℕ,
      (p : ℝ) ^ δ < currentOrder →
      (currentOrder : ℝ) < (p : ℝ) ^ (1 - δ) →
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 < currentOrder ∧
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) * currentOrder < p)
    (hBound : WeightedTraceTorsionIntersectionBound p (quadraticFiniteField p))
    (x : NormalizedMarkoffSurface (ZMod p))
    (hlower : (p : ℝ) ^ δ < maximalCoordinateRotationOrder x.1)
    (hbelow : (maximalCoordinateRotationOrder x.1 : ℝ) <
      (p : ℝ) ^ ((1 : ℝ) / 2 + δ)) :
    ∃ y : NormalizedMarkoffSurface (ZMod p),
      SameNormalizedComponent x y ∧
        maximalCoordinateRotationOrder x.1 < maximalCoordinateRotationOrder y.1 := by
  obtain ⟨x', hxx', hx'Order⟩ :=
    exists_sameNormalizedComponent_firstRotation_eq_maximal x
  have hpOne : (1 : ℝ) ≤ p := by
    exact_mod_cast (show 1 ≤ p by exact (Fact.out : p.Prime).one_le)
  have hx'Lower : (p : ℝ) ^ δ < rotationOrder x'.1.u1 := by
    simpa [hx'Order] using hlower
  have hx'Below : (rotationOrder x'.1.u1 : ℝ) <
      (p : ℝ) ^ ((1 : ℝ) / 2 + δ) := by
    simpa [hx'Order] using hbelow
  have hx'0 : x'.1.u1 ≠ 0 := by
    intro hzero
    have hle := rotationOrder_zero_le_four p
    rw [hzero] at hx'Lower
    have : (rotationOrder (0 : ZMod p) : ℝ) ≤ 4 := by exact_mod_cast hle
    linarith
  have hx'Nonparabolic : x'.1.u1 ^ 2 ≠ 4 := by
    intro hparabolic
    have hcases : x'.1.u1 = 2 ∨ x'.1.u1 = -2 := by
      apply (sq_eq_sq_iff_eq_or_eq_neg).mp
      calc
        x'.1.u1 ^ 2 = 4 := hparabolic
        _ = (2 : ZMod p) ^ 2 := by norm_num
    have hexponentLe : (1 : ℝ) / 2 + δ ≤ 1 := by linarith
    have hrpowLe : (p : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ (p : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hpOne hexponentLe
    rcases hcases with htwo | hnegTwo
    · rw [htwo, rotationOrder_two] at hx'Below
      linarith
    · rw [hnegTwo, rotationOrder_neg_two p hpTwo] at hx'Below
      have htwoP : (((2 * p : ℕ) : ℝ)) = 2 * (p : ℝ) := by norm_num
      rw [htwoP] at hx'Below
      have hpPos : (0 : ℝ) < p := by positivity
      linarith
  have hupperExponent : (1 : ℝ) / 2 + δ ≤ 1 - δ := by linarith
  have hupperPower : (p : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ (p : ℝ) ^ (1 - δ) :=
    Real.rpow_le_rpow_of_exponent_le hpOne hupperExponent
  have hx'Upper : (rotationOrder x'.1.u1 : ℝ) < (p : ℝ) ^ (1 - δ) :=
    hx'Below.trans_le hupperPower
  obtain ⟨hcube, hlinear⟩ := hsize (rotationOrder x'.1.u1) hx'Lower hx'Upper
  obtain ⟨n, hnIncrease⟩ :=
    exists_iterate_with_larger_secondRotationOrder_of_weightedTraceBound
      p hpTwo δ (by linarith) x'.1 x'.property
      hx'0 hx'Nonparabolic hx'Below hcube hlinear hBound
  let y := (normalizedRotate1Surface^[n]) x'
  have hcoe : y.1 = (normalizedRotate1^[n]) x'.1 :=
    coe_iterate_normalizedRotate1Surface x' n
  refine ⟨y, sameNormalizedComponent_trans hxx'
    (sameNormalizedComponent_iterate_normalizedRotate1Surface x' n), ?_⟩
  rw [← hx'Order]
  exact hnIncrease.trans_le <| by
    have hmeasureEq : maximalCoordinateRotationOrder y.1 =
        maximalCoordinateRotationOrder ((normalizedRotate1^[n]) x'.1) :=
      congrArg maximalCoordinateRotationOrder hcoe
    calc
      rotationOrder ((normalizedRotate1^[n]) x'.1).u2 ≤
          maximalCoordinateRotationOrder ((normalizedRotate1^[n]) x'.1) :=
        rotationOrder_second_le_maximalCoordinateRotationOrder _
      _ = maximalCoordinateRotationOrder y.1 := hmeasureEq.symm

/-- One middle-game step strictly increases the maximum coordinate order when the two
Corvaja--Zannier size inequalities are supplied directly.  Unlike
`exists_sameNormalizedComponent_maximalOrder_increase_of_middleRange`, this interface does not
require a fixed lower power threshold for the current order. -/
theorem exists_sameNormalizedComponent_maximalOrder_increase_of_directBounds
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    [Fintype (quadraticFiniteField p)] (hpTwo : p ≠ 2)
    {δ : ℝ} (hδ : δ ≤ (1 : ℝ) / 2)
    (hBound : WeightedTraceTorsionIntersectionBound p (quadraticFiniteField p))
    (x : NormalizedMarkoffSurface (ZMod p))
    (hbelow : (maximalCoordinateRotationOrder x.1 : ℝ) <
      (p : ℝ) ^ ((1 : ℝ) / 2 + δ))
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 <
        maximalCoordinateRotationOrder x.1)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card) *
        maximalCoordinateRotationOrder x.1 < p) :
    ∃ y : NormalizedMarkoffSurface (ZMod p),
      SameNormalizedComponent x y ∧
        maximalCoordinateRotationOrder x.1 < maximalCoordinateRotationOrder y.1 := by
  obtain ⟨x', hxx', hx'Order⟩ :=
    exists_sameNormalizedComponent_firstRotation_eq_maximal x
  have hx'Cube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 <
        rotationOrder x'.1.u1 := by
    simpa [hx'Order] using hcube
  have hx'Linear :
      corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card) *
        rotationOrder x'.1.u1 < p := by
    simpa [hx'Order] using hlinear
  have hsumPos :
      0 < (p - 1).divisors.card + (p + 1).divisors.card := by
    have hpPlus : p + 1 ≠ 0 := by omega
    have hone : 1 ∈ (p + 1).divisors := Nat.one_mem_divisors.mpr hpPlus
    have hcard : 0 < (p + 1).divisors.card := Finset.card_pos.mpr ⟨1, hone⟩
    omega
  have hbase :
      4 < (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 := by
    have hcoeff : corvajaZannierCorollaryTwoSafeCoefficient ≤
        corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card) := by
      simp only [corvajaZannierCorollaryTwoSafeCoefficient]
      nlinarith
    calc
      4 < corvajaZannierCorollaryTwoSafeCoefficient ^ 3 := by
        norm_num [corvajaZannierCorollaryTwoSafeCoefficient]
      _ ≤ (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 :=
        Nat.pow_le_pow_left hcoeff 3
  have hx'AboveFour : 4 < rotationOrder x'.1.u1 := hbase.trans hx'Cube
  have hx'Below : (rotationOrder x'.1.u1 : ℝ) <
      (p : ℝ) ^ ((1 : ℝ) / 2 + δ) := by
    simpa [hx'Order] using hbelow
  have hx'0 : x'.1.u1 ≠ 0 := by
    intro hzero
    have hle := rotationOrder_zero_le_four p
    rw [hzero] at hx'AboveFour
    omega
  have hx'Nonparabolic : x'.1.u1 ^ 2 ≠ 4 := by
    intro hparabolic
    have hcases : x'.1.u1 = 2 ∨ x'.1.u1 = -2 := by
      apply (sq_eq_sq_iff_eq_or_eq_neg).mp
      calc
        x'.1.u1 ^ 2 = 4 := hparabolic
        _ = (2 : ZMod p) ^ 2 := by norm_num
    have hpOne : (1 : ℝ) ≤ p := by
      exact_mod_cast (show 1 ≤ p by exact (Fact.out : p.Prime).one_le)
    have hexponentLe : (1 : ℝ) / 2 + δ ≤ 1 := by linarith
    have hrpowLe : (p : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ (p : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hpOne hexponentLe
    rcases hcases with htwo | hnegTwo
    · rw [htwo, rotationOrder_two] at hx'Below
      linarith
    · rw [hnegTwo, rotationOrder_neg_two p hpTwo] at hx'Below
      have htwoP : (((2 * p : ℕ) : ℝ)) = 2 * (p : ℝ) := by norm_num
      rw [htwoP] at hx'Below
      have hpPos : (0 : ℝ) < p := by positivity
      linarith
  obtain ⟨n, hnIncrease⟩ :=
    exists_iterate_with_larger_secondRotationOrder_of_weightedTraceBound
      p hpTwo δ hδ x'.1 x'.property hx'0 hx'Nonparabolic hx'Below
      hx'Cube hx'Linear hBound
  let y := (normalizedRotate1Surface^[n]) x'
  have hcoe : y.1 = (normalizedRotate1^[n]) x'.1 :=
    coe_iterate_normalizedRotate1Surface x' n
  refine ⟨y, sameNormalizedComponent_trans hxx'
    (sameNormalizedComponent_iterate_normalizedRotate1Surface x' n), ?_⟩
  rw [← hx'Order]
  exact hnIncrease.trans_le <| by
    have hmeasureEq : maximalCoordinateRotationOrder y.1 =
        maximalCoordinateRotationOrder ((normalizedRotate1^[n]) x'.1) :=
      congrArg maximalCoordinateRotationOrder hcoe
    calc
      rotationOrder ((normalizedRotate1^[n]) x'.1).u2 ≤
          maximalCoordinateRotationOrder ((normalizedRotate1^[n]) x'.1) :=
        rotationOrder_second_le_maximalCoordinateRotationOrder _
      _ = maximalCoordinateRotationOrder y.1 := hmeasureEq.symm

/-- Repeated weighted-trace escape steps reach the real endgame threshold. -/
theorem exists_threshold_middleGame_reaches_endgame
    (hBound : ∀ (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)],
      WeightedTraceTorsionIntersectionBound p (quadraticFiniteField p))
    {δ : ℝ} (hδ : 0 < δ) (hδQuarter : δ ≤ (1 : ℝ) / 4) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] → ∀ hpThree : p ≠ 3,
      letI : Invertible (3 : ZMod p) :=
        invertibleOfNonzero (three_ne_zero_zmod_of_prime_ne_three p hpThree)
      ∀ x : NormalizedMarkoffSurface (ZMod p),
        (p : ℝ) ^ δ < maximalCoordinateRotationOrder x.1 →
        ∃ y : NormalizedMarkoffSurface (ZMod p),
          SameNormalizedComponent x y ∧
            (p : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤
              maximalCoordinateRotationOrder y.1 := by
  obtain ⟨sizeThreshold, hsizeThreshold⟩ :=
    eventually_atTop.mp (eventually_middleGame_corvajaZannier_sizeBounds hδ)
  have hfourEventually :
      ∀ᶠ p : ℕ in atTop, (4 : ℝ) < (p : ℝ) ^ δ := by
    simpa using
      (eventually_const_mul_rpow_lt_rpow
        (C := (4 : ℝ)) (a := (0 : ℝ)) (b := δ) hδ)
  obtain ⟨fourThreshold, hfourThreshold⟩ := eventually_atTop.mp hfourEventually
  refine ⟨max (max sizeThreshold fourThreshold) 7, ?_⟩
  intro p hp _ hpThree
  let : Invertible (3 : ZMod p) :=
    invertibleOfNonzero
      (three_ne_zero_zmod_of_prime_ne_three p hpThree)
  let : Fintype (quadraticFiniteField p) := Fintype.ofFinite _
  intro x hxLower
  have hpSize : sizeThreshold ≤ p :=
    (le_max_left sizeThreshold fourThreshold).trans
      ((le_max_left (max sizeThreshold fourThreshold) 7).trans hp)
  have hpFour : fourThreshold ≤ p :=
    (le_max_right sizeThreshold fourThreshold).trans
      ((le_max_left (max sizeThreshold fourThreshold) 7).trans hp)
  have hsize := hsizeThreshold p hpSize
  have hfour := hfourThreshold p hpFour
  let endgameReal : ℝ := (p : ℝ) ^ ((1 : ℝ) / 2 + δ)
  let target : ℕ := Nat.ceil endgameReal
  let MiddleState := {q : NormalizedMarkoffSurface (ZMod p) //
    (p : ℝ) ^ δ < maximalCoordinateRotationOrder q.1}
  let start : MiddleState := ⟨x, hxLower⟩
  let r : MiddleState → MiddleState → Prop := fun q z =>
    SameNormalizedComponent q.1 z.1
  let measure : MiddleState → ℕ := fun q => maximalCoordinateRotationOrder q.1.1
  have hstep : ∀ q : MiddleState, measure q < target →
      ∃ z : MiddleState, r q z ∧ measure q < measure z := by
    intro q hqTarget
    have hqBelow : (maximalCoordinateRotationOrder q.1.1 : ℝ) < endgameReal := by
      exact (Nat.lt_ceil.mp hqTarget)
    obtain ⟨z, hqz, hincrease⟩ :=
      exists_sameNormalizedComponent_maximalOrder_increase_of_middleRange
        p (by omega) hδ hδQuarter hfour hsize (hBound p) q.1 q.2 hqBelow
    exact ⟨⟨z, q.2.trans_le (by exact_mod_cast hincrease.le)⟩, hqz, hincrease⟩
  obtain ⟨finish, hchain, htarget⟩ :=
    BGS.exists_reflTransGen_measure_ge r measure target hstep start
  have hcomponent : SameNormalizedComponent x finish.1 := by
    have hchainComponent : ∀ {q z : MiddleState}, Relation.ReflTransGen r q z →
        SameNormalizedComponent q.1 z.1 := by
      intro q z hqz
      induction hqz with
      | refl => exact sameNormalizedComponent_refl q.1
      | tail hqa hab ih =>
          exact sameNormalizedComponent_trans ih hab
    exact hchainComponent hchain
  have hendgame : endgameReal ≤ (maximalCoordinateRotationOrder finish.1.1 : ℝ) := by
    exact (Nat.ceil_le.mp htarget)
  exact ⟨finish.1, hcomponent, hendgame⟩

/-- The weighted-trace middle-game bound, followed by the completed endgame,
lands every point above the opening threshold in the selected split cage. -/
theorem exists_threshold_middleGame_to_splitCage
    (hBound : ∀ (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)],
      WeightedTraceTorsionIntersectionBound p (quadraticFiniteField p))
    (splitCoefficient : ℕ)
    (hSplitWeil : WeightedSplitTraceWeilBoundAssumption splitCoefficient)
    (nonsplitCoefficient : ℕ)
    (hNonsplitWeil : SeededNonsplitTraceWeilBoundAssumption nonsplitCoefficient)
    {δ : ℝ} (hδ : 0 < δ) (hδQuarter : δ ≤ (1 : ℝ) / 4) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] → ∀ hpThree : p ≠ 3,
      letI : Invertible (3 : ZMod p) :=
        invertibleOfNonzero (three_ne_zero_zmod_of_prime_ne_three p hpThree)
      ∀ x : NormalizedMarkoffSurface (ZMod p),
        (p : ℝ) ^ δ < maximalCoordinateRotationOrder x.1 →
        ∃ y : NormalizedMarkoffSurface (ZMod p),
          SameNormalizedComponent x y ∧ IsInSplitCage p y := by
  obtain ⟨middleThreshold, hmiddle⟩ :=
    exists_threshold_middleGame_reaches_endgame hBound hδ hδQuarter
  obtain ⟨endgameThreshold, hendgame⟩ :=
    exists_threshold_largeOrder_to_splitCage splitCoefficient hSplitWeil
      nonsplitCoefficient hNonsplitWeil hδ
  refine ⟨max middleThreshold endgameThreshold, ?_⟩
  intro p hp _ hpThree
  let : Invertible (3 : ZMod p) :=
    invertibleOfNonzero (three_ne_zero_zmod_of_prime_ne_three p hpThree)
  intro x hxLarge
  have hpMiddle : middleThreshold ≤ p := (le_max_left _ _).trans hp
  have hpEndgame : endgameThreshold ≤ p := (le_max_right _ _).trans hp
  obtain ⟨z, hxz, hzLarge⟩ := hmiddle p hpMiddle hpThree x hxLarge
  obtain ⟨z', hzz', hz'First⟩ :=
    exists_sameNormalizedComponent_firstRotation_eq_maximal z
  have hz'Large : (p : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ rotationOrder z'.1.u1 := by
    simpa [hz'First] using hzLarge
  obtain ⟨y, hz'y, hyCage⟩ := hendgame p hpEndgame hpThree z' (Or.inl hz'Large)
  exact ⟨y, sameNormalizedComponent_trans hxz
    (sameNormalizedComponent_trans hzz' hz'y), hyCage⟩

end

end BGS.Markoff
