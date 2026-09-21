/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.MoveWiring
import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.ParabolicEscape
import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.RightSubgroups
import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.WeightedTraceEquation

/-!
# The nonparabolic middle-game order-escape step

This module composes the weighted finite escape, the concrete roots-of-unity right subgroups,
the split/nonsplit trace classification, and the weighted coset coordinate identity.  The only
deep input is the weighted Corvaja--Zannier cardinal estimate on the actual solution finsets.
-/

namespace BGS.Markoff

/-- Scalar extension commutes with every iterate of the normalized rotation. -/
theorem algebraMapNormalizedPoint_iterate_normalizedRotate1
    (p n : ℕ) [Fact p.Prime] (x : NormalizedPoint (ZMod p)) :
    algebraMapNormalizedPoint p ((normalizedRotate1^[n]) x) =
      (normalizedRotate1^[n]) (algebraMapNormalizedPoint p x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        algebraMapNormalizedPoint_normalizedRotate1, ih]

/-- A nonparabolic trace whose rotation order is at most `currentOrder` has a candidate order
dividing `p - 1` or `p + 1`. -/
theorem rotationOrder_mem_middleGameCandidateOrders_of_nonparabolic
    (p currentOrder : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (t : ZMod p) (hnonparabolic : t ^ 2 ≠ 4)
    (hsmall : rotationOrder t ≤ currentOrder) :
    rotationOrder t ∈ middleGameCandidateOrders p currentOrder := by
  have hpMinus : p - 1 ≠ 0 := by
    have hpLower := (Fact.out : p.Prime).two_le
    omega
  rcases exists_split_or_quadraticNormOneTrace p hpTwo t hnonparabolic with
    ⟨w, htrace, hw⟩ | ⟨w, htrace, hw⟩
  · have horder : orderOf w = rotationOrder t := by
      rw [← rotationOrder_splitTorusTrace w hw, htrace]
    have hdvd : rotationOrder t ∣ p - 1 := by
      rw [← horder]
      simpa [ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : p.Prime)] using
        orderOf_dvd_natCard w
    exact mem_middleGameCandidateOrders_iff.mpr
      ⟨hsmall, Or.inl ⟨hdvd, hpMinus⟩⟩
  · have horder : orderOf w = rotationOrder t := by
      rw [← rotationOrder_quadraticNormOneTrace p w hw, htrace]
    have hdvd : rotationOrder t ∣ p + 1 := by
      rw [← horder, ← quadraticNormOneTorus_natCard p]
      exact orderOf_dvd_natCard w
    exact mem_middleGameCandidateOrders_iff.mpr ⟨hsmall, Or.inr hdvd⟩

/-- The split-fiber invariant is never one in odd characteristic. -/
theorem splitFiberProduct_ne_one_of_four_ne_zero
    {E : Type*} [Field E] (w : Eˣ) (hfour : (4 : E) ≠ 0) :
    splitFiberProduct w ≠ 1 := by
  intro hone
  by_cases hdenom : splitTorusTrace w ^ 2 - 4 = 0
  · simp [splitFiberProduct, hdenom] at hone
  · rw [splitFiberProduct] at hone
    field_simp [hdenom] at hone
    exact hfour (by linear_combination hone)

/-- Complete nonparabolic order escape from a diagonalized presentation of the current fiber.

The numeric hypotheses are the already-isolated finite middle-game range.  `hCZ` is the sole
deep premise: the weighted Corvaja--Zannier estimate for the actual cyclic left subgroup and the
canonical right subgroups. -/
theorem exists_iterate_with_larger_secondRotationOrder_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)] (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (x : NormalizedPoint (ZMod p))
    (w s : (quadraticFiniteField p)ˣ)
    (hw : (w : quadraticFiniteField p) ^ 2 ≠ 1)
    (hpoint : algebraMapNormalizedPoint p x = splitFiberPoint w s)
    (hbelowEndgame :
      (rotationOrder x.u1 : ℝ) < (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 <
        rotationOrder x.u1)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) *
          rotationOrder x.u1 < p)
    (hCZ :
      (s : quadraticFiniteField p) *
          (splitFiberProduct w * ((s⁻¹ : (quadraticFiniteField p)ˣ) :
            quadraticFiniteField p)) ≠ 1 →
      ∀ d ∈ middleGameCandidateOrders p (rotationOrder x.u1),
        ((weightedTraceEquationSolutions
          (s : quadraticFiniteField p)
          (splitFiberProduct w * ((s⁻¹ : (quadraticFiniteField p)ˣ) :
            quadraticFiniteField p))
          (Subgroup.zpowers w) (middleGameRightSubgroup p d)).card : ℝ) ≤
          corvajaZannierTraceUpperBound p (rotationOrder x.u1)
            (Nat.card (middleGameRightSubgroup p d))) :
    ∃ n : ℕ,
      rotationOrder x.u1 < rotationOrder ((normalizedRotate1^[n]) x).u2 := by
  let alpha : quadraticFiniteField p := s
  let beta : quadraticFiniteField p :=
    splitFiberProduct w * ((s⁻¹ : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)
  let H₁ : Subgroup (quadraticFiniteField p)ˣ := Subgroup.zpowers w
  have htrace :
      algebraMap (ZMod p) (quadraticFiniteField p) x.u1 = splitTorusTrace w :=
    congrArg NormalizedPoint.u1 hpoint
  have horder : orderOf w = rotationOrder x.u1 := by
    rw [← rotationOrder_eq_orderOf_extensionEigenvalue x.u1 w hw htrace]
  have hleftCard : Nat.card H₁ = rotationOrder x.u1 := by
    rw [Nat.card_zpowers, horder]
  have hfour : (4 : quadraticFiniteField p) ≠ 0 := by
    exact (map_ne_zero (algebraMap (ZMod p) (quadraticFiniteField p))).mpr (by
      intro hzero
      have hpDvd : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp hzero
      have hpPrime := (Fact.out : p.Prime)
      have hpDvdPow : p ∣ 2 ^ 2 := by simpa using hpDvd
      have hpDvdTwo : p ∣ 2 := hpPrime.dvd_of_dvd_pow hpDvdPow
      have hpLeTwo : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvdTwo
      exact hpTwo (Nat.le_antisymm hpLeTwo hpPrime.two_le))
  have hnondegenerate : alpha * beta ≠ 1 := by
    rw [show alpha * beta = splitFiberProduct w by
      exact splitFiberOrbit_weights_mul w s]
    exact splitFiberProduct_ne_one_of_four_ne_zero w hfour
  have hcurrentOrder : 0 < Nat.card H₁ := by
    rw [hleftCard]
    exact rotationOrder_pos x.u1
  have hrightOrder :
      ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
        Nat.card (middleGameRightSubgroup p d) = d := by
    intro d hd
    exact middleGameRightSubgroup_natCard p (Nat.card H₁) d hd
  have hCZ' : alpha * beta ≠ 1 →
      ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
        ((weightedTraceEquationSolutions alpha beta H₁
          (middleGameRightSubgroup p d)).card : ℝ) ≤
          corvajaZannierTraceUpperBound p (Nat.card H₁)
            (Nat.card (middleGameRightSubgroup p d)) := by
    intro _ d hd
    simpa [alpha, beta, H₁, hleftCard] using
      hCZ hnondegenerate d (by simpa [hleftCard] using hd)
  obtain ⟨h, hEscapes⟩ :=
    exists_left_element_escaping_of_weightedCorvajaZannierEstimate_and_sizeBounds
      p alpha beta H₁ (fun d ↦ middleGameRightSubgroup p d)
      hrightOrder hCZ' hnondegenerate
      hcurrentOrder (by simpa [hleftCard] using hcube) (by simpa [hleftCard] using hlinear)
  obtain ⟨n, hn⟩ := exists_iterate_splitFiberPoint_eq_mul_zpowers w s h
  refine ⟨n, ?_⟩
  let y := (normalizedRotate1^[n]) x
  have hyPoint : algebraMapNormalizedPoint p y =
      splitFiberPoint w (s * (h : (quadraticFiniteField p)ˣ)) := by
    calc
      algebraMapNormalizedPoint p y =
          (normalizedRotate1^[n]) (algebraMapNormalizedPoint p x) :=
        algebraMapNormalizedPoint_iterate_normalizedRotate1 p n x
      _ = (normalizedRotate1^[n]) (splitFiberPoint w s) := by rw [hpoint]
      _ = splitFiberPoint w (s * (h : (quadraticFiniteField p)ˣ)) := hn
  apply lt_of_not_ge
  intro hsmall
  have hnonparabolicY : y.u2 ^ 2 ≠ 4 := by
    intro hparabolic
    have hcases := (normalizedTrace_sq_eq_four_iff_parabolic p y.u2).mp hparabolic
    have hthreshold := endgamePowerThreshold_le_rotationOrder_of_parabolicTrace
      p hpTwo delta hdelta y.u2 hcases
    have hsmallReal : (rotationOrder y.u2 : ℝ) ≤ (rotationOrder x.u1 : ℝ) := by
      exact_mod_cast hsmall
    exact (not_le_of_gt hbelowEndgame) (hthreshold.trans hsmallReal)
  have hd := rotationOrder_mem_middleGameCandidateOrders_of_nonparabolic
    p (rotationOrder x.u1) hpTwo y.u2 hnonparabolicY hsmall
  obtain ⟨h₂, h₂trace⟩ :=
    exists_middleGameRightSubgroup_trace_of_nonparabolic_rotationOrder
      p (rotationOrder y.u2) hpTwo y.u2 hnonparabolicY rfl
  apply hEscapes (rotationOrder y.u2) (by simpa [hleftCard] using hd) h₂
  have hyCoordinate := congrArg NormalizedPoint.u2 hyPoint
  change algebraMap (ZMod p) (quadraticFiniteField p) y.u2 =
    (splitFiberPoint w (s * (h : (quadraticFiniteField p)ˣ))).u2 at hyCoordinate
  rw [splitFiberOrbit_secondCoordinate_eq_weightedSplitTorusTrace] at hyCoordinate
  change weightedSplitTorusTrace alpha beta h = splitTorusTrace h₂
  rw [← h₂trace]
  simpa [alpha, beta] using hyCoordinate.symm

end BGS.Markoff
