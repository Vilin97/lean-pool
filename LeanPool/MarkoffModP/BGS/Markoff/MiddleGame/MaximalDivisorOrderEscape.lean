/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.MaximalDivisorCorvajaZannierStep

/-!
# Nonparabolic order escape using maximal divisors

This is the geometric middle-game step with the maximal-divisor cover wired
all the way through.  The Corvaja--Zannier hypothesis and both numerical
inequalities are required only for divisibility-maximal candidate orders.
-/

namespace BGS.Markoff

/-- Complete nonparabolic order escape from a diagonalized fiber, with the
Corvaja--Zannier union restricted to maximal candidate orders. -/
theorem exists_iterate_with_larger_secondRotationOrder_of_diagonalizedFiber_maximalOrders
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (x : NormalizedPoint (ZMod p))
    (w s : (quadraticFiniteField p)ˣ)
    (hw : (w : quadraticFiniteField p) ^ 2 ≠ 1)
    (hpoint : algebraMapNormalizedPoint p x = splitFiberPoint w s)
    (hbelowEndgame :
      (rotationOrder x.u1 : ℝ) < (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        (middleGameMaximalOrders p (rotationOrder x.u1)).card) ^ 3 <
          rotationOrder x.u1)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        (middleGameMaximalOrders p (rotationOrder x.u1)).card *
          rotationOrder x.u1 < p)
    (hCZ :
      (s : quadraticFiniteField p) *
          (splitFiberProduct w * ((s⁻¹ : (quadraticFiniteField p)ˣ) :
            quadraticFiniteField p)) ≠ 1 →
      ∀ d ∈ middleGameMaximalOrders p (rotationOrder x.u1),
        ((weightedTraceEquationSolutions
          (s : quadraticFiniteField p)
          (splitFiberProduct w * ((s⁻¹ : (quadraticFiniteField p)ˣ) :
            quadraticFiniteField p))
          (Subgroup.zpowers w) (middleGameRightSubgroup p d)).card : ℝ) ≤
          corvajaZannierTraceUpperBound p (rotationOrder x.u1)
            (Nat.card (middleGameRightSubgroup p d))) :
    ∃ n : ℕ,
      rotationOrder x.u1 <
        rotationOrder ((normalizedRotate1^[n]) x).u2 := by
  let alpha : quadraticFiniteField p := s
  let beta : quadraticFiniteField p :=
    splitFiberProduct w *
      ((s⁻¹ : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)
  let Hleft : Subgroup (quadraticFiniteField p)ˣ := Subgroup.zpowers w
  have htrace :
      algebraMap (ZMod p) (quadraticFiniteField p) x.u1 =
        splitTorusTrace w :=
    congrArg NormalizedPoint.u1 hpoint
  have horder : orderOf w = rotationOrder x.u1 := by
    rw [← rotationOrder_eq_orderOf_extensionEigenvalue x.u1 w hw htrace]
  have hleftCard : Nat.card Hleft = rotationOrder x.u1 := by
    rw [Nat.card_zpowers, horder]
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hfour : (4 : quadraticFiniteField p) ≠ 0 := by
    exact (map_ne_zero
      (algebraMap (ZMod p) (quadraticFiniteField p))).mpr (by
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
  have hcurrentOrder : 0 < Nat.card Hleft := by
    rw [hleftCard]
    exact rotationOrder_pos x.u1
  have hrightOrder :
      ∀ d ∈ middleGameMaximalOrders p (Nat.card Hleft),
        Nat.card (middleGameRightSubgroup p d) = d := by
    intro d hd
    exact middleGameMaximalOrder_rightSubgroup_natCard
      p (Nat.card Hleft) d hp hd
  have hCZ' : alpha * beta ≠ 1 →
      ∀ d ∈ middleGameMaximalOrders p (Nat.card Hleft),
        ((weightedTraceEquationSolutions alpha beta Hleft
          (middleGameRightSubgroup p d)).card : ℝ) ≤
          corvajaZannierTraceUpperBound p (Nat.card Hleft)
            (Nat.card (middleGameRightSubgroup p d)) := by
    intro _ d hd
    simpa [alpha, beta, Hleft, hleftCard] using
      hCZ hnondegenerate d (by simpa [hleftCard] using hd)
  obtain ⟨h, hEscapes⟩ :=
    exists_left_element_escaping_of_weightedCorvajaZannierEstimate_maximalOrders
      p alpha beta Hleft (fun d ↦ middleGameRightSubgroup p d)
      hrightOrder hCZ' hnondegenerate hcurrentOrder hp
      (by simpa [hleftCard] using hcube)
      (by simpa [hleftCard] using hlinear)
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
      _ = splitFiberPoint w
          (s * (h : (quadraticFiniteField p)ˣ)) := hn
  apply lt_of_not_ge
  intro hsmall
  have hnonparabolicY : y.u2 ^ 2 ≠ 4 := by
    intro hparabolic
    have hcases :=
      (normalizedTrace_sq_eq_four_iff_parabolic p y.u2).mp hparabolic
    have hthreshold :=
      endgamePowerThreshold_le_rotationOrder_of_parabolicTrace
        p hpTwo delta hdelta y.u2 hcases
    have hsmallReal :
        (rotationOrder y.u2 : ℝ) ≤ (rotationOrder x.u1 : ℝ) := by
      exact_mod_cast hsmall
    exact (not_le_of_gt hbelowEndgame) (hthreshold.trans hsmallReal)
  obtain ⟨m, hm, hright, hrightTrace⟩ :=
    exists_middleGameMaximalOrder_trace_of_nonparabolic
      p (rotationOrder x.u1) hpTwo hp y.u2 hnonparabolicY hsmall
  apply hEscapes m (by simpa [hleftCard] using hm) hright
  have hyCoordinate := congrArg NormalizedPoint.u2 hyPoint
  change algebraMap (ZMod p) (quadraticFiniteField p) y.u2 =
    (splitFiberPoint w
      (s * (h : (quadraticFiniteField p)ˣ))).u2 at hyCoordinate
  rw [splitFiberOrbit_secondCoordinate_eq_weightedSplitTorusTrace] at hyCoordinate
  change weightedSplitTorusTrace alpha beta h = splitTorusTrace hright
  rw [← hrightTrace]
  simpa [alpha, beta] using hyCoordinate.symm

end BGS.Markoff
