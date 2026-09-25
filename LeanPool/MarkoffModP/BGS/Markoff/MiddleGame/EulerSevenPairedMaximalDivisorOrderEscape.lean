/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.MaximalDivisorOrderEscape
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.EulerSevenPairedMaximalDivisorCorvajaZannierStep

/-!
# Euler-seven paired nonparabolic order escape

This is the diagonalized-fiber wiring for the exact cube condition
`189*K^3 < currentOrder`.
-/

@[expose] public section

namespace BGS.Markoff

theorem
    exists_iterate_with_larger_secondRotationOrder_of_diagonalizedFiber_eulerSevenPairedMaximalOrders
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (x : NormalizedPoint (ZMod p))
    (w s : (quadraticFiniteField p)ˣ)
    (hw : (w : quadraticFiniteField p) ^ 2 ≠ 1)
    (hpoint : algebraMapNormalizedPoint p x = splitFiberPoint w s)
    (hadmissible :
      WeightedTraceCurveIsCorvajaZannierAdmissible
        (s : quadraticFiniteField p)
        (splitFiberProduct w *
          ((s⁻¹ : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)))
    (hbelowEndgame :
      (rotationOrder x.u1 : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hcube :
      189 *
        (middleGameMaximalOrders p (rotationOrder x.u1)).card ^ 3 <
          rotationOrder x.u1)
    (hlinear :
      24 * (middleGameMaximalOrders p (rotationOrder x.u1)).card *
          rotationOrder x.u1 < p) :
    ∃ n : ℕ,
      rotationOrder x.u1 <
        rotationOrder ((normalizedRotate1^[n]) x).u2 := by
  classical
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
  have hcurrentOrder : 0 < Nat.card Hleft := by
    rw [hleftCard]
    exact rotationOrder_pos x.u1
  have hrightOrder :
      ∀ d ∈ middleGameMaximalOrders p (Nat.card Hleft),
        Nat.card (middleGameRightSubgroup p d) = d := by
    intro d hd
    exact middleGameMaximalOrder_rightSubgroup_natCard
      p (Nat.card Hleft) d hp hd
  have hcube' :
      189 *
          (middleGameMaximalOrders p (Nat.card Hleft)).card ^ 3 <
        Nat.card Hleft := by
    rw [hleftCard]
    exact hcube
  have hlinear' :
      24 * (middleGameMaximalOrders p (Nat.card Hleft)).card *
        Nat.card Hleft < p := by
    rw [hleftCard]
    exact hlinear
  obtain ⟨h, hEscapes⟩ :=
    exists_left_element_escaping_nonparabolic_maximalOrders_eulerSeven
      p (quadraticFiniteField p) alpha beta Hleft
      (fun d ↦ middleGameRightSubgroup p d)
      hrightOrder (by simpa [alpha, beta] using hadmissible)
      hcurrentOrder hp hcube' hlinear'
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
  obtain ⟨m, hm, hright, hrightTrace, hrightSq⟩ :=
    exists_middleGameMaximalOrder_nonparabolic_trace
      p (rotationOrder x.u1) hpTwo hp y.u2 hnonparabolicY hsmall
  have hm' : m ∈ middleGameMaximalOrders p (Nat.card Hleft) := by
    rw [hleftCard]
    exact hm
  apply hEscapes m hm' hright hrightSq
  have hyCoordinate := congrArg NormalizedPoint.u2 hyPoint
  change algebraMap (ZMod p) (quadraticFiniteField p) y.u2 =
    (splitFiberPoint w
      (s * (h : (quadraticFiniteField p)ˣ))).u2 at hyCoordinate
  rw [splitFiberOrbit_secondCoordinate_eq_weightedSplitTorusTrace]
    at hyCoordinate
  change weightedSplitTorusTrace alpha beta h = splitTorusTrace hright
  rw [← hrightTrace]
  simpa [alpha, beta] using hyCoordinate.symm

end BGS.Markoff
