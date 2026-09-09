/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseHistoryLipschitz
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentMeanCoercivity

@[expose] public section

/-! A fixed polynomial upper bound for the history's computed sensitivity.
The time reciprocal and inverse Gram bound are independent scalar inputs;
no operator or solution norm occurs in the resulting envelope. -/

noncomputable section

namespace EulerTransverseHistoryBounds

open EulerTimeH1GeneratorBounds EulerTransverseEndpointBounds
  EulerTransverseEndpointDifference EulerTransverseGeneratorDifference
  EulerPacketParentMeanCoercivity

def slopeEnvelope (Ti d a r : ℝ) : ℝ :=
  r*(1+d^2*(2*r^2)*a)*(2*Ti*d)

def slopeDifferenceEnvelope (Ti d a r x y : ℝ) : ℝ :=
  r*(2*Ti*endpointDifferenceCost d (2*r^2) a x y+x*slopeEnvelope Ti d a r)

def generatorDifferenceEnvelope (ci q q1 x y : ℝ) : ℝ :=
  (4*ci^2*q^2*q1+2*ci*q1)*x+2*ci*q*y

def differenceEnvelope (Ti ci q q1 d a r x y z : ℝ) : ℝ :=
  x*(2*(Ti+4*ci*q*q1))*slopeEnvelope Ti d a r+
    q*(4*generatorDifferenceEnvelope ci q q1 x y*slopeEnvelope Ti d a r+
      (2*(Ti+4*ci*q*q1))*slopeDifferenceEnvelope Ti d a r (y+x) z)

theorem differenceEnvelope_nonneg (Ti ci q q1 d a r x y z : ℝ)
    (hTi : 0 ≤ Ti) (hci : 0 ≤ ci) (hq : 0 ≤ q) (hq1 : 0 ≤ q1)
    (hd : 0 ≤ d) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ differenceEnvelope Ti ci q q1 d a r x y z := by
  unfold differenceEnvelope slopeDifferenceEnvelope
    generatorDifferenceEnvelope slopeEnvelope endpointDifferenceCost
  positivity

theorem historyDifferenceCost_le_envelope (T c Ti ci q q1 d a r x y z : ℝ)
    (hT : 0 < T) (hT1 : T ≤ 1) (hTi : T⁻¹ ≤ Ti) (hc : 0 < c) (hci : c⁻¹ ≤ ci)
    (hq : 0 ≤ q) (hq1 : 0 ≤ q1) (hd : 0 ≤ d) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    historyDifferenceCost T c q q1 d a r x y z ≤
      differenceEnvelope Ti ci q q1 d a r x y z := by
  have hTi0 := (inv_pos.mpr hT).le.trans hTi
  have hci0 := (inv_pos.mpr hc).le.trans hci
  have hSlope0 : 0 ≤ slopeCost T d a r := by unfold slopeCost affineCost; positivity
  have hGen0 : 0 ≤ generatorDifferenceCost c q q1 x y := by
    unfold generatorDifferenceCost; positivity
  have hGenE0 : 0 ≤ generatorDifferenceEnvelope ci q q1 x y := by
    unfold generatorDifferenceEnvelope; positivity
  have hSd0 : 0 ≤ slopeDifferenceCost T d a r (T*y+x) (T^2*z) := by
    unfold slopeDifferenceCost slopeCost affineCost endpointDifferenceCost
    positivity
  have hAff : affineCost T ≤ 2*Ti := by
    unfold affineCost
    rw [abs_of_pos (inv_pos.mpr hT)]
    calc
      (1+T)*T⁻¹ ≤ (1+1)*Ti := by gcongr
      _ = 2*Ti := by ring
  have hTrace : traceCost T (2*c⁻¹*q*q1) ≤ 2*(Ti+4*ci*q*q1) := by
    unfold traceCost
    calc
      (1+T)*(T⁻¹+2*(2*c⁻¹*q*q1)) ≤ (1+1)*(Ti+2*(2*ci*q*q1)) := by gcongr
      _ = 2*(Ti+4*ci*q*q1) := by ring
  have hSlope : slopeCost T d a r ≤ slopeEnvelope Ti d a r := by
    unfold slopeCost slopeEnvelope
    gcongr
  have hGen : generatorDifferenceCost c q q1 x y ≤ generatorDifferenceEnvelope ci q q1 x y := by
    unfold generatorDifferenceCost generatorDifferenceEnvelope
    gcongr
  have hSd : slopeDifferenceCost T d a r (T*y+x) (T^2*z) ≤
      slopeDifferenceEnvelope Ti d a r (y+x) z := by
    unfold slopeDifferenceCost slopeDifferenceEnvelope
    have hxy : T*y+x ≤ y+x := by nlinarith
    have hzT : T^2*z ≤ z := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ hT.le hT1 : T^2 ≤ 1) hz
    have hEndpoint0 : 0 ≤ endpointDifferenceCost d (2*r^2) a (T*y+x) (T^2*z) := by
      unfold endpointDifferenceCost
      positivity
    have hEndpoint : endpointDifferenceCost d (2*r^2) a (T*y+x) (T^2*z) ≤
        endpointDifferenceCost d (2*r^2) a (y+x) z := by
      unfold endpointDifferenceCost
      gcongr
    gcongr
  unfold historyDifferenceCost differenceEnvelope
  calc
    _ ≤ x*(2*(Ti+4*ci*q*q1))*slopeEnvelope Ti d a r+
        q*(2*(1+1)*generatorDifferenceEnvelope ci q q1 x y*slopeEnvelope Ti d a r+
          (2*(Ti+4*ci*q*q1))*slopeDifferenceEnvelope Ti d a r (y+x) z) := by
      gcongr
    _ = _ := by ring

theorem differenceEnvelope_mono
    {Ti ci q q1 d a r x y z Ti' ci' q' q1' d' a' r' x' y' z' : ℝ}
    (hTi : 0 ≤ Ti) (hci : 0 ≤ ci) (hq : 0 ≤ q) (hq1 : 0 ≤ q1)
    (hd : 0 ≤ d) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hTi' : Ti ≤ Ti') (hci' : ci ≤ ci') (hq' : q ≤ q') (hq1' : q1 ≤ q1')
    (hd' : d ≤ d') (ha' : a ≤ a') (hr' : r ≤ r')
    (hx' : x ≤ x') (hy' : y ≤ y') (hz' : z ≤ z') :
    differenceEnvelope Ti ci q q1 d a r x y z ≤
      differenceEnvelope Ti' ci' q' q1' d' a' r' x' y' z' := by
  have hTi0 := hTi.trans hTi'
  have hci0 := hci.trans hci'
  have hq0 := hq.trans hq'
  have hq10 := hq1.trans hq1'
  have hd0 := hd.trans hd'
  have ha0 := ha.trans ha'
  have hr0 := hr.trans hr'
  have hx0 := hx.trans hx'
  have hy0 := hy.trans hy'
  have hz0 := hz.trans hz'
  unfold differenceEnvelope slopeDifferenceEnvelope
    generatorDifferenceEnvelope slopeEnvelope endpointDifferenceCost
  gcongr

def parentDifferenceEnvelope (Ti C C1 CH R : ℝ) : ℝ :=
  differenceEnvelope Ti (gramInverseEnvelope C) C C1 (C1+C) (1+CH)
    (transportEnvelope C C1) (C*R) (C1*R) (CH*R)

end EulerTransverseHistoryBounds
