/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketParentMeanCoercivity
public import LeanPool.NavierStokesAndEuler.Euler.TransverseHistoryBounds

/-! A fixed polynomial upper bound for the history's computed sensitivity.
The time reciprocal and inverse Gram bound are independent scalar inputs;
no operator or solution norm occurs in the resulting envelope. -/

@[expose] public section


noncomputable section

namespace EulerTransverseHistoryBounds

open EulerTimeH1GeneratorBounds EulerTransverseEndpointBounds
  EulerTransverseEndpointDifference EulerTransverseGeneratorDifference
  EulerPacketParentMeanCoercivity

/-- Slope envelope, given by `r*(1+d^2*(2*r^2)*a)*(2*Ti*d)`. -/
def slopeEnvelope (Ti d a r : ℝ) : ℝ :=
  r*(1+d^2*(2*r^2)*a)*(2*Ti*d)

/-- Slope difference envelope, given by `r*(2*Ti*endpointDifferenceCost d (2*r^2) a x
y+x*slopeEnvelope Ti d a r)`. -/
def slopeDifferenceEnvelope (Ti d a r x y : ℝ) : ℝ :=
  r*(2*Ti*endpointDifferenceCost d (2*r^2) a x y+x*slopeEnvelope Ti d a r)

/-- Generator difference envelope, given by `(4*ci^2*q^2*q1+2*ci*q1)*x+2*ci*q*y`. -/
def generatorDifferenceEnvelope (ci q q1 x y : ℝ) : ℝ :=
  (4*ci^2*q^2*q1+2*ci*q1)*x+2*ci*q*y

/-- Difference envelope as an element of `ℝ`. -/
def differenceEnvelope (Ti ci q q1 d a r x y z : ℝ) : ℝ :=
  x*(2*(Ti+4*ci*q*q1))*slopeEnvelope Ti d a r +
    q*(4*generatorDifferenceEnvelope ci q q1 x y*slopeEnvelope Ti d a r +
      (2*(Ti+4*ci*q*q1))*slopeDifferenceEnvelope Ti d a r (y+x) z)

/-- A nonnegative quantity bounded above passes its bound through a sum. -/
theorem bound_add {a a' b b' : ℝ} (ha : 0 ≤ a ∧ a ≤ a') (hb : 0 ≤ b ∧ b ≤ b') :
    0 ≤ a + b ∧ a + b ≤ a' + b' :=
  ⟨add_nonneg ha.1 hb.1, add_le_add ha.2 hb.2⟩

/-- A nonnegative quantity bounded above passes its bound through a product. -/
theorem bound_mul {a a' b b' : ℝ} (ha : 0 ≤ a ∧ a ≤ a') (hb : 0 ≤ b ∧ b ≤ b') :
    0 ≤ a * b ∧ a * b ≤ a' * b' :=
  ⟨mul_nonneg ha.1 hb.1, mul_le_mul ha.2 hb.2 hb.1 (ha.1.trans ha.2)⟩

/-- A nonnegative quantity bounded above passes its bound through a power. -/
theorem bound_pow {a a' : ℝ} (ha : 0 ≤ a ∧ a ≤ a') (n : ℕ) :
    0 ≤ a ^ n ∧ a ^ n ≤ a' ^ n :=
  ⟨pow_nonneg ha.1 n, pow_le_pow_left₀ ha.1 ha.2 n⟩

theorem bound_refl {a : ℝ} (ha : 0 ≤ a) : 0 ≤ a ∧ a ≤ a := ⟨ha, le_rfl⟩

theorem slopeEnvelope_bound {Ti d a r Ti' d' a' r' : ℝ}
    (hTi : 0 ≤ Ti ∧ Ti ≤ Ti') (hd : 0 ≤ d ∧ d ≤ d') (ha : 0 ≤ a ∧ a ≤ a')
    (hr : 0 ≤ r ∧ r ≤ r') :
    0 ≤ slopeEnvelope Ti d a r ∧ slopeEnvelope Ti d a r ≤ slopeEnvelope Ti' d' a' r' := by
  have two : (0 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 2 := bound_refl zero_le_two
  unfold slopeEnvelope
  exact bound_mul (bound_mul hr (bound_add (bound_refl zero_le_one)
    (bound_mul (bound_mul (bound_pow hd 2) (bound_mul two (bound_pow hr 2))) ha)))
    (bound_mul (bound_mul two hTi) hd)

theorem endpointDifferenceCost_bound {d i a x y d' i' a' x' y' : ℝ}
    (hd : 0 ≤ d ∧ d ≤ d') (hi : 0 ≤ i ∧ i ≤ i') (ha : 0 ≤ a ∧ a ≤ a')
    (hx : 0 ≤ x ∧ x ≤ x') (hy : 0 ≤ y ∧ y ≤ y') :
    0 ≤ endpointDifferenceCost d i a x y ∧
      endpointDifferenceCost d i a x y ≤ endpointDifferenceCost d' i' a' x' y' := by
  have two : (0 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 2 := bound_refl zero_le_two
  have three : (0 : ℝ) ≤ 3 ∧ (3 : ℝ) ≤ 3 := bound_refl zero_le_three
  unfold endpointDifferenceCost
  exact bound_add
    (bound_mul (bound_add
      (bound_add (bound_refl zero_le_one)
        (bound_mul (bound_mul (bound_mul three (bound_pow hd 2)) hi) ha))
      (bound_mul (bound_mul (bound_mul two (bound_pow hd 4)) (bound_pow hi 2))
        (bound_pow ha 2))) hx)
    (bound_mul (bound_add (bound_mul (bound_pow hd 3) hi)
      (bound_mul (bound_mul (bound_pow hd 5) (bound_pow hi 2)) ha)) hy)

theorem slopeDifferenceEnvelope_bound {Ti d a r x y Ti' d' a' r' x' y' : ℝ}
    (hTi : 0 ≤ Ti ∧ Ti ≤ Ti') (hd : 0 ≤ d ∧ d ≤ d') (ha : 0 ≤ a ∧ a ≤ a')
    (hr : 0 ≤ r ∧ r ≤ r') (hx : 0 ≤ x ∧ x ≤ x') (hy : 0 ≤ y ∧ y ≤ y') :
    0 ≤ slopeDifferenceEnvelope Ti d a r x y ∧
      slopeDifferenceEnvelope Ti d a r x y ≤ slopeDifferenceEnvelope Ti' d' a' r' x' y' := by
  have two : (0 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 2 := bound_refl zero_le_two
  unfold slopeDifferenceEnvelope
  exact bound_mul hr (bound_add
    (bound_mul (bound_mul two hTi)
      (endpointDifferenceCost_bound hd (bound_mul two (bound_pow hr 2)) ha hx hy))
    (bound_mul hx (slopeEnvelope_bound hTi hd ha hr)))

theorem generatorDifferenceEnvelope_bound {ci q q1 x y ci' q' q1' x' y' : ℝ}
    (hci : 0 ≤ ci ∧ ci ≤ ci') (hq : 0 ≤ q ∧ q ≤ q') (hq1 : 0 ≤ q1 ∧ q1 ≤ q1')
    (hx : 0 ≤ x ∧ x ≤ x') (hy : 0 ≤ y ∧ y ≤ y') :
    0 ≤ generatorDifferenceEnvelope ci q q1 x y ∧
      generatorDifferenceEnvelope ci q q1 x y ≤ generatorDifferenceEnvelope ci' q' q1' x' y' := by
  have two : (0 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 2 := bound_refl zero_le_two
  have four : (0 : ℝ) ≤ 4 ∧ (4 : ℝ) ≤ 4 := bound_refl zero_le_four
  unfold generatorDifferenceEnvelope
  exact bound_add
    (bound_mul (bound_add
      (bound_mul (bound_mul (bound_mul four (bound_pow hci 2)) (bound_pow hq 2)) hq1)
      (bound_mul (bound_mul two hci) hq1)) hx)
    (bound_mul (bound_mul (bound_mul two hci) hq) hy)

theorem differenceEnvelope_bound {Ti ci q q1 d a r x y z Ti' ci' q' q1' d' a' r' x' y' z' : ℝ}
    (hTi : 0 ≤ Ti ∧ Ti ≤ Ti') (hci : 0 ≤ ci ∧ ci ≤ ci') (hq : 0 ≤ q ∧ q ≤ q')
    (hq1 : 0 ≤ q1 ∧ q1 ≤ q1') (hd : 0 ≤ d ∧ d ≤ d') (ha : 0 ≤ a ∧ a ≤ a')
    (hr : 0 ≤ r ∧ r ≤ r') (hx : 0 ≤ x ∧ x ≤ x') (hy : 0 ≤ y ∧ y ≤ y')
    (hz : 0 ≤ z ∧ z ≤ z') :
    0 ≤ differenceEnvelope Ti ci q q1 d a r x y z ∧
      differenceEnvelope Ti ci q q1 d a r x y z ≤
        differenceEnvelope Ti' ci' q' q1' d' a' r' x' y' z' := by
  have two : (0 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 2 := bound_refl zero_le_two
  have four : (0 : ℝ) ≤ 4 ∧ (4 : ℝ) ≤ 4 := bound_refl zero_le_four
  have hS := slopeEnvelope_bound hTi hd ha hr
  have hA := bound_mul two (bound_add hTi (bound_mul (bound_mul (bound_mul four hci) hq) hq1))
  unfold differenceEnvelope
  exact bound_add (bound_mul (bound_mul hx hA) hS)
    (bound_mul hq (bound_add
      (bound_mul (bound_mul four (generatorDifferenceEnvelope_bound hci hq hq1 hx hy)) hS)
      (bound_mul hA (slopeDifferenceEnvelope_bound hTi hd ha hr (bound_add hy hx) hz))))

theorem differenceEnvelope_nonneg (Ti ci q q1 d a r x y z : ℝ)
    (hTi : 0 ≤ Ti) (hci : 0 ≤ ci) (hq : 0 ≤ q) (hq1 : 0 ≤ q1)
    (hd : 0 ≤ d) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ differenceEnvelope Ti ci q q1 d a r x y z :=
  (differenceEnvelope_bound (bound_refl hTi) (bound_refl hci) (bound_refl hq) (bound_refl hq1)
    (bound_refl hd) (bound_refl ha) (bound_refl hr) (bound_refl hx) (bound_refl hy)
    (bound_refl hz)).1

theorem historyDifferenceCost_le_envelope (T c Ti ci q q1 d a r x y z : ℝ)
    (hT : 0 < T) (hT1 : T ≤ 1) (hTi : T⁻¹ ≤ Ti) (hc : 0 < c) (hci : c⁻¹ ≤ ci)
    (hq : 0 ≤ q) (hq1 : 0 ≤ q1) (hd : 0 ≤ d) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    historyDifferenceCost T c q q1 d a r x y z ≤
      differenceEnvelope Ti ci q q1 d a r x y z := by
  have two : (0 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 2 := bound_refl zero_le_two
  have hTi' : 0 ≤ T⁻¹ ∧ T⁻¹ ≤ Ti := ⟨(inv_pos.mpr hT).le, hTi⟩
  have hci' : 0 ≤ c⁻¹ ∧ c⁻¹ ≤ ci := ⟨(inv_pos.mpr hc).le, hci⟩
  have hT2 : 0 ≤ 1 + T ∧ 1 + T ≤ 1 + 1 := bound_add (bound_refl zero_le_one) ⟨hT.le, hT1⟩
  have hq' := bound_refl hq
  have hd' := bound_refl hd
  have ha' := bound_refl ha
  have hr' := bound_refl hr
  have hx' := bound_refl hx
  have hAff : 0 ≤ affineCost T ∧ affineCost T ≤ 2 * Ti := by
    unfold affineCost
    rw [abs_of_pos (inv_pos.mpr hT), ← one_add_one_eq_two]
    exact bound_mul hT2 hTi'
  have hTrace : 0 ≤ traceCost T (2*c⁻¹*q*q1) ∧ traceCost T (2*c⁻¹*q*q1) ≤ 2*(Ti+4*ci*q*q1) := by
    have h := bound_mul hT2 (bound_add hTi'
      (bound_mul two (bound_mul (bound_mul (bound_mul two hci') hq') (bound_refl hq1))))
    exact ⟨h.1, h.2.trans_eq (by ring)⟩
  have hSlope : 0 ≤ slopeCost T d a r ∧ slopeCost T d a r ≤ slopeEnvelope Ti d a r := by
    unfold slopeCost slopeEnvelope
    exact bound_mul (bound_mul hr' (bound_add (bound_refl zero_le_one)
      (bound_mul (bound_mul (bound_pow hd' 2) (bound_mul two (bound_pow hr' 2))) ha')))
      (bound_mul hAff hd')
  have hGen : 0 ≤ generatorDifferenceCost c q q1 x y ∧
      generatorDifferenceCost c q q1 x y ≤ generatorDifferenceEnvelope ci q q1 x y :=
    generatorDifferenceEnvelope_bound hci' hq' (bound_refl hq1) hx' (bound_refl hy)
  have hxy : 0 ≤ T*y+x ∧ T*y+x ≤ y+x :=
    bound_add ⟨mul_nonneg hT.le hy, mul_le_of_le_one_left hy hT1⟩ hx'
  have hzT : 0 ≤ T^2*z ∧ T^2*z ≤ z :=
    ⟨mul_nonneg (sq_nonneg T) hz, mul_le_of_le_one_left hz (pow_le_one₀ hT.le hT1)⟩
  have hSd : 0 ≤ slopeDifferenceCost T d a r (T*y+x) (T^2*z) ∧
      slopeDifferenceCost T d a r (T*y+x) (T^2*z) ≤
        slopeDifferenceEnvelope Ti d a r (y+x) z := by
    unfold slopeDifferenceCost slopeDifferenceEnvelope
    exact bound_mul hr' (bound_add
      (bound_mul hAff (endpointDifferenceCost_bound hd' (bound_mul two (bound_pow hr' 2)) ha'
        hxy hzT))
      (bound_mul hxy hSlope))
  unfold historyDifferenceCost differenceEnvelope
  calc
    _ ≤ x*(2*(Ti+4*ci*q*q1))*slopeEnvelope Ti d a r +
        q*(2*(1+1)*generatorDifferenceEnvelope ci q q1 x y*slopeEnvelope Ti d a r +
          (2*(Ti+4*ci*q*q1))*slopeDifferenceEnvelope Ti d a r (y+x) z) :=
      (bound_add (bound_mul (bound_mul hx' hTrace) hSlope) (bound_mul hq' (bound_add
        (bound_mul (bound_mul (bound_mul two hT2) hGen) hSlope) (bound_mul hTrace hSd)))).2
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
      differenceEnvelope Ti' ci' q' q1' d' a' r' x' y' z' :=
  (differenceEnvelope_bound ⟨hTi, hTi'⟩ ⟨hci, hci'⟩ ⟨hq, hq'⟩ ⟨hq1, hq1'⟩ ⟨hd, hd'⟩ ⟨ha, ha'⟩
    ⟨hr, hr'⟩ ⟨hx, hx'⟩ ⟨hy, hy'⟩ ⟨hz, hz'⟩).2

/-- Parent difference envelope, given by `differenceEnvelope Ti (gramInverseEnvelope C) C C1
(C1+C) (1+CH) (transportEnvelope C C1) (C*R) (C1*R) (CH*R)`. -/
def parentDifferenceEnvelope (Ti C C1 CH R : ℝ) : ℝ :=
  differenceEnvelope Ti (gramInverseEnvelope C) C C1 (C1+C) (1+CH)
    (transportEnvelope C C1) (C*R) (C1*R) (CH*R)

end EulerTransverseHistoryBounds
