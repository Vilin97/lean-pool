/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownPieceBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderLinearTermBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteVelocityBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketUnweightedAdvection

/-! Bounds for the actual advection products in the surviving finite packet tail. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic EulerParameterWordGevrey

theorem tail_product_amplitude (H c C : ℝ) (hH : 1 ≤ H) (hc : 0 ≤ c) (hcC : c ≤ C)
    (i j n : ℕ) (hij : i + j ≤ n + 1) :
    c*(3*H^(2*i))*(3*H^(2*j)) ≤ 9*C*H^(2*n+2) := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hC : 0 ≤ C := hc.trans hcC
  calc
    _ = 9*c*H^(2*(i+j)) := by rw [Nat.mul_add,pow_add]; ring
    _ ≤ 9*C*H^(2*(i+j)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcC (by norm_num)) (pow_nonneg hH0 _)
    _ ≤ 9*C*H^(2*n+2) := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hH (by omega)) (mul_nonneg (by norm_num) hC)

theorem tail_product_shift (i j n : ℕ) (hij : i + j ≤ n + 1) :
    highShift i+highShift j+1 ≤ 110*(n+1) := by
  unfold highShift
  omega

namespace PrefixBound

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile}
  {F : PrefixFields P T (N + 1) a} {hT : 0 ≤ T}
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ} (B : PrefixBound F hT S R)
  {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)

include B

theorem tail_slow_product_bound (hN : 1 ≤ N) (hR : 1 ≤ R)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (hc : (a 0).corrector = 0) (hb : (a 1).mean = 0)
    (i j n : ℕ) (hij : i + j = n) :
    (SpatialJetField.slowAdvection C.inverse (F.knownJet O (by omega) i)
      (F.knownJet O (by omega) j)).WordBound 6 R
      (9*BC.termCost*S.H0^(2*n+2)) (110*(n+1)) := by
  have hi := B.knownJet_bound O (by omega) hR hc hb i
  have hj := B.knownJet_bound O (by omega) hR hc hb j
  have hi0 : 0 ≤ 3*S.H0^(2*i) := mul_nonneg (by norm_num) (pow_nonneg S.H0_pos.le _)
  have hj0 : 0 ≤ 3*S.H0^(2*j) := mul_nonneg (by norm_num) (pow_nonneg S.H0_pos.le _)
  have h := BC.slow_unnormalized_bound _ _ hi hj (zero_le_one.trans hR) hi0 hj0 hRc
  have h0 := mul_nonneg (mul_nonneg BC.slowCost_nonneg hi0) hj0
  have hs := h.mono_shift hR h0 (tail_product_shift i j n (by omega))
  exact hs.mono_amplitude (zero_le_one.trans hR)
    (tail_product_amplitude S.H0 BC.slowCost BC.termCost S.H0_one_le BC.slowCost_nonneg
      BC.slowCost_le i j n (by omega))

theorem tail_fast_product_bound (hN : 1 ≤ N) (hR : 1 ≤ R)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (hc : (a 0).corrector = 0) (hb : (a 1).mean = 0)
    (i j n : ℕ) (hij : i + j = n + 1) :
    (SpatialJetField.fastAdvection C.normal (F.knownJet O (by omega) i)
      (F.knownJet O (by omega) j)).WordBound 6 R
      (9*BC.termCost*S.H0^(2*n+2)) (110*(n+1)) := by
  have hi := B.knownJet_bound O (by omega) hR hc hb i
  have hj := B.knownJet_bound O (by omega) hR hc hb j
  have hi0 : 0 ≤ 3*S.H0^(2*i) := mul_nonneg (by norm_num) (pow_nonneg S.H0_pos.le _)
  have hj0 : 0 ≤ 3*S.H0^(2*j) := mul_nonneg (by norm_num) (pow_nonneg S.H0_pos.le _)
  have h := BC.fast_unnormalized_bound _ _ hi hj (zero_le_one.trans hR) hi0 hj0 hRc
  have h0 := mul_nonneg (mul_nonneg BC.fastCost_nonneg hi0) hj0
  have hs := h.mono_shift hR h0 (tail_product_shift i j n (by omega))
  exact hs.mono_amplitude (zero_le_one.trans hR)
    (tail_product_amplitude S.H0 BC.fastCost BC.termCost S.H0_one_le BC.fastCost_nonneg
      BC.fastCost_le i j n (by omega))

end PrefixBound
end EulerPacketCylinderField
