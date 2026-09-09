/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketResidualTailFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketTailProductBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketConvolutionBounds

@[expose] public section

/-! The complete nonlinear tail is bounded using its actual finite convolution. -/

noncomputable section

namespace EulerPacketCylinderField.PrefixBound

open Set Finset EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerParameterWordGevrey

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile}
  {F : PrefixFields P T (N+1) a} {hT : 0 ≤ T}
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ} (B : PrefixBound F hT S R)
  {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)

include B

theorem tail_nonlinear_bound (hN : 1 ≤ N) (hR : 1 ≤ R)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (hc : (a 0).corrector = 0) (hb : (a 1).mean = 0) (n : ℕ) :
    (F.tailNonlinearField C n).WordBound 6 R
      (18*((N+2 : ℕ) : ℝ)^2*BC.termCost*S.H0^(2*n+2)) (110*(n+1)) := by
  let J := F.knownJet O (by omega)
  have hA : 0 ≤ 9*BC.termCost*S.H0^(2*n+2) :=
    mul_nonneg (mul_nonneg (by norm_num) BC.termCost_nonneg) (pow_nonneg S.H0_pos.le _)
  have hS := Field.wordBound_convolution (N+1) n
    (fun i j z => slowAdvection (O.inverseFrame z) (knownJets O (N+1) a z i) (knownJets O (N+1) a z
      j))
    (fun i j => SpatialJetField.slowAdvection C.inverse (J i) (J j))
    6 R (9*BC.termCost*S.H0^(2*n+2)) (110*(n+1)) (zero_le_one.trans hR) hA
    (fun i _ j _ hij => B.tail_slow_product_bound BC hN hR hRc hc hb i j n hij)
  have hH := Field.wordBound_convolution (N+1) (n+1)
    (fun i j z => fastAdvection (O.normal z) (knownJets O (N+1) a z i) (knownJets O (N+1) a z j))
    (fun i j => SpatialJetField.fastAdvection C.normal (J i) (J j))
    6 R (9*BC.termCost*S.H0^(2*n+2)) (110*(n+1)) (zero_le_one.trans hR) hA
    (fun i _ j _ hij => B.tail_fast_product_bound BC hN hR hRc hc hb i j n hij)
  have hs := hS.add hH
  have he : ((N+1+1 : ℕ) : ℝ)^2*(9*BC.termCost*S.H0^(2*n+2))+
      ((N+1+1 : ℕ) : ℝ)^2*(9*BC.termCost*S.H0^(2*n+2)) =
      18*((N+2 : ℕ) : ℝ)^2*BC.termCost*S.H0^(2*n+2) := by
    push_cast
    ring
  rw [he] at hs
  exact hs.of_raw_eq (F.tailNonlinearField C n) (fun _ _ _ => rfl)

end EulerPacketCylinderField.PrefixBound
