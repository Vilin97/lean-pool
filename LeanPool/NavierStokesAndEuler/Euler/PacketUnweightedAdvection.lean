/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderLinearTermBudget

@[expose] public section

/-! The literal advection fields obey the same fixed coefficient costs before the final tail split.
  -/

noncomputable section

namespace EulerPacketCylinderField.CoefficientBudget

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerParameterWordGevrey EulerCylinderScalarPrimitive

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {C : CoefficientData P T O}
  (BC : CoefficientBudget C) {J K : Domain → VectorJet}
  (G : SpatialJetField P T J) (H : SpatialJetField P T K)

theorem slow_unnormalized_bound {R A B : ℝ} {d e : ℕ}
    (hG : G.field.WordBound 6 R A d) (hH : H.field.WordBound 6 R B e)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R) :
    (SpatialJetField.slowAdvection C.inverse G H).WordBound 6 R (BC.slowCost*A*B) (d+e+1) := by
  have hm := hG.multiply C.inverse BC.Rc BC.amplitude BC.Rc_nonneg BC.amplitude_nonneg hA hRc
    BC.inverse_bound
  have ham : 0 ≤ 3*sobolevCoefficientAmplitude (Fin 4) 6 BC.Rc BC.amplitude*A :=
    mul_nonneg BC.multiplierCost_nonneg hA
  have hs := (hm.spatialTransport hH hR ham hB).of_path_eq
    (SpatialJetField.slowAdvection C.inverse G H) rfl
  have he : 9*EulerCylinderPathProduct.productBlockConstant P*
      (3*sobolevCoefficientAmplitude (Fin 4) 6 BC.Rc BC.amplitude*A)*B = BC.slowCost*A*B := by
    unfold slowCost multiplierCost
    ring
  simpa only [he] using hs

theorem fast_unnormalized_bound {R A B : ℝ} {d e : ℕ}
    (hG : G.field.WordBound 6 R A d) (hH : H.field.WordBound 6 R B e)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R) :
    (SpatialJetField.fastAdvection C.normal G H).WordBound 6 R (BC.fastCost*A*B) (d+e+1) := by
  have hm := hG.multiply C.normal.normalMatrix BC.Rc BC.amplitude BC.Rc_nonneg BC.amplitude_nonneg
    hA hRc
    (C.normal.normalMatrix_bound BC.Rc BC.amplitude BC.normal_bound)
  have hd := hH.derivative 0
  have ham : 0 ≤ 3*sobolevCoefficientAmplitude (Fin 4) 6 BC.Rc BC.amplitude*A :=
    mul_nonneg BC.multiplierCost_nonneg hA
  have hs := (hm.scalarProduct hd scalarProject (le_of_eq scalarProject_norm) hR ham hB).of_path_eq
    (SpatialJetField.fastAdvection C.normal G H) rfl
  have he : 3*EulerCylinderPathProduct.productBlockConstant P*
      (3*sobolevCoefficientAmplitude (Fin 4) 6 BC.Rc BC.amplitude*A)*B = BC.fastCost*A*B := by
    unfold fastCost multiplierCost
    ring
  simpa only [he,Nat.add_assoc] using hs

end EulerPacketCylinderField.CoefficientBudget
