/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedProduct
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetOperations
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear

/-! Same-radius normalized bounds for the literal slow and fast packet jet expressions. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerPacketPointJets EulerPacketProfileRecursion EulerCylinderPathProduct
  EulerCylinderScalarPrimitive EulerMeanCoefficients EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

namespace SpatialJetField

variable {P T : ℝ} [Fact (0 < P)] {J K : Domain → VectorJet}
  (G : SpatialJetField P T J) (H : SpatialJetField P T K) (hT : 0 ≤ T)
  (g h b : C(Icc (0 : ℝ) T, ℝ))
  (hg : ∀ t, 0 < g t) (hh : ∀ t, 0 < h t) (hb : ∀ t, 0 < b t)

theorem slowAdvection_normalized_bound
    {inverse : Domain → Space →L[ℝ] Space} (F : MatrixCoefficient T inverse)
    {R A B : ℝ} {d e : ℕ}
    (hG : (G.field.normalized hT g hg).WordBound 6 R A d)
    (hH : (H.field.normalized hT h hh).WordBound 6 R B e)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hRF : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hF : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath F.path) a‖ ≤ C * majorant Rc 0 n)
    (c : ℝ) (hc : 0 ≤ c) (hprofile : ∀ t, |productProfileRatio g h b hb t| ≤ c) :
    ((slowAdvection F G H).normalized hT b hb).WordBound 6 R
      (c*(9*productBlockConstant P*(3*sobolevCoefficientAmplitude (Fin 4) 6 Rc C*A)*B))
      (d+e+1) := by
  have hm := Field.WordBound.normalized_multiply hT hG F Rc C hRc hC hA hRF hF
  have ham : 0 ≤ 3*sobolevCoefficientAmplitude (Fin 4) 6 Rc C*A :=
    mul_nonneg (mul_nonneg (by norm_num)
      (sobolevCoefficientAmplitude_nonneg 6 Rc C hRc hC)) hA
  have hs := Field.WordBound.normalized_spatialTransport hT hm hH hR ham hB c hc hprofile
  exact hs.of_path_eq _ rfl

theorem fastAdvection_normalized_bound
    {normal : VectorField} (N : VectorCoefficient T normal)
    {R A B : ℝ} {d e : ℕ}
    (hG : (G.field.normalized hT g hg).WordBound 6 R A d)
    (hH : (H.field.normalized hT h hh).WordBound 6 R B e)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hRN : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hN : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath N.path) a‖ ≤ C * majorant Rc 0 n)
    (c : ℝ) (hc : 0 ≤ c) (hprofile : ∀ t, |productProfileRatio g h b hb t| ≤ c) :
    ((fastAdvection N G H).normalized hT b hb).WordBound 6 R
      (c*(3*productBlockConstant P*(3*sobolevCoefficientAmplitude (Fin 4) 6 Rc C*A)*B))
      (d+e+1) := by
  have hm := Field.WordBound.normalized_multiply hT hG N.normalMatrix Rc C hRc hC hA hRN
    (N.normalMatrix_bound Rc C hN)
  have hd := Field.WordBound.normalized_derivative hT hH 0
  have ham : 0 ≤ 3*sobolevCoefficientAmplitude (Fin 4) 6 Rc C*A :=
    mul_nonneg (mul_nonneg (by norm_num)
      (sobolevCoefficientAmplitude_nonneg 6 Rc C hRc hC)) hA
  have hs := Field.WordBound.normalized_scalarProduct hT hm hd scalarProject
    (le_of_eq scalarProject_norm) hR ham hB c hc hprofile
  have he := hs.of_path_eq ((fastAdvection N G H).normalized hT b hb) rfl
  simpa only [Nat.add_assoc] using he

end SpatialJetField

namespace Field

variable {P T : ℝ} [Fact (0 < P)] (hT : 0 ≤ T)
  (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)

theorem WordBound.normalized_slowPressure
    {inverse : Domain → Space →L[ℝ] Space} (F : MatrixCoefficient T inverse)
    (p : ScalarField) (G : Field P T (pressureGradient p))
    {q d : ℕ} {R A : ℝ} (hG : (G.normalized hT g hg).WordBound q R A d)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hRF : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hF : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath F.path) a‖ ≤ C * majorant Rc 0 n) :
    ((slowPressure F p G).normalized hT g hg).WordBound q R
      (3*sobolevCoefficientAmplitude (Fin 4) q Rc C*A) d := by
  have hm := WordBound.normalized_multiply hT hG F.adjoint Rc C hRc hC hA hRF
    (F.adjoint_bound Rc C hF)
  exact hm.of_path_eq _ rfl

theorem WordBound.normalized_linearPart
    {strain : Domain → Space →L[ℝ] Space} (M : MatrixCoefficient T strain)
    {raw raw_t : VectorField} (G : Field P T raw) (H : Field P T raw_t)
    (hTpos : 0 < T) (hd : TimeDerivative hTpos.le G H)
    (s : Set ℝ) (hs : s = Icc (0 : ℝ) T)
    {q d : ℕ} {R A B : ℝ}
    (hG : (G.normalized hT g hg).WordBound q R A d)
    (hH : (H.normalized hT g hg).WordBound q R B d)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hRM : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hM : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath M.path) a‖ ≤ C * majorant Rc 0 n) :
    ((linearPart M G H hTpos hd s hs).normalized hT g hg).WordBound q R
      (B+3*sobolevCoefficientAmplitude (Fin 4) q Rc C*A) d := by
  have hm := WordBound.normalized_multiply hT hG M Rc C hRc hC hA hRM hM
  have ha := WordBound.normalized_add hT hH hm
  exact ha.of_path_eq _ rfl

end Field
end EulerPacketCylinderField
