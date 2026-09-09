/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldWeight
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAverage

@[expose] public section

/-! Linear operations and spatial derivatives of actual profile-normalized packet fields. -/

noncomputable section

namespace EulerPacketCylinderField.Field

open Set Finset ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerCylinderSobolev EulerLpCylinderTranslation
  EulerCylinderAngleAverage EulerContinuousTimeWeight EulerCylinderPotential
  EulerParameterWordGevrey EulerGevrey EulerPacketProfileRecursion
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] {raw raw' : VectorField}
  {G : Field P T raw} {H : Field P T raw'}

theorem WordBound.of_path_eq {q d : ℕ} {R A : ℝ} (hG : G.WordBound q R A d)
    (H : Field P T raw') (he : H.path = G.path) : H.WordBound q R A d := by
  unfold WordBound at *
  rw [he]
  exact hG

variable (G H) (hT : 0 ≤ T) (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)

theorem normalized_add_path : ((G.add H).normalized hT g hg).path =
    ((G.normalized hT g hg).add (H.normalized hT g hg)).path :=
  (normalize g hg).map_add G.path H.path

theorem normalized_sub_path : ((G.sub H).normalized hT g hg).path =
    ((G.normalized hT g hg).sub (H.normalized hT g hg)).path := by
  change normalize g hg (G.path + -H.path) = normalize g hg G.path + -normalize g hg H.path
  rw [map_add,map_neg]

theorem normalized_neg_path : (G.neg.normalized hT g hg).path = (G.normalized hT g hg).neg.path :=
  (normalize g hg).map_neg G.path

theorem normalized_multiply_path
    {coef : EulerPacketPointJets.Domain → Space →L[ℝ] Space} (K : MatrixCoefficient T coef) :
    ((K.multiply G).normalized hT g hg).path = (K.multiply (G.normalized hT g hg)).path :=
  (fullMultiplier_weight P (reciprocal g hg) G.path K.path).symm

theorem normalized_finsetSum_path {ι : Type*} (s : Finset ι) (f : ι → VectorField)
    (W : ∀ i, Field P T (f i)) :
    ((Field.finsetSum s f W).normalized hT g hg).path =
      (Field.finsetSum s (fun i z => (g (projIcc 0 T hT z.1))⁻¹ • f i z)
        (fun i => (W i).normalized hT g hg)).path :=
  map_sum (normalize g hg) (fun i => (W i).path) s

variable {G H g hg}

theorem WordBound.normalized_add {q d : ℕ} {R A B : ℝ}
    (hG : (G.normalized hT g hg).WordBound q R A d)
    (hH : (H.normalized hT g hg).WordBound q R B d) :
    ((G.add H).normalized hT g hg).WordBound q R (A+B) d :=
  (hG.add hH).of_path_eq _ (G.normalized_add_path H hT g hg)

theorem WordBound.normalized_sub {q d : ℕ} {R A B : ℝ}
    (hG : (G.normalized hT g hg).WordBound q R A d)
    (hH : (H.normalized hT g hg).WordBound q R B d) :
    ((G.sub H).normalized hT g hg).WordBound q R (A+B) d :=
  (hG.sub hH).of_path_eq _ (G.normalized_sub_path H hT g hg)

theorem WordBound.normalized_neg {q d : ℕ} {R A : ℝ}
    (hG : (G.normalized hT g hg).WordBound q R A d) :
    (G.neg.normalized hT g hg).WordBound q R A d :=
  hG.neg.of_path_eq _ (G.normalized_neg_path hT g hg)

theorem WordBound.normalized_derivative {q d : ℕ} {R A : ℝ}
    (hG : (G.normalized hT g hg).WordBound q R A d) (i : Fin 4) :
    ((G.derivative i).normalized hT g hg).WordBound q R A (d+1) :=
  (hG.derivative i).of_path_eq _ (G.derivative_normalized_path hT g hg i).symm

theorem WordBound.normalized_multiply {q d : ℕ} {R A : ℝ}
    (hG : (G.normalized hT g hg).WordBound q R A d)
    {coef : EulerPacketPointJets.Domain → Space →L[ℝ] Space} (K : MatrixCoefficient T coef)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hK : ∀ n a, ‖iteratedFDeriv ℝ n (EulerMeanCoefficients.translateCoefficientPath K.path) a‖ ≤
      C*majorant Rc 0 n) :
    ((K.multiply G).normalized hT g hg).WordBound q R
      (3*sobolevCoefficientAmplitude (Fin 4) q Rc C*A) d :=
  (hG.multiply K Rc C hRc hC hA hR hK).of_path_eq _ (G.normalized_multiply_path hT g hg K)

theorem wordBound_normalized_finsetSum {ι : Type*} (s : Finset ι) (f : ι → VectorField)
    (W : ∀ i, Field P T (f i)) (q : ℕ) (R : ℝ) (d : ℕ) (A : ι → ℝ)
    (hW : ∀ i ∈ s, ((W i).normalized hT g hg).WordBound q R (A i) d) :
    ((Field.finsetSum s f W).normalized hT g hg).WordBound q R (∑ i ∈ s,A i) d :=
  (wordBound_finsetSum s _ (fun i => (W i).normalized hT g hg) A hW).of_path_eq _
    (normalized_finsetSum_path hT g hg s f W)

theorem WordBound.angleMean {q d : ℕ} {R A : ℝ} (hG : G.WordBound q R A d) :
    G.angleMean.WordBound q R A d := by
  intro n
  have he : (fun a : LiftTangent => pathTranslate P a G.angleMean.path) =
      (pathAverage P) ∘ (fun a : LiftTangent => pathTranslate P a G.path) :=
    funext (fun a => (pathAverage_translation P a G.path).symm)
  rw [he]
  have h := block_comp_clm_le standardDirection q (pathAverage P)
    (fun a : LiftTangent => pathTranslate P a G.path) G.orbit n 0
  have hb := h.trans (mul_le_mul_of_nonneg_right (pathAverage_norm P)
    (block_nonneg standardDirection q (fun a : LiftTangent => pathTranslate P a G.path) n 0))
  simpa only [one_mul] using hb.trans (by simpa only [one_mul] using hG n)

variable (G g hg)

theorem normalized_angleMean_path : (G.angleMean.normalized hT g hg).path =
    (G.normalized hT g hg).angleMean.path := by
  apply ContinuousMap.ext
  intro t
  exact ((average P).map_smul ((g t)⁻¹) (G.path t)).symm

variable {G g hg}

theorem WordBound.normalized_angleMean {q d : ℕ} {R A : ℝ}
    (hG : (G.normalized hT g hg).WordBound q R A d) :
    (G.angleMean.normalized hT g hg).WordBound q R A d :=
  hG.angleMean.of_path_eq _ (G.normalized_angleMean_path hT g hg)

end EulerPacketCylinderField.Field
