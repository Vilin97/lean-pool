/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientData
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAdvection
public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldCalculus

@[expose] public section

/-! Norm-one coefficient constructions used by the actual slow and fast packet terms. -/

noncomputable section

namespace EulerPacketCylinderField

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerLiftedGradientSpace
  EulerMeanCoefficients EulerCylinderScalarPrimitive EulerBoundedFieldCalculus
  EulerPacketPointJets EulerPacketProfileRecursion EulerGevrey
open scoped ContDiff BoundedContinuousFunction

private theorem mapped_derivative_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (f : Space → E) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (a : Space) : ‖iteratedFDeriv ℝ n (L ∘ f) a‖ ≤ ‖iteratedFDeriv ℝ n f a‖ := by
  have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := Space)
    L (hf.contDiffAt (x := a)) (n := n) (by simp)
  exact h.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hL (norm_nonneg (iteratedFDeriv ℝ n f a)))

theorem normalComponentMap_norm : ‖normalComponentMap‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro m
  rw [one_mul]
  apply opNorm_le_bound _ (norm_nonneg m)
  intro v
  rw [normalComponentMap_apply,scalarEmbed,toSpanSingleton_apply,norm_smul,unitVector_norm,mul_one]
  exact norm_inner_le_norm m v

private theorem mapCoefficientPath_norm_le
    {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) : ‖mapCoefficientPath (K := K) L‖ ≤ ‖L‖ := by
  apply opNorm_le_bound _ (norm_nonneg L)
  intro A
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg L) (norm_nonneg A))).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg L) (norm_nonneg A))).mpr
  intro x
  exact (L.le_opNorm (A t x)).trans (mul_le_mul_of_nonneg_left
    (((A t).norm_coe_le_norm x).trans (A.norm_coe_le_norm t)) (norm_nonneg L))

namespace VectorCoefficient

variable {T : ℝ} {raw : VectorField} (N : VectorCoefficient T raw)

def normalMatrix : MatrixCoefficient T (fun z => normalComponentMap (raw z)) where
  path := normalComponentPath N.path
  orbit := normalComponentPath_orbit N.path N.orbit
  raw_eq t x θ := by rw [N.raw_eq]; rfl

theorem normalMatrix_bound (Rc C : ℝ)
    (hN : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath N.path) a‖ ≤ C*majorant Rc 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath N.normalMatrix.path) a‖ ≤ C*majorant Rc 0 n := by
  have he : translateCoefficientPath N.normalMatrix.path =
      (mapCoefficientPath (K := Icc (0 : ℝ) T) normalComponentMap) ∘ translateCoefficientPath
        N.path := by
    funext b
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  rw [he]
  exact (mapped_derivative_le (mapCoefficientPath (K := Icc (0 : ℝ) T) normalComponentMap)
    ((mapCoefficientPath_norm_le normalComponentMap).trans normalComponentMap_norm)
    _ N.orbit n a).trans (hN n a)

end VectorCoefficient

namespace MatrixCoefficient

variable {T : ℝ} {raw : Domain → Space →L[ℝ] Space} (K : MatrixCoefficient T raw)

theorem adjoint_bound (Rc C : ℝ)
    (hK : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath K.path) a‖ ≤ C*majorant Rc 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath K.adjoint.path) a‖ ≤ C*majorant Rc 0 n := by
  let A : (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space) :=
    EulerTransverseGramInverse.realAdjoint
  have hA : ‖A‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    change ‖v.adjoint‖ ≤ 1*‖v‖
    rw [LinearIsometryEquiv.norm_map,one_mul]
  have he : translateCoefficientPath K.adjoint.path =
      (mapCoefficientPath (K := Icc (0 : ℝ) T) A) ∘ translateCoefficientPath K.path := by
    funext b
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  rw [he]
  have hm := mapped_derivative_le
    (mapCoefficientPath (K := Icc (0 : ℝ) T) A)
    ((mapCoefficientPath_norm_le A).trans hA)
    (translateCoefficientPath K.path) K.orbit n a
  exact hm.trans (hK n a)

end MatrixCoefficient
end EulerPacketCylinderField
