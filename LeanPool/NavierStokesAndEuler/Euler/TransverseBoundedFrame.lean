/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPathMap
public import LeanPool.NavierStokesAndEuler.Euler.TransverseSourceCoefficientPath

@[expose] public section

/-!
# The literal source frame as a uniformly smooth bounded coefficient path

The reference-plane restriction is a fixed linear contraction. The actual
source fields F and F_t therefore construct the full bounded frame fields,
with their genuine jets and time derivative. A pointwise bound on F⁻¹ proves
the uniform frame coercivity used by the constructed Gram inverse.
-/

noncomputable section

namespace EulerTransverseBoundedFrame

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransverseFrameCoordinates EulerTransverseSourceFrame EulerTransverseSourceCoefficientPath
  EulerVolterraConvolution
open scoped BoundedContinuousFunction ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m₀ : Space) (R : U ≃ₗᵢ[ℝ] referencePlane m₀)

/-- Restricting a matrix to the orthonormal reference plane is a contraction. -/
theorem restriction_norm : ‖referenceRestriction m₀ R‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  change ‖A.comp (referenceEmbedding m₀ R)‖ ≤ 1*‖A‖
  exact (opNorm_comp_le A (referenceEmbedding m₀ R)).trans
    (by simpa only [mul_one,one_mul] using
      mul_le_mul_of_nonneg_left (referenceEmbedding_norm m₀ R) (norm_nonneg A))

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The actual source F R⊥, including all its uniformly continuous spatial jets. -/
def coefficient (F : SmoothCoefficientPath K (Space →L[ℝ] Space)) :
    SmoothCoefficientPath K (U →L[ℝ] Space) :=
  SmoothCoefficientPath.map (referenceRestriction m₀ R) F

@[simp] theorem coefficient_apply (F : SmoothCoefficientPath K (Space →L[ℝ] Space))
    (t : K) (x : Space) (v : U) : (coefficient m₀ R F).field t x v = F.field t x (R v : Space) :=
      rfl

/-- The original pointwise source coefficient derivative bound survives without loss. -/
theorem coefficient_derivative_bound (F : SmoothCoefficientPath K (Space →L[ℝ] Space))
    (n : ℕ) (C : ℝ)
    (hF : ∀ t x, ‖iteratedFDeriv ℝ n (F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C)
    (t : K) (x : Space) :
    ‖iteratedFDeriv ℝ n ((coefficient m₀ R F).field t : Space → U →L[ℝ] Space) x‖ ≤ C :=
  SmoothCoefficientPath.map_derivative_bound (referenceRestriction m₀ R) (restriction_norm m₀ R) F
    n C hF t x

/-- The uniform inverse-frame bound gives the precise squared lower frame bound. -/
theorem coefficient_lower (F : SmoothCoefficientPath K (Space →L[ℝ] Space))
    (FInv : K → Space → Space →L[ℝ] Space) (B : ℝ) (hB : 0 < B)
    (hInv : ∀ t x v, FInv t x (F.field t x v) = v)
    (hNorm : ∀ t x, ‖FInv t x‖ ≤ B) (t : K) (x : Space) (v : U) :
    (B⁻¹)^2*‖v‖^2 ≤ ‖(coefficient m₀ R F).field t x v‖^2 := by
  have hn : ‖v‖ ≤ B*‖(coefficient m₀ R F).field t x v‖ := by
    calc
      ‖v‖ = ‖(R v : Space)‖ := (R.norm_map v).symm
      _ = ‖FInv t x (F.field t x (R v : Space))‖ := congrArg norm (hInv t x (R v : Space)).symm
      _ ≤ ‖FInv t x‖*‖F.field t x (R v : Space)‖ := (FInv t x).le_opNorm _
      _ ≤ B*‖(coefficient m₀ R F).field t x v‖ :=
        mul_le_mul_of_nonneg_right (hNorm t x) (norm_nonneg _)
  have hdiv : ‖v‖/B ≤ ‖(coefficient m₀ R F).field t x v‖ :=
    (div_le_iff₀ hB).2 (by simpa only [mul_comm] using hn)
  have hs := (sq_le_sq₀ (div_nonneg (norm_nonneg v) hB.le) (norm_nonneg _)).2 hdiv
  simpa only [div_eq_mul_inv,mul_pow,mul_comm] using hs

section Time

variable (T : ℝ) (hT : 0 ≤ T)
  (F F₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))

/-- The actual source time derivative also commutes with the reference restriction. -/
theorem coefficient_hasDerivWithinAt
    (hF : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
      HasDerivWithinAt (fun s => extendPath T hT F.field s x)
        (extendPath T hT F₁.field t x) (Icc (0 : ℝ) T) t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : Space) :
    HasDerivWithinAt (fun s => extendPath T hT (coefficient m₀ R F).field s x)
      (extendPath T hT (coefficient m₀ R F₁).field t x) (Icc (0 : ℝ) T) t := by
  have hd := (referenceRestriction m₀ R).hasFDerivAt.comp_hasDerivWithinAt t (hF t ht x)
  exact hd

end Time

end EulerTransverseBoundedFrame
