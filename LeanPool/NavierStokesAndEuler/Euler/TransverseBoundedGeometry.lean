/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseBoundedFrame

/-!
# Source geometry for the bounded frame and normal

The literal fields Q=F R⊥ and m=F⁻ᵀm₀ satisfy the tangency, range, strain,
and quantitative normal lower bounds used by the actual transverse solver.
Only the original deformation and its genuine pointwise inverse are inputs.
-/

@[expose] public section


noncomputable section

namespace EulerTransverseBoundedFrame

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerTransverseFrameCoordinates
open scoped BoundedContinuousFunction ContDiff

variable (m₀ : Space)

/-- The fixed linear operation sending F⁻¹ to F⁻ᵀm₀. -/
def normalMap : (Space →L[ℝ] Space) →L[ℝ] Space :=
  (ContinuousLinearMap.apply ℝ Space m₀).comp
    (ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap :
      (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space))

@[simp] theorem normalMap_apply (A : Space →L[ℝ] Space) : normalMap m₀ A = A.adjoint m₀ := rfl

theorem normalMap_norm (hm₀ : ‖m₀‖ = 1) : ‖normalMap m₀‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  change ‖A.adjoint m₀‖ ≤ 1*‖A‖
  have h := A.adjoint.le_opNorm m₀
  simpa only [hm₀,mul_one,one_mul,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.norm_map] using h

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The normal has the genuine spatial jets inherited from the inverse deformation. -/
def normalCoefficient (FInv : SmoothCoefficientPath K (Space →L[ℝ] Space)) :
    SmoothCoefficientPath K Space := SmoothCoefficientPath.map (normalMap m₀) FInv

@[simp] theorem normalCoefficient_apply (FInv : SmoothCoefficientPath K (Space →L[ℝ] Space))
    (t : K) (x : Space) : (normalCoefficient m₀ FInv).field t x = (FInv.field t x).adjoint m₀ := rfl

theorem normalCoefficient_derivative_bound (FInv : SmoothCoefficientPath K (Space →L[ℝ] Space))
    (hm₀ : ‖m₀‖ = 1) (n : ℕ) (C : ℝ)
    (hF : ∀ t x, ‖iteratedFDeriv ℝ n (FInv.field t : Space → Space →L[ℝ] Space) x‖ ≤ C)
    (t : K) (x : Space) :
    ‖iteratedFDeriv ℝ n ((normalCoefficient m₀ FInv).field t : Space → Space) x‖ ≤ C :=
  SmoothCoefficientPath.map_derivative_bound (normalMap m₀) (normalMap_norm m₀ hm₀) FInv n C hF t x

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (R : U ≃ₗᵢ[ℝ] referencePlane m₀)
  (F FInv : SmoothCoefficientPath K (Space →L[ℝ] Space))

theorem coefficient_tangent
    (hInv : ∀ t x v, FInv.field t x (F.field t x v) = v) (t : K) (x : Space) (v : U) :
    ⟪(normalCoefficient m₀ FInv).field t x,(coefficient m₀ R F).field t x v⟫_ℝ = 0 := by
  rw [normalCoefficient_apply,coefficient_apply,adjoint_inner_left,hInv]
  have h := (R v).property
  rwa [Submodule.mem_orthogonal_singleton_iff_inner_right] at h

theorem coefficient_range
    (hInv : ∀ t x v, F.field t x (FInv.field t x v) = v)
    (t : K) (x η : Space) (hη : ⟪(normalCoefficient m₀ FInv).field t x, η⟫_ℝ = 0) :
    ∃ v, (coefficient m₀ R F).field t x v = η := by
  have hmem : FInv.field t x η ∈ referencePlane m₀ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simpa only [normalCoefficient_apply,adjoint_inner_left] using hη
  let z : referencePlane m₀ := ⟨FInv.field t x η,hmem⟩
  refine ⟨R.symm z,?_⟩
  rw [coefficient_apply,R.apply_symm_apply]
  exact hInv t x η

theorem coefficient_strain (F₁ M : SmoothCoefficientPath K (Space →L[ℝ] Space))
    (hFlow : ∀ t x v, F₁.field t x v = M.field t x (F.field t x v)) (t : K) (x : Space) :
    (coefficient m₀ R F₁).field t x = (M.field t x).comp ((coefficient m₀ R F).field t x) := by
  apply ContinuousLinearMap.ext
  intro v
  exact hFlow t x (R v : Space)

/-- The source inverse identity also prevents degeneration of the normal. -/
theorem normalCoefficient_lower (hm₀ : ‖m₀‖ = 1)
    (hInv : ∀ t x v, FInv.field t x (F.field t x v) = v)
    (B : ℝ) (hB : 0 < B) (hFnorm : ∀ t x, ‖F.field t x‖ ≤ B) (t : K) (x : Space) :
    (B⁻¹)^2 ≤ ‖(normalCoefficient m₀ FInv).field t x‖^2 := by
  have he : (F.field t x).adjoint ((normalCoefficient m₀ FInv).field t x) = m₀ := by
    apply ext_inner_right ℝ
    intro v
    rw [adjoint_inner_left,normalCoefficient_apply,adjoint_inner_left,hInv]
  have hnorm : ‖(F.field t x).adjoint‖ = ‖F.field t x‖ :=
    ContinuousLinearMap.adjoint.norm_map (F.field t x)
  have hn : 1 ≤ B*‖(normalCoefficient m₀ FInv).field t x‖ := by
    calc
      1 = ‖(F.field t x).adjoint ((normalCoefficient m₀ FInv).field t x)‖ := by rw [he,hm₀]
      _ ≤ ‖(F.field t x).adjoint‖*‖(normalCoefficient m₀ FInv).field t x‖ :=
        (F.field t x).adjoint.le_opNorm _
      _ ≤ B*‖(normalCoefficient m₀ FInv).field t x‖ := by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_right (hFnorm t x) (norm_nonneg _)
  have hd : B⁻¹ ≤ ‖(normalCoefficient m₀ FInv).field t x‖ := by
    rw [← one_div]
    exact (div_le_iff₀ hB).2 (by simpa only [mul_comm] using hn)
  exact (sq_le_sq₀ (inv_nonneg.mpr hB.le) (norm_nonneg _)).2 hd

end EulerTransverseBoundedFrame
