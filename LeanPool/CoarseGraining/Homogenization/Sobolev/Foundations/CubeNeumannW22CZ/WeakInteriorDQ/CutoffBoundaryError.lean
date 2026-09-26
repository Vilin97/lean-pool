/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.CutoffTail

/-! # Cutoff Boundary Error -/

@[expose] public section

namespace Homogenization

open scoped ENNReal Manifold

noncomputable section

/-- The coordinate collar where the `i`-direction derivative of an inner cube
cutoff may be nonzero. -/
def cubeCoordInnerCollar {d : ℕ} (Q : TriadicCube d) (ρ : ℝ) (i : Fin d) :
    Set (Vec d) :=
  {x | ρ * cubeRadius Q ≤ |x i - cubeCenter Q i|}

theorem measurableSet_cubeCoordInnerCollar {d : ℕ}
    (Q : TriadicCube d) (ρ : ℝ) (i : Fin d) :
    MeasurableSet (cubeCoordInnerCollar Q ρ i) := by
  dsimp [cubeCoordInnerCollar]
  exact (isClosed_le continuous_const
    (continuous_abs.comp ((continuous_apply i).sub continuous_const))).measurableSet

theorem support_canonicalFun_fderiv_apply_basisVec_subset_cubeCoordInnerCollar {d : ℕ}
    (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂)
    (i : Fin d) :
    Function.support
        (fun x : Vec d =>
          (fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i)) ⊆
      cubeCoordInnerCollar Q ρ₁ i := by
  simpa [cubeCoordInnerCollar] using
    QuantitativeCubeCutoff.support_fderiv_canonicalFun_apply_basisVec_subset_coord_abs_ge_inner
        Q hρ₁ hρ₁₂ i

theorem support_canonicalFun_coordDeriv_mul_subset_cubeCoordInnerCollar {d : ℕ}
    (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂)
    (i : Fin d) (ψ : Vec d → ℝ) :
    Function.support
        (fun x : Vec d =>
          (fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i) *
            ψ x) ⊆
      cubeCoordInnerCollar Q ρ₁ i :=
  (Function.support_mul_subset_left _ _).trans
    (support_canonicalFun_fderiv_apply_basisVec_subset_cubeCoordInnerCollar
      Q hρ₁ hρ₁₂ i)

private theorem norm_basisVec {d : ℕ} (i : Fin d) : ‖basisVec i‖ = (1 : ℝ) := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).2 ?_
    intro j
    by_cases hji : j = i
    · subst hji
      simp [basisVec]
    · simp [basisVec, hji]
  · have hi : ‖basisVec i i‖ ≤ ‖basisVec i‖ := norm_le_pi_norm (basisVec i) i
    simpa [basisVec] using hi

private theorem quantitativeCubeCutoffGradientConst_nonneg (d : ℕ) :
    0 ≤ quantitativeCubeCutoffGradientConst d := by
  dsimp [quantitativeCubeCutoffGradientConst]
  nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ (d : ℝ)),
    smoothTransitionProfile.derivBound_nonneg]

/-- If a smooth test is at most `B` times the cutoff transition width on the
coordinate collar, then the cutoff-derivative error is uniformly bounded. -/
theorem norm_canonicalFun_coordDeriv_mul_le_of_collar_bound {d : ℕ}
    (Q : TriadicCube d) {ρ₁ ρ₂ B : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂)
    (hB : 0 ≤ B) (i : Fin d) (ψ : Vec d → ℝ)
    (hψ :
      ∀ x ∈ cubeCoordInnerCollar Q ρ₁ i,
        ‖ψ x‖ ≤ B * ((ρ₂ - ρ₁) * cubeRadius Q)) :
    ∀ x : Vec d,
      ‖(fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i) *
          ψ x‖ ≤
        B * quantitativeCubeCutoffGradientConst d := by
  intro x
  by_cases hzero :
      (fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i) = 0
  · simp [hzero, mul_nonneg hB (quantitativeCubeCutoffGradientConst_nonneg d)]
  · have hx_collar :
        x ∈ cubeCoordInnerCollar Q ρ₁ i :=
      support_canonicalFun_fderiv_apply_basisVec_subset_cubeCoordInnerCollar
        Q hρ₁ hρ₁₂ i hzero
    have hgap_pos : 0 < (ρ₂ - ρ₁) * cubeRadius Q :=
      mul_pos (sub_pos.mpr hρ₁₂) (cubeRadius_pos Q)
    have hgap_nonneg : 0 ≤ (ρ₂ - ρ₁) * cubeRadius Q := le_of_lt hgap_pos
    have hconst_nonneg : 0 ≤ quantitativeCubeCutoffGradientConst d :=
      quantitativeCubeCutoffGradientConst_nonneg d
    have hcoord :
        ‖(fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i)‖ ≤
          quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q) := by
      calc
        ‖(fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i)‖
            ≤ ‖fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x‖ *
                ‖basisVec i‖ := by
              exact (fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x).le_opNorm
                (basisVec i)
        _ = ‖fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x‖ := by
              simp [norm_basisVec]
        _ ≤ quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q) := by
              let η : QuantitativeCubeCutoff Q ρ₁ ρ₂ :=
                QuantitativeCubeCutoff.canonical Q ρ₁ ρ₂ hρ₁ hρ₁₂
              simpa [η, QuantitativeCubeCutoff.canonical] using η.gradient_bound x
    calc
      ‖(fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i) *
          ψ x‖
          =
        ‖(fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i)‖ *
          ‖ψ x‖ := norm_mul _ _
      _ ≤
          (quantitativeCubeCutoffGradientConst d /
              ((ρ₂ - ρ₁) * cubeRadius Q)) *
            (B * ((ρ₂ - ρ₁) * cubeRadius Q)) := by
        exact mul_le_mul hcoord (hψ x hx_collar)
          (norm_nonneg (ψ x))
          (div_nonneg hconst_nonneg hgap_nonneg)
      _ = B * quantitativeCubeCutoffGradientConst d := by
        rw [show
          (quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q)) *
              (B * ((ρ₂ - ρ₁) * cubeRadius Q)) =
            B * ((quantitativeCubeCutoffGradientConst d /
              ((ρ₂ - ρ₁) * cubeRadius Q)) * ((ρ₂ - ρ₁) * cubeRadius Q)) by
          ring]
        rw [div_mul_cancel₀ _ hgap_pos.ne']

/-- `L²` version of `norm_canonicalFun_coordDeriv_mul_le_of_collar_bound`,
localized to the coordinate collar where the derivative can be nonzero. -/
theorem eLpNorm_canonicalFun_coordDeriv_mul_le_of_collar_bound {d : ℕ}
    {U : Set (Vec d)} (Q : TriadicCube d) {ρ₁ ρ₂ B : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) (hB : 0 ≤ B)
    (i : Fin d) (ψ : Vec d → ℝ)
    (hψ :
      ∀ x ∈ cubeCoordInnerCollar Q ρ₁ i,
        ‖ψ x‖ ≤ B * ((ρ₂ - ρ₁) * cubeRadius Q)) :
    MeasureTheory.eLpNorm
        (fun x : Vec d =>
          (fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i) *
            ψ x)
        2 (volumeMeasureOn U) ≤
      ENNReal.ofReal (B * quantitativeCubeCutoffGradientConst d) *
        (volumeMeasureOn U (cubeCoordInnerCollar Q ρ₁ i)) ^
          (1 / (2 : ENNReal).toReal) := by
  let F : Vec d → ℝ :=
    fun x =>
      (fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i) *
        ψ x
  have hC_nonneg : 0 ≤ B * quantitativeCubeCutoffGradientConst d :=
    mul_nonneg hB (quantitativeCubeCutoffGradientConst_nonneg d)
  have hdist : ∀ x : Vec d, dist (F x) 0 ≤ B * quantitativeCubeCutoffGradientConst d := by
    intro x
    simpa [F, dist_eq_norm] using
      norm_canonicalFun_coordDeriv_mul_le_of_collar_bound
        Q hρ₁ hρ₁₂ hB i ψ hψ x
  have hsupport :
      Function.support F ⊆ cubeCoordInnerCollar Q ρ₁ i := by
    simpa [F] using
      support_canonicalFun_coordDeriv_mul_subset_cubeCoordInnerCollar
        Q hρ₁ hρ₁₂ i ψ
  have hzero_support :
      Function.support (0 : Vec d → ℝ) ⊆ cubeCoordInnerCollar Q ρ₁ i := by
    simp
  have hmain :=
    MeasureTheory.eLpNorm_sub_le_of_dist_bdd
      (μ := volumeMeasureOn U) (p := (2 : ENNReal))
      (s := cubeCoordInnerCollar Q ρ₁ i)
      (by norm_num : (2 : ENNReal) ≠ ∞)
      (measurableSet_cubeCoordInnerCollar Q ρ₁ i)
      hC_nonneg hdist hsupport hzero_support
  have hsub : F - (fun _ : Vec d => (0 : ℝ)) = F := by
    funext x
    simp
  rw [hsub] at hmain
  simpa [F] using hmain

end
end Homogenization
