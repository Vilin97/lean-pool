/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Qian Tang
-/

/- Copyright (c) 2026 Qian Tang; the RCLike extension is adapted from
https://github.com/dtq1997/zeta2-zeta3-linear-independence at
669c92bf7a3728e0de9ad80c373bc29fb5ca3d58 (Apache-2.0). -/
module
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Andréief's identity over real or complex scalars

The RCLike formulation shares one proof between the real Zeta5 determinant
and the complex Zeta32 contour determinant. The original real API is retained below.
The real proof is from mo271/Zeta5 by Moritz Firsching; the scalar generalization
is from Qian Tang's Zeta32 development, with its full attribution in `LeanPool/Zeta32.lean`.
-/

public section

open MeasureTheory Finset Equiv

namespace Zeta5Irrational.AndreiefGeneral

variable {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The coordinate permutation `x ↦ (i ↦ x (τ i))` as a measurable equivalence. -/
noncomputable def permEquiv (τ : Perm (Fin n)) : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
  MeasurableEquiv.arrowCongr' τ.symm (MeasurableEquiv.refl ℝ)

lemma permEquiv_apply (τ : Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    permEquiv τ x i = x (τ i) := by
  simp [permEquiv, MeasurableEquiv.arrowCongr', Equiv.arrowCongr']

lemma measurePreserving_permEquiv (τ : Perm (Fin n)) :
    MeasurePreserving (permEquiv τ) (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n =>
      μ) :=
  measurePreserving_arrowCongr' (fun _ : Fin n => μ) (fun _ : Fin n => μ) τ.symm
    (MeasurableEquiv.refl ℝ)
    (fun _ => ⟨(MeasurableEquiv.refl ℝ).measurable, Measure.map_id⟩)

/-- The basic integral `I(ρ) = ∫ ∏ᵢ f (ρ i) (xᵢ) g i (xᵢ)`. -/
noncomputable def andreiefI (f g : Fin n → ℝ → 𝕜) (ρ : Perm (Fin n)) : 𝕜 :=
  ∫ x : Fin n → ℝ, ∏ i, f (ρ i) (x i) * g i (x i) ∂(Measure.pi fun _ : Fin n => μ)

lemma integral_prod_prod_eq (f g : Fin n → ℝ → 𝕜) (σ τ : Perm (Fin n)) :
    ∫ x : Fin n → ℝ, (∏ i, f (σ i) (x i)) * (∏ i, g (τ i) (x i)) ∂(Measure.pi fun _ : Fin n => μ) =
      andreiefI (μ := μ) f g (σ * τ⁻¹) := by
  unfold andreiefI
  have hpt : ∀ x : Fin n → ℝ, (∏ i, f (σ i) (x i)) * (∏ i, g (τ i) (x i)) =
      (fun y : Fin n → ℝ => ∏ k, f ((σ * τ⁻¹) k) (y k) * g k (y k)) (permEquiv τ⁻¹ x) := by
    intro x
    simp only [permEquiv_apply, ← Finset.prod_mul_distrib]
    rw [← Equiv.prod_comp τ (fun k => f ((σ * τ⁻¹) k) (x (τ⁻¹ k)) * g k (x (τ⁻¹ k)))]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [Perm.mul_apply]
  simp_rw [hpt]
  exact (measurePreserving_permEquiv (μ := μ) τ⁻¹).integral_comp (permEquiv τ⁻¹).measurableEmbedding
    (fun y : Fin n → ℝ => ∏ k, f ((σ * τ⁻¹) k) (y k) * g k (y k))

/-- **Andréief's identity**. -/
theorem andreief (f g : Fin n → ℝ → 𝕜) (hfg : ∀ i j, Integrable (fun x => f i x * g j x) μ) :
    (Matrix.of fun i j => ∫ x, f i x * g j x ∂μ).det =
      (1 / (n.factorial : 𝕜)) * ∫ x : Fin n → ℝ,
        (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det
          ∂(Measure.pi fun _ : Fin n => μ) := by
  -- the left-hand side as a sum over permutations of basic integrals
  have hL : (Matrix.of fun i j => ∫ x, f i x * g j x ∂μ).det =
      ∑ ρ : Perm (Fin n), (Perm.sign ρ : 𝕜) * andreiefI (μ := μ) f g ρ := by
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [Matrix.of_apply, andreiefI]
    rw [integral_fintype_prod_eq_prod (fun i x => f (ρ i) x * g i x)]
  -- the right-hand side
  have hint : ∀ σ τ : Perm (Fin n), Integrable
      (fun x : Fin n → ℝ => (Perm.sign σ : 𝕜) * (Perm.sign τ : 𝕜) *
        ((∏ i, f (σ i) (x i)) * (∏ i, g (τ i) (x i)))) (Measure.pi fun _ : Fin n => μ) := by
    intro σ τ
    have : (fun x : Fin n → ℝ => (∏ i, f (σ i) (x i)) * (∏ i, g (τ i) (x i))) =
        fun x => ∏ i, (fun i y => f (σ i) y * g (τ i) y) i (x i) := by
      funext x; simp only [← Finset.prod_mul_distrib]
    refine Integrable.const_mul ?_ _
    rw [this]
    exact Integrable.fintype_prod fun i => hfg (σ i) (τ i)
  have hR : ∫ x : Fin n → ℝ,
      (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det
        ∂(Measure.pi fun _ : Fin n => μ) =
      ∑ τ : Perm (Fin n), ∑ σ : Perm (Fin n), (Perm.sign σ : 𝕜) * (Perm.sign τ : 𝕜) *
        andreiefI (μ := μ) f g (σ * τ⁻¹) := by
    have hpt : ∀ x : Fin n → ℝ,
        (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det =
        ∑ τ : Perm (Fin n), ∑ σ : Perm (Fin n), (Perm.sign σ : 𝕜) * (Perm.sign τ : 𝕜) *
          ((∏ i, f (σ i) (x i)) * (∏ i, g (τ i) (x i))) := by
      intro x
      rw [Matrix.det_apply', Matrix.det_apply', Finset.sum_mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun σ _ => ?_
      simp only [Matrix.of_apply]
      ring
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun τ _ => integrable_finsetSum _ (fun σ _ => hint σ τ))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [integral_finsetSum _ (fun σ _ => hint σ τ)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [integral_const_mul, integral_prod_prod_eq]
  -- each inner sum is the left-hand side
  have hsign : ∀ σ τ : Perm (Fin n),
      (Perm.sign (σ * τ⁻¹) : 𝕜) = (Perm.sign σ : 𝕜) * (Perm.sign τ : 𝕜) := by
    intro σ τ
    rw [Perm.sign_mul, Perm.sign_inv]
    push_cast
    ring
  have hinner : ∀ τ : Perm (Fin n), ∑ σ : Perm (Fin n), (Perm.sign σ : 𝕜) * (Perm.sign τ : 𝕜) *
      andreiefI (μ := μ) f g (σ * τ⁻¹) =
      ∑ ρ : Perm (Fin n), (Perm.sign ρ : 𝕜) * andreiefI (μ := μ) f g ρ := by
    intro τ
    conv_rhs => rw [← Equiv.sum_comp (Equiv.mulRight τ⁻¹)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Equiv.coe_mulRight]
    rw [hsign]
  rw [hR]
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, hL]
  have : (n.factorial : 𝕜) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp
  try ring

end Zeta5Irrational.AndreiefGeneral


namespace Zeta5Irrational

variable {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]

/-- Coordinate permutation, retained under the original real API. -/
noncomputable abbrev permEquiv (τ : Perm (Fin n)) := AndreiefGeneral.permEquiv τ

lemma permEquiv_apply (τ : Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    permEquiv τ x i = x (τ i) := AndreiefGeneral.permEquiv_apply τ x i

lemma measurePreserving_permEquiv (τ : Perm (Fin n)) :
    MeasurePreserving (permEquiv τ) (Measure.pi fun _ : Fin n => μ)
      (Measure.pi fun _ : Fin n => μ) := AndreiefGeneral.measurePreserving_permEquiv τ

/-- The real basic integral in Andréief's identity. -/
noncomputable abbrev andreiefI (f g : Fin n → ℝ → ℝ) (ρ : Perm (Fin n)) : ℝ :=
  AndreiefGeneral.andreiefI (μ := μ) f g ρ

lemma integral_prod_prod_eq (f g : Fin n → ℝ → ℝ) (σ τ : Perm (Fin n)) :
    ∫ x : Fin n → ℝ,
        (∏ i, f (σ i) (x i)) * (∏ i, g (τ i) (x i)) ∂(Measure.pi fun _ : Fin n => μ) =
      andreiefI (μ := μ) f g (σ * τ⁻¹) := AndreiefGeneral.integral_prod_prod_eq f g σ τ

/-- Andréief's identity, with the original real-valued statement. -/
theorem andreief (f g : Fin n → ℝ → ℝ) (hfg : ∀ i j, Integrable (fun x => f i x * g j x) μ) :
    (Matrix.of fun i j => ∫ x, f i x * g j x ∂μ).det =
      (1 / (n.factorial : ℝ)) * ∫ x : Fin n → ℝ,
        (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det
          ∂(Measure.pi fun _ : Fin n => μ) := AndreiefGeneral.andreief f g hfg

end Zeta5Irrational

end
