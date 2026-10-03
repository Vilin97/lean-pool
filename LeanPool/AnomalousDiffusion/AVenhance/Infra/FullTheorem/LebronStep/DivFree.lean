/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.Drift
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsDivFree
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVelContinuous

/-! # Divergence-freeness of finite stream velocities (Lemma r.LeBron, step (b))

The `IsDivFree` (distributional divergence on each slice) holds for `streamVel Ψ` with `Ψ`
admissible: the classical divergence vanishes (`streamVel_vecDiv_eq_zero`) and the velocity is
smooth, so integration by parts against compactly supported smooth tests gives zero. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- A time-indexed family of `C¹` fields with vanishing classical divergence is `IsDivFree`. -/
theorem isDivFree_of_vecDiv_zero {b : ℝ → Vec 2 → Vec 2}
    (hb : ∀ t, ∀ i : Fin 2, ContDiff ℝ 1 (fun x => b t x i))
    (hdiv : ∀ t x, vecDiv (b t) x = 0) : IsDivFree b := by
  intro t _ φ hφ hφc
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφ' : ∀ i : Fin 2, Continuous (fun x => fderiv ℝ φ x (basisVec i)) := fun i =>
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ'c : ∀ i : Fin 2, HasCompactSupport (fun x => fderiv ℝ φ x (basisVec i)) := fun i =>
    hφc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hint : ∀ i : Fin 2, ∫ x, b t x i * fderiv ℝ φ x (basisVec i) =
      -∫ x, fderiv ℝ (fun y => b t y i) x (basisVec i) * φ x := by
    intro i
    have hbc : Continuous (fun x => b t x i) := (hb t i).continuous
    have hbd : Differentiable ℝ (fun x => b t x i) := (hb t i).differentiable (by simp)
    have hbd' : Continuous (fun x => fderiv ℝ (fun y => b t y i) x (basisVec i)) :=
      ((hb t i).continuous_fderiv (by simp)).clm_apply continuous_const
    have h1 : Integrable (fun x => fderiv ℝ (fun y => b t y i) x (basisVec i) * φ x) volume :=
      (hbd'.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    have h2 : Integrable (fun x => b t x i * fderiv ℝ φ x (basisVec i)) volume :=
      (hbc.mul (hφ' i)).integrable_of_hasCompactSupport (hφ'c i).mul_left
    have h3 : Integrable (fun x => b t x i * φ x) volume :=
      (hbc.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun x => b t x i) (g := φ) (v := basisVec i) h1 h2 h3 (fun x _ => hbd x)
      (fun x _ => hφd x)
  have hint2 : ∀ i : Fin 2, Integrable (fun x => b t x i * fderiv ℝ φ x (basisVec i)) volume :=
    fun i => ((hb t i).continuous.mul (hφ' i)).integrable_of_hasCompactSupport
      (hφ'c i).mul_left
  have hint1 : ∀ i : Fin 2,
      Integrable (fun x => fderiv ℝ (fun y => b t y i) x (basisVec i) * φ x) volume := fun i =>
    ((((hb t i).continuous_fderiv (by simp)).clm_apply continuous_const).mul
      hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  have hvec : (fun x => vecDot (b t x) (spaceGrad φ x)) =
      fun x => ∑ i : Fin 2, b t x i * fderiv ℝ φ x (basisVec i) := by
    funext x; simp [vecDot, spaceGrad]
  have hdz : (fun x => ∑ i : Fin 2, fderiv ℝ (fun y => b t y i) x (basisVec i) * φ x) =
      fun _ => (0 : ℝ) := by
    funext x
    have := hdiv t x
    simp only [vecDiv, spaceGrad] at this
    rw [← Finset.sum_mul, this, zero_mul]
  rw [hvec, integral_finsetSum _ (fun i _ => hint2 i)]
  simp_rw [hint]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hint1 i), hdz]
  simp

/-- The velocity of an admissible stream is `IsDivFree`. -/
theorem isDivFree_streamVel {Ψ : ℝ → Vec 2 → ℝ} (hΨ : IsAdmissibleStream Ψ) :
    IsDivFree (streamVel Ψ) := by
  refine isDivFree_of_vecDiv_zero ?_ (Classical.streamVel_vecDiv_eq_zero Ψ hΨ)
  intro t i
  have hs := (Classical.streamVel_smoothPeriodic Ψ hΨ).smooth
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) :=
    contDiff_const.prodMk contDiff_id
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => streamVel Ψ t x) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => Function.uncurry (streamVel Ψ) (t, x))
    exact hs.comp hmap
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => streamVel Ψ t x i) :=
    (contDiff_pi.1 h1) i
  exact h2.of_le (by exact_mod_cast le_top)

end AVenhance.Infra.FullTheorem
