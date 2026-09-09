/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSourceVariationalInverse
public import LeanPool.NavierStokesAndEuler.Euler.MeanStrongInverse
public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryPhysicalSupport

@[expose] public section

/-! The actual strong mean inverse under the manuscript's spatial hypotheses. -/

noncomputable section

namespace EulerMeanSourceInverse

open MeasureTheory Set InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanHarmonic EulerMeanBoundary EulerLiftedPressure EulerTimeLp
  EulerMeanVariationalInverse EulerVolterraConvolution
open scoped NNReal

/-- The constructed source mean inverse has H² solenoidal coordinates and the
original compact-support-producing initial velocity condition. -/
theorem sourceMeanSolver_strong (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (M : Space → Space →L[ℝ] Space) (hM : AEStronglyMeasurable M volume)
    (C : ℝ≥0) (hC : ∀ x, ‖M x‖ ≤ C)
    (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
    (hL : boundaryLocalizationC1 * Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1/4)
    (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be * ‖v‖^2 ≤ ⟪M x v, v⟫_ℝ)
    (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc * ‖v‖^2 ≤ ⟪M x v, v⟫_ℝ)
    (FInv F F₁ F₂ H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (K : ℝ) (hK : 0 ≤ K)
    (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
    (hH : ∀ t z, ⟪H t z, z⟫_ℝ ≤ K*‖z‖^2)
    (hsmall : K*(T^2/2) + Be*T + boundaryLocalizationC2*Bc*r^3*T ≤ 1/2)
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (hF₁ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F₁) (F₂ t) (Icc (0 : ℝ) T) t)
    (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x)
    (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), F t (FInv t x) = x)
    (hF₁₀ : F₁ ⟨0, le_rfl, hT⟩ = coefficientOperator M hM C hC)
    (hODE : ∀ t, F₂ t = -(H t).comp (F t)) (f : TimeLp T L2) :
    Nonempty (StrongMeanEvolution T hT FInv F F₁ (boundaryOperator (scaledCutoff ℓ hℓ)) L
      (sourceMeanSolver T hT ℓ hℓ M hM C hC Be Bc L r hBe hBc hL hr hrquarter
        hext hcore FInv H K hK hF0 hH hsmall f) f) :=
  meanSolver_strong T hT FInv F F₁ F₂ H (coefficientOperator M hM C hC)
    (boundaryOperator (scaledCutoff ℓ hℓ)) L K (effectiveNegativeBound Be Bc r)
    hK (effectiveNegativeBound_nonneg Be Bc r hBe hBc hr) hF0 hH
    (scaled_mean_boundary_lower_bound ℓ hℓ M hM C hC Be Bc L r hBe hBc hL hr hrquarter hext hcore)
    (source_smallness T K Be Bc r hsmall)
    hF hF₁ hInv hRight hF₁₀ hODE
    (fun z _ => boundaryOperator_solenoidal (scaledCutoff ℓ hℓ) z) f

theorem sourceStrong_initial_ae_support (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (L : ℝ) (u f : TimeLp T L2)
    (S : StrongMeanEvolution T hT FInv F F₁ (boundaryOperator (scaledCutoff ℓ hℓ)) L u f) :
    ∀ᵐ x ∂volume, 2 < ‖ℓ • x‖ → (S.velocity 0 : L2) x = 0 := by
  have H := scaledBoundary_multiple_zero_outside ℓ hℓ L (S.label 0 : L2)
  rw [← S.initial_velocity] at H
  exact H

/-- A continuous representative of the actual initial mean velocity is compactly supported. -/
theorem sourceStrong_initial_compact (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (L : ℝ) (u f : TimeLp T L2)
    (S : StrongMeanEvolution T hT FInv F F₁ (boundaryOperator (scaledCutoff ℓ hℓ)) L u f)
    (b : Space → Space) (hb : Continuous b) (hrep : b =ᵐ[volume] (S.velocity 0 : L2)) :
    HasCompactSupport b := by
  apply scaledBoundary_continuous_compact ℓ hℓ L (S.label 0 : L2) b hb
  rw [← S.initial_velocity]
  exact hrep

end EulerMeanSourceInverse
