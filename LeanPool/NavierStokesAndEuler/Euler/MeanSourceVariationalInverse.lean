/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryCoercivity
public import LeanPool.NavierStokesAndEuler.Euler.MeanVariationalInverse

/-!
The mean inverse with the source's actual nonlocal boundary operator.
The boundary lower bound is proved from the spatial hypotheses (5), not an input.
-/

@[expose] public section


noncomputable section

namespace EulerMeanSourceInverse

open MeasureTheory Set InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanHarmonic EulerMeanBoundary EulerLiftedPressure EulerTimeLp
  EulerMeanVariationalInverse EulerTransverseVariationalInverse
open scoped NNReal

/-- Effective negative bound, given by `Be + boundaryLocalizationC2 * Bc * r^3`. -/
def effectiveNegativeBound (Be Bc r : ℝ) : ℝ :=
  Be + boundaryLocalizationC2 * Bc * r^3

theorem effectiveNegativeBound_nonneg (Be Bc r : ℝ)
    (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc) (hr : 0 ≤ r) :
    0 ≤ effectiveNegativeBound Be Bc r := by
  unfold effectiveNegativeBound
  have hc := boundaryLocalizationC2_nonneg
  positivity

theorem source_smallness (T K Be Bc r : ℝ)
    (hsmall : K * (T ^ 2 / 2) + Be * T + boundaryLocalizationC2 * Bc * r ^ 3 * T ≤ 1 / 2) :
    K*(T^2/2) + effectiveNegativeBound Be Bc r * T ≤ 1/2 := by
  calc
    _ = K*(T^2/2) + Be*T + boundaryLocalizationC2*Bc*r^3*T := by
      unfold effectiveNegativeBound
      ring
    _ ≤ _ := hsmall

variable (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ)
  (M : Space → Space →L[ℝ] Space) (hM : AEStronglyMeasurable M volume)
  (C : ℝ≥0) (hC : ∀ x, ‖M x‖ ≤ C)
  (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
  (hL : boundaryLocalizationC1 * Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1 / 4)
  (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be * ‖v‖ ^ 2 ≤ ⟪M x v, v⟫_ℝ)
  (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc * ‖v‖ ^ 2 ≤ ⟪M x v, v⟫_ℝ)
  (FInv H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (K : ℝ) (hK : 0 ≤ K)
  (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t z, ⟪H t z, z⟫_ℝ ≤ K * ‖z‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) + Be * T + boundaryLocalizationC2 * Bc * r ^ 3 * T ≤ 1 / 2)

/-- This is the actual Lax–Milgram mean inverse, with spatial coercivity discharged. -/
def sourceMeanSolver : TimeLp T L2 →L[ℝ] meanDerivatives T hT FInv :=
  meanSolver T hT FInv H (coefficientOperator M hM C hC)
    (boundaryOperator (scaledCutoff ℓ hℓ)) L K (effectiveNegativeBound Be Bc r)
    hK (effectiveNegativeBound_nonneg Be Bc r hBe hBc hr) hF0 hH
    (scaled_mean_boundary_lower_bound ℓ hℓ M hM C hC Be Bc L r hBe hBc hL hr hrquarter hext hcore)
    (source_smallness T K Be Bc r hsmall)

theorem sourceMeanSolver_norm (f : TimeLp T L2) :
    ‖sourceMeanSolver T hT ℓ hℓ M hM C hC Be Bc L r hBe hBc hL hr hrquarter
      hext hcore FInv H K hK hF0 hH hsmall f‖ ≤ 2*T*‖f‖ :=
  meanSolver_norm T hT FInv H (coefficientOperator M hM C hC)
    (boundaryOperator (scaledCutoff ℓ hℓ)) L K (effectiveNegativeBound Be Bc r)
    hK (effectiveNegativeBound_nonneg Be Bc r hBe hBc hr) hF0 hH
    (scaled_mean_boundary_lower_bound ℓ hℓ M hM C hC Be Bc L r hBe hBc hL hr hrquarter hext hcore)
    (source_smallness T K Be Bc r hsmall) f

/-- The literal mean weak equation, retaining both original initial boundary terms. -/
theorem sourceMeanSolver_weak (f : TimeLp T L2) (v : meanDerivatives T hT FInv) :
    let u := sourceMeanSolver T hT ℓ hℓ M hM C hC Be Bc L r hBe hBc hL hr hrquarter
      hext hcore FInv H K hK hF0 hH hsmall f
    ⟪(u : TimeLp T L2), (v : TimeLp T L2)⟫_ℝ -
      ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u), meanPrimitive T hT FInv v⟫_ℝ +
      ⟪coefficientOperator M hM C hC (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ +
      L * ⟪boundaryOperator (scaledCutoff ℓ hℓ) (meanTrace T hT FInv u),
        meanTrace T hT FInv v⟫_ℝ = -⟪f, meanPrimitive T hT FInv v⟫_ℝ :=
  meanSolver_weak T hT FInv H (coefficientOperator M hM C hC)
    (boundaryOperator (scaledCutoff ℓ hℓ)) L K (effectiveNegativeBound Be Bc r)
    hK (effectiveNegativeBound_nonneg Be Bc r hBe hBc hr) hF0 hH
    (scaled_mean_boundary_lower_bound ℓ hℓ M hM C hC Be Bc L r hBe hBc hL hr hrquarter hext hcore)
    (source_smallness T K Be Bc r hsmall) f v

include hK hF0 hH hsmall hBe hBc hL hr hrquarter hext hcore in
/-- Existence and uniqueness from the actual source spatial and time assumptions. -/
theorem existsUnique_source_mean_weak_solution (f : TimeLp T L2) :
    ∃! u : meanDerivatives T hT FInv, ∀ v : meanDerivatives T hT FInv,
      ⟪(u : TimeLp T L2), (v : TimeLp T L2)⟫_ℝ -
        ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u), meanPrimitive T hT FInv v⟫_ℝ +
        ⟪coefficientOperator M hM C hC (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ +
        L * ⟪boundaryOperator (scaledCutoff ℓ hℓ) (meanTrace T hT FInv u),
          meanTrace T hT FInv v⟫_ℝ = -⟪f, meanPrimitive T hT FInv v⟫_ℝ :=
  existsUnique_mean_weak_solution T hT FInv H (coefficientOperator M hM C hC)
    (boundaryOperator (scaledCutoff ℓ hℓ)) L K (effectiveNegativeBound Be Bc r)
    hK (effectiveNegativeBound_nonneg Be Bc r hBe hBc hr) hF0 hH
    (scaled_mean_boundary_lower_bound ℓ hℓ M hM C hC Be Bc L r hBe hBc hL hr hrquarter hext hcore)
    (source_smallness T K Be Bc r hsmall) f

end EulerMeanSourceInverse
