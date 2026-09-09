/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanStrongEquation

@[expose] public section

/-!
# Strong regularity of the genuinely constructed mean inverse

The result applies the strong-coordinate theorem to the actual coercive solve.
The input boundary inequality still has to be supplied by the concrete cutoff
operator and harmonic localization. No solution, momentum equation, acceleration,
or initial velocity condition is included in the hypotheses.
-/

noncomputable section

namespace EulerMeanVariationalInverse

open Set InnerProductSpace EulerTimeLp EulerTerminalTimePrimitive EulerMeanSolenoidal
  EulerVolterraConvolution

/-- The actual bounded mean solution operator produces a strong mean evolution
with the literal projected equation and original initial velocity condition. -/
theorem meanSolver_strong (T : ℝ) (hT : 0 ≤ T)
    (FInv F F₁ F₂ H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (M0 A : L2 →L[ℝ] L2) (L K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hFInv₀ : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
    (hH : ∀ t z, ⟪H t z, z⟫_ℝ ≤ K*‖z‖^2)
    (hboundary : ∀ z : L2, z ∈ solenoidalSpace →
      -B*‖z‖^2 ≤ ⟪M0 z, z⟫_ℝ+L*⟪A z, z⟫_ℝ)
    (hsmall : K*(T^2/2)+B*T ≤ 1/2)
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (hF₁ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F₁) (F₂ t) (Icc (0 : ℝ) T) t)
    (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x)
    (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), F t (FInv t x) = x)
    (hF₁₀ : F₁ ⟨0, le_rfl, hT⟩ = M0)
    (hODE : ∀ t, F₂ t = -(H t).comp (F t))
    (hAσ : ∀ z : L2, z ∈ solenoidalSpace → A z ∈ solenoidalSpace)
    (f : TimeLp T L2) :
    Nonempty (StrongMeanEvolution T hT FInv F F₁ A L
      (meanSolver T hT FInv H M0 A L K B hK hB hFInv₀ hH hboundary hsmall f) f) :=
  meanWeakSolution_strong T hT FInv F F₁ F₂ H M0 A L hF hF₁ hInv hRight hFInv₀ hF₁₀ hODE hAσ
    (meanSolver T hT FInv H M0 A L K B hK hB hFInv₀ hH hboundary hsmall f) f
    (meanSolver_weak T hT FInv H M0 A L K B hK hB hFInv₀ hH hboundary hsmall f)

end EulerMeanVariationalInverse
