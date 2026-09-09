/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPeriodicPotential

/-! The actual high/corrector pair, with all potential regularity derived from the high field. -/

@[expose] public section


noncomputable section

namespace EulerPacketConstructedPiola

open EulerSmoothLimit EulerPacketPiola EulerPacketPeriodicPotential EulerPacketCrossProduct
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
  Set MeasureTheory InnerProductSpace
open scoped ContDiff

/-- Normal, given by `(F y).symm.toContinuousLinearMap.adjoint m₀`. -/
def normal (F : Space → Space ≃L[ℝ] Space) (m₀ : Space) (y : Space) : Space :=
  (F y).symm.toContinuousLinearMap.adjoint m₀

theorem normal_ne_zero (F : Space → Space ≃L[ℝ] Space) (m₀ : Space) (hm₀ : m₀ ≠ 0)
    (y : Space) : normal F m₀ y ≠ 0 := by
  intro hz
  have he := congrArg (fun v : Space => ⟪v,F y m₀⟫_ℝ) hz
  change ⟪(F y).symm.toContinuousLinearMap.adjoint m₀,F y m₀⟫_ℝ = ⟪0,F y m₀⟫_ℝ at he
  rw [ContinuousLinearMap.adjoint_inner_left] at he
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
      inner_zero_left] at he
  exact hm₀ (inner_self_eq_zero.mp he)

variable (P : ℝ) [Fact (0 < P)]

/-- Corrector, given by `liftedSlowCurl P F (field P (normal F m₀) A)`. -/
def corrector (F : Space → Space ≃L[ℝ] Space) (m₀ : Space) (A : LiftDomain P → Space) :
    LiftDomain P → Space := liftedSlowCurl P F (field P (normal F m₀) A)

variable (κ : ℝ) (m₀ : Space) (Ξ : Space → Space) (A : LiftDomain P → Space)
  (hΞ : ContDiff ℝ ∞ Ξ) (hAc : HasCompactSupport A)
  (F : Space → Space ≃L[ℝ] Space)
  (hN : ContDiff ℝ ∞ (normal F m₀)) (hm₀ : m₀ ≠ 0)
  (hA : ∀ x, ContDiff ℝ ∞ (localFieldLift P A x))
  (hmean : ∀ y, (∫ θ in (0 : ℝ)..P, A (y, (θ : AddCircle P))) = 0)

/-- Pair Lᵖ, constructed using `piolaPairLp`. -/
def pairLp (p : ℕ) : LiftL2 P :=
  piolaPairLp P κ m₀ Ξ (field P (normal F m₀) A) hΞ
    (field_compact P (normal F m₀) A hAc)
    (field_smooth P (normal F m₀) A hN (normal_ne_zero F m₀ hm₀) hA hmean) p

theorem pairLp_mem (p : ℕ) :
    pairLp P κ m₀ Ξ A hΞ hAc F hN hm₀ hA hmean p ∈ divergenceFreeSpace P κ m₀ :=
  piolaPairLp_mem P κ m₀ Ξ (field P (normal F m₀) A) hΞ
    (field_compact P (normal F m₀) A hAc)
    (field_smooth P (normal F m₀) A hN (normal_ne_zero F m₀ hm₀) hA hmean) p

/-- The entire pair is the literal source formula, as an actual divergence-free L² field. -/
theorem pairLp_ae
    (hF : ∀ y, fderiv ℝ Ξ y = (F y).toContinuousLinearMap)
    (hdet : ∀ y, (operatorMatrix (F y).toContinuousLinearMap).det = 1)
    (htan : ∀ x, ⟪normal F m₀ x.1, A x⟫_ℝ = 0) (p : ℕ) :
    (pairLp P κ m₀ Ξ A hΞ hAc F hN hm₀ hA hmean p : LiftDomain P → Space) =ᵐ[liftMeasure P]
      fun x => (F x.1).symm (κ^p • A x+κ^(p+1) • corrector P F m₀ A x) :=
  piolaPairLp_ae P κ m₀ Ξ A (field P (normal F m₀) A) hΞ
    (field_compact P (normal F m₀) A hAc)
    (field_smooth P (normal F m₀) A hN (normal_ne_zero F m₀ hm₀) hA hmean)
    F hF hdet (normal_ne_zero F m₀ hm₀) htan
    (field_angle_derivative P (normal F m₀) A hN (normal_ne_zero F m₀ hm₀) hA hmean) p

end EulerPacketConstructedPiola
