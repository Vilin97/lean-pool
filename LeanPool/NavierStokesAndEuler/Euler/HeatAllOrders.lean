/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevSmoothApproximation
public import LeanPool.NavierStokesAndEuler.Euler.SobolevSmoothProduct

@[expose] public section

/-! Positive-time Gaussian heat has every actual Sobolev derivative, enabling genuine H∞
  approximations. -/

noncomputable section

namespace EulerSobolevHeat

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerGaussianCylinderHeat
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderMollifier
    EulerMollifierRepresentative
  EulerMetricTransport EulerStrongSmoothJet EulerNoncompactTransport
open scoped Topology ContDiff NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Positive-time actual cylinder heat belongs to every finite Sobolev space, for every L² datum. -/
theorem cylinderHeat_all_orders (q : ℕ) (v : ℝ≥0) (hv : 0 < v) (f : LiftL2 period) :
    ∃ u : SobolevSpace period q, value period u = cylinderHeat period v f := by
  induction q generalizing v with
  | zero => exact ⟨ofJet period (SpatialJet.zero (cylinderHeat period v f)), value_ofJet period _⟩
  | succ q ih =>
    have hh : 0 < v/2 := div_pos hv (by norm_num)
    obtain ⟨u, hu⟩ := ih (v/2) hh
    refine ⟨heatGain period q (v/2) hh u, ?_⟩
    rw [heatGain_value, hu, cylinderHeat_semigroup, add_halves]

/-- Mollified positive-time heat has an actual smooth representative whose derivatives of every order are in L². -/
theorem mollified_heat_all_memLp (n : ℕ) (v : ℝ≥0) (hv : 0 < v) (f : LiftL2 period) :
    ∀ j, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w (smoothMollifier period n (cylinderHeat period v f)))
        2 (liftMeasure period) := by
  intro j w
  obtain ⟨u, hu⟩ := cylinderHeat_all_orders period j v hv f
  have h := sobolevMollifier_word_ae period (le_refl j) n u w
  rw [hu] at h
  exact (Lp.memLp _).ae_eq h

/-- The earlier contractive high-regularity approximations are in fact genuine smooth H∞ fields. -/
theorem smoothApprox_representative_all {q : ℕ} (n : ℕ) (u : SobolevSpace period q) :
    ∃ f : LiftDomain period → Vector3,
      (value period (smoothApprox period q n u) : LiftDomain period → Vector3) =ᵐ[liftMeasure
        period] f ∧
      (∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) ∧
      ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)
        := by
  let v := smoothingVariance n+(smoothingVariance n+smoothingVariance n)
  have hv : 0 < v := add_pos_of_pos_of_nonneg (smoothingVariance_pos n) bot_le
  let f := smoothMollifier period n (cylinderHeat period v (value period u))
  refine ⟨f, ?_, smoothMollifier_smooth period n _, mollified_heat_all_memLp period n v hv (value
    period u)⟩
  have h := sobolevMollifier_representative period n
    (heatGainThree period q (smoothingVariance n) (smoothingVariance_pos n) u)
  rw [heatGainThree_value] at h
  exact h

end EulerSobolevHeat
