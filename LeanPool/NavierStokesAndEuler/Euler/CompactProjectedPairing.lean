/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryHelmholtzField

@[expose] public section

/-!
# Pairing the projected Euler right-hand side

A solenoidal `L²` test field removes the Helmholtz projection from the
Euler right-hand side. For a smooth divergence-free test field, this gives
the ordinary spatial integral against advection. Compactly supported smooth
tests automatically satisfy the required `L²` assumption.
-/

noncomputable section

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerOrdinarySobolev
  EulerVectorCalculus
open scoped ContDiff

namespace EulerCompactProjectedPairing

/-- The Helmholtz projection can be removed in a solenoidal pairing. -/
theorem inner_solenoidalProjection (φ b : L2) (hφ : φ ∈ solenoidalSpace) :
    ⟪φ, solenoidalProjection b⟫_ℝ = ⟪φ, b⟫_ℝ := by
  have hz := pressure_pairing_zero (sub_solenoidalProjection_mem_gradient b) hφ
  rw [real_inner_comm, inner_sub_right] at hz
  exact (sub_eq_zero.mp hz).symm

/-- A solenoidal test sees precisely negative advection in the projected
Euler right-hand side. -/
theorem inner_projectedRhs (φ : L2) (hφ : φ ∈ solenoidalSpace)
    (A : SmoothL2Field Space) :
    ⟪φ, (projectedRhs A).toLp⟫_ℝ = -⟪φ, (advectionField A A).toLp⟫_ℝ := by
  rw [projectedRhs_toLp, inner_neg_right, inner_solenoidalProjection _ _ hφ]

/-- Integral form of the projected pairing for an arbitrary solenoidal
`L²` representative. -/
theorem inner_projectedRhs_eq_integral (φ : Space → Space)
    (hLp : MemLp φ 2 (volume : Measure Space))
    (hφ : hLp.toLp φ ∈ solenoidalSpace) (A : SmoothL2Field Space) :
    ⟪hLp.toLp φ, (projectedRhs A).toLp⟫_ℝ =
      -∫ x, ⟪φ x, fderiv ℝ A.field x (A.field x)⟫_ℝ := by
  rw [inner_projectedRhs _ hφ, MeasureTheory.L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [hLp.coeFn_toLp, (advectionField A A).toLp_ae] with x hφx hAx
  rw [hφx, hAx, advectionField_field]

/-- Smooth divergence-free `L²` tests remove the pressure projection. -/
theorem smooth_inner_projectedRhs_eq_integral (φ : Space → Space)
    (hs : ContDiff ℝ ∞ φ) (hLp : MemLp φ 2 (volume : Measure Space))
    (hdiv : ∀ x, divergence φ x = 0) (A : SmoothL2Field Space) :
    ⟪hLp.toLp φ, (projectedRhs A).toLp⟫_ℝ =
      -∫ x, ⟪φ x, fderiv ℝ A.field x (A.field x)⟫_ℝ :=
  inner_projectedRhs_eq_integral φ hLp (smooth_mem_solenoidal φ hs hLp hdiv) A

/-- In particular, every compactly supported smooth divergence-free test
has the projected Euler pairing required by the Comparator bridge. -/
theorem compact_inner_projectedRhs_eq_integral (φ : Space → Space)
    (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hdiv : ∀ x, divergence φ x = 0) (A : SmoothL2Field Space) :
    ⟪(hs.continuous.memLp_of_hasCompactSupport hc).toLp φ,
        (projectedRhs A).toLp⟫_ℝ =
      -∫ x, ⟪φ x, fderiv ℝ A.field x (A.field x)⟫_ℝ :=
  smooth_inner_projectedRhs_eq_integral φ hs
    (hs.continuous.memLp_of_hasCompactSupport hc) hdiv A

end EulerCompactProjectedPairing
