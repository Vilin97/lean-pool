/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.PressureRecovery
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.PressureFluxIdentity

@[expose] public section

/-!
# The actual pressure flux equals the canonical pressure flux

The scalar gradient identification is supplied by the proved pressure recovery
theorem. The only compact support in this identity is that of the cutoff.
-/


noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NavierStokesR3.ActualPressureFlux

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicUniqueness
open Comparison PressureRecovery PressureFluxIdentity

theorem difference_slice_smooth {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ht : t ∈ Ioo 0 T) :
    ContDiff ℝ ∞ (fun x : Space => (u - v) (t, x)) :=
  spatial_smooth (H.smooth_u.sub H.smooth_v) (Ioo_subset_Icc_self ht)

theorem actual_pressure_flux_integrable {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ht : t ∈ Ioo 0 T) {χ : Space → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    Integrable (fun x : Space => (p - q) (t, x) * fderiv ℝ χ x ((u - v) (t, x))) :=
  integrable_pressure_flux hχ
    (spatial_smooth (H.smooth_p.sub H.smooth_q) (Ioo_subset_Icc_self ht))
    (difference_slice_smooth H ht) hcχ

/-- The pressure flux of the actual difference equation has the canonical
Riesz-pairing representation, with no additional pressure hypothesis. -/
theorem pressure_flux_eq_canonical {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ht : t ∈ Ioo 0 T) {χ : Space → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    (∫ x : Space, (p - q) (t, x) * fderiv ℝ χ x ((u - v) (t, x))) =
      (∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorDiff u v t i j)
        (realTest (fun x : Space => fderiv ℝ χ x ((u - v) (t, x)))
          (fluxFunction_smooth hχ (difference_slice_smooth H ht))
          (fluxFunction_hasCompactSupport hcχ (fun x : Space => (u - v) (t, x))))).re := by
  obtain ⟨_M, _hM, hg⟩ := H.tensor_bound
  have hdiv : ∀ x : Space,
      (∑ k : Fin 3, partialD k (fun y => (u - v) (t, y)) x k) = 0 := by
    intro x
    change spatialDivergence (u - v) t x = 0
    rw [spatialDivergence_sub (spatial_smooth H.smooth_u (Ioo_subset_Icc_self ht))
      (spatial_smooth H.smooth_v (Ioo_subset_Icc_self ht)),
      H.div_u t ht, H.div_v t ht, sub_self]
  exact pressure_flux_eq_of_gradient_identification
    (spatial_smooth (H.smooth_p.sub H.smooth_q) (Ioo_subset_Icc_self ht))
    hχ (difference_slice_smooth H ht) hcχ
    (fun i j => (hg t (Ioo_subset_Icc_self ht) i j).1) hdiv
    (fun k ψ hψ hcψ => gradient_recovery H ht hψ hcψ k)

end NavierStokesR3.ActualPressureFlux
