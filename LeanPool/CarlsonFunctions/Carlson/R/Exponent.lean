/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.Deriv

/-!
# Analytic dependence on the exponent of Carlson's R-integral

Unlike the Dirichlet parameters, the exponent has no convergence restriction on the
right-half-plane node domain. This is the continuation input for fixed-parameter
recurrences initially obtained from a convergent single-integral representation.
-/

open Complex MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped Classical Topology

@[expose] public noncomputable section

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- Differentiation in the exponent inserts the logarithm of the affine form into
the regularized Dirichlet integral. -/
theorem hasDerivAt_regCarlsonRIntegral_exponent (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    HasDerivAt (fun s ↦ regCarlsonRIntegral s b z)
      (regDirichletIntegral b
        (fun u ↦ carlsonAffineForm z u ^ t * log (carlsonAffineForm z u))) t := by
  let K := Convexity.StdSimplex.coordinateSet ℝ ι
  let μ := stdSimplexMeasure.restrict K
  let g : ℂ → (ι → ℝ) → ℂ := fun s u ↦
    carlsonAffineForm z u ^ s * log (carlsonAffineForm z u)
  have hpow (s : ℂ) : ContinuousOn (fun u ↦ carlsonAffineForm z u ^ s) K :=
    (continuous_carlsonAffineForm z).continuousOn.cpow_const
      (fun _ hu ↦ carlsonAffineForm_mem_slitPlane hz hu)
  have hlog : ContinuousOn (fun u ↦ log (carlsonAffineForm z u)) K := by
    intro u hu
    exact ((continuousAt_clog (carlsonAffineForm_mem_slitPlane hz hu)).comp
      (continuous_carlsonAffineForm z).continuousAt).continuousWithinAt
  have hg (s : ℂ) : ContinuousOn (g s) K := (hpow s).mul hlog
  have hjoint : ContinuousOn (fun p : ℂ × (ι → ℝ) ↦ g p.1 p.2)
      (Metric.closedBall t 1 ×ˢ K) := by
    apply ContinuousOn.mul
    · exact ((continuous_carlsonAffineForm z).comp continuous_snd).continuousOn.cpow
        continuous_fst.continuousOn (fun p hp ↦ carlsonAffineForm_mem_slitPlane hz hp.2)
    · exact hlog.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (((isCompact_closedBall t 1).prod (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)).bddAbove_image hjoint.norm)
  have hdens : Integrable (regDirichletDensity b) μ := by
    simpa only [mul_one, IntegrableOn, μ, K] using integrableOn_regDirichletDensity_mul b hb
      (continuousOn_const : ContinuousOn (fun _ : ι → ℝ ↦ (1 : ℂ)) K)
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun s u ↦ regDirichletDensity b u * carlsonAffineForm z u ^ s)
    (F' := fun s u ↦ regDirichletDensity b u * g s u)
    (bound := fun u ↦ C * ‖regDirichletDensity b u‖)
    (Metric.closedBall_mem_nhds t zero_lt_one)
    (Filter.Eventually.of_forall (fun s ↦
      (integrableOn_regDirichletDensity_mul b hb (hpow s)).aestronglyMeasurable))
    (integrableOn_regDirichletDensity_mul b hb (hpow t))
    (integrableOn_regDirichletDensity_mul b hb (hg t)).aestronglyMeasurable
    (by
      filter_upwards [self_mem_ae_restrict (μ := stdSimplexMeasure)
        (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
      intro s hs
      simp only [norm_mul]
      calc
        ‖regDirichletDensity b u‖ * ‖g s u‖ ≤ ‖regDirichletDensity b u‖ * C :=
          mul_le_mul_of_nonneg_left (hC _ ⟨(s, u), ⟨hs, hu⟩, rfl⟩) (norm_nonneg _)
        _ = C * ‖regDirichletDensity b u‖ := mul_comm _ _)
    (hdens.norm.const_mul C)
    (by
      filter_upwards [self_mem_ae_restrict (μ := stdSimplexMeasure)
        (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
      intro s _
      exact (Complex.hasStrictDerivAt_const_cpow
        (Or.inl (slitPlane_ne_zero (carlsonAffineForm_mem_slitPlane hz hu)))).hasDerivAt.const_mul
          (regDirichletDensity b u))
  exact hdiff.2

/-- The regularized native R-integral is entire in its exponent. -/
theorem analyticOnNhd_regCarlsonRIntegral_exponent {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    AnalyticOnNhd ℂ (fun t ↦ regCarlsonRIntegral t b z) Set.univ := by
  intro t _
  rw [analyticAt_iff_eventually_differentiableAt]
  exact Filter.Eventually.of_forall fun s ↦
    (hasDerivAt_regCarlsonRIntegral_exponent s hb hz).differentiableAt

/-- The normalized native R-integral is entire in its exponent. -/
theorem analyticOnNhd_carlsonRIntegral_exponent {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    AnalyticOnNhd ℂ (fun t ↦ carlsonRIntegral t b z) Set.univ := by
  exact analyticOnNhd_const.mul (analyticOnNhd_regCarlsonRIntegral_exponent hb hz)

end DirichletTransform

end
