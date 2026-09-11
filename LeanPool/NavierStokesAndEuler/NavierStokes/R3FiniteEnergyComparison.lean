/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3CompactCandidate
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ProblemStatement
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.WholeSpaceUniqueness
import Mathlib.MeasureTheory.Function.L2Space
public import LeanPool.NavierStokesAndEuler.NavierStokes.ComparatorBridge

/-!
# Comparison with the compact candidate on all of R³

The whole-space uniqueness proof is ported from the verified R³ development.
The competitor retains exactly the smoothness and finite-energy conditions
of the comparator. The candidate's compact support supplies the reference
solution's bounds on each closed interval before time one.
-/

section

/-!
# Viscosity normalization for the whole-space comparator

This version retains the comparator's square integrability and uniform kinetic
energy bound. It makes no periodicity or compact-support assumption on a
hypothetical global solution.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ComparatorBridge

open Set MeasureTheory InnerProductSpace ProblemStatement
open scoped ContDiff Laplacian

theorem zero_initial_condition_decay :
    Comparator.InitialVelocityConditionDecay (fun _ : Space => (0 : Space)) := by
  refine ⟨⟨fun x => Comparator.divergence_const 0 x, contDiff_const⟩, ?_⟩
  intro m K
  exact ⟨0, by simp⟩

/-- A global whole-space solution in the original physical coordinates. -/
structure GlobalSolutionRn (f : VelocityField) (v : VelocityField) (p : PressureField) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ v futureDomain
  pressure_smooth : ContDiffOn ℝ ∞ p futureDomain
  initial_velocity : ∀ x : Space, v (0, x) = 0
  divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Space, spatialDivergence v t x = 0
  navier_stokes : ∀ t : ℝ, 0 < t → ∀ x : Space, navierStokesResidual v p t x = f (t, x)
  integrable : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Space => ‖v (t, x)‖) 2
  globally_bounded_energy : ∃ E : ℝ, ∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖v (t, x)‖ ^ 2) < E

theorem comparator_equation_Rn {ν : ℝ} {u₀ : Space → Space} {f v : Space → ℝ → Space}
    {p : Space → ℝ → ℝ}
    (h : Comparator.NavierStokesExistenceAndSmoothnessRn ν u₀ f v p)
    {t : ℝ} (ht : 0 < t) (x : Space) :
    temporalDerivative (fromComparator v) t x + advection (fromComparator v) t x -
      ν • spatialLaplacian (fromComparator v) t x +
      pressureGradient (fromComparator p) t x = f x t := by
  have hv := smooth_space_slice (fromComparator_smooth h.velocity_smooth) ht.le
  rw [temporalDerivative_eq _ ht, laplacian_eq _ _ _
    (hv.of_le (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2).le), gradient_eq]
  change derivWithin (v x) (Ici 0) t + fderiv ℝ (v · t) x (v x t) -
    ν • Δ (v · t) x + gradient (p · t) x = f x t
  rw [h.navier_stokes x t ht.le]
  abel

/-- Normalize an arbitrary global finite-energy comparison solution to viscosity one. -/
theorem normalized_solution_Rn {ν : ℝ} (hν : 0 < ν) {f : VelocityField}
    {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : Comparator.NavierStokesExistenceAndSmoothnessRn ν (fun _ => 0)
      (toComparator (rescaledForce ν f)) v p) :
    GlobalSolutionRn f (rescale ν⁻¹ ν⁻¹ (fromComparator v))
      (rescale (ν⁻¹ ^ 2) ν⁻¹ (fromComparator p)) := by
  have hc : 0 < ν⁻¹ := inv_pos.mpr hν
  have hv := fromComparator_smooth h.velocity_smooth
  have hp := fromComparator_smooth h.pressure_smooth
  refine ⟨rescale_smooth hv _ hc.le, rescale_smooth hp _ hc.le, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [rescale, fromComparator, h.initial_condition]
  · intro t ht x
    rw [rescale_divergence, divergence_eq]
    change ν⁻¹ * Comparator.divergence (v · (ν⁻¹ * t)) x = 0
    rw [h.div_free x (ν⁻¹ * t) (mul_nonneg hc.le ht), mul_zero]
  · intro t ht x
    rw [navierStokesResidual, rescale_temporalDerivative _ _ _ _ _
      (differentiable_time_slice hv (mul_pos hc ht) x),
      rescale_advection, rescale_laplacian, rescale_gradient]
    have he := congrArg (fun z : Space => ν⁻¹ ^ 2 • z)
      (comparator_equation_Rn h (mul_pos hc ht) x)
    have hcoef : ν⁻¹ ^ 2 * ν = ν⁻¹ := by field_simp
    have hforce : ν⁻¹ ^ 2 • toComparator (rescaledForce ν f) x (ν⁻¹ * t) = f (t, x) := by
      simp [toComparator, rescaledForce, rescale, smul_smul, hν.ne']
    rw [hforce] at he
    simp only [smul_add, smul_sub, smul_smul] at he
    rw [hcoef] at he
    simpa only [pow_two] using he
  · intro t ht
    simpa only [rescale, fromComparator, norm_smul] using
      (h.integrable (ν⁻¹ * t) (mul_nonneg hc.le ht)).const_mul ‖ν⁻¹‖
  · obtain ⟨E, hE⟩ := h.globally_bounded_energy
    refine ⟨ν⁻¹ ^ 2 * E, ?_⟩
    intro t ht
    simp only [rescale, fromComparator, norm_smul, Real.norm_eq_abs,
      abs_of_pos hc, mul_pow, integral_const_mul]
    exact mul_lt_mul_of_pos_left (hE (ν⁻¹ * t) (mul_nonneg hc.le ht)) (sq_pos_of_pos hc)

end NavierStokes.ComparatorBridge

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ComparatorBridge

open Set MeasureTheory ProblemStatement
open scoped ContDiff

theorem GlobalSolutionRn.uniformFiniteEnergy {f v : VelocityField} {q : PressureField}
    (h : GlobalSolutionRn f v q) (T : ℝ) :
    NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v := by
  obtain ⟨E, hE⟩ := h.globally_bounded_energy
  refine ⟨max 0 (E / 2), le_max_left _ _, ?_⟩
  intro t ht
  constructor
  · simpa only [NavierStokesR3.ProblemStatement.SquareIntegrableAtTime, norm_norm] using!
      (memLp_two_iff_integrable_sq_norm (h.integrable t ht.1).1).mp (h.integrable t ht.1)
  · change (1 / 2 : ℝ) * (∫ x : Space, ‖v (t, x)‖ ^ 2) ≤ max 0 (E / 2)
    have hb := (hE t ht.1).le
    have hm := le_max_right 0 (E / 2)
    linarith

/-- A compact candidate with unbounded speed excludes every global smooth
solution having the comparator's finite-energy bound. -/
theorem compact_candidate_excludes_global_solution
    {u v f : VelocityField} {p q : PressureField}
    (h : R3CompactCandidate.Properties u p f) (hv : GlobalSolutionRn f v q) : False := by
  apply h.not_global_agreement hv.velocity_smooth
  obtain ⟨K, hK, hs⟩ := h.velocity_support
  intro t ht x
  by_cases ht0 : t = 0
  · subst t
    rw [h.zero_initial_velocity, hv.initial_velocity]
  have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hpre : NavierStokesR3.Comparison.slab 0 t ⊆ preSingularDomain := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt ht.2⟩, hz.2⟩
  have hfuture : NavierStokesR3.Comparison.slab 0 t ⊆ futureDomain := by
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  have hsupport : ∀ r ∈ Icc (0 : ℝ) t, tsupport (fun y => u (r, y)) ⊆ K := by
    intro r hr
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_contra hyK
    exact hy (hs r ⟨hr.1, hr.2.trans_lt ht.2⟩ y hyK)
  have heq := NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc hpos
    (h.velocity_smooth.mono hpre) (hv.velocity_smooth.mono hfuture)
    (h.pressure_smooth.mono hpre) (hv.pressure_smooth.mono hfuture)
    hK hsupport (hv.uniformFiniteEnergy t)
    (fun r hr => h.divergence_free r ⟨hr.1.le, hr.2.trans ht.2⟩)
    (fun r hr => hv.divergence_free r hr.1.le)
    (fun r hr y => by
      simpa only [NavierStokesR3.ProblemStatement.navierStokesResidual,
        navierStokesResidual, one_smul] using
        (h.navier_stokes r ⟨hr.1, hr.2.trans ht.2⟩ y).trans
          (hv.navier_stokes r hr.1 y).symm)
    (fun y => (h.zero_initial_velocity y).trans (hv.initial_velocity y).symm)
  exact heq t ⟨ht.1, le_rfl⟩ x

end NavierStokes.ComparatorBridge
