/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Integral
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Moment determination for measures supported on the standard simplex
-/

open Real MeasureTheory MeasureTheory.Measure
open scoped Topology

@[expose] public noncomputable section

namespace ProbabilityTheory

open scoped ENNReal

/-- A continuous real function is integrable against a finite measure supported on the simplex. -/
theorem integrable_of_continuous_of_restrict_stdSimplex
    {α : Type*} [Fintype α] {μ : Measure (α → ℝ)} [IsFiniteMeasure μ]
    (hμ : μ.restrict (Convexity.StdSimplex.coordinateSet ℝ α) = μ) {g : (α → ℝ) → ℝ}
    (hg : Continuous g) : Integrable g μ := by
  have hint : IntegrableOn g (Convexity.StdSimplex.coordinateSet ℝ α) μ :=
    hg.continuousOn.integrableOn_compact (Convexity.StdSimplex.isCompact_coordinateSet ℝ α)
  rwa [IntegrableOn, hμ] at hint

/-- Finite Borel measures supported on the standard simplex are determined by their
monomial moments. -/
theorem eq_of_forall_monomial_integral_eq_of_restrict_stdSimplex
    {α : Type*} [Fintype α]
    {μ ν : Measure (α → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ.restrict (Convexity.StdSimplex.coordinateSet ℝ α) = μ)
    (hν : ν.restrict (Convexity.StdSimplex.coordinateSet ℝ α) = ν)
    (h : ∀ m : α → ℕ, ∫ x, (∏ i, x i ^ m i) ∂μ = ∫ x, (∏ i, x i ^ m i) ∂ν) :
    μ = ν := by
  classical
  let coord : α → C(α → ℝ, ℝ) := fun k =>
    ⟨fun v => v k, continuous_apply k⟩
  let A : Subalgebra ℝ C(α → ℝ, ℝ) := (MvPolynomial.aeval coord).range
  have hA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨k, hk⟩ := not_forall.mp (mt funext hxy)
    refine ⟨(coord k : (α → ℝ) → ℝ), ?_, hk⟩
    exact ⟨coord k, ⟨MvPolynomial.X k, MvPolynomial.aeval_X coord k⟩, rfl⟩
  have hK : IsCompact (Convexity.StdSimplex.coordinateSet ℝ α) := Convexity.StdSimplex.isCompact_coordinateSet ℝ α
  have hae_μ : ∀ᵐ x ∂μ, x ∈ Convexity.StdSimplex.coordinateSet ℝ α := by
    rw [ae_iff]
    change μ (Convexity.StdSimplex.coordinateSet ℝ α)ᶜ = 0
    have hs := (Convexity.StdSimplex.isClosed_coordinateSet ℝ α).measurableSet
    have h' := congrArg (fun η : Measure (α → ℝ) => η (Convexity.StdSimplex.coordinateSet ℝ α)ᶜ) hμ
    rw [Measure.restrict_apply hs.compl] at h'
    simpa [Set.inter_compl_self] using h'.symm
  have hae_ν : ∀ᵐ x ∂ν, x ∈ Convexity.StdSimplex.coordinateSet ℝ α := by
    rw [ae_iff]
    change ν (Convexity.StdSimplex.coordinateSet ℝ α)ᶜ = 0
    have hs := (Convexity.StdSimplex.isClosed_coordinateSet ℝ α).measurableSet
    have h' := congrArg (fun η : Measure (α → ℝ) => η (Convexity.StdSimplex.coordinateSet ℝ α)ᶜ) hν
    rw [Measure.restrict_apply hs.compl] at h'
    simpa [Set.inter_compl_self] using h'.symm
  have heval (q : MvPolynomial α ℝ) (v : α → ℝ) :
      (MvPolynomial.aeval coord q) v = MvPolynomial.eval v q := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', MvPolynomial.eval_eq']
    simp [coord, algebraMap_apply]
  have hpoly (q : MvPolynomial α ℝ) :
      ∫ x, (MvPolynomial.aeval coord q) x ∂μ =
        ∫ x, (MvPolynomial.aeval coord q) x ∂ν := by
    simp_rw [heval, MvPolynomial.eval_eq']
    have hterm (d : α →₀ ℕ) :
        Integrable (fun x : α → ℝ => q.coeff d * ∏ i, x i ^ d i) μ :=
      (integrable_of_continuous_of_restrict_stdSimplex hμ (by fun_prop)).const_mul _
    have hterm' (d : α →₀ ℕ) :
        Integrable (fun x : α → ℝ => q.coeff d * ∏ i, x i ^ d i) ν :=
      (integrable_of_continuous_of_restrict_stdSimplex hν (by fun_prop)).const_mul _
    rw [integral_finsetSum _ fun d _ => hterm d,
      integral_finsetSum _ fun d _ => hterm' d]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [integral_const_mul, integral_const_mul, h fun i => d i]
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
  let gC : C(α → ℝ, ℝ) := g.toContinuousMap
  have hgμ : Integrable (g : (α → ℝ) → ℝ) μ :=
    integrable_of_continuous_of_restrict_stdSimplex hμ g.continuous
  have hgν : Integrable (g : (α → ℝ) → ℝ) ν :=
    integrable_of_continuous_of_restrict_stdSimplex hν g.continuous
  have happrox (ε : ℝ) (hε : 0 < ε) :
      |∫ x, (g : (α → ℝ) → ℝ) x ∂μ - ∫ x, (g : (α → ℝ) → ℝ) x ∂ν| ≤
        ε * (μ.real Set.univ + ν.real Set.univ) := by
    obtain ⟨p, hpA, hpapprox⟩ :=
      ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
        hA gC hK hε
    obtain ⟨q, hq⟩ : ∃ q, MvPolynomial.aeval coord q = p := by
      simpa [A, AlgHom.mem_range] using hpA
    have hpμ : Integrable (fun x : α → ℝ => p x) μ :=
      integrable_of_continuous_of_restrict_stdSimplex hμ p.continuous
    have hpν : Integrable (fun x : α → ℝ => p x) ν :=
      integrable_of_continuous_of_restrict_stdSimplex hν p.continuous
    have hpeq : ∫ x, p x ∂μ = ∫ x, p x ∂ν := by
      simpa [hq] using hpoly q
    have hdiffμ : ‖∫ x, (g : (α → ℝ) → ℝ) x - p x ∂μ‖ ≤ ε * μ.real Set.univ := by
      refine norm_integral_le_of_norm_le_const ?_
      filter_upwards [hae_μ] with x hx
      rw [show (g : (α → ℝ) → ℝ) x = gC x from rfl, norm_sub_rev]
      exact (hpapprox x hx).le
    have hdiffν : ‖∫ x, (g : (α → ℝ) → ℝ) x - p x ∂ν‖ ≤ ε * ν.real Set.univ := by
      refine norm_integral_le_of_norm_le_const ?_
      filter_upwards [hae_ν] with x hx
      rw [show (g : (α → ℝ) → ℝ) x = gC x from rfl, norm_sub_rev]
      exact (hpapprox x hx).le
    have hμ' : |∫ x, (g : (α → ℝ) → ℝ) x ∂μ - ∫ x, p x ∂μ| ≤ ε * μ.real Set.univ := by
      rw [← integral_sub hgμ hpμ, ← Real.norm_eq_abs]
      exact hdiffμ
    have hν' : |∫ x, (g : (α → ℝ) → ℝ) x ∂ν - ∫ x, p x ∂ν| ≤ ε * ν.real Set.univ := by
      rw [← integral_sub hgν hpν, ← Real.norm_eq_abs]
      exact hdiffν
    have hsplit :
        ∫ x, (g : (α → ℝ) → ℝ) x ∂μ - ∫ x, (g : (α → ℝ) → ℝ) x ∂ν =
          (∫ x, (g : (α → ℝ) → ℝ) x ∂μ - ∫ x, p x ∂μ) +
            (∫ x, p x ∂ν - ∫ x, (g : (α → ℝ) → ℝ) x ∂ν) := by
      rw [hpeq]; ring
    calc
      |∫ x, (g : (α → ℝ) → ℝ) x ∂μ - ∫ x, (g : (α → ℝ) → ℝ) x ∂ν|
          ≤ |∫ x, (g : (α → ℝ) → ℝ) x ∂μ - ∫ x, p x ∂μ| +
              |∫ x, p x ∂ν - ∫ x, (g : (α → ℝ) → ℝ) x ∂ν| := by
            rw [hsplit]
            exact abs_add_le _ _
      _ ≤ ε * μ.real Set.univ + ε * ν.real Set.univ := by
          rw [abs_sub_comm (∫ x, p x ∂ν)]
          exact add_le_add hμ' hν'
      _ = ε * (μ.real Set.univ + ν.real Set.univ) := by ring
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  set C := μ.real Set.univ + ν.real Set.univ
  have hC : 0 ≤ C := by positivity
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases hC0 : C = 0
  · have := happrox 1 one_pos
    simp only [hC0, mul_zero] at this
    linarith
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have := happrox (ε / C) (div_pos hε hCpos)
    have hcancel : ε / C * C = ε := div_mul_cancel₀ ε (ne_of_gt hCpos)
    linarith

end ProbabilityTheory

end
