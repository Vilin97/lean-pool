/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CoerciveProjection
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedPressure
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCalculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The ordinary three-dimensional solenoidal space for the mean inverse

This is the actual Lebesgue L² space on R³. Its solenoidal subspace is defined
by orthogonality to genuine compactly supported smooth gradients, and the weak
divergence test characterization is proved. The projected coefficient inverse
below acts on this space, rather than on the lifted cylinder used by the
oscillatory correction construction.
-/

@[expose] public section


noncomputable section

namespace EulerMeanSolenoidal

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerCoerciveProjection
  EulerLiftedPressure
open scoped ContDiff ENNReal NNReal

/-- L²: an abbreviation for `MeasureTheory.Lp Space 2 (volume : Measure Space)`. -/
abbrev L2 := MeasureTheory.Lp Space 2 (volume : Measure Space)

theorem contDiff_gradient {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (gradient φ) := by
  exact (toDual ℝ Space).symm.toContinuousLinearEquiv.contDiff.comp
    (hφ.fderiv_right (m := ∞) (by simp))

theorem compactSupport_gradient {φ : Space → ℝ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (gradient φ) := by
  exact (hφ.fderiv (𝕜 := ℝ)).comp_left (map_zero (toDual ℝ Space).symm)

theorem gradient_memLp {φ : Space → ℝ}
    (hc : HasCompactSupport φ) (hs : ContDiff ℝ ∞ φ) :
    MemLp (gradient φ) 2 (volume : Measure Space) :=
  (contDiff_gradient hs).continuous.memLp_of_hasCompactSupport (compactSupport_gradient hc)

/-- Test gradient, given by `(gradient_memLp hc hs).toLp (gradient φ)`. -/
def testGradient (φ : Space → ℝ) (hc : HasCompactSupport φ)
    (hs : ContDiff ℝ ∞ φ) : L2 :=
  (gradient_memLp hc hs).toLp (gradient φ)

theorem testGradient_ae (φ : Space → ℝ) (hc : HasCompactSupport φ)
    (hs : ContDiff ℝ ∞ φ) : testGradient φ hc hs =ᵐ[volume] gradient φ :=
  (gradient_memLp hc hs).coeFn_toLp

/-- Gradient generators, given by `{g | ∃ φ : Space → ℝ, HasCompactSupport φ ∧ ContDiff ℝ ∞ φ ∧
g =ᵐ[volume] gradient φ}`. -/
def gradientGenerators : Set L2 :=
  {g | ∃ φ : Space → ℝ, HasCompactSupport φ ∧ ContDiff ℝ ∞ φ ∧
    g =ᵐ[volume] gradient φ}

/-- Gradient space, given by `(Submodule.span ℝ gradientGenerators).topologicalClosure`. -/
def gradientSpace : Submodule ℝ L2 :=
  (Submodule.span ℝ gradientGenerators).topologicalClosure

theorem gradientSpace_closed : IsClosed (gradientSpace : Set L2) :=
  (Submodule.span ℝ gradientGenerators).isClosed_topologicalClosure

instance : CompleteSpace gradientSpace := gradientSpace_closed.completeSpace_coe

/-- Solenoidal space, given by `gradientSpace.orthogonal instance : CompleteSpace
solenoidalSpace := gradientSpace.isClosed_orthogonal.completeSpace_coe`. -/
def solenoidalSpace : Submodule ℝ L2 := gradientSpace.orthogonal

instance : CompleteSpace solenoidalSpace :=
  gradientSpace.isClosed_orthogonal.completeSpace_coe

theorem testGradient_mem (φ : Space → ℝ) (hc : HasCompactSupport φ)
    (hs : ContDiff ℝ ∞ φ) : testGradient φ hc hs ∈ gradientSpace :=
  (Submodule.span ℝ gradientGenerators).le_topologicalClosure
    (Submodule.subset_span ⟨φ, hc, hs, testGradient_ae φ hc hs⟩)

theorem weak_divergence_test {u : L2} (hu : u ∈ solenoidalSpace)
    (φ : Space → ℝ) (hc : HasCompactSupport φ) (hs : ContDiff ℝ ∞ φ) :
    ∫ x, ⟪gradient φ x, u x⟫_ℝ = 0 := by
  have h := hu (testGradient φ hc hs) (testGradient_mem φ hc hs)
  rw [MeasureTheory.L2.inner_def] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [testGradient_ae φ hc hs] with x hx
  rw [hx]

/-- Orthogonality is equivalent to the ordinary distributional divergence test. -/
theorem mem_solenoidal_iff (u : L2) : u ∈ solenoidalSpace ↔
    ∀ φ : Space → ℝ, HasCompactSupport φ → ContDiff ℝ ∞ φ →
      ∫ x, ⟪gradient φ x, u x⟫_ℝ = 0 := by
  constructor
  · exact fun hu => weak_divergence_test hu
  · intro hu
    let K := (innerSL ℝ u).ker
    have hg : Submodule.span ℝ gradientGenerators ≤ K := by
      apply Submodule.span_le.2
      rintro g ⟨φ, hc, hs, hg⟩
      change ⟪u, g⟫_ℝ = 0
      rw [real_inner_comm, MeasureTheory.L2.inner_def]
      calc
        (∫ x, ⟪g x, u x⟫_ℝ) = ∫ x, ⟪gradient φ x, u x⟫_ℝ := by
          apply integral_congr_ae
          filter_upwards [hg] with x hx
          rw [hx]
        _ = 0 := hu φ hc hs
    have hclosure : gradientSpace ≤ K :=
      (Submodule.span ℝ gradientGenerators).topologicalClosure_minimal hg
        (innerSL ℝ u).isClosed_ker
    intro g hg
    rw [real_inner_comm]
    exact hclosure hg

/-- Solenoidal projection, given by `solenoidalSpace.starProjection`. -/
def solenoidalProjection : L2 →L[ℝ] L2 := solenoidalSpace.starProjection

theorem solenoidalProjection_mem (u : L2) :
    solenoidalProjection u ∈ solenoidalSpace := solenoidalSpace.starProjection_apply_mem u

theorem solenoidalProjection_norm_le : ‖solenoidalProjection‖ ≤ 1 :=
  solenoidalSpace.starProjection_norm_le

theorem solenoidalProjection_apply_norm_le (u : L2) : ‖solenoidalProjection u‖ ≤ ‖u‖ :=
  solenoidalSpace.norm_starProjection_apply_le u

theorem solenoidal_orthogonal : solenoidalSpace.orthogonal = gradientSpace :=
  gradientSpace.orthogonal_orthogonal

/-- The pressure component of the ordinary Helmholtz decomposition. -/
theorem sub_solenoidalProjection_mem_gradient (u : L2) :
    u - solenoidalProjection u ∈ gradientSpace := by
  rw [← solenoidal_orthogonal]
  exact solenoidalSpace.sub_starProjection_mem_orthogonal u

theorem solenoidalProjection_eq_zero_iff (u : L2) :
    solenoidalProjection u = 0 ↔ u ∈ gradientSpace := by
  change u ∈ solenoidalSpace.starProjection.ker ↔ u ∈ gradientSpace
  rw [Submodule.ker_starProjection, solenoidal_orthogonal]

theorem pressure_pairing_zero {p u : L2} (hp : p ∈ gradientSpace)
    (hu : u ∈ solenoidalSpace) : ⟪p, u⟫_ℝ = 0 := hu p hp

section ClassicalFields

open EulerVectorCalculus

/-- Classical integration by parts against a compact smooth test, on R³. -/
theorem gradient_test_integration_by_parts (u : Space → Space)
    (hu : ContDiff ℝ ∞ u) (φ : Space → ℝ)
    (hc : HasCompactSupport φ) (hs : ContDiff ℝ ∞ φ) :
    (∫ x, ⟪gradient φ x, u x⟫_ℝ) = -∫ x, φ x * divergence u x := by
  let ui (i : Fin 3) (x : Space) := u x i
  have hui (i : Fin 3) : ContDiff ℝ ∞ (ui i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hu
  have hi₁ (i : Fin 3) : Integrable (fun x => partialDerivative φ i x * ui i x) :=
    ((contDiff_partialDerivative φ hs i).continuous.mul (hui
        i).continuous).integrable_of_hasCompactSupport
        ((hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)).mul_right)
  have hi₂ (i : Fin 3) : Integrable (fun x => φ x * partialDerivative (ui i) i x) :=
    (hs.continuous.mul (contDiff_partialDerivative _ (hui i)
        i).continuous).integrable_of_hasCompactSupport
      hc.mul_right
  have hibp (i : Fin 3) : (∫ x, partialDerivative φ i x * ui i x) =
      -∫ x, φ x * partialDerivative (ui i) i x := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure Space)) (v := EuclideanSpace.single i 1)
      (hi₁ i) (hi₂ i)
      ((hs.continuous.mul (hui i).continuous).integrable_of_hasCompactSupport hc.mul_right)
      (fun x _ => (hs.differentiable (by simp)).differentiableAt)
      (fun x _ => ((hui i).differentiable (by simp)).differentiableAt)
    change (∫ x, φ x * partialDerivative (ui i) i x) =
      -∫ x, partialDerivative φ i x * ui i x at h
    linarith
  have hinner (x : Space) : ⟪gradient φ x, u x⟫_ℝ =
      ∑ i : Fin 3, partialDerivative φ i x * ui i x := by
    rw [inner_gradient_left]
    have hre : ∑ i : Fin 3, u x i • (EuclideanSpace.single i 1 : Space) = u x := by
      simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (u x)
    calc
      fderiv ℝ φ x (u x) =
          fderiv ℝ φ x (∑ i : Fin 3, u x i • EuclideanSpace.single i 1) :=
        congrArg (fderiv ℝ φ x) hre.symm
      _ = ∑ i : Fin 3, partialDerivative φ i x * ui i x := by
        simp only [map_sum, map_smul, smul_eq_mul, partialDerivative, ui, mul_comm]
  have hdiv (x : Space) : φ x * divergence u x =
      ∑ i : Fin 3, φ x * partialDerivative (ui i) i x := by
    rw [divergence_eq_coordinate_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (fderiv_coordinate u x ((hu.differentiable (by simp)).differentiableAt)
      i (EuclideanSpace.single i 1)).symm
  simp_rw [hinner, hdiv]
  rw [integral_finsetSum _ (fun i _ => hi₁ i),
    integral_finsetSum _ (fun i _ => hi₂ i)]
  simp only [hibp, Finset.sum_neg_distrib]

/-- A classical divergence-free L² field lies in the actual closed mean space. -/
theorem smooth_mem_solenoidal (u : Space → Space) (hu : ContDiff ℝ ∞ u)
    (hLp : MemLp u 2 (volume : Measure Space))
    (hdiv : ∀ x, divergence u x = 0) : hLp.toLp u ∈ solenoidalSpace := by
  apply (mem_solenoidal_iff _).2
  intro φ hc hs
  calc
    (∫ x, ⟪gradient φ x, hLp.toLp u x⟫_ℝ) = ∫ x, ⟪gradient φ x, u x⟫_ℝ := by
      apply integral_congr_ae
      filter_upwards [hLp.coeFn_toLp] with x hx
      rw [hx]
    _ = -∫ x, φ x * divergence u x := gradient_test_integration_by_parts u hu φ hc hs
    _ = 0 := by simp only [hdiv, mul_zero, integral_zero, neg_zero]

/-- In particular, every smooth L² curl is solenoidal in the ordinary space. -/
theorem curl_mem_solenoidal (ψ : Fin 3 → Space → ℝ)
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    (hLp : MemLp (curl ψ) 2 (volume : Measure Space)) :
    hLp.toLp (curl ψ) ∈ solenoidalSpace :=
  smooth_mem_solenoidal (curl ψ) (contDiff_curl ψ hψ) hLp (divergence_curl ψ hψ)

end ClassicalFields

section CoefficientInverse

variable (A : Space → Space →L[ℝ] Space)
  (hA : AEStronglyMeasurable A (volume : Measure Space))
  (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C)
  (c : ℝ) (hc : 0 < c)
  (hpositive : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ)

/-- The concrete inverse of the projected ordinary-space coefficient multiplier. -/
def metricInverse : solenoidalSpace →L[ℝ] solenoidalSpace :=
  projectedInverse solenoidalSpace (coefficientOperator A hA C hbound) c hc
    (coefficientOperator_coercive A hA C hbound c hpositive)

theorem metricInverse_equation (f : solenoidalSpace) :
    solenoidalSpace.orthogonalProjectionOnto
      (coefficientOperator A hA C hbound
        (metricInverse A hA C hbound c hc hpositive f : L2)) = f :=
  projectedOperator_inverse_apply solenoidalSpace (coefficientOperator A hA C hbound)
    c hc (coefficientOperator_coercive A hA C hbound c hpositive) f

theorem metricInverse_norm_le : ‖metricInverse A hA C hbound c hc hpositive‖ ≤ c⁻¹ :=
  projectedInverse_norm_le solenoidalSpace (coefficientOperator A hA C hbound)
    c hc (coefficientOperator_coercive A hA C hbound c hpositive)

include hc hpositive in
/-- A forcing in the ambient L² space has one solenoidal solution of the
projected metric equation. No inverse or solution is supplied as an input. -/
theorem existsUnique_metric_solution (f : L2) :
    ∃! u : solenoidalSpace,
      solenoidalSpace.orthogonalProjectionOnto (coefficientOperator A hA C hbound (u : L2)) =
        solenoidalSpace.orthogonalProjectionOnto f :=
  existsUnique_projected_solution solenoidalSpace (coefficientOperator A hA C hbound)
    c hc (coefficientOperator_coercive A hA C hbound c hpositive) f

/-- The residual of the solved projected equation is a genuine weak gradient. -/
theorem metric_solution_residual_gradient (f : L2) (u : solenoidalSpace)
    (hu : solenoidalSpace.orthogonalProjectionOnto
      (coefficientOperator A hA C hbound (u : L2)) =
        solenoidalSpace.orthogonalProjectionOnto f) :
    f - coefficientOperator A hA C hbound (u : L2) ∈ gradientSpace := by
  apply (solenoidalProjection_eq_zero_iff _).1
  change solenoidalSpace.starProjection
    (f - coefficientOperator A hA C hbound (u : L2)) = 0
  rw [map_sub]
  have h := congrArg (fun v : solenoidalSpace => (v : L2)) hu
  change solenoidalSpace.starProjection (coefficientOperator A hA C hbound (u : L2)) =
    solenoidalSpace.starProjection f at h
  rw [h, sub_self]

end CoefficientInverse

end EulerMeanSolenoidal
