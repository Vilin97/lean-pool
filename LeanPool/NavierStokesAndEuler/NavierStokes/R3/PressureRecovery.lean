/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.PressureRecoveryHelpers
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.PressureFunctionals
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonTimeAverages
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonFiniteEnergy
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.HarmonicTestFunctionals
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.PressureTemporalIdentity
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszSymbolRegularity
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszTestOperators
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.TemporalTestUniqueness
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.WeakTimeContinuity

/-!
# Pressure recovery for smooth finite-energy comparisons

The physical pressure is tested only against compact smooth functions. Its
canonical representative is recovered from the conservative equation, time
averaging, and the vanishing theorem for harmonic Sobolev-bounded functionals.
-/

@[expose] public section



noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace NavierStokesR3.PressureRecovery

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness
open Comparison ConservativeDifference HarmonicTestFunctionals PressureFunctionals

/-- These are exactly the local smooth equation and uniform finite-energy
hypotheses of the comparison argument. -/
structure Hypotheses (T : ℝ) (u v : VelocityField) (p q : PressureField) : Prop where
  positive : 0 < T
  smooth_u : ContDiffOn ℝ ∞ u (Comparison.slab 0 T)
  smooth_v : ContDiffOn ℝ ∞ v (Comparison.slab 0 T)
  smooth_p : ContDiffOn ℝ ∞ p (Comparison.slab 0 T)
  smooth_q : ContDiffOn ℝ ∞ q (Comparison.slab 0 T)
  div_u : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence u t x = 0
  div_v : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence v t x = 0
  equation : ∀ t ∈ Ioo 0 T, ∀ x,
    navierStokesResidual u p t x = navierStokesResidual v q t x
  energy_u : NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) u
  energy_v : NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v

/-- Velocity average, given by `timeAverage T a (fun z => (u - v) z k)`. -/
def velocityAverage (T : ℝ) (a : ℝ → ℝ) (u v : VelocityField) (k : Fin 3) : Space → ℝ :=
  timeAverage T a (fun z => (u - v) z k)

/-- Tensor average, given by `timeAverage T a (fun z => tensorDiff u v z.1 i j z.2)`. -/
def tensorAverage (T : ℝ) (a : ℝ → ℝ) (u v : VelocityField)
    (i j : Fin 3) : Space → ℝ :=
  timeAverage T a (fun z => tensorDiff u v z.1 i j z.2)

theorem continuous_deriv_of_smooth {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) :
    Continuous (deriv a) := by
  have hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)
  change Continuous (fun t => fderiv ℝ a t 1)
  exact ((ha.fderiv_right hinf).clm_apply contDiff_const).continuous

theorem Hypotheses.velocityAverage_memLp {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T)) (k : Fin 3) :
    MemLp (velocityAverage T a u v k) 2 :=
  timeAverage_difference_component_memLp_two ha H.smooth_u.continuousOn H.smooth_v.continuousOn
    H.energy_u H.energy_v k

theorem Hypotheses.tensorAverage_integrable {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T)) (i j : Fin 3) :
    Integrable (tensorAverage T a u v i j) :=
  timeAverage_tensorDiff_integrable ha H.smooth_u.continuousOn H.smooth_v.continuousOn
    H.energy_u H.energy_v i j

theorem Hypotheses.tensor_bound {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, ∀ i j : Fin 3,
      Integrable (tensorDiff u v t i j) ∧ (∫ x, ‖tensorDiff u v t i j x‖) ≤ M :=
  uniformFiniteEnergy_tensorDiff_bound
    (fun _t ht => (spatial_smooth H.smooth_u ht).continuous.aestronglyMeasurable)
    (fun _t ht => (spatial_smooth H.smooth_v ht).continuous.aestronglyMeasurable)
    H.energy_u H.energy_v

theorem velocityAverage_pairing {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T))
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, velocityAverage T a u v k x * ψ x) =
      ∫ t in Icc 0 T, a t * (∫ x, (u - v) (t, x) k * ψ x) := by
  obtain ⟨M, _, hM⟩ := uniformFiniteEnergy_difference_component_l2Sq_bound
    H.smooth_u.continuousOn H.smooth_v.continuousOn H.energy_u H.energy_v k
  have hf : ContinuousOn (fun z => (u - v) z k) (Comparison.slab 0 T) :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_continuousOn
      (H.smooth_u.continuousOn.sub H.smooth_v.continuousOn)
  have h := timeAverage_complex_pairing_of_memLp_two
    (f := fun z => (u - v) z k) (ψ := (realTest ψ hψ hcψ : Space → ℂ)) ha hf
    (fun t ht => (hM t ht).1) (fun t ht => (hM t ht).2)
    (realTest ψ hψ hcψ).continuous ((realTest ψ hψ hcψ).memLp 2)
  apply Complex.ofReal_injective
  simpa only [velocityAverage, realTest_apply, ← Complex.ofReal_mul, integral_complex_ofReal] using
      h

theorem tensorAverage_pairing {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T))
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (i j : Fin 3) :
    (∫ x, tensorAverage T a u v i j x * ψ x) =
      ∫ t in Icc 0 T, a t * (∫ x, tensorDiff u v t i j x * ψ x) := by
  obtain ⟨M, _, hM⟩ := H.tensor_bound
  obtain ⟨C, hC⟩ := hcψ.exists_bound_of_continuous hψ.continuous
  have h := timeAverage_complex_pairing_of_bounded
    (f := fun z => tensorDiff u v z.1 i j z.2)
    (ψ := (realTest ψ hψ hcψ : Space → ℂ)) ha
    (continuousOn_tensorDiff_field H.smooth_u.continuousOn H.smooth_v.continuousOn i j)
    (fun t ht => (hM t ht i j).1) (fun t ht => (hM t ht i j).2)
    (realTest ψ hψ hcψ).continuous ⟨C, fun x => by simpa using hC x⟩
  apply Complex.ofReal_injective
  simpa only [tensorAverage, realTest_apply, ← Complex.ofReal_mul, integral_complex_ofReal] using h

/-- Fubini for the actual canonical pressure pairing. The Riesz test is
bounded, so the uniform tensor `L¹` bound controls the whole product. -/
theorem pressurePair_tensorAverage {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T))
    (i j : Fin 3) (ψ : ComplexTest) :
    pressurePair i j (tensorAverage T a u v i j) ψ =
      ∫ t in Icc 0 T, (a t : ℂ) * pressurePair i j (tensorDiff u v t i j) ψ := by
  obtain ⟨M, _, hM⟩ := H.tensor_bound
  obtain ⟨C, _, hC⟩ := RieszTestOperators.exists_bound_rieszTest i j ψ
  exact timeAverage_complex_pairing_of_bounded ha
    (continuousOn_tensorDiff_field H.smooth_u.continuousOn H.smooth_v.continuousOn i j)
    (fun t ht => (hM t ht i j).1) (fun t ht => (hM t ht i j).2)
    (RieszTestOperators.continuous_rieszTest i j ψ)
    ⟨C, hC⟩

theorem noncanonical_average_identity {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, (velocityAverage T a u v k x : ℂ) * laplacianCLM (realTest ψ hψ hcψ) x) +
      (∫ x, (velocityAverage T (deriv a) u v k x : ℂ) * realTest ψ hψ hcψ x) +
      (∑ i : Fin 3, ∫ x, (tensorAverage T a u v k i x : ℂ) *
        partialCLM i (realTest ψ hψ hcψ) x) =
      ((∫ t in Icc 0 T, a t *
        (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) : ℝ) : ℂ) := by
  have hsum : (∑ i : Fin 3, ∫ x, tensorAverage T a u v k i x * spatialPartial i ψ x) =
      ∫ t in Icc 0 T, a t * (∑ i : Fin 3, ∫ x, tensorDiff u v t k i x * spatialPartial i ψ x) := by
    have hpair : (∑ i : Fin 3, ∫ x, tensorAverage T a u v k i x * spatialPartial i ψ x) =
        ∑ i : Fin 3, ∫ t in Icc 0 T, a t * (∫ x, tensorDiff u v t k i x * spatialPartial i ψ x) :=
            by
      apply Finset.sum_congr rfl
      intro i _
      exact tensorAverage_pairing (ψ := spatialPartial i ψ) H ha.continuous.continuousOn
        (spatial_partial_contDiff hψ i) (CompactEnergy.compact_partial hcψ i) k i
    rw [hpair]
    simp only [Finset.mul_sum]
    exact (integral_finsetSum _ (fun i _ =>
      (ha.continuous.continuousOn.mul
        (PressureTemporalIdentity.tensor_test_continuousOn H.smooth_u.continuousOn
          H.smooth_v.continuousOn (spatial_partial_contDiff hψ i).continuous
            (CompactEnergy.compact_partial hcψ i) k i)).integrableOn_Icc)).symm
  have hreal : (∫ x, velocityAverage T a u v k x * scalarLaplacian ψ x) +
      (∫ x, velocityAverage T (deriv a) u v k x * ψ x) +
      (∑ i : Fin 3, ∫ x, tensorAverage T a u v k i x * spatialPartial i ψ x) =
      ∫ t in Icc 0 T, a t *
        (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) := by
    rw [velocityAverage_pairing H ha.continuous.continuousOn (scalarLaplacian_contDiff hψ)
        (compact_scalarLaplacian hcψ) k,
      velocityAverage_pairing H (continuous_deriv_of_smooth ha).continuousOn hψ hcψ k, hsum]
    exact (PressureTemporalIdentity.pressure_time_identity H.positive H.smooth_u H.smooth_v
      H.smooth_p H.smooth_q H.div_u H.div_v H.equation ha hsupp hψ hcψ k).symm
  simp only [laplacianCLM_realTest, partialCLM_realTest, realTest_apply,
    ← Complex.ofReal_mul, integral_complex_ofReal]
  change ((∫ x, velocityAverage T a u v k x * scalarLaplacian ψ x : ℝ) : ℂ) +
      ((∫ x, velocityAverage T (deriv a) u v k x * ψ x : ℝ) : ℂ) +
      (∑ i : Fin 3, ∫ x, (tensorAverage T a u v k i x : ℂ) *
        ((spatialPartial i ψ x : ℝ) : ℂ)) = _
  simpa only [← Complex.ofReal_mul, integral_complex_ofReal, Complex.ofReal_add,
    Complex.ofReal_sum] using congrArg Complex.ofReal hreal

theorem averaged_value_realTest {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    averagedPressureDifferenceValue (velocityAverage T a u v k)
      (velocityAverage T (deriv a) u v k) (tensorAverage T a u v) k (realTest ψ hψ hcψ) =
      ((∫ t in Icc 0 T, a t *
        (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) : ℝ) : ℂ) +
      ∑ i : Fin 3, ∑ j : Fin 3,
        pressurePair i j (tensorAverage T a u v i j) (partialCLM k (realTest ψ hψ hcψ)) := by
  unfold averagedPressureDifferenceValue
  rw [noncanonical_average_identity H ha hsupp hψ hcψ k]

/-- Averaging the differentiated Poisson equation commutes with each compact
tensor pairing. All derivatives remain on the compact test. -/
theorem averaged_gradient_poisson {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ t in Icc 0 T, a t *
      (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * scalarLaplacian ψ x)) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, tensorAverage T a u v i j x *
        spatialPartial i (spatialPartial j (spatialPartial k ψ)) x := by
  have hD (i j : Fin 3) :
      ContDiff ℝ ∞ (spatialPartial i (spatialPartial j (spatialPartial k ψ))) :=
    spatial_partial_contDiff (spatial_partial_contDiff (spatial_partial_contDiff hψ k) j) i
  have hC (i j : Fin 3) :
      HasCompactSupport (spatialPartial i (spatialPartial j (spatialPartial k ψ))) :=
    CompactEnergy.compact_partial
      (CompactEnergy.compact_partial (CompactEnergy.compact_partial hcψ k) j) i
  have hi (i j : Fin 3) : IntegrableOn (fun t => a t * (∫ x, tensorDiff u v t i j x *
      spatialPartial i (spatialPartial j (spatialPartial k ψ)) x)) (Icc 0 T) :=
    (ha.continuous.continuousOn.mul
      (PressureTemporalIdentity.tensor_test_continuousOn H.smooth_u.continuousOn
        H.smooth_v.continuousOn (hD i j).continuous (hC i j) i j)).integrableOn_Icc
  have hpoint : (fun t => a t *
      (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * scalarLaplacian ψ x)) =
      (fun t => a t * (∑ i : Fin 3, ∑ j : Fin 3, ∫ x, tensorDiff u v t i j x *
        spatialPartial i (spatialPartial j (spatialPartial k ψ)) x)) := by
    funext t
    by_cases ht : t ∈ Ioo 0 T
    · rw [gradient_poisson_test H.smooth_u H.smooth_v H.smooth_p H.smooth_q ht
        H.div_u H.div_v (H.equation t ht) hψ hcψ k]
    · have hat : a t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hsupp h))
      simp only [hat, zero_mul]
  rw [hpoint]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact (tensorAverage_pairing (ψ := spatialPartial i (spatialPartial j (spatialPartial k ψ)))
    H ha.continuous.continuousOn (hD i j) (hC i j) i j).symm

theorem averaged_gradient_poisson_complex {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    ((∫ t in Icc 0 T, a t *
      (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * scalarLaplacian ψ x) : ℝ) : ℂ) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, (tensorAverage T a u v i j x : ℂ) *
        partialCLM i (partialCLM j (partialCLM k (realTest ψ hψ hcψ))) x := by
  have htest (i j : Fin 3) :
      partialCLM i (partialCLM j (partialCLM k (realTest ψ hψ hcψ))) =
        realTest (spatialPartial i (spatialPartial j (spatialPartial k ψ)))
          (spatial_partial_contDiff (spatial_partial_contDiff
            (spatial_partial_contDiff hψ k) j) i)
          (CompactEnergy.compact_partial (CompactEnergy.compact_partial
            (CompactEnergy.compact_partial hcψ k) j) i) :=
    (congrArg (fun t => partialCLM i (partialCLM j t))
      (partialCLM_realTest ψ hψ hcψ k)).trans
      ((congrArg (partialCLM i) (partialCLM_realTest (spatialPartial k ψ)
        (spatial_partial_contDiff hψ k) (CompactEnergy.compact_partial hcψ k) j)).trans
        (partialCLM_realTest (spatialPartial j (spatialPartial k ψ))
          (spatial_partial_contDiff (spatial_partial_contDiff hψ k) j)
          (CompactEnergy.compact_partial (CompactEnergy.compact_partial hcψ k) j) i))
  simp only [htest]
  change _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, (tensorAverage T a u v i j x : ℂ) *
    ((spatialPartial i (spatialPartial j (spatialPartial k ψ)) x : ℝ) : ℂ)
  simpa only [← Complex.ofReal_mul, integral_complex_ofReal, Complex.ofReal_sum] using
    congrArg Complex.ofReal (averaged_gradient_poisson H ha hsupp hψ hcψ k)

/-- The averaged physical-minus-canonical pressure-gradient functional is
harmonic on every compact real test, by the two actual Poisson identities. -/
theorem averaged_value_real_harmonic {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    averagedPressureDifferenceValue (velocityAverage T a u v k)
      (velocityAverage T (deriv a) u v k) (tensorAverage T a u v) k
        (laplacianCLM (realTest ψ hψ hcψ)) = 0 := by
  calc
    _ = ((∫ t in Icc 0 T, a t *
        (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * scalarLaplacian ψ x) : ℝ) : ℂ) +
        ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorAverage T a u v i j)
          (partialCLM k (laplacianCLM (realTest ψ hψ hcψ))) := by
      simpa only [laplacianCLM_realTest] using
        averaged_value_realTest H ha hsupp (scalarLaplacian_contDiff hψ)
          (compact_scalarLaplacian hcψ) k
    _ = ((∫ t in Icc 0 T, a t *
        (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * scalarLaplacian ψ x) : ℝ) : ℂ) -
        (∑ i : Fin 3, ∑ j : Fin 3, ∫ x, (tensorAverage T a u v i j x : ℂ) *
          partialCLM i (partialCLM j (partialCLM k (realTest ψ hψ hcψ))) x) := by
      simp only [partial_laplacian_realTest, RieszTestOperators.pressurePair_laplacianCLM,
        Finset.sum_neg_distrib, sub_eq_add_neg]
    _ = 0 := by
      rw [averaged_gradient_poisson_complex H ha hsupp hψ hcψ k, sub_self]

/-- The genuine `H³` bound and compact harmonicity force the whole averaged
functional to vanish. No representative of the physical pressure on Schwartz
tests has been introduced. -/
theorem averaged_value_zero {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T) (k : Fin 3) (ψ : ComplexTest) :
    averagedPressureDifferenceValue (velocityAverage T a u v k)
      (velocityAverage T (deriv a) u v k) (tensorAverage T a u v) k ψ = 0 := by
  have hW0 := H.velocityAverage_memLp ha.continuous.continuousOn k
  have hW1 := H.velocityAverage_memLp (continuous_deriv_of_smooth ha).continuousOn k
  have hG := H.tensorAverage_integrable ha.continuous.continuousOn
  let F : ComplexTest →ₗ[ℂ] ℂ := averagedPressureDifference (velocityAverage T a u v k)
    (velocityAverage T (deriv a) u v k) (tensorAverage T a u v) hW0 hW1 hG k
  obtain ⟨C, hC, hbound⟩ := averagedPressureDifference_bound hW0 hW1 hG k
  have hharmonic : ∀ φ : ComplexTest, HasCompactSupport (φ : Space → ℂ) →
      F (laplacianCLM φ) = 0 := by
    apply compact_harmonic_of_real F
    intro φ hφ hcφ
    simpa only [F, averagedPressureDifference_apply] using
      averaged_value_real_harmonic H ha hsupp hφ hcφ k
  have hz : F = 0 := eq_zero_of_compact_harmonic F hC hbound hharmonic
  have hvalue : F ψ = 0 := by rw [hz]; rfl
  simpa only [F, averagedPressureDifference_apply] using hvalue

/-- The uniform tensor bound and spatial decay of a Riesz test give
continuity of its canonical pairing in time, including the slab endpoints. -/
theorem pressurePair_continuousOn {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (i j : Fin 3) (ψ : ComplexTest) :
    ContinuousOn (fun t => pressurePair i j (tensorDiff u v t i j) ψ) (Icc 0 T) := by
  obtain ⟨M, _, hM⟩ := H.tensor_bound
  exact WeakTimeContinuity.continuousOn_pairing
    (continuousOn_tensorDiff_field H.smooth_u.continuousOn H.smooth_v.continuousOn i j)
    (fun t ht => (hM t ht i j).1) (fun t ht => (hM t ht i j).2)
    (RieszTestOperators.continuous_rieszTest i j ψ)
    (RieszTestOperators.rieszTest_tendsto_zero i j ψ)

theorem canonical_sum_continuousOn {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ψ : ComplexTest) :
    ContinuousOn (fun t => ∑ i : Fin 3, ∑ j : Fin 3,
      pressurePair i j (tensorDiff u v t i j) ψ) (Icc 0 T) :=
  continuousOn_finsetSum _ (fun i _ =>
    continuousOn_finsetSum _ (fun j _ => pressurePair_continuousOn H i j ψ))

theorem canonical_sum_timeAverage {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T))
    (ψ : ComplexTest) :
    (∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorAverage T a u v i j) ψ) =
      ∫ t in Icc 0 T, (a t : ℂ) *
        (∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorDiff u v t i j) ψ) := by
  have hi (i j : Fin 3) : IntegrableOn (fun t =>
      (a t : ℂ) * pressurePair i j (tensorDiff u v t i j) ψ) (Icc 0 T) :=
    ((Complex.continuous_ofReal.comp_continuousOn ha).mul
      (pressurePair_continuousOn H i j ψ)).integrableOn_Icc
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorAverage T a u v i j) ψ) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ t in Icc 0 T,
        (a t : ℂ) * pressurePair i j (tensorDiff u v t i j) ψ := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact pressurePair_tensorAverage H ha i j ψ
  rw [hsum]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_finsetSum _ (fun j _ => hi i j)).symm

/-- Every compact temporal test annihilates the difference between the
physical and canonical pressure gradients, at a fixed compact spatial test. -/
theorem time_test_gradient_difference_zero {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ t in Icc 0 T, a t •
      (((∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x : ℝ) : ℂ) +
        ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorDiff u v t i j)
          (partialCLM k (realTest ψ hψ hcψ)))) = 0 := by
  let P : ℝ → ℝ := fun t => ∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x
  let Ψ := partialCLM k (realTest ψ hψ hcψ)
  let Q : ℝ → ℂ := fun t => ∑ i : Fin 3, ∑ j : Fin 3,
    pressurePair i j (tensorDiff u v t i j) Ψ
  have hP : ContinuousOn P (Ioo 0 T) :=
    pressure_gradient_pairing_continuousOn H.smooth_u H.smooth_v H.smooth_p H.smooth_q
      H.div_u H.div_v H.equation hψ hcψ k
  have hPweight : Continuous (fun t => a t * P t) :=
    PressureTemporalIdentity.continuous_cutoff_mul ha.continuous hP isOpen_Ioo hsupp
  have hiP : IntegrableOn (fun t => (a t : ℂ) * (P t : ℂ)) (Icc 0 T) := by
    have hi : IntegrableOn (fun t => ((a t * P t : ℝ) : ℂ)) (Icc 0 T) :=
      (Complex.continuous_ofReal.comp hPweight).continuousOn.integrableOn_Icc
    simpa only [Complex.ofReal_mul] using hi
  have hQ : ContinuousOn Q (Icc 0 T) := canonical_sum_continuousOn H Ψ
  have hiQ : IntegrableOn (fun t => (a t : ℂ) * Q t) (Icc 0 T) :=
    ((Complex.continuous_ofReal.comp_continuousOn ha.continuous.continuousOn).mul
        hQ).integrableOn_Icc
  have hz := averaged_value_zero H ha hsupp k (realTest ψ hψ hcψ)
  rw [averaged_value_realTest H ha hsupp hψ hcψ k] at hz
  change (((∫ t in Icc 0 T, a t * P t : ℝ) : ℂ) +
    ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorAverage T a u v i j) Ψ) = 0 at hz
  rw [canonical_sum_timeAverage H ha.continuous.continuousOn Ψ] at hz
  change (∫ t in Icc 0 T, a t • ((P t : ℂ) + Q t)) = 0
  simp only [Complex.real_smul, mul_add]
  rw [integral_add hiP hiQ]
  simp only [← Complex.ofReal_mul, integral_complex_ofReal]
  exact hz

/-- Actual pressure-gradient recovery at every interior time. This equality
is obtained from the equation and uniform finite energy, rather than assumed
as a pressure normalization. -/
theorem gradient_recovery_complex {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ht : t ∈ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    ((∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x : ℝ) : ℂ) =
      -(∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorDiff u v t i j)
        (partialCLM k (realTest ψ hψ hcψ))) := by
  have hP := pressure_gradient_pairing_continuousOn
    H.smooth_u H.smooth_v H.smooth_p H.smooth_q H.div_u H.div_v H.equation hψ hcψ k
  have hQ := canonical_sum_continuousOn H (partialCLM k (realTest ψ hψ hcψ))
  have hcontinuous := (Complex.continuous_ofReal.comp_continuousOn hP).add
    (hQ.mono Ioo_subset_Icc_self)
  have hzero := TemporalTestUniqueness.eq_zero_on_Ioo_of_setIntegral_tests hcontinuous (by
    intro a ha _hca hsupp
    exact time_test_gradient_difference_zero H ha hsupp hψ hcψ k)
  exact eq_neg_of_add_eq_zero_left (hzero t ht)

theorem gradient_recovery {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ht : t ∈ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) =
      -(∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorDiff u v t i j)
        (partialCLM k (realTest ψ hψ hcψ))).re := by
  simpa only [Complex.ofReal_re, Complex.neg_re] using
    congrArg Complex.re (gradient_recovery_complex H ht hψ hcψ k)

/-- The explicit comparison-hypothesis form of pressure recovery. Only the
spatial test is compactly supported; both velocities and both pressures are
allowed on all of Euclidean space. -/
theorem pressure_gradient_recovery {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (hT : 0 < T)
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hdivu : ∀ s ∈ Ioo 0 T, ∀ x, spatialDivergence u s x = 0)
    (hdivv : ∀ s ∈ Ioo 0 T, ∀ x, spatialDivergence v s x = 0)
    (hNS : ∀ s ∈ Ioo 0 T, ∀ x,
      navierStokesResidual u p s x = navierStokesResidual v q s x)
    (heu : NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) u)
    (hev : NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v)
    (ht : t ∈ Ioo 0 T) {ψ : Space → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) =
      -(∑ i : Fin 3, ∑ j : Fin 3, (pressurePair i j (tensorDiff u v t i j)
        (partialCLM k (realTest ψ hψ hcψ))).re) := by
  let H : Hypotheses T u v p q := ⟨hT, hu, hv, hp, hq, hdivu, hdivv, hNS, heu, hev⟩
  have h := congrArg (fun z : ℂ => Complex.reCLM z) (gradient_recovery_complex H ht hψ hcψ k)
  simpa only [map_neg, map_sum, Complex.reCLM_apply, Complex.ofReal_re] using h

end NavierStokesR3.PressureRecovery
