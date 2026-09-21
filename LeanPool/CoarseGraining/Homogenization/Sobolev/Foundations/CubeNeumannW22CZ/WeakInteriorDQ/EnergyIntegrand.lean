/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.DifferenceQuotientH1
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H1Graph.Preliminaries
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.QuantitativeCutoff
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Order.Filter.Finite

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.TestSubmodule

/-! # Energy Integrand -/

namespace Homogenization

open scoped Manifold
open scoped ENNReal Topology

noncomputable section

namespace WeakPoissonEquationOn

variable {d : ℕ} {U V : Set (Vec d)}
variable {u : H1Function U} {f : Vec d → ℝ}


/-!
# Localized difference-quotient tests for weak Poisson equations

These lemmas are the first formal bridge in the difference-quotient route to
the interior `H²` estimate.  They say that after restricting the weak equation
to an interior domain `V`, the smooth-cutoff times forward/backward
difference quotient tests constructed in `DifferenceQuotientH1` are legal
`H¹₀(V)` tests.
-/

/-- Algebraic splitting of the cutoff-energy integrand. -/
theorem vecDot_cutoff_energy_integrand (A B : Vec d) (a b : ℝ) :
    vecDot A (fun j => a * A j + b * B j) =
      a * vecDot A A + b * vecDot A B := by
  have hA : (fun j => a * A j) = a • A := by
    ext j
    simp
  have hB : (fun j => b * B j) = b • B := by
    ext j
    simp
  rw [show (fun j => a * A j + b * B j) = a • A + b • B by
    ext j
    simp]
  simp [vecDot_add_right, vecDot_smul_right]

/-- A coordinate square is bounded by the full squared Euclidean norm. -/
theorem coord_sq_le_vecNormSq (A : Vec d) (i : Fin d) :
    A i ^ 2 ≤ vecNormSq A := by
  unfold vecNormSq vecDot
  simpa [pow_two] using
    Finset.single_le_sum (fun j _ => sq_nonneg (A j)) (Finset.mem_univ i)

/-- Pointwise Young bound for the cutoff-error term when the cutoff is a
square, so the gradient contribution has the form `2η ∇η`. -/
theorem abs_sq_cutoff_error_integrand_le
    (η w : ℝ) (A B : Vec d) :
    |w * vecDot A (fun j => 2 * η * B j)| ≤
      η ^ 2 * vecNormSq A / 2 + 2 * w ^ 2 * vecNormSq B := by
  have hyoung :=
    abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq η (2 * w) A B
  have harg :
      η * (2 * w) * vecDot A B =
        w * vecDot A (fun j => 2 * η * B j) := by
    rw [show (fun j => 2 * η * B j) = (2 * η) • B by
      ext j
      simp]
    rw [vecDot_smul_right]
    ring
  have hrhs :
      η ^ 2 * vecNormSq A / 2 + (2 * w) ^ 2 * vecNormSq B / 2 =
        η ^ 2 * vecNormSq A / 2 + 2 * w ^ 2 * vecNormSq B := by
    ring
  simpa [harg, hrhs] using hyoung

/-- Non-absolute-value form of `abs_sq_cutoff_error_integrand_le`. -/
theorem sq_cutoff_error_integrand_le
    (η w : ℝ) (A B : Vec d) :
    w * vecDot A (fun j => 2 * η * B j) ≤
      η ^ 2 * vecNormSq A / 2 + 2 * w ^ 2 * vecNormSq B :=
  (le_abs_self _).trans (abs_sq_cutoff_error_integrand_le η w A B)

/-- The same pointwise bound for the negative cutoff-error term. -/
theorem neg_sq_cutoff_error_integrand_le
    (η w : ℝ) (A B : Vec d) :
    -w * vecDot A (fun j => 2 * η * B j) ≤
      η ^ 2 * vecNormSq A / 2 + 2 * w ^ 2 * vecNormSq B := by
  have hneg : -w * vecDot A (fun j => 2 * η * B j) =
      -(w * vecDot A (fun j => 2 * η * B j)) := by
    ring
  rw [hneg]
  exact (neg_le_abs _).trans (abs_sq_cutoff_error_integrand_le η w A B)

/-- Integral absorption algebra for a cutoff energy identity.

If `main + cross = rhs` after integration and the pointwise estimate
`-cross ≤ main / 2 + error` is integrable, then half of the main energy is
controlled by the right-hand side plus the error term. -/
theorem integral_half_main_le_rhs_add_error_of_add_energy_identity
    {m c r e : Vec d → ℝ}
    (henergy :
      ∫ x in V, (m x + c x) ∂MeasureTheory.volume =
        ∫ x in V, r x ∂MeasureTheory.volume)
    (hpoint :
      (fun x => -c x) ≤ᵐ[MeasureTheory.volume.restrict V]
        fun x => m x / 2 + e x)
    (hm : MeasureTheory.IntegrableOn m V)
    (hc : MeasureTheory.IntegrableOn c V)
    (he : MeasureTheory.IntegrableOn e V) :
    (1 / 2 : ℝ) * ∫ x in V, m x ∂MeasureTheory.volume ≤
      ∫ x in V, r x ∂MeasureTheory.volume +
        ∫ x in V, e x ∂MeasureTheory.volume := by
  have hleft_sum :
      ∫ x in V, (m x + c x) ∂MeasureTheory.volume =
        ∫ x in V, m x ∂MeasureTheory.volume +
          ∫ x in V, c x ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_add hm hc]
  have hmain_eq :
      ∫ x in V, m x ∂MeasureTheory.volume =
        ∫ x in V, r x ∂MeasureTheory.volume -
          ∫ x in V, c x ∂MeasureTheory.volume := by
    linarith
  have hneg_int : MeasureTheory.IntegrableOn (fun x => -c x) V := hc.neg
  have hhalf_int : MeasureTheory.IntegrableOn (fun x => m x / 2) V := by
    simpa [div_eq_mul_inv, mul_comm] using! hm.const_mul ((2 : ℝ)⁻¹)
  have hbound_int : MeasureTheory.IntegrableOn (fun x => m x / 2 + e x) V :=
    hhalf_int.add he
  have hmono := MeasureTheory.integral_mono_ae hneg_int hbound_int hpoint
  have hneg_eq :
      ∫ x in V, -c x ∂MeasureTheory.volume =
        -∫ x in V, c x ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_neg]
  have hhalf_eq :
      ∫ x in V, m x / 2 ∂MeasureTheory.volume =
        (1 / 2 : ℝ) * ∫ x in V, m x ∂MeasureTheory.volume := by
    calc
      ∫ x in V, m x / 2 ∂MeasureTheory.volume =
          ∫ x in V, (1 / 2 : ℝ) * m x ∂MeasureTheory.volume := by
            congr with x
            ring
      _ = (1 / 2 : ℝ) * ∫ x in V, m x ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
  have hbound_eq :
      ∫ x in V, (m x / 2 + e x) ∂MeasureTheory.volume =
        (1 / 2 : ℝ) * ∫ x in V, m x ∂MeasureTheory.volume +
          ∫ x in V, e x ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_add hhalf_int he]
    rw [hhalf_eq]
  rw [hneg_eq, hbound_eq] at hmono
  nlinarith

/-- Integral absorption algebra for a cutoff energy identity with a scalar
right-hand side.

This variant is useful for the direct difference-quotient test, whose forcing
term naturally remains as an ambient integral over the original domain. -/
theorem integral_half_main_le_scalar_rhs_add_error_of_add_energy_identity
    {m c e : Vec d → ℝ} {R : ℝ}
    (henergy :
      ∫ x in V, (m x + c x) ∂MeasureTheory.volume = R)
    (hpoint :
      (fun x => -c x) ≤ᵐ[MeasureTheory.volume.restrict V]
        fun x => m x / 2 + e x)
    (hm : MeasureTheory.IntegrableOn m V)
    (hc : MeasureTheory.IntegrableOn c V)
    (he : MeasureTheory.IntegrableOn e V) :
    (1 / 2 : ℝ) * ∫ x in V, m x ∂MeasureTheory.volume ≤
      R + ∫ x in V, e x ∂MeasureTheory.volume := by
  have hleft_sum :
      ∫ x in V, (m x + c x) ∂MeasureTheory.volume =
        ∫ x in V, m x ∂MeasureTheory.volume +
          ∫ x in V, c x ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_add hm hc]
  have hmain_eq :
      ∫ x in V, m x ∂MeasureTheory.volume =
        R - ∫ x in V, c x ∂MeasureTheory.volume := by
    linarith
  have hneg_int : MeasureTheory.IntegrableOn (fun x => -c x) V := hc.neg
  have hhalf_int : MeasureTheory.IntegrableOn (fun x => m x / 2) V := by
    simpa [div_eq_mul_inv, mul_comm] using! hm.const_mul ((2 : ℝ)⁻¹)
  have hbound_int : MeasureTheory.IntegrableOn (fun x => m x / 2 + e x) V :=
    hhalf_int.add he
  have hmono := MeasureTheory.integral_mono_ae hneg_int hbound_int hpoint
  have hneg_eq :
      ∫ x in V, -c x ∂MeasureTheory.volume =
        -∫ x in V, c x ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_neg]
  have hhalf_eq :
      ∫ x in V, m x / 2 ∂MeasureTheory.volume =
        (1 / 2 : ℝ) * ∫ x in V, m x ∂MeasureTheory.volume := by
    calc
      ∫ x in V, m x / 2 ∂MeasureTheory.volume =
          ∫ x in V, (1 / 2 : ℝ) * m x ∂MeasureTheory.volume := by
            congr with x
            ring
      _ = (1 / 2 : ℝ) * ∫ x in V, m x ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
  have hbound_eq :
      ∫ x in V, (m x / 2 + e x) ∂MeasureTheory.volume =
        (1 / 2 : ℝ) * ∫ x in V, m x ∂MeasureTheory.volume +
          ∫ x in V, e x ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_add hhalf_int he]
    rw [hhalf_eq]
  rw [hneg_eq, hbound_eq] at hmono
  nlinarith

/-- Pointwise Young's inequality integrated over a set, in the sign needed for
the direct forcing term. -/
theorem neg_integral_mul_le_half_integral_sq_add_half_integral_sq_of_memScalarL2
    {F G : Vec d → ℝ} (hF : MemScalarL2 U F) (hG : MemScalarL2 U G) :
    -∫ x in U, F x * G x ∂MeasureTheory.volume ≤
      (1 / 2 : ℝ) * ∫ x in U, F x ^ 2 ∂MeasureTheory.volume +
        (1 / 2 : ℝ) * ∫ x in U, G x ^ 2 ∂MeasureTheory.volume := by
  have hFG : MeasureTheory.IntegrableOn (fun x => F x * G x) U :=
    hF.integrable_mul hG
  have hneg : MeasureTheory.IntegrableOn (fun x => -(F x * G x)) U :=
    hFG.neg
  have hFsq : MeasureTheory.IntegrableOn (fun x => F x ^ 2) U := by
    simpa [pow_two, MeasureTheory.IntegrableOn, volumeMeasureOn] using!
      hF.integrable_mul hF
  have hGsq : MeasureTheory.IntegrableOn (fun x => G x ^ 2) U := by
    simpa [pow_two, MeasureTheory.IntegrableOn, volumeMeasureOn] using!
      hG.integrable_mul hG
  have hFhalf : MeasureTheory.IntegrableOn (fun x => F x ^ 2 / 2) U := by
    simpa [div_eq_mul_inv, mul_comm] using! hFsq.const_mul ((2 : ℝ)⁻¹)
  have hGhalf : MeasureTheory.IntegrableOn (fun x => G x ^ 2 / 2) U := by
    simpa [div_eq_mul_inv, mul_comm] using! hGsq.const_mul ((2 : ℝ)⁻¹)
  have hright :
      MeasureTheory.IntegrableOn (fun x => F x ^ 2 / 2 + G x ^ 2 / 2) U :=
    hFhalf.add hGhalf
  have hpoint :
      (fun x => -(F x * G x)) ≤ᵐ[MeasureTheory.volume.restrict U]
        fun x => F x ^ 2 / 2 + G x ^ 2 / 2 := by
    filter_upwards with x
    nlinarith [sq_nonneg (F x + G x)]
  have hmono := MeasureTheory.integral_mono_ae hneg hright hpoint
  have hneg_eq :
      ∫ x in U, -(F x * G x) ∂MeasureTheory.volume =
        -∫ x in U, F x * G x ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_neg]
  have hFhalf_eq :
      ∫ x in U, F x ^ 2 / 2 ∂MeasureTheory.volume =
        (1 / 2 : ℝ) * ∫ x in U, F x ^ 2 ∂MeasureTheory.volume := by
    calc
      ∫ x in U, F x ^ 2 / 2 ∂MeasureTheory.volume =
          ∫ x in U, (1 / 2 : ℝ) * F x ^ 2 ∂MeasureTheory.volume := by
            congr with x
            ring
      _ = (1 / 2 : ℝ) * ∫ x in U, F x ^ 2 ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
  have hGhalf_eq :
      ∫ x in U, G x ^ 2 / 2 ∂MeasureTheory.volume =
        (1 / 2 : ℝ) * ∫ x in U, G x ^ 2 ∂MeasureTheory.volume := by
    calc
      ∫ x in U, G x ^ 2 / 2 ∂MeasureTheory.volume =
          ∫ x in U, (1 / 2 : ℝ) * G x ^ 2 ∂MeasureTheory.volume := by
            congr with x
            ring
      _ = (1 / 2 : ℝ) * ∫ x in U, G x ^ 2 ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
  have hright_eq :
      ∫ x in U, F x ^ 2 / 2 + G x ^ 2 / 2 ∂MeasureTheory.volume =
        (1 / 2 : ℝ) * ∫ x in U, F x ^ 2 ∂MeasureTheory.volume +
          (1 / 2 : ℝ) * ∫ x in U, G x ^ 2 ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_add hFhalf hGhalf]
    rw [hFhalf_eq, hGhalf_eq]
  rwa [hneg_eq, hright_eq] at hmono

/-- A small-test-coefficient Young bound for the direct forcing term.

This fixed form is tuned for the later Caccioppoli absorption: the forcing
constant is worse, but the test-square coefficient is strictly below the
energy coefficient. -/
theorem neg_integral_mul_le_two_integral_sq_add_eighth_integral_sq_of_memScalarL2
    {F G : Vec d → ℝ} (hF : MemScalarL2 U F) (hG : MemScalarL2 U G) :
    -∫ x in U, F x * G x ∂MeasureTheory.volume ≤
      (2 : ℝ) * ∫ x in U, F x ^ 2 ∂MeasureTheory.volume +
        (1 / 8 : ℝ) * ∫ x in U, G x ^ 2 ∂MeasureTheory.volume := by
  have hFG : MeasureTheory.IntegrableOn (fun x => F x * G x) U :=
    hF.integrable_mul hG
  have hneg : MeasureTheory.IntegrableOn (fun x => -(F x * G x)) U :=
    hFG.neg
  have hFsq : MeasureTheory.IntegrableOn (fun x => F x ^ 2) U := by
    simpa [pow_two, MeasureTheory.IntegrableOn, volumeMeasureOn] using!
      hF.integrable_mul hF
  have hGsq : MeasureTheory.IntegrableOn (fun x => G x ^ 2) U := by
    simpa [pow_two, MeasureTheory.IntegrableOn, volumeMeasureOn] using!
      hG.integrable_mul hG
  have hFtwo : MeasureTheory.IntegrableOn (fun x => (2 : ℝ) * F x ^ 2) U :=
    hFsq.const_mul (2 : ℝ)
  have hGeighth : MeasureTheory.IntegrableOn (fun x => (1 / 8 : ℝ) * G x ^ 2) U :=
    hGsq.const_mul (1 / 8 : ℝ)
  have hright :
      MeasureTheory.IntegrableOn
        (fun x => (2 : ℝ) * F x ^ 2 + (1 / 8 : ℝ) * G x ^ 2) U :=
    hFtwo.add hGeighth
  have hpoint :
      (fun x => -(F x * G x)) ≤ᵐ[MeasureTheory.volume.restrict U]
        fun x => (2 : ℝ) * F x ^ 2 + (1 / 8 : ℝ) * G x ^ 2 := by
    filter_upwards with x
    nlinarith [sq_nonneg ((4 : ℝ) * F x + G x)]
  have hmono := MeasureTheory.integral_mono_ae hneg hright hpoint
  have hneg_eq :
      ∫ x in U, -(F x * G x) ∂MeasureTheory.volume =
        -∫ x in U, F x * G x ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_neg]
  have hFtwo_eq :
      ∫ x in U, (2 : ℝ) * F x ^ 2 ∂MeasureTheory.volume =
        (2 : ℝ) * ∫ x in U, F x ^ 2 ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_const_mul]
  have hGeighth_eq :
      ∫ x in U, (1 / 8 : ℝ) * G x ^ 2 ∂MeasureTheory.volume =
        (1 / 8 : ℝ) * ∫ x in U, G x ^ 2 ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_const_mul]
  have hright_eq :
      ∫ x in U, (2 : ℝ) * F x ^ 2 + (1 / 8 : ℝ) * G x ^ 2
          ∂MeasureTheory.volume =
        (2 : ℝ) * ∫ x in U, F x ^ 2 ∂MeasureTheory.volume +
          (1 / 8 : ℝ) * ∫ x in U, G x ^ 2 ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_add hFtwo hGeighth]
    rw [hFtwo_eq, hGeighth_eq]
  rwa [hneg_eq, hright_eq] at hmono

/-- Multiplying an integrable function by a continuous compactly supported
factor preserves integrability on a restricted domain. -/
theorem integrableOn_mul_left_of_continuous_hasCompactSupport
    {φ F : Vec d → ℝ}
    (hφ : Continuous φ) (hφ_compact : HasCompactSupport φ)
    (hF : MeasureTheory.IntegrableOn F V) :
    MeasureTheory.IntegrableOn (fun x => φ x * F x) V := by
  have hφ_top :
      MeasureTheory.MemLp φ ⊤ (volumeMeasureOn V) :=
    hφ.memLp_top_of_hasCompactSupport hφ_compact (volumeMeasureOn V)
  have hF_int :
      MeasureTheory.Integrable F (volumeMeasureOn V) := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using hF
  simpa [MeasureTheory.IntegrableOn, volumeMeasureOn, Pi.mul_apply] using!
    hF_int.mul_of_top_right hφ_top

/-- Move an `L²` function from an interior set to a larger ambient restricted
measure when its pointwise support is contained in the interior set. -/
theorem memLp_restrict_of_support_subset_of_memLp
    {F : Vec d → ℝ} (hV_meas : MeasurableSet V)
    (hF_support : Function.support F ⊆ V)
    (hF : MeasureTheory.MemLp F 2 (MeasureTheory.volume.restrict V)) :
    MeasureTheory.MemLp F 2 (MeasureTheory.volume.restrict U) := by
  have hindicator_eq : V.indicator F = F := by
    funext x
    by_cases hx : x ∈ V
    · simp [Set.indicator_of_mem hx]
    · have hFx : F x = 0 := by
        by_contra hne
        exact hx (hF_support hne)
      simp [Set.indicator_of_notMem hx, hFx]
  have hindicator_mem :
      MeasureTheory.MemLp (V.indicator F) 2 (MeasureTheory.volume.restrict U) := by
    rw [MeasureTheory.memLp_indicator_iff_restrict hV_meas]
    exact hF.mono_measure
      (MeasureTheory.Measure.restrict_mono_measure
        MeasureTheory.Measure.restrict_le_self V)
  simpa [hindicator_eq] using hindicator_mem

/-- If a function is supported in an interior set `V ⊆ U`, its set integral
over `U` is the same as its set integral over `V`. -/
theorem integral_subset_of_support_subset
    {F : Vec d → ℝ} (hVU : V ⊆ U) (hF_support : Function.support F ⊆ V) :
    ∫ x in U, F x ∂MeasureTheory.volume =
      ∫ x in V, F x ∂MeasureTheory.volume := by
  have hzeroV : ∀ x, x ∉ V → F x = 0 := by
    intro x hxV
    by_contra hne
    exact hxV (hF_support hne)
  have hzeroU : ∀ x, x ∉ U → F x = 0 := by
    intro x hxU
    exact hzeroV x (fun hxV => hxU (hVU hxV))
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzeroU,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzeroV]

/-- If a function is supported in an interior set `V ⊆ U`, its `eLpNorm` on
the ambient restricted measure agrees with its `eLpNorm` on `V`. -/
theorem eLpNorm_restrict_eq_restrict_of_support_subset
    {E : Type*} [NormedAddCommGroup E] {F : Vec d → E} {p : ℝ≥0∞}
    (hVU : V ⊆ U) (hF_support : Function.support F ⊆ V) :
    MeasureTheory.eLpNorm F p (MeasureTheory.volume.restrict U) =
      MeasureTheory.eLpNorm F p (MeasureTheory.volume.restrict V) := by
  have hsupportU : Function.support F ⊆ U := hF_support.trans hVU
  rw [MeasureTheory.eLpNorm_restrict_eq_of_support_subset hsupportU]
  rw [← MeasureTheory.eLpNorm_restrict_eq_of_support_subset hF_support]

/-- Translation invariance of global `eLpNorm` for a coordinate shift. -/
theorem eLpNorm_comp_euclideanCoordShift_of_aestronglyMeasurable
    {F : Vec d → ℝ} (hF : MeasureTheory.AEStronglyMeasurable F MeasureTheory.volume)
    (step : ℝ) (i : Fin d) (p : ℝ≥0∞) :
    MeasureTheory.eLpNorm (fun x => F (euclideanCoordShift step i x)) p
        MeasureTheory.volume =
      MeasureTheory.eLpNorm F p MeasureTheory.volume := by
  let z : Vec d := step • basisVec i
  have hmp :
      MeasureTheory.MeasurePreserving (fun x : Vec d => x + z)
        MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.measurePreserving_add_right MeasureTheory.volume z
  have hcomp :=
    MeasureTheory.eLpNorm_comp_measurePreserving
      (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
      (p := p)
      (g := F) (f := fun x : Vec d => x + z) hF hmp
  simpa [Function.comp, euclideanCoordShift, z] using! hcomp

/-- Backward coordinate difference quotients are continuous on global `L²`.

This is the approximation bridge needed for the direct test: if smooth
approximants converge in `L²`, then their backward difference quotients also
converge in `L²`, with the elementary translation bound. -/
theorem eLpNorm_backwardDifferenceQuotient_sub_le
    {F G : Vec d → ℝ}
    (hΔ : MeasureTheory.AEStronglyMeasurable
      (fun x => F x - G x) MeasureTheory.volume)
    (step : ℝ) (i : Fin d) :
    MeasureTheory.eLpNorm
        (fun x =>
          euclideanBackwardDifferenceQuotient step i F x -
            euclideanBackwardDifferenceQuotient step i G x)
        2 MeasureTheory.volume ≤
      ‖(step⁻¹ : ℝ)‖ₑ *
        (MeasureTheory.eLpNorm (fun x => F x - G x) 2 MeasureTheory.volume +
          MeasureTheory.eLpNorm (fun x => F x - G x) 2 MeasureTheory.volume) := by
  let Δ : Vec d → ℝ := fun x => F x - G x
  have hshift_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun x => Δ (euclideanCoordShift (-step) i x)) MeasureTheory.volume := by
    let z : Vec d := (-step) • basisVec i
    have hmp :
        MeasureTheory.MeasurePreserving (fun x : Vec d => x + z)
          MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.measurePreserving_add_right MeasureTheory.volume z
    simpa [Δ, Function.comp, euclideanCoordShift, z] using!
      hΔ.comp_measurePreserving hmp
  have hshift_norm :
      MeasureTheory.eLpNorm (fun x => Δ (euclideanCoordShift (-step) i x))
          2 MeasureTheory.volume =
        MeasureTheory.eLpNorm Δ 2 MeasureTheory.volume :=
    eLpNorm_comp_euclideanCoordShift_of_aestronglyMeasurable
      (F := Δ) (by simpa [Δ] using hΔ) (-step) i 2
  have hpoint :
      (fun x =>
          euclideanBackwardDifferenceQuotient step i F x -
            euclideanBackwardDifferenceQuotient step i G x) =
        fun x => (step⁻¹ : ℝ) • (Δ x - Δ (euclideanCoordShift (-step) i x)) := by
    funext x
    simp [Δ, euclideanBackwardDifferenceQuotient, div_eq_mul_inv, smul_eq_mul]
    ring
  have hscale :=
    MeasureTheory.eLpNorm_const_smul_le
      (μ := MeasureTheory.volume) (p := (2 : ℝ≥0∞))
      (c := (step⁻¹ : ℝ))
      (f := fun x => Δ x - Δ (euclideanCoordShift (-step) i x))
  have htri :
      MeasureTheory.eLpNorm
          (fun x => Δ x - Δ (euclideanCoordShift (-step) i x))
          2 MeasureTheory.volume ≤
        MeasureTheory.eLpNorm Δ 2 MeasureTheory.volume +
          MeasureTheory.eLpNorm (fun x => Δ (euclideanCoordShift (-step) i x))
            2 MeasureTheory.volume := by
    simpa [sub_eq_add_neg] using!
      MeasureTheory.eLpNorm_add_le
        (μ := MeasureTheory.volume) (p := (2 : ℝ≥0∞))
        hΔ hshift_meas.neg (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  calc
    MeasureTheory.eLpNorm
        (fun x =>
          euclideanBackwardDifferenceQuotient step i F x -
            euclideanBackwardDifferenceQuotient step i G x)
        2 MeasureTheory.volume =
        MeasureTheory.eLpNorm
          ((step⁻¹ : ℝ) •
            (fun x => Δ x - Δ (euclideanCoordShift (-step) i x)))
          2 MeasureTheory.volume := by
          rw [hpoint]
          rfl
    _ ≤ ‖(step⁻¹ : ℝ)‖ₑ *
          MeasureTheory.eLpNorm
            (fun x => Δ x - Δ (euclideanCoordShift (-step) i x))
            2 MeasureTheory.volume := hscale
    _ ≤ ‖(step⁻¹ : ℝ)‖ₑ *
          (MeasureTheory.eLpNorm Δ 2 MeasureTheory.volume +
            MeasureTheory.eLpNorm (fun x => Δ (euclideanCoordShift (-step) i x))
              2 MeasureTheory.volume) :=
          mul_le_mul_right htri _
    _ = ‖(step⁻¹ : ℝ)‖ₑ *
          (MeasureTheory.eLpNorm (fun x => F x - G x) 2 MeasureTheory.volume +
            MeasureTheory.eLpNorm (fun x => F x - G x) 2 MeasureTheory.volume) := by
          rw [hshift_norm]

/-- The difference of two backward difference quotients is globally
a.e.-strongly-measurable when the underlying scalar difference is. -/
theorem aestronglyMeasurable_backwardDifferenceQuotient_sub_of_aestronglyMeasurable
    {F G : Vec d → ℝ}
    (hΔ : MeasureTheory.AEStronglyMeasurable
      (fun x => F x - G x) MeasureTheory.volume)
    (step : ℝ) (i : Fin d) :
    MeasureTheory.AEStronglyMeasurable
      (fun x =>
        euclideanBackwardDifferenceQuotient step i F x -
          euclideanBackwardDifferenceQuotient step i G x)
      MeasureTheory.volume := by
  let Δ : Vec d → ℝ := fun x => F x - G x
  have hshift_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun x => Δ (euclideanCoordShift (-step) i x)) MeasureTheory.volume := by
    let z : Vec d := (-step) • basisVec i
    have hmp :
        MeasureTheory.MeasurePreserving (fun x : Vec d => x + z)
          MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.measurePreserving_add_right MeasureTheory.volume z
    simpa [Δ, Function.comp, euclideanCoordShift, z] using!
      hΔ.comp_measurePreserving hmp
  have hpoint :
      (fun x =>
        euclideanBackwardDifferenceQuotient step i F x -
          euclideanBackwardDifferenceQuotient step i G x) =
        (step⁻¹ : ℝ) •
          (fun x => Δ x - Δ (euclideanCoordShift (-step) i x)) := by
    funext x
    simp [Δ, euclideanBackwardDifferenceQuotient, div_eq_mul_inv, smul_eq_mul]
    ring
  rw [hpoint]
  exact (hΔ.sub hshift_meas).const_smul (step⁻¹ : ℝ)

/-- Convergence in global `L²` is preserved by a fixed backward coordinate
difference quotient, with the elementary translation bound above. -/
theorem tendsto_eLpNorm_backwardDifferenceQuotient_sub_zero
    {F : ℕ → Vec d → ℝ} {G : Vec d → ℝ}
    (hΔ : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun x => F n x - G x) MeasureTheory.volume)
    (hΔ_tendsto :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm (fun x => F n x - G x) 2 MeasureTheory.volume)
        Filter.atTop (nhds 0))
    (step : ℝ) (i : Fin d) :
    Filter.Tendsto
      (fun n =>
        MeasureTheory.eLpNorm
          (fun x =>
            euclideanBackwardDifferenceQuotient step i (F n) x -
              euclideanBackwardDifferenceQuotient step i G x)
          2 MeasureTheory.volume)
      Filter.atTop (nhds 0) := by
  let A : ℕ → ℝ≥0∞ := fun n =>
    MeasureTheory.eLpNorm (fun x => F n x - G x) 2 MeasureTheory.volume
  have hsum :
      Filter.Tendsto (fun n => A n + A n) Filter.atTop (nhds 0) := by
    simpa [A, zero_add] using hΔ_tendsto.add hΔ_tendsto
  have hconst_ne_top : ‖(step⁻¹ : ℝ)‖ₑ ≠ (⊤ : ℝ≥0∞) := by
    finiteness
  have hupper : ∀ n : ℕ,
      MeasureTheory.eLpNorm
          (fun x =>
            euclideanBackwardDifferenceQuotient step i (F n) x -
              euclideanBackwardDifferenceQuotient step i G x)
          2 MeasureTheory.volume ≤
        ‖(step⁻¹ : ℝ)‖ₑ * (A n + A n) := by
    intro n
    simpa [A] using
      eLpNorm_backwardDifferenceQuotient_sub_le (F := F n) (G := G)
        (hΔ n) step i
  have hscaled :
      Filter.Tendsto
        (fun n => ‖(step⁻¹ : ℝ)‖ₑ * (A n + A n))
        Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hsum (Or.inr hconst_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hscaled (fun n => zero_le) hupper

/-- If a function is supported in `U`, then its global `L²` norm is the same
as its `L²` norm over `U`.  This is just mathlib's support-restriction lemma
with the equality oriented for H¹₀ approximation limits. -/
theorem eLpNorm_eq_restrict_of_support_subset
    {F : Vec d → ℝ} (hF_support : Function.support F ⊆ U) :
    MeasureTheory.eLpNorm F 2 MeasureTheory.volume =
      MeasureTheory.eLpNorm F 2 (MeasureTheory.volume.restrict U) :=
  (MeasureTheory.eLpNorm_restrict_eq_of_support_subset hF_support).symm

/-- A restricted a.e.-strongly-measurable scalar function with genuine support
in `U` is globally a.e.-strongly-measurable after extension by zero. -/
theorem aestronglyMeasurable_of_restrict_of_support_subset
    {F : Vec d → ℝ} (hU_meas : MeasurableSet U)
    (hF_restrict : MeasureTheory.AEStronglyMeasurable F
      (MeasureTheory.volume.restrict U))
    (hF_support : Function.support F ⊆ U) :
    MeasureTheory.AEStronglyMeasurable F MeasureTheory.volume := by
  have hindicator : F = Set.indicator U F := by
    funext x
    by_cases hx : x ∈ U
    · simp [Set.indicator_of_mem hx]
    · have hFx : F x = 0 := by
        exact Function.support_subset_iff'.mp hF_support x hx
      simp [Set.indicator_of_notMem hx, hFx]
  rw [hindicator]
  exact (aestronglyMeasurable_indicator_iff hU_meas).2 hF_restrict

end WeakPoissonEquationOn

end

end Homogenization
