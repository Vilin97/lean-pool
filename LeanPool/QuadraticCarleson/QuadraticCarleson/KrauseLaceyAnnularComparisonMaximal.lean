/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyScaleOffsetPointwise
import LeanPool.QuadraticCarleson.QuadraticCarleson.HardyLittlewoodMaximalSparse

/-!
# The actual finite annular-comparison maximal operator

This is the finite maximum of the actual differences between the smooth
high-pass cutoff at each positive radius and its adjacent dyadic cutoff.
Its pointwise bound costs `24` copies of the centered maximal operator, and
its sparse `(1,p)` bound is `11520 = 24 * 480` for every `p ≥ 1`.
Neither estimate depends on the number of radii or on the modulation.
-/

open Function MeasureTheory Set
open scoped ENNReal NNReal Topology ComplexConjugate

namespace QuadraticCarleson.KrauseLaceyAnnularComparisonMaximal

open KrauseLaceySharpSmoothAdapter KrauseLaceySparseDilation
open KrauseLaceyScaleOffsetPointwise KrauseLaceySparseReflection
open KrauseLaceyFiniteRadiusSmoothSparse KrauseLaceyCompactPairingStabilization
open HardyLittlewoodBoundaryControl HardyLittlewoodMaximalSparse


noncomputable
section

/-- The genuine finite maximum of smooth annular differences. -/
def finiteAnnularComparisonMaxNNNorm (lam : ℝ) (s : Finset PositiveSmoothRadius)
    (f : L0Infinity) (x : ℝ) : NNReal :=
  s.sup fun ρ ↦ ‖smoothQuadraticHighPass lam ρ.1 f x -
    smoothQuadraticHighPass lam (dyadicCeilRadius ρ.1 ρ.2) f x‖₊

/-- Complex-valued test-operator packaging, with nonnegative real output. -/
def finiteAnnularComparisonMaxOperator (lam : ℝ) (s : Finset PositiveSmoothRadius) :
    TestOperator :=
  fun f x ↦ ((finiteAnnularComparisonMaxNNNorm lam s f x : ℝ) : ℂ)

@[simp] theorem norm_finiteAnnularComparisonMaxOperator
    (lam : ℝ) (s : Finset PositiveSmoothRadius) (f : L0Infinity) (x : ℝ) :
    ‖finiteAnnularComparisonMaxOperator lam s f x‖ =
      (finiteAnnularComparisonMaxNNNorm lam s f x : ℝ) := by
  simp [finiteAnnularComparisonMaxOperator]

@[simp] theorem enorm_finiteAnnularComparisonMaxOperator
    (lam : ℝ) (s : Finset PositiveSmoothRadius) (f : L0Infinity) (x : ℝ) :
    ‖finiteAnnularComparisonMaxOperator lam s f x‖ₑ =
      s.sup (fun ρ ↦ ‖smoothQuadraticHighPass lam ρ.1 f x -
        smoothQuadraticHighPass lam (dyadicCeilRadius ρ.1 ρ.2) f x‖ₑ) := by
  rw [← ofReal_norm, norm_finiteAnnularComparisonMaxOperator, ENNReal.ofReal_coe_nnreal]
  simp only [finiteAnnularComparisonMaxNNNorm, ENNReal.coe_finset_sup]
  rfl

@[simp] theorem absoluteValue_finiteAnnularComparisonMaxOperator
    (lam : ℝ) (s : Finset PositiveSmoothRadius) :
    absoluteValueOperator (finiteAnnularComparisonMaxOperator lam s) =
      finiteAnnularComparisonMaxOperator lam s := by
  funext f x
  simp [absoluteValueOperator, finiteAnnularComparisonMaxOperator]

/-- One common maximal-function error controls the full finite family. -/
theorem enorm_finiteAnnularComparisonMax_le_maximal
    (lam : ℝ) (s : Finset PositiveSmoothRadius) (f : L0Infinity) (x : ℝ) :
    ‖finiteAnnularComparisonMaxOperator lam s f x‖ₑ ≤
      24 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  rw [enorm_finiteAnnularComparisonMaxOperator]
  exact Finset.sup_le fun ρ _ ↦ enorm_smoothHighPass_sub_dyadicRounded_le_maximal
    lam ρ.2 f.measurable_toFun f.integrable x

theorem norm_finiteAnnularComparisonMax_le_boundary
    (lam : ℝ) (s : Finset PositiveSmoothRadius) (f : L0Infinity) (x : ℝ) :
    ‖finiteAnnularComparisonMaxOperator lam s f x‖ ≤
      24 * ‖centeredHardyLittlewoodBoundaryOperator f x‖ := by
  have h := enorm_finiteAnnularComparisonMax_le_maximal lam s f x
  rw [← enorm_centeredHardyLittlewoodBoundaryOperator] at h
  apply (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) (norm_nonneg _))).mp
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 24),
    ENNReal.ofReal_ofNat, ofReal_norm] using h

theorem measurable_finiteAnnularComparisonMaxOperator
    (lam : ℝ) (s : Finset PositiveSmoothRadius) (f : L0Infinity) :
    Measurable (finiteAnnularComparisonMaxOperator lam s f) := by
  classical
  have hmeas (ρ : ℝ) : Measurable (fun x ↦ smoothQuadraticHighPass lam ρ f x) := by
    unfold smoothQuadraticHighPass
    have hk := (measurable_smoothQuadraticHighPassKernel lam ρ).comp
      (measurable_fst.sub measurable_snd)
    have hj : StronglyMeasurable (fun z : ℝ × ℝ ↦
        smoothQuadraticHighPassKernel lam ρ (z.1 - z.2) * f z.2) :=
      (hk.mul (f.measurable_toFun.comp measurable_snd)).stronglyMeasurable
    exact hj.integral_prod_right'.measurable
  have hmax : Measurable (fun x ↦ (finiteAnnularComparisonMaxNNNorm lam s f x : ℝ)) := by
    unfold finiteAnnularComparisonMaxNNNorm
    induction s using Finset.induction_on with
    | empty => simp
    | @insert ρ s hρ ih =>
        simp only [Finset.sup_insert, NNReal.coe_max, coe_nnnorm]
        exact ((hmeas _).sub (hmeas _)).norm.max ih
  exact Complex.measurable_ofReal.comp hmax

/-- The actual operator has locally integrable outputs, so none of its
testing integrals rely on the total integral's nonintegrable convention. -/
theorem locallyIntegrable_finiteAnnularComparisonMaxOperator
    (lam : ℝ) (s : Finset PositiveSmoothRadius) (f : L0Infinity) :
    LocallyIntegrable (finiteAnnularComparisonMaxOperator lam s f) volume := by
  apply ((centeredHardyLittlewoodBoundaryOperator_locallyIntegrable f).smul (24 : ℂ)).mono
    (measurable_finiteAnnularComparisonMaxOperator lam s f).aestronglyMeasurable
  filter_upwards with x
  simpa only [Pi.smul_apply, norm_smul, Complex.norm_ofNat] using
    norm_finiteAnnularComparisonMax_le_boundary lam s f x

theorem norm_pairing_finiteAnnularComparisonMax_le_boundary
    (lam : ℝ) (s : Finset PositiveSmoothRadius) (f g : L0Infinity) :
    ‖operatorPairing (finiteAnnularComparisonMaxOperator lam s) f g‖ ≤
      24 * ‖operatorPairing centeredHardyLittlewoodBoundaryOperator f (normInput g)‖ := by
  have hbd : ‖operatorPairing centeredHardyLittlewoodBoundaryOperator f (normInput g)‖ =
      ∫ x, ‖centeredHardyLittlewoodBoundaryOperator f x‖ * ‖g x‖ := by
    simpa only [absoluteValue_centeredHardyLittlewoodBoundaryOperator] using
      norm_operatorPairing_absolute_normInput centeredHardyLittlewoodBoundaryOperator f g
  have hi : Integrable (fun x ↦ ‖centeredHardyLittlewoodBoundaryOperator f x‖ * ‖g x‖) := by
    simpa only [norm_mul, norm_star] using
      (integrable_pairing_of_locallyIntegrable
        (centeredHardyLittlewoodBoundaryOperator_locallyIntegrable f) g).norm
  rw [hbd, ← integral_const_mul]
  apply norm_integral_le_of_norm_le (hi.const_mul 24)
  filter_upwards with x
  rw [norm_mul, norm_star]
  calc
    _ ≤ (24 * ‖centeredHardyLittlewoodBoundaryOperator f x‖) * ‖g x‖ :=
      mul_le_mul_of_nonneg_right
        (norm_finiteAnnularComparisonMax_le_boundary lam s f x) (norm_nonneg _)
    _ = _ := by ring

/-- The comparison family's genuine sparse bound, with the explicit
constant `11520 = 24 * 480` and unchanged `1/4` sparseness. -/
theorem hasSparseOnePBound_finiteAnnularComparisonMaxOperator
    (lam : ℝ) (s : Finset PositiveSmoothRadius) {p : ℝ} (hp : 1 ≤ p) :
    HasSparseOnePBound 11520 p (finiteAnnularComparisonMaxOperator lam s) := by
  intro f g
  obtain ⟨R, hR, hb⟩ :=
    hasSparseOnePBound_centeredHardyLittlewoodBoundaryOperator hp f (normInput g)
  rw [sparseForm_normInput] at hb
  refine ⟨R, hR, ?_⟩
  have hc := ENNReal.ofReal_le_ofReal
    (norm_pairing_finiteAnnularComparisonMax_le_boundary lam s f g)
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 24), ENNReal.ofReal_ofNat] at hc
  calc
    _ ≤ 24 * ENNReal.ofReal
        ‖operatorPairing centeredHardyLittlewoodBoundaryOperator f (normInput g)‖ := hc
    _ ≤ 24 * (ENNReal.ofReal 480 * sparseForm p f g R) := mul_le_mul' le_rfl hb
    _ = _ := by norm_num; ring

private theorem enorm_le_add_enorm_sub (z w : ℂ) :
    ‖z‖ₑ ≤ ‖w‖ₑ + ‖z - w‖ₑ := by
  calc
    ‖z‖ₑ = ‖w + (z - w)‖ₑ := by rw [add_comm, sub_add_cancel]
    _ ≤ _ := enorm_add_le _ _

/-- The finite arbitrary-radius smooth maximum is controlled by its actual
adjacent dyadic maximum plus the actual annular-difference maximum. -/
theorem enorm_finiteSmoothMax_le_dyadicMax_add_annularComparisonMax
    (lam : ℝ) (s : Finset PositiveSmoothRadius) (f : L0Infinity) (x : ℝ) :
    ‖finiteSmoothMaxOperator lam s f x‖ₑ ≤
      ‖dyadicSmoothHighPassMaxOperator lam (adjacentDyadicLowerIndex s) f x‖ₑ +
        ‖finiteAnnularComparisonMaxOperator lam s f x‖ₑ := by
  rw [enorm_finiteSmoothMaxOperator]
  apply Finset.sup_le
  intro ρ hρ
  have herror : ‖smoothQuadraticHighPass lam ρ.1 f x -
        smoothQuadraticHighPass lam (dyadicCeilRadius ρ.1 ρ.2) f x‖ₑ ≤
      ‖finiteAnnularComparisonMaxOperator lam s f x‖ₑ := by
    rw [enorm_finiteAnnularComparisonMaxOperator]
    exact Finset.le_sup (s := s) (b := ρ)
      (f := fun δ : PositiveSmoothRadius ↦ ‖smoothQuadraticHighPass lam δ.1 f x -
      smoothQuadraticHighPass lam (dyadicCeilRadius δ.1 δ.2) f x‖ₑ) hρ
  exact (enorm_le_add_enorm_sub
    (smoothQuadraticHighPass lam ρ.1 f x)
    (smoothQuadraticHighPass lam (dyadicCeilRadius ρ.1 ρ.2) f x)).trans
      (add_le_add (enorm_adjacentRounded_le_dyadicMax lam s ρ hρ f x) herror)


end
end QuadraticCarleson.KrauseLaceyAnnularComparisonMaximal
