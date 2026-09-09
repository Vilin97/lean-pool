/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyData
public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionEquation
import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionSplit
import LeanPool.NavierStokesAndEuler.Euler.GevreyNonlinearEstimate
import LeanPool.NavierStokesAndEuler.Euler.GevreyRadiusReduction
import LeanPool.NavierStokesAndEuler.Euler.GevreyRestriction
import LeanPool.NavierStokesAndEuler.Euler.GevreyUniformConstants
import LeanPool.NavierStokesAndEuler.Euler.InviscidSobolevEvolution
import Mathlib.Algebra.Order.Star.Real

/-! Actual raw-source, elliptic-pressure, and time-source bounds at a smaller radius. -/

@[expose] public section


noncomputable section

namespace EulerGevreyCorrectionSourceBounds

open Set Finset EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevGevreyOperators
  EulerGevreyRadiusReduction EulerGevreyRestriction EulerH6Nonlinear EulerSobolevTransport
  EulerGevreyOrderZero EulerGevreyNonlinearEstimate EulerGevreyUniformConstants
  EulerCorrectionEnergyData EulerSobolevCoefficientPressure EulerInviscidSobolevEvolution

variable (period : ℝ) [Fact (0 < period)]

/-- The explicit polynomial controlling the literal unprojected correction source. -/
def sourceBound (B0 B1 A0 A2 residual E DE : ℝ) : ℝ :=
  productConstant period 3*(B0+E)*DE + residual +
    (productConstant period 3*B1+A0+2*A2*productConstant period 3*B0)*E +
    A2*productConstant period 3*E^2

theorem sourceBound_nonneg {B0 B1 A0 A2 residual E DE : ℝ}
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hA0 : 0 ≤ A0) (hA2 : 0 ≤ A2)
    (hr : 0 ≤ residual) (hE : 0 ≤ E) (hDE : 0 ≤ DE) :
    0 ≤ sourceBound period B0 B1 A0 A2 residual E DE := by
  have hP := productConstant_nonneg period 3
  unfold sourceBound
  positivity

/-- The actual transport estimate uses the sum of genuine derivative
norms, rather than a derivative bound on a hypothetical solution. -/
theorem weightedNorm_transport {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N + 6 ≤ s)
    (r : ℝ) (hr : 0 < r) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) :
    weightedNorm period 6 N r (transportBilinear period hs L hL u v) ≤
      productConstant period 3*weightedNorm period 6 N r u *
        ∑ i : Fin 4, weightedNorm period 6 N r (derivativeOperator period s i v) := by
  rw [transportBilinear_apply]
  apply (weightedNorm_sum_le period 6 N hN r hr univ _).trans
  calc
    _ ≤ ∑ i : Fin 4, productConstant period 3 *
        weightedNorm period 6 N r (truncateOperator period s u) *
        weightedNorm period 6 N r (derivativeOperator period s i v) :=
      sum_le_sum fun i _ => weightedNorm_product period hs N hN r hr (L i) (hL i) _ _
    _ = _ := by rw [weightedNorm_truncate period 6 N hN, ← mul_sum]

variable {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
  {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)}
  {P : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}

/-- All inputs on the right are the actual prescribed coefficient and
background budgets, and norms of the given error and its derivatives. -/
theorem rawSource_smallerRadius_bound (S : SpatialBudget period hq D P R)
    (N : ℕ) (hNP : N ≤ P) (hN : N + 6 ≤ q + 1) (t : Icc (0 : ℝ) T)
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ R t) (E DE : ℝ)
    (e : SobolevSpace period ((q + 1) + 1))
    (he : weightedNorm period 6 N r e ≤ E)
    (hde : (∑ i : Fin 4, weightedNorm period 6 N r (derivativeOperator period (q + 1) i e)) ≤ DE) :
    weightedNorm period 6 N r (D.rawSource period hq t e) ≤
      sourceBound period S.B0 S.B1 S.A0 S.A2 S.residual E DE := by
  have hP0 := productConstant_nonneg period 3
  have hE0 := (weightedNorm_nonneg period 6 N r hr e).trans he
  have hDE0 := (sum_nonneg (fun i (_ : i ∈ (univ : Finset (Fin 4))) =>
    weightedNorm_nonneg period 6 N r hr (derivativeOperator period (q+1) i e))).trans hde
  have hz : weightedNorm period 6 N r (D.approximation t) ≤ S.B0 :=
    ((weightedNorm_mono_radius period 6 N hr.le hrR _).trans
      (weightedNorm_mono_cutoff period 6 hNP (R t) (S.radius_pos t) _)).trans (S.background t)
  have hdz : (∑ i : Fin 4, weightedNorm period 6 N r
      (derivativeOperator period (q+1) i (D.approximation t))) ≤ S.B1 := by
    apply le_trans _ (S.background_derivative t)
    exact sum_le_sum fun i _ => (weightedNorm_mono_radius period 6 N hr.le hrR _).trans
      (weightedNorm_mono_cutoff period 6 hNP (R t) (S.radius_pos t) _)
  have hl : weightedCoefficient period (D.linear.jet t) 6 N r ≤ S.A0 :=
    ((weightedCoefficient_mono_radius period _ 6 N hr.le hrR).trans
      (weightedCoefficient_mono_cutoff period _ 6 hNP (R t) (S.radius_pos t))).trans (S.linear t)
  have hc : (∑ i : Fin 3, weightedCoefficient period ((D.quadratic i).jet t) 6 N r) ≤ S.A2 := by
    apply le_trans _ (S.quadratic t)
    exact sum_le_sum fun i _ => (weightedCoefficient_mono_radius period _ 6 N hr.le hrR).trans
      (weightedCoefficient_mono_cutoff period _ 6 hNP (R t) (S.radius_pos t))
  have hf : weightedNorm period 6 N r (D.residual t) ≤ S.residual :=
    ((weightedNorm_mono_radius period 6 N hr.le hrR _).trans
      (weightedNorm_mono_cutoff period 6 hNP (R t) (S.radius_pos t) _)).trans (S.residual_bound t)
  let L := velocityComponents D.κ D.direction
  have hL : ∀ i, ‖L i‖ ≤ 1 := velocityComponents_norm D.κ D.direction D.scale_bound
      D.direction_bound
  have hzE : weightedNorm period 6 N r (D.approximation t+e) ≤ S.B0+E :=
    (weightedNorm_add_le period 6 N (by omega) r hr _ _).trans (add_le_add hz he)
  have htransport := weightedNorm_transport period hq N hN r hr L hL (D.approximation t+e) e
  have htransport' : weightedNorm period 6 N r
      (transportBilinear period hq L hL (D.approximation t+e) e) ≤
      productConstant period 3*(S.B0+E)*DE := by
    apply htransport.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left hzE hP0) hde
      (sum_nonneg fun i _ => weightedNorm_nonneg period 6 N r hr _)
      (mul_nonneg hP0 (add_nonneg S.B0_nonneg hE0))
  have ho := orderZeroSource_uniform period hq N hN r hr L hL
    (D.linear.coefficient t) (D.linear.jet t) (fun i => (D.quadratic i).coefficient t)
    (fun i => (D.quadratic i).jet t) (D.approximation t) e (D.residual t)
    S.B0 S.B1 S.A0 S.A2 S.residual S.A2_nonneg hz hdz hl hc hf
  have hlin : 0 ≤ productConstant period 3*S.B1+S.A0+2*S.A2*productConstant period 3*S.B0 := by
    have := S.B1_nonneg; have := S.A0_nonneg; have := S.A2_nonneg; have := S.B0_nonneg
    positivity
  have ho' := ho.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left he hlin))
    (mul_le_mul_of_nonneg_left (sq_le_sq₀ (weightedNorm_nonneg period 6 N r hr e) hE0 |>.mpr he)
      (mul_nonneg S.A2_nonneg hP0)))
  rw [correctionData_rawSource_split]
  exact (weightedNorm_add_le period 6 N hN r hr _ _).trans
    ((add_le_add htransport' ho').trans_eq (by unfold sourceBound; ring))

/-- The actual elliptic inverse acts at the smaller radius using the same
proved coefficient budget. -/
theorem pressure_smallerRadius_bound (S : SpatialBudget period hq D P R)
    (N : ℕ) (hNP : N ≤ P) (hN : N + 6 ≤ q + 1) (t : Icc (0 : ℝ) T)
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ R t) (E DE : ℝ)
    (e : SobolevSpace period ((q + 1) + 1))
    (he : weightedNorm period 6 N r e ≤ E)
    (hde : (∑ i : Fin 4, weightedNorm period 6 N r (derivativeOperator period (q + 1) i e)) ≤ DE) :
    weightedNorm period 6 N r (D.pressure period hq t e) ≤
      2*S.M*sourceBound period S.B0 S.B1 S.A0 S.A2 S.residual E DE := by
  have hM : 0 ≤ S.M := zero_le_one.trans S.M_one_le
  have hsmall : 4*S.M*(r*S.Rc) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrR S.Rc_nonneg) (by positivity)).trans
      (S.radius_small t)
  rw [CorrectionData.pressure, weightedNorm_neg period 6 N hN]
  exact (weightedNorm_pressure period (D.metric.jet t) D.κ D.direction D.coercivity D.coercivity_pos
    (D.metric_pos t) N hN r S.Rc S.M hr S.Rc_nonneg S.M_one_le (S.inverse_six t) hsmall
    (fun l hl hlN => S.metric_derivatives t l hl (hlN.trans hNP)) _).trans
      (mul_le_mul_of_nonneg_left
        (rawSource_smallerRadius_bound period S N hNP hN t r hr hrR E DE e he hde) (by positivity))

/-- The metric multiplication cost remains independent of the cutoff. -/
theorem metric_smallerRadius_bound (S : SpatialBudget period hq D P R)
    (N : ℕ) (hNP : N ≤ P) (t : Icc (0 : ℝ) T)
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ R t) :
    weightedCoefficient period (D.metric.jet t) 6 N r ≤ 448*S.B+1 := by
  have hM : 0 ≤ S.M := zero_le_one.trans S.M_one_le
  have hx : 0 ≤ r*S.Rc := mul_nonneg hr.le S.Rc_nonneg
  have hsmall : 4*S.M*(r*S.Rc) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrR S.Rc_nonneg) (by positivity)).trans
      (S.radius_small t)
  have hhalf : r*S.Rc ≤ 1/2 := by nlinarith [S.M_one_le]
  exact weightedCoefficient_uniform period (D.metric.jet t) N r S.Rc S.B hr S.Rc_nonneg hhalf
    (S.metric_base t) (fun l hl hlN => S.metric_derivatives t l hl (hlN.trans hNP))

/-- The actual projected time source is bounded by the raw source and its
constructed signed pressure, with no time-derivative hypothesis. -/
theorem timeSource_smallerRadius_bound (S : SpatialBudget period hq D P R)
    (N : ℕ) (hNP : N ≤ P) (hN : N + 6 ≤ q + 1) (t : Icc (0 : ℝ) T)
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ R t) (E DE : ℝ)
    (e : SobolevSpace period ((q + 1) + 1))
    (he : weightedNorm period 6 N r e ≤ E)
    (hde : (∑ i : Fin 4, weightedNorm period 6 N r (derivativeOperator period (q + 1) i e)) ≤ DE) :
    weightedNorm period 6 N r ((D.coefficients period hq).apply t e) ≤
      (1+2*S.M*(448*S.B+1))*sourceBound period S.B0 S.B1 S.A0 S.A2 S.residual E DE := by
  have hraw := rawSource_smallerRadius_bound period S N hNP hN t r hr hrR E DE e he hde
  have hp := pressure_smallerRadius_bound period S N hNP hN t r hr hrR E DE e he hde
  have hmetric := metric_smallerRadius_bound period S N hNP t r hr hrR
  have hB0 := S.B_nonneg
  rw [CorrectionData.source_sobolev, sub_eq_add_neg]
  apply (weightedNorm_add_le period 6 N hN r hr _ _).trans
  rw [weightedNorm_neg period 6 N hN, weightedNorm_neg period 6 N hN]
  have hm := (weightedNorm_coefficient period (D.metric.jet t) 6 N hN r hr
    (D.pressure period hq t e)).trans
      (mul_le_mul hmetric hp (weightedNorm_nonneg period 6 N r hr _) (by positivity))
  exact (add_le_add hraw hm).trans_eq (by ring)

end EulerGevreyCorrectionSourceBounds
