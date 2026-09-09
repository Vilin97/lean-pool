/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LiftedTransportComponents
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevDensity

@[expose] public section

/-! Genuine metric transport energy on finite Sobolev fields, obtained by smooth convolution
  limits. -/

noncomputable section

namespace EulerSobolevMetricTransport

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace EulerSobolevL2Product
  EulerSobolevTransport EulerMollifierRepresentative EulerCylinderGradient
open scoped Topology ContDiff ENNReal NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Actual lifted transport is a bounded map H¹→L² for each fixed Hq velocity, q≥3. -/
def transportOperator {q : ℕ} (hq : 3 ≤ q) (κ : ℝ) (m : Vector3)
    (z : SobolevSpace period q) : SobolevSpace period 1 →L[ℝ] LiftL2 period :=
  ∑ i : Fin 4, (scalarProductBilinear period hq (velocityComponents κ m i) z).comp
    ((valueOperator period 0).comp (derivativeOperator period 0 i))

/-- The Sobolev transport operator is the literal sum of coefficient-times-coordinate-derivative products. -/
theorem transportOperator_apply {q : ℕ} (hq : 3 ≤ q) (κ : ℝ) (m : Vector3)
    (z : SobolevSpace period q) (e : SobolevSpace period 1) :
    transportOperator period hq κ m z e = ∑ i : Fin 4,
      scalarProduct period hq (velocityComponents κ m i) z
        (value period (derivativeOperator period 0 i e)) := by
  simp only [transportOperator, sum_apply, ContinuousLinearMap.comp_apply,
    scalarProductBilinear_apply]
  rfl

/-- A smooth representative of an actual H¹ class has its full classical gradient in L². -/
theorem representative_fderiv_memLp (e : SobolevSpace period 1)
    (g : LiftDomain period → Vector3)
    (he : (value period e : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0) 2 (liftMeasure period) := by
  apply fieldFDeriv_memLp_of_coordinates period g hg
  intro i
  exact (Lp.memLp _).ae_eq (EulerStrongSmoothJet.translation_derivative_ae period
    (standardDirection i)
    (value period e) (value period (derivativeOperator period 0 i e)) g he hg
    (derivativeOperator_hasDerivAt period i e))

/-- On any actual smooth representative, Sobolev transport equals the genuine classical lifted differential expression. -/
theorem transportOperator_eq_representative {q : ℕ} (hq : 3 ≤ q) (κ : ℝ) (m : Vector3)
    (z : SobolevSpace period q) (e : SobolevSpace period 1) (g : LiftDomain period → Vector3)
    (he : (value period e : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hDg : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0) 2 (liftMeasure period))
    (B : ℝ≥0) (hzB : ∀ᵐ x ∂liftMeasure period, ‖value period z x‖ ≤ B) :
    transportOperator period hq κ m z e =
      EulerRepresentativeMetricEvolution.liftedTransport period κ m g (value period z) hDg B hzB :=
        by
  rw [transportOperator_apply]
  apply Lp.ext
  have hd (i : Fin 4) := EulerStrongSmoothJet.translation_derivative_ae period (standardDirection i)
    (value period e) (value period (derivativeOperator period 0 i e)) g he hg
    (derivativeOperator_hasDerivAt period i e)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin 4 =>
    scalarProduct period hq (velocityComponents κ m i) z (value period (derivativeOperator period 0
      i e))),
    ae_all_iff.mpr (fun i => scalarProduct_ae period hq (velocityComponents κ m i) z
      (value period (derivativeOperator period 0 i e))), ae_all_iff.mpr hd,
    EulerRepresentativeMetricEvolution.liftedTransport_ae period κ m g (value period z) hDg B hzB]
    with x hsum hprod hder htrans
  simp only [Finset.sum_apply] at hsum
  rw [hsum, htrans, ← velocityComponents_direction κ m (value period z x), map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hprod i, hder i, map_smul]
  rfl

/-- Metric transport cancellation extends from actual smooth convolutions to every H¹ field. -/
theorem metric_transport_bound {q : ℕ} (hq : 3 ≤ q) (κ : ℝ) (m : Vector3)
    (K : SmoothCoefficient period) (z : SobolevSpace period q) (e : SobolevSpace period 1)
    (hsym : ∀ x v w, ⟪K.coefficient x v, w⟫_ℝ = ⟪v, K.coefficient x w⟫_ℝ)
    (hz : value period z ∈ divergenceFreeSpace period κ m)
    (B : ℝ≥0) (hzB : ∀ᵐ x ∂liftMeasure period, ‖value period z x‖ ≤ B) :
    |⟪K.operator (value period e), transportOperator period hq κ m z e⟫_ℝ| ≤
      (1 / 2 : ℝ) * K.firstBound * ((|κ| + ‖m‖) * B) * ‖value period e‖ ^ 2 := by
  let E := fun n => sobolevMollifier period 1 n e
  let g := fun n => smoothMollifier period n (value period e)
  have hE := sobolevMollifier_tendsto period e
  have hEv := (valueOperator period 1).continuous.continuousAt.tendsto.comp hE
  have hT := (transportOperator period hq κ m z).continuous.continuousAt.tendsto.comp hE
  have hK := K.operator.continuous.continuousAt.tendsto.comp hEv
  have hleft := (hK.inner (𝕜 := ℝ) hT).abs
  have hright := (hEv.norm.pow 2).const_mul
    ((1 / 2 : ℝ) * K.firstBound * ((|κ| + ‖m‖) * B))
  apply le_of_tendsto_of_tendsto hleft hright
  apply Filter.Eventually.of_forall
  intro n
  have hrep := sobolevMollifier_representative period n e
  have hg := smoothMollifier_smooth period n (value period e)
  have hDg := representative_fderiv_memLp period (E n) (g n) hrep hg
  have heq := transportOperator_eq_representative period hq κ m z (E n) (g n) hrep hg hDg B hzB
  change |⟪K.operator (value period (E n)), transportOperator period hq κ m z (E n)⟫_ℝ| ≤ _
  rw [heq]
  exact EulerRepresentativeMetricEvolution.metric_transport_inner_bound period κ m K.coefficient
    K.measurable
    (value period (E n)) (g n) (value period z) hrep K.smooth hg hDg hsym hz
    K.bound K.firstBound B K.norm_bound K.norm_first hzB

end EulerSobolevMetricTransport
