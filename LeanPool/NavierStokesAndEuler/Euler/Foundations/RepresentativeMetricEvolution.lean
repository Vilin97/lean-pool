/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedPressure
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.MetricTransport
import LeanPool.NavierStokesAndEuler.Euler.Foundations.MetricEnergyEvolution
import LeanPool.NavierStokesAndEuler.Euler.Foundations.NoncompactTransport

/-! Metric-energy evolution using a separate actual smooth representative of each L² class. -/

@[expose] public section

noncomputable section

namespace EulerRepresentativeMetricEvolution

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerMetricTransport EulerNoncompactTransport EulerMetricEnergyEvolution
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual directional transport derivative is square integrable under H¹ and bounded velocity.
-/
theorem liftedTransport_memLp (κ : ℝ) (m : Vector3) (g : LiftDomain period → Vector3) (z : LiftL2
    period)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0
      (transportDirection κ m (z x))) 2 (liftMeasure period) := by
  apply hDe.of_le_mul (c := (|κ| + ‖m‖) * B)
  · exact aestronglyMeasurable_apply period hDe.aestronglyMeasurable
      (transportDirection_aestronglyMeasurable period κ m z)
  filter_upwards [hzB] with x hx
  have hv := (transportDirection_norm_le κ m (z x)).trans
    (mul_le_mul_of_nonneg_left hx (add_nonneg (abs_nonneg _) (norm_nonneg _)))
  calc
    _ ≤ ‖fderiv ℝ (localFieldLift period g x) 0‖ *
        ‖transportDirection κ m (z x)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (localFieldLift period g x) 0‖ * ((|κ| + ‖m‖) * B) :=
      mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ = _ := by ring

/-- The genuine L² element represented by the lifted directional transport derivative. -/
def liftedTransport (κ : ℝ) (m : Vector3) (g : LiftDomain period → Vector3) (z : LiftL2 period)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) : LiftL2 period :=
  (liftedTransport_memLp period κ m g z hDe B hzB).toLp _

theorem liftedTransport_ae (κ : ℝ) (m : Vector3) (g : LiftDomain period → Vector3) (z : LiftL2
    period)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    liftedTransport period κ m g z hDe B hzB =ᵐ[liftMeasure period]
      fun x => fderiv ℝ (localFieldLift period g x) 0
        (transportDirection κ m (z x)) :=
  (liftedTransport_memLp period κ m g z hDe B hzB).coeFn_toLp

/-- The Hilbert metric pairing equals the actual spatial transport integral. -/
theorem metric_transport_inner_eq (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : AEStronglyMeasurable K (liftMeasure period)) (C : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C)
    (e : LiftL2 period) (g : LiftDomain period → Vector3) (z : LiftL2 period)
    (hrep : (e : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    ⟪coefficientOperator K hKm C hC e, liftedTransport period κ m g z hDe B hzB⟫_ℝ =
      ∫ x, ⟪K x (g x), fderiv ℝ (localFieldLift period g x) 0
        (transportDirection κ m (z x))⟫_ℝ ∂liftMeasure period := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coefficientOperator_ae K hKm C hC e, liftedTransport_ae period κ m g z hDe B hzB,
      hrep]
    with x hx hy hr
  rw [hx, hy, hr]

/-- The transport bound required by the Hilbert energy theorem, with genuine spatial fields. -/
theorem metric_transport_inner_bound (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : AEStronglyMeasurable K (liftMeasure period))
    (e : LiftL2 period) (g : LiftDomain period → Vector3) (z : LiftL2 period)
    (hrep : (e : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0)
      2 (liftMeasure period))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    (hz : z ∈ divergenceFreeSpace period κ m)
    (C D B : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C)
    (hD : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ D)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    |⟪coefficientOperator K hKm C hC e, liftedTransport period κ m g z hDe B hzB⟫_ℝ| ≤
      (1 / 2 : ℝ) * D * ((|κ| + ‖m‖) * B) * ‖e‖ ^ 2 := by
  rw [metric_transport_inner_eq period κ m K hKm C hC e g z hrep hDe B hzB]
  have hn : (∫ x, ‖g x‖ ^ 2 ∂liftMeasure period) = ‖e‖ ^ 2 := by
    calc
      _ = ∫ x, ‖e x‖ ^ 2 ∂liftMeasure period := by
        apply integral_congr_ae
        filter_upwards [hrep] with x hx
        rw [hx]
      _ = _ := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        simp only [real_inner_self_eq_norm_sq]
  simpa only [hn] using metric_transport_H1_bound period κ m K g
    hK he ((memLp_congr_ae hrep).mp (Lp.memLp e)) hDe hsym hz C D B hC hD hzB

/-- A pointwise matrix family acting on the actual lifted L² space. -/
def metricFamily (K : ℝ → LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : ∀ t, AEStronglyMeasurable (K t) (liftMeasure period))
    (C : ℝ≥0) (hC : ∀ t x, ‖K t x‖ ≤ C) : ℝ → LiftL2 period →L[ℝ] LiftL2 period :=
  fun t => coefficientOperator (K t) (hKm t) C (hC t)

/-- The metric norm estimate for the actual lifted transport-pressure equation. -/
theorem lifted_regularized_energy_evolution (κ : ℝ) (m : Vector3)
    (K : ℝ → LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : ∀ t, AEStronglyMeasurable (K t) (liftMeasure period))
    (C : ℝ≥0) (hC : ∀ t x, ‖K t x‖ ≤ C)
    (e : ℝ → LiftL2 period) (t δ c : ℝ)
    (K' : LiftL2 period →L[ℝ] LiftL2 period) (e' z p forcing : LiftL2 period)
    (hδ : 0 < δ) (hc : 0 < c)
    (hKt : HasDerivAt (metricFamily period K hKm C hC) K' t) (het : HasDerivAt e e' t)
    (hKs : ∀ x, ContDiff ℝ ∞ (localFieldLift period (K t) x))
    (g : LiftDomain period → Vector3)
    (hrep : (e t : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hes : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0)
      2 (liftMeasure period))
    (hsym : ∀ x v w, ⟪K t x v, w⟫_ℝ = ⟪v, K t x w⟫_ℝ)
    (hpos : ∀ x v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪K t x v, v⟫_ℝ)
    (G : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hGm : AEStronglyMeasurable G (liftMeasure period)) (E : ℝ≥0) (hG : ∀ x, ‖G x‖ ≤ E)
    (hKG : ∀ x v, K t x (G x v) = v)
    (hep : e t ∈ divergenceFreeSpace period κ m) (hp : p ∈ gradientSpace period κ m)
    (hz : z ∈ divergenceFreeSpace period κ m) (D B : ℝ≥0)
    (hD : ∀ x, ‖fderiv ℝ (localFieldLift period (K t) x) 0‖ ≤ D)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B)
    (heq : e' + liftedTransport period κ m g z hDe B hzB +
      coefficientOperator G hGm E hG p = forcing) :
    deriv (fun s => Real.sqrt (⟪metricFamily period K hKm C hC s (e s), e s⟫_ℝ + δ ^ 2)) t ≤
      ((‖K'‖ + (D : ℝ) * ((|κ| + ‖m‖) * B)) / (2 * c ^ 2)) *
        Real.sqrt (⟪metricFamily period K hKm C hC t (e t), e t⟫_ℝ + δ ^ 2) +
      ((C : ℝ) / c) * ‖forcing‖ := by
  let A := metricFamily period K hKm C hC
  let β : ℝ := (1 / 2 : ℝ) * D * ((|κ| + ‖m‖) * B)
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hsymL : ∀ v w, ⟪A t v, w⟫_ℝ = ⟪v, A t w⟫_ℝ :=
    coefficientOperator_inner_swap (K t) (hKm t) C (hC t) hsym
  have hposL : c ^ 2 * ‖e t‖ ^ 2 ≤ ⟪A t (e t), e t⟫_ℝ :=
    coefficientOperator_coercive (K t) (hKm t) C (hC t) (c ^ 2) hpos (e t)
  have hpL : ⟪A t (e t), coefficientOperator G hGm E hG p⟫_ℝ = 0 :=
    metric_pressure_cancellation period κ m (K t) G (hKm t) hGm C E (hC t) hG hsym hKG hep hp
  have htL := metric_transport_inner_bound period κ m (K t) (hKm t) (e t) g z hrep
    hKs hes hDe hsym hz C D B (hC t) hD hzB
  have h := regularized_metric_norm_evolution A e t δ c β K' e'
    (liftedTransport period κ m g z hDe B hzB) (coefficientOperator G hGm E hG p)
    forcing hδ hc hβ hposL hKt het hsymL heq hpL htL
  have hA : ‖A t‖ ≤ C := coefficientOperator_norm_le (K t) (hKm t) C (hC t)
  have hb : 2 * β = (D : ℝ) * ((|κ| + ‖m‖) * B) := by dsimp [β]; ring
  rw [hb] at h
  exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hA hc.le) (norm_nonneg forcing)) _)

end EulerRepresentativeMetricEvolution
