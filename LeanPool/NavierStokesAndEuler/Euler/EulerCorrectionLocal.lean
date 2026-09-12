/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.LiftedTransportComponents
public import LeanPool.NavierStokesAndEuler.Euler.QuadraticHeatLocal
import LeanPool.NavierStokesAndEuler.Euler.DivergenceFreeHeat
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionOperators
public import LeanPool.NavierStokesAndEuler.Euler.QuadraticCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.SobolevCoefficientPressure
import LeanPool.NavierStokesAndEuler.Euler.SobolevPressureResolvent
import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.RCLike.Basic

import Mathlib.Analysis.Calculus.Deriv.Mul

/-! A genuine local divergence-free viscous correction for the transformed Euler equation. -/

section

/-! The actual time-dependent coefficients and nonlinear source of the lifted Euler correction. -/

section

/-! Local boundedness, continuity, and differentiation derived from an exact operator resolvent
identity. -/

@[expose] public section

noncomputable section

namespace EulerResolventCalculus

open scoped Topology

variable {R : Type*} [NormedRing R]

/-- An exact resolvent identity gives a local inverse bound without assuming a uniform inverse
estimate. -/
theorem local_norm_bound (P Q M N : R) (hres : Q - P = Q * ((M - N) * P))
    (hsmall : ‖M - N‖ * ‖P‖ ≤ 1 / 2) : ‖Q‖ ≤ 2 * ‖P‖ := by
  have hresnorm : ‖Q - P‖ ≤ ‖Q‖ * (‖M - N‖ * ‖P‖) := by
    rw [hres]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg Q))
  have hhalf : ‖Q - P‖ ≤ ‖Q‖ / 2 :=
    hresnorm.trans ((mul_le_mul_of_nonneg_left hsmall (norm_nonneg Q)).trans_eq (by ring))
  have htri : ‖Q‖ ≤ ‖Q - P‖ + ‖P‖ := by
    calc
      ‖Q‖ = ‖Q - P + P‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  linarith

/-- The exact resolvent identity yields a local Lipschitz estimate using only the reference inverse
norm. -/
theorem local_difference_bound (P Q M N : R) (hres : Q - P = Q * ((M - N) * P))
    (hsmall : ‖M - N‖ * ‖P‖ ≤ 1 / 2) :
    ‖Q - P‖ ≤ (2 * ‖P‖ ^ 2) * ‖M - N‖ := by
  have hQ := local_norm_bound P Q M N hres hsmall
  rw [hres]
  calc
    ‖Q * ((M - N) * P)‖ ≤ ‖Q‖ * (‖M - N‖ * ‖P‖) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg Q))
    _ ≤ (2 * ‖P‖) * (‖M - N‖ * ‖P‖) :=
      mul_le_mul_of_nonneg_right hQ (mul_nonneg (norm_nonneg _) (norm_nonneg P))
    _ = _ := by ring

/-- Continuity of the coefficient operator implies continuity of actual resolvents, with no separate
inverse-continuity assumption. -/
theorem continuousAt_of_resolvent {α : Type*} [TopologicalSpace α] (P M : α → R)
    (hres : ∀ s t, P s - P t = P s * ((M t - M s) * P t)) (t : α)
    (hM : ContinuousAt M t) : ContinuousAt P t := by
  have hdelta : Filter.Tendsto (fun s => ‖M t - M s‖) (𝓝 t) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hM.const_sub (M t)).norm
  have hsmall : ∀ᶠ s in 𝓝 t, ‖M t - M s‖ * ‖P t‖ ≤ 1 / 2 := by
    have hlim : Filter.Tendsto (fun s => ‖M t - M s‖ * ‖P t‖) (𝓝 t) (𝓝 0) := by
      simpa only [zero_mul] using hdelta.mul_const ‖P t‖
    exact (hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h => h.le
  have hbound : ∀ᶠ s in 𝓝 t, ‖P s - P t‖ ≤ (2 * ‖P t‖ ^ 2) * ‖M t - M s‖ :=
    hsmall.mono fun s hs => local_difference_bound (P t) (P s) (M t) (M s) (hres s t) hs
  have hlim : Filter.Tendsto (fun s => (2 * ‖P t‖ ^ 2) * ‖M t - M s‖) (𝓝 t) (𝓝 0) := by
    simpa only [mul_zero] using hdelta.const_mul (2 * ‖P t‖ ^ 2)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound hlim

variable [NormedAlgebra ℝ R]

/-- Differentiating the actual resolvent identity gives the inverse derivative, after continuity has
been proved from the same identity. -/
theorem hasDerivAt_of_resolvent (P M : ℝ → R)
    (hres : ∀ s t, P s - P t = P s * ((M t - M s) * P t))
    (t : ℝ) (M' : R) (hM : HasDerivAt M M' t) :
    HasDerivAt P (-(P t * (M' * P t))) t := by
  have hP := continuousAt_of_resolvent P M hres t hM.continuousAt
  have hshift : Filter.Tendsto (fun r => P (t + r)) (𝓝[≠] 0) (𝓝 (P t)) := by
    have h : Filter.Tendsto (fun r => P (t + r)) (𝓝 (0 : ℝ)) (𝓝 (P t)) := by
      have hadd : Filter.Tendsto (fun r : ℝ => t + r) (𝓝 (0 : ℝ)) (𝓝 t) := by
        simpa only [add_zero, id_eq] using (tendsto_const_nhds.add (Filter.tendsto_id :
            Filter.Tendsto id (𝓝 (0 : ℝ)) (𝓝 0)))
      exact hP.tendsto.comp hadd
    exact h.mono_left nhdsWithin_le_nhds
  have hneg : Filter.Tendsto (fun r : ℝ => r⁻¹ • (M t - M (t + r))) (𝓝[≠] 0) (𝓝 (-M')) := by
    simpa only [← smul_neg, neg_sub] using hM.tendsto_slope_zero.neg
  have hlim : Filter.Tendsto (fun r : ℝ => P (t + r) * ((r⁻¹ • (M t - M (t + r))) * P t))
      (𝓝[≠] 0) (𝓝 (P t * ((-M') * P t))) := hshift.mul (hneg.mul tendsto_const_nhds)
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have he : (fun r : ℝ => r⁻¹ • (P (t + r) - P t)) =
      fun r : ℝ => P (t + r) * ((r⁻¹ • (M t - M (t + r))) * P t) := by
    funext r
    rw [hres]
    simp only [smul_mul_assoc, mul_smul_comm]
  rw [he]
  simpa only [neg_mul, mul_neg] using hlim

end EulerResolventCalculus

end
end

end

section

/-! Time regularity of the actual Sobolev pressure inverse, derived from its genuine resolvent. -/

@[expose] public section

noncomputable section

namespace EulerSobolevCoefficientPressure

open InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerResolventCalculus
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The inherited normed group of Sobolev endomorphisms, named to keep instance inference shallow.
-/
local instance sobolevEndNormedGroup (q : ℕ) :
    NormedAddCommGroup (SobolevSpace period q →L[ℝ] SobolevSpace period q) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The inherited real normed-space structure of Sobolev endomorphisms. -/
local instance sobolevEndNormedSpace (q : ℕ) :
    NormedSpace ℝ (SobolevSpace period q →L[ℝ] SobolevSpace period q) :=
  ContinuousLinearMap.toNormedSpace

/-- Coefficient-multiplier continuity implies continuity of the actual pressure operator in Hq norm.
-/
theorem pressureSobolev_continuousAt {α : Type*} [TopologicalSpace α] {q : ℕ}
    (A : α → SmoothCoefficient period) (K : ∀ s, CoefficientJet period standardDirection q (A s))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ s x v, c * ‖v‖ ^ 2 ≤ ⟪(A s).coefficient x v, v⟫_ℝ) (t : α)
    (hM : ContinuousAt (fun s => coefficientSobolevOperator period (K s)) t) :
    ContinuousAt (fun s => pressureSobolevOperator period (K s) κ m c hc (hpos s)) t := by
  apply continuousAt_of_resolvent
    (fun s => pressureSobolevOperator period (K s) κ m c hc (hpos s))
    (fun s => coefficientSobolevOperator period (K s)) _ t hM
  intro s r
  exact pressure_resolvent period (K s) (K r) κ m c c hc hc (hpos s) (hpos r)

/-- The actual pressure-corrected source operator is continuous whenever the coefficient multiplier
is continuous. -/
theorem projectedSource_continuousAt {α : Type*} [TopologicalSpace α] {q : ℕ}
    (A : α → SmoothCoefficient period) (K : ∀ s, CoefficientJet period standardDirection q (A s))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ s x v, c * ‖v‖ ^ 2 ≤ ⟪(A s).coefficient x v, v⟫_ℝ) (t : α)
    (hM : ContinuousAt (fun s => coefficientSobolevOperator period (K s)) t) :
    ContinuousAt (fun s => projectedSourceOperator period (K s) κ m c hc (hpos s)) t := by
  have hP := pressureSobolev_continuousAt period A K κ m c hc hpos t hM
  have hMP := hM.clm_comp hP
  exact hMP.const_sub (ContinuousLinearMap.id ℝ (SobolevSpace period q))

/-- Differentiating the genuine resolvent gives the actual Hq pressure derivative −P M′ P. -/
theorem pressureSobolev_hasDerivAt {q : ℕ}
    (A : ℝ → SmoothCoefficient period) (K : ∀ s, CoefficientJet period standardDirection q (A s))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ s x v, c * ‖v‖ ^ 2 ≤ ⟪(A s).coefficient x v, v⟫_ℝ)
    (t : ℝ) (M' : SobolevSpace period q →L[ℝ] SobolevSpace period q)
    (hM : HasDerivAt (fun s => coefficientSobolevOperator period (K s)) M' t) :
    HasDerivAt (fun s => pressureSobolevOperator period (K s) κ m c hc (hpos s))
      (-((pressureSobolevOperator period (K t) κ m c hc (hpos t)).comp
        (M'.comp (pressureSobolevOperator period (K t) κ m c hc (hpos t))))) t := by
  apply hasDerivAt_of_resolvent
    (fun s => pressureSobolevOperator period (K s) κ m c hc (hpos s))
    (fun s => coefficientSobolevOperator period (K s)) _ t M' hM
  intro s r
  exact pressure_resolvent period (K s) (K r) κ m c c hc hc (hpos s) (hpos r)

/-- The complete Sobolev pressure-corrected source has the actual derivative obtained by the product
rule. -/
theorem projectedSource_hasDerivAt {q : ℕ}
    (A : ℝ → SmoothCoefficient period) (K : ∀ s, CoefficientJet period standardDirection q (A s))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ s x v, c * ‖v‖ ^ 2 ≤ ⟪(A s).coefficient x v, v⟫_ℝ)
    (t : ℝ) (M' : SobolevSpace period q →L[ℝ] SobolevSpace period q)
    (hM : HasDerivAt (fun s => coefficientSobolevOperator period (K s)) M' t) :
    HasDerivAt (fun s => projectedSourceOperator period (K s) κ m c hc (hpos s))
      (-(M'.comp (pressureSobolevOperator period (K t) κ m c hc (hpos t)) +
        (coefficientSobolevOperator period (K t)).comp
          (-((pressureSobolevOperator period (K t) κ m c hc (hpos t)).comp
            (M'.comp (pressureSobolevOperator period (K t) κ m c hc (hpos t))))))) t := by
  have hP := pressureSobolev_hasDerivAt period A K κ m c hc hpos t M' hM
  have hMP := hM.clm_comp hP
  simpa only [zero_sub, Pi.sub_def, projectedSourceOperator] using
    (hasDerivAt_const t (ContinuousLinearMap.id ℝ (SobolevSpace period q))).sub hMP

end EulerSobolevCoefficientPressure

end
end

end

@[expose] public section

noncomputable section

namespace EulerCorrectionOperators

open MeasureTheory InnerProductSpace Set EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace
  EulerSobolevCoefficientPressure EulerQuadraticSource
open scoped Topology

variable {X Y T : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [TopologicalSpace T]

/-- Continuous coefficient multipliers act continuously on any fixed genuine bilinear product. -/
theorem postcompose_continuous (A : T → Y →L[ℝ] Y) (hA : Continuous A)
    (B : X →L[ℝ] X →L[ℝ] Y) : Continuous (fun t => postcompose (A t) B) :=
  ((ContinuousLinearMap.compL ℝ X Y Y).continuous.comp hA).clm_comp_const B

variable (period : ℝ) [Fact (0 < period)]

/-- Cache the standard `NormedAddCommGroup (SobolevSpace period q)` instance to shorten
typeclass synthesis. -/
local instance timeSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (SobolevSpace period q)` instance to shorten typeclass
synthesis. -/
local instance timeSobolevRealSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance
/-- Cache the standard `SeminormedAddCommGroup (SobolevSpace period (q+1) →L[ℝ] SobolevSpace
period (q+1) →L[ℝ] SobolevSpace period q)` instance to shorten typeclass synthesis. -/
local instance timeSobolevBilinearGroup (q : ℕ) : SeminormedAddCommGroup
    (SobolevSpace period (q+1) →L[ℝ] SobolevSpace period (q+1) →L[ℝ] SobolevSpace period q) :=
        inferInstance

/-- Time continuity of the actual order-zero quadratic terms. -/
theorem algebraicBilinear_continuous {q : ℕ} (hq : 6 ≤ q)
    (C : T → Fin 3 → SobolevSpace period q →L[ℝ] SobolevSpace period q)
    (hC : ∀ i, Continuous (fun t => C t i)) : Continuous (fun t => algebraicBilinear period hq (C
        t)) := by
  apply continuous_finsetSum
  intro i _
  exact postcompose_continuous (fun t => C t i) (hC i) (coordinateProduct period hq i)

/-- Time continuity of the literal transport-plus-algebraic Euler nonlinearity. -/
theorem eulerBilinear_continuous {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C : T → Fin 3 → SobolevSpace period q →L[ℝ] SobolevSpace period q)
    (hC : ∀ i, Continuous (fun t => C t i)) : Continuous (fun t => eulerBilinear period hq L hL (C
        t)) := by
  have ht : Continuous (fun _ : T => EulerSobolevTransport.transportBilinear period hq L hL) :=
      continuous_const
  exact ht.add (algebraicBilinear_continuous period hq C hC)

/-- The actual Sobolev pressure projection as a continuous coefficient path. -/
def pressureProjectionPath {q : ℕ}
    (G : T → SmoothCoefficient period) (K : ∀ t, CoefficientJet period standardDirection q (G t))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c * ‖v‖ ^ 2 ≤ ⟪(G t).coefficient x v, v⟫_ℝ)
    (hG : Continuous (fun t => coefficientSobolevOperator period (K t))) :
    C(T, SobolevSpace period q →L[ℝ] SobolevSpace period q) where
  toFun t := projectedSourceOperator period (K t) κ m c hc (hpos t)
  continuous_toFun := continuous_iff_continuousAt.mpr fun t =>
    projectedSource_continuousAt period G K κ m c hc hpos t hG.continuousAt

/-- Concrete coefficient data for equation (17): actual pressure, actual transport, and actual
order-zero coefficient multipliers. -/
def correctionCoefficients {q : ℕ} (hq : 6 ≤ q)
    (G : T → SmoothCoefficient period) (K : ∀ t, CoefficientJet period standardDirection q (G t))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c * ‖v‖ ^ 2 ≤ ⟪(G t).coefficient x v, v⟫_ℝ)
    (hG : Continuous (fun t => coefficientSobolevOperator period (K t)))
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C₀ : C(T, SobolevSpace period q →L[ℝ] SobolevSpace period q))
    (C : Fin 3 → C(T, SobolevSpace period q →L[ℝ] SobolevSpace period q))
    (z : C(T, SobolevSpace period (q + 1))) (r : C(T, SobolevSpace period q)) :
    Coefficients T (SobolevSpace period (q+1)) (SobolevSpace period q) where
  projection := pressureProjectionPath period G K κ m c hc hpos hG
  forcing := r
  linear := ⟨fun t => linearize (eulerBilinear period hq L hL (fun i => C i t))
      ((C₀ t).comp (truncateOperator period q)) (z t),
    linearize_continuous _ _ _ (eulerBilinear_continuous period hq L hL _ (fun i => (C
        i).continuous))
      (C₀.continuous.clm_comp_const (truncateOperator period q)) z.continuous⟩
  quadratic := ⟨fun t => eulerBilinear period hq L hL (fun i => C i t),
    eulerBilinear_continuous period hq L hL _ (fun i => (C i).continuous)⟩

/-- The correction is exactly pressure applied to the residual and the nonlinear increment about z.
-/
theorem correction_source_identity {q : ℕ} (hq : 6 ≤ q)
    (G : T → SmoothCoefficient period) (K : ∀ t, CoefficientJet period standardDirection q (G t))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c * ‖v‖ ^ 2 ≤ ⟪(G t).coefficient x v, v⟫_ℝ)
    (hG : Continuous (fun t => coefficientSobolevOperator period (K t)))
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C₀ : C(T, SobolevSpace period q →L[ℝ] SobolevSpace period q))
    (C : Fin 3 → C(T, SobolevSpace period q →L[ℝ] SobolevSpace period q))
    (z : C(T, SobolevSpace period (q + 1))) (r : C(T, SobolevSpace period q))
    (t : T) (e : SobolevSpace period (q + 1)) :
    (correctionCoefficients period hq G K κ m c hc hpos hG L hL C₀ C z r).apply t e =
      -(projectedSourceOperator period (K t) κ m c hc (hpos t)
        (r t + C₀ t (truncateOperator period q e) +
          eulerBilinear period hq L hL (fun i => C i t) (z t+e) (z t+e) -
          eulerBilinear period hq L hL (fun i => C i t) (z t) (z t))) := by
  change -(projectedSourceOperator period (K t) κ m c hc (hpos t)
    (r t + linearize (eulerBilinear period hq L hL (fun i => C i t))
      ((C₀ t).comp (truncateOperator period q)) (z t) e +
      eulerBilinear period hq L hL (fun i => C i t) e e)) = _
  congr 2
  simp only [linearize_apply, map_add, add_apply, ContinuousLinearMap.comp_apply]
  abel

/-- The actual nonlinear correction source is divergence-free for every input. -/
theorem correction_source_gradient_zero {q : ℕ} (hq : 6 ≤ q)
    (G : T → SmoothCoefficient period) (K : ∀ t, CoefficientJet period standardDirection q (G t))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c * ‖v‖ ^ 2 ≤ ⟪(G t).coefficient x v, v⟫_ℝ)
    (hG : Continuous (fun t => coefficientSobolevOperator period (K t)))
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C₀ : C(T, SobolevSpace period q →L[ℝ] SobolevSpace period q))
    (C : Fin 3 → C(T, SobolevSpace period q →L[ℝ] SobolevSpace period q))
    (z : C(T, SobolevSpace period (q + 1))) (r : C(T, SobolevSpace period q))
    (t : T) (e : SobolevSpace period (q + 1)) :
    gradientProjection period κ m (value period
      ((correctionCoefficients period hq G K κ m c hc hpos hG L hL C₀ C z r).apply t e)) = 0 := by
  rw [correction_source_identity]
  change gradientProjection period κ m (-value period (projectedSourceOperator period (K t) κ m c
      hc (hpos t) _)) = 0
  rw [map_neg, projectedSource_gradient_zero, neg_zero]

end EulerCorrectionOperators

end
end

end

section

/-! The local quadratic heat construction preserves the actual lifted divergence constraint. -/

@[expose] public section

noncomputable section

namespace EulerQuadraticSource

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerDivergenceFreeHeat
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Cache the standard `NormedAddCommGroup (SobolevSpace period q)` instance to shorten
typeclass synthesis. -/
local instance constraintSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (SobolevSpace period q)` instance to shorten typeclass
synthesis. -/
local instance constraintSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) :=
    inferInstance

/-- A local solution driven by the actual divergence-free projected source has zero lifted
divergence at every time. -/
theorem exists_local_quadratic_divergenceFree (q : ℕ) (ν : ℝ) (hν : 0 < ν) (S : ℝ) (hS : 0 < S)
    (κ : ℝ) (m : Vector3) (u₀ : SobolevSpace period (q + 1))
    (hu₀ : gradientProjection period κ m (value period u₀) = 0)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace period (q + 1)) (SobolevSpace period q))
    (hC : ∀ t u, gradientProjection period κ m (value period (C.apply t u)) = 0) :
    ∃ (T : ℝ) (hT : 0 < T) (hTS : T ≤ S),
      ∃ u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)),
        ‖u‖ ≤ ‖u₀‖+1 ∧ u ⟨0, le_rfl, hT.le⟩ = u₀ ∧
        (∀ t, value period (u t) ∈ divergenceFreeSpace period κ m) ∧
        ∀ t, u t = quadraticDuhamel period ν hν hT.le hTS C u₀ u t := by
  obtain ⟨T, hT, hTS, u, hu, hi, hsol⟩ := exists_local_quadratic_mild period q ν hν S hS u₀ C
  refine ⟨T, hT, hTS, u, hu, hi, ?_, hsol⟩
  let F := (C.comp (timeInclusion hTS)).apply
  have hF : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace period (q+1) => F p.1 p.2) :=
    (C.comp (timeInclusion hTS)).continuous
  have hz := mild_solution_preserves_gradient_zero period κ m ν hν T hT.le u₀ hu₀ F hF
    (fun t v => hC (timeInclusion hTS t) v) u hsol
  intro t
  exact (gradientEvaluation_zero_iff period κ m (u t)).mp (hz t)

end EulerQuadraticSource

end
end

end

@[expose] public section

noncomputable section

namespace EulerCorrectionOperators

open MeasureTheory InnerProductSpace Set EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace EulerSobolevTransport
  EulerSobolevCoefficientPressure EulerQuadraticSource
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Cache the standard `NormedAddCommGroup (SobolevSpace period q)` instance to shorten
typeclass synthesis. -/
local instance dataSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (SobolevSpace period q)` instance to shorten typeclass
synthesis. -/
local instance dataSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- An actual smooth spatial coefficient with its genuine finite Sobolev jet and continuous time
action. -/
structure CoefficientPath (q : ℕ) (T : Type*) [TopologicalSpace T] where
  /-- Coefficient of `CoefficientPath`, of type `T → SmoothCoefficient period`. -/
  coefficient : T → SmoothCoefficient period
  /-- Jet of `CoefficientPath`, of type `∀ t, CoefficientJet period standardDirection q
  (coefficient t)`. -/
  jet : ∀ t, CoefficientJet period standardDirection q (coefficient t)
  continuous : Continuous (fun t => coefficientSobolevOperator period (jet t))

/-- The path acts by actual pointwise multiplication at each time. -/
def CoefficientPath.operatorPath {q : ℕ} {T : Type*} [TopologicalSpace T]
    (A : CoefficientPath period q T) : C(T, SobolevSpace period q →L[ℝ] SobolevSpace period q) :=
  ⟨fun t => coefficientSobolevOperator period (A.jet t), A.continuous⟩

/-- The concrete coefficient and approximate-solution data of the viscous Euler error equation. -/
structure CorrectionData (q : ℕ) (T : Type*) [TopologicalSpace T] where
  /-- Κ of `CorrectionData`, of type `ℝ`. -/
  κ : ℝ
  /-- Direction of `CorrectionData`, of type `Vector3`. -/
  direction : Vector3
  scale_bound : |κ| ≤ 1
  direction_bound : ‖direction‖ ≤ 1
  /-- Metric of `CorrectionData`, of type `CoefficientPath period q T`. -/
  metric : CoefficientPath period q T
  /-- Coercivity of `CorrectionData`, of type `ℝ`. -/
  coercivity : ℝ
  coercivity_pos : 0 < coercivity
  metric_pos : ∀ t x v, coercivity * ‖v‖^2 ≤ ⟪(metric.coefficient t).coefficient x v,v⟫_ℝ
  /-- Linear of `CorrectionData`, of type `CoefficientPath period q T`. -/
  linear : CoefficientPath period q T
  /-- Quadratic of `CorrectionData`, of type `Fin 3 → CoefficientPath period q T`. -/
  quadratic : Fin 3 → CoefficientPath period q T
  /-- Approximation of `CorrectionData`, of type `C(T, SobolevSpace period (q+1))`. -/
  approximation : C(T, SobolevSpace period (q+1))
  /-- Residual of `CorrectionData`, of type `C(T, SobolevSpace period q)`. -/
  residual : C(T, SobolevSpace period q)

/-- The actual pressure-projected nonlinear correction source generated by the concrete data. -/
def CorrectionData.coefficients {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) :
    Coefficients T (SobolevSpace period (q+1)) (SobolevSpace period q) :=
  correctionCoefficients period hq D.metric.coefficient D.metric.jet D.κ D.direction D.coercivity
    D.coercivity_pos D.metric_pos D.metric.continuous (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    D.linear.operatorPath (fun i => (D.quadratic i).operatorPath) D.approximation D.residual

/-- The actual error source is exactly divergence-free; this property is derived from pressure
coercivity. -/
theorem CorrectionData.source_gradient_zero {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T) (u : SobolevSpace period (q + 1)) :
    gradientProjection period D.κ D.direction (value period ((D.coefficients period hq).apply t u))
        = 0 :=
  correction_source_gradient_zero period hq D.metric.coefficient D.metric.jet D.κ D.direction
      D.coercivity
    D.coercivity_pos D.metric_pos D.metric.continuous (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    D.linear.operatorPath (fun i => (D.quadratic i).operatorPath) D.approximation D.residual t u

/-- The actual Euler correction equation has a positive-time mild solution with zero initial error
and the genuine divergence constraint. -/
theorem exists_local_euler_correction {q : ℕ} (hq : 6 ≤ q) (ν : ℝ) (hν : 0 < ν)
    (S : ℝ) (hS : 0 < S) (D : CorrectionData period q (Icc (0 : ℝ) S)) :
    ∃ (T : ℝ) (hT : 0 < T) (hTS : T ≤ S),
      ∃ e : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)),
        ‖e‖ ≤ 1 ∧ e ⟨0, le_rfl, hT.le⟩ = 0 ∧
        (∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction) ∧
        ∀ t, e t = quadraticDuhamel period ν hν hT.le hTS (D.coefficients period hq) 0 e t := by
  have hzero : gradientProjection period D.κ D.direction (value period (0 : SobolevSpace period
      (q+1))) = 0 := map_zero _
  obtain ⟨T, hT, hTS, e, he, hi, hd, hsol⟩ := exists_local_quadratic_divergenceFree period q ν hν S
      hS
    D.κ D.direction 0 hzero (D.coefficients period hq) (D.source_gradient_zero period hq)
  exact ⟨T, hT, hTS, e, by simpa only [norm_zero, zero_add] using he, hi, hd, hsol⟩

end EulerCorrectionOperators
